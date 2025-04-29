use anyhow::{bail, Result};
use async_compression::tokio::bufread::GzipDecoder;
#[cfg(feature = "extended")]
use charabia::Segment;
use either::Either;
use hashbrown::HashMap;
use lazy_static::lazy_static;
use pagefind_stem::{Algorithm, Stemmer};
use path_slash::PathExt as _;
use regex::Regex;
use std::collections::BTreeMap;
use std::io::Error;
use std::ops::Mul;
use std::path::{Path, PathBuf};
use tokio::fs::File;
use tokio::io::AsyncBufReadExt;
use tokio::io::{AsyncReadExt, BufReader};
use tokio::time::{sleep, Duration};

use crate::fragments::{PageAnchorData, PageFragment, PageFragmentData};
use crate::SearchOptions;
use parser::DomParser;

use self::parser::DomParserResult;
use self::splitting::get_discrete_words;

lazy_static! {
    static ref NEWLINES: Regex = Regex::new("(\n|\r\n)+").unwrap();
    static ref TRIM_NEWLINES: Regex = Regex::new("^[\n\r\\s]+|[\n\r\\s]+$").unwrap();
    static ref EXTRANEOUS_SPACES: Regex = Regex::new("\\s{2,}").unwrap();
    static ref PRIVATE_PAGEFIND: Regex = Regex::new("___PAGEFIND_[\\S]+\\s?").unwrap();
    // TODO: i18n?
    static ref SPECIAL_CHARS: Regex = Regex::new("[^\\w]").unwrap();
}

pub mod parser;
mod splitting;

#[derive(Debug, Clone, PartialEq)]
pub struct FossickedWord {
    pub position: u32,
    pub weight: u8,
}

#[derive(Debug, Clone)]
pub struct FossickedData {
    pub url: String,
    pub fragment: PageFragment,
    pub word_data: HashMap<String, Vec<FossickedWord>>,
    pub sort: BTreeMap<String, String>,
    pub has_custom_body: bool,
    pub force_inclusion: bool,
    pub has_html_element: bool,
    pub has_old_bundle_reference: bool,
    pub language: String,
}

#[derive(Debug)]
pub struct Fossicker {
    file_path: Option<PathBuf>,
    /// Built URLs should be relative to this directory
    root_path: Option<PathBuf>,
    page_url: Option<String>,
    synthetic_content: Option<String>,
    data: Option<DomParserResult>,
}

impl Fossicker {
    pub fn new_relative_to(file_path: PathBuf, root_path: PathBuf) -> Self {
        Self {
            file_path: Some(file_path),
            root_path: Some(root_path),
            page_url: None,
            synthetic_content: None,
            data: None,
        }
    }

    pub fn new_synthetic(
        file_path: Option<PathBuf>,
        page_url: Option<String>,
        contents: String,
    ) -> Self {
        Self {
            file_path,
            root_path: None,
            page_url,
            synthetic_content: Some(contents),
            data: None,
        }
    }

    pub fn new_with_data(url: String, data: DomParserResult) -> Self {
        Self {
            file_path: None,
            root_path: None,
            page_url: Some(url),
            synthetic_content: None,
            data: Some(data),
        }
    }

    async fn read_file(&mut self, options: &SearchOptions) -> Result<(), Error> {
        let Some(file_path) = &self.file_path else {
            return Ok(());
        }; // TODO: Change to thiserror
        let file = File::open(file_path).await?;

        let mut rewriter = DomParser::new(options);

        let mut br = BufReader::new(file);
        let mut buf = [0; 20000];

        let is_gzip = if let Ok(read) = br.fill_buf().await {
            read.len() >= 3 && read[0] == 0x1F && read[1] == 0x8B && read[2] == 0x08
        } else {
            false
        };

        if is_gzip {
            let mut br = GzipDecoder::new(br);
            while let Ok(read) = br.read(&mut buf).await {
                if read == 0 {
                    break;
                }
                if let Err(error) = rewriter.write(&buf[..read]) {
                    options.logger.error(format!(
                        "Failed to parse file {} — skipping this file. Error:\n{error}",
                        file_path.to_str().unwrap_or("[unknown file]"),
                    ));
                    return Ok(());
                }
            }
        } else {
            while let Ok(read) = br.read(&mut buf).await {
                if read == 0 {
                    break;
                }
                if let Err(error) = rewriter.write(&buf[..read]) {
                    options.logger.error(format!(
                        "Failed to parse file {} — skipping this file. Error:\n{error}",
                        file_path.to_str().unwrap_or("[unknown file]")
                    ));
                    return Ok(());
                }
            }
        }

        let mut data = rewriter.wrap();
        if let Some(forced_language) = &options.force_language {
            data.language = forced_language.clone();
        }

        self.data = Some(data);

        Ok(())
    }

    async fn read_synthetic(&mut self, options: &SearchOptions) -> Result<(), Error> {
        let Some(contents) = self.synthetic_content.as_ref() else {
            return Ok(());
        };

        let mut rewriter = DomParser::new(options);

        let mut br = BufReader::new(contents.as_bytes());
        let mut buf = [0; 20000];

        while let Ok(read) = br.read(&mut buf).await {
            if read == 0 {
                break;
            }
            if let Err(error) = rewriter.write(&buf[..read]) {
                options.logger.error(format!(
                    "Failed to parse file {} — skipping this file. Error:\n{error}",
                    &self
                        .file_path
                        .as_ref()
                        .map(|p| p.to_str())
                        .flatten()
                        .or(self.page_url.as_ref().map(|u| u.as_str()))
                        .unwrap_or("[unknown file]")
                ));
                return Ok(());
            }
        }

        let mut data = rewriter.wrap();
        if let Some(forced_language) = &options.force_language {
            data.language = forced_language.clone();
        }

        self.data = Some(data);

        Ok(())
    }

    fn parse_digest(
        &mut self,
    ) -> (
        String,
        HashMap<String, Vec<FossickedWord>>,
        Vec<(String, String, String, u32)>,
        usize,
    ) {
        let mut map: HashMap<String, Vec<FossickedWord>> = HashMap::new();
        let mut anchors = Vec::new();
        // TODO: push this error handling up a level and return an Err from parse_digest
        if self.data.as_ref().is_none() {
            return ("".into(), map, anchors, 0); // empty page result, will be dropped from search
        }
        let data = self.data.as_ref().unwrap();
        let stemmer = get_stemmer(&data.language);

        let mut content = String::with_capacity(data.digest.len());

        let mut store_word = |full_word: &str, word_index: usize, word_weight: u8| {
            let word = if let Some(stemmer) = &stemmer {
                stemmer.stem(&full_word).into_owned()
            } else {
                full_word.to_string()
            };

            let entry = FossickedWord {
                position: word_index.try_into().unwrap(),
                weight: word_weight,
            };
            if let Some(repeat) = map.get_mut(&word) {
                repeat.push(entry);
            } else {
                map.insert(word, vec![entry]);
            }
        };

        // TODO: Consider reading newlines and jump the word_index up some amount,
        // so that separate bodies of text don't return exact string
        // matches across the boundaries. Or otherwise use some marker byte for the boundary.

        // TODO: Configure this or use segmenting across all languages

        let segment_chunks = data.digest.split_whitespace();

        #[cfg(feature = "extended")]
        let should_segment = matches!(data.language.split('-').next().unwrap(), "zh" | "ja");

        #[cfg(feature = "extended")]
        let coarse_segments = segment_chunks.map(|seg| {
            if seg.starts_with("___") {
                Either::Left(seg)
            } else {
                if should_segment {
                    // Run a segmenter only for any languages which require it.
                    Either::Right(seg.segment_str())
                } else {
                    // Currently hesitant to run segmentation during indexing
                    // that we can't also run during search, since we don't
                    // ship a segmenter to the browser. This logic is easier
                    // to replicate in the JavaScript that parses a search query.
                    Either::Left(seg)
                }
            }
        });

        #[cfg(not(feature = "extended"))]
        let coarse_segments =
            segment_chunks.map(|s| Either::<&str, core::slice::Iter<&str>>::Left(s));

        let mut total_word_index = 0;
        let mut max_word_index = 0;
        let weight_multiplier = 24.0;
        let weight_max = 10.0;
        debug_assert!(((weight_max * weight_multiplier) as u8) < std::u8::MAX);

        let mut weight_stack: Vec<u8> = vec![(1.0 * weight_multiplier) as u8];

        let mut track_word = |word: &str, append_whitespace: bool| {
            if word.chars().next() == Some('_') {
                if word.starts_with("___PAGEFIND_ANCHOR___") {
                    if let Some((element_name, anchor_id)) =
                        word.replace("___PAGEFIND_ANCHOR___", "").split_once(':')
                    {
                        let element_text = data
                            .anchor_content
                            .get(anchor_id)
                            .map(|t| normalize_content(t))
                            .unwrap_or_default();

                        if let Some((_, element_id)) = anchor_id.split_once(':') {
                            anchors.push((
                                element_name.to_string(),
                                element_id.to_string(),
                                normalize_content(&element_text),
                                total_word_index as u32,
                            ));
                        }
                    }
                    return;
                }

                if word.starts_with("___PAGEFIND_WEIGHT___") {
                    let weight = word
                        .replace("___PAGEFIND_WEIGHT___", "")
                        .parse::<f32>()
                        .ok()
                        .unwrap_or(1.0);
                    if weight <= 0.0 {
                        weight_stack.push(0);
                    } else {
                        weight_stack.push(
                            (weight.clamp(0.0, weight_max).mul(weight_multiplier) as u8).max(1),
                        );
                    }
                    return;
                }

                // Auto weights are provided by the parser, and should only
                // apply if we aren't inside an explicitly weighted block,
                // in which case we should just inherit that weight.
                if word.starts_with("___PAGEFIND_AUTO_WEIGHT___") {
                    if weight_stack.len() == 1 {
                        let weight = word
                            .replace("___PAGEFIND_AUTO_WEIGHT___", "")
                            .parse::<f32>()
                            .ok()
                            .unwrap_or(1.0);
                        weight_stack
                            .push(weight.clamp(0.0, weight_max).mul(weight_multiplier) as u8);
                    } else {
                        weight_stack.push(weight_stack.last().cloned().unwrap_or_default());
                    }
                    return;
                }

                if word.starts_with("___END_PAGEFIND_WEIGHT___") {
                    weight_stack.pop();
                    return;
                }
            }

            // We use zero-width spaces as boundary values for some languages,
            // so we make sure that all are removed from the source content before going into the index.
            let normalized_word = word.replace('\u{200B}', "");
            if normalized_word.is_empty() {
                return;
            }

            content.push_str(&word.replace('\u{200B}', ""));
            if append_whitespace {
                content.push(' ');
            }
            #[cfg(feature = "extended")]
            if should_segment {
                content.push('\u{200B}');
            }
            let normalized_word = SPECIAL_CHARS
                .replace_all(word, "")
                .into_owned()
                .to_lowercase();

            let word_weight = weight_stack.last().unwrap_or(&1);
            if !normalized_word.is_empty() {
                store_word(&normalized_word, total_word_index, *word_weight);
            }

            // For words that may be CompoundWords, also index them as their constituent parts
            if normalized_word != word {
                let (word_parts, extras) = get_discrete_words(word);
                // Only proceed if the word was broken into multiple parts
                if word_parts.contains(|c: char| c.is_whitespace()) {
                    let part_words: Vec<_> = word_parts.split_whitespace().collect();

                    if !part_words.is_empty() {
                        // Index constituents of a compound word as a proportion of the
                        // weight of the full word.
                        let per_weight = if *word_weight == 0 {
                            0
                        } else {
                            (word_weight
                                / part_words.len().try_into().unwrap_or(std::u8::MAX))
                            .max(1)
                        };

                        // Only index two+ character words
                        for part_word in part_words.into_iter().filter(|w| w.len() > 1) {
                            store_word(part_word, total_word_index, per_weight);
                        }
                    }
                }
                // Additionally store any special extra characters we are given
                if let Some(extras) = extras {
                    for extra in extras {
                        store_word(&extra, total_word_index, *word_weight);
                    }
                }
            }

            max_word_index = total_word_index;
            total_word_index += 1;
        };

        for segment in coarse_segments {
            match segment {
                Either::Left(word) => {
                    track_word(word, true);
                }
                Either::Right(words) => {
                    let mut words = words.peekable();
                    while let Some(word) = words.next() {
                        track_word(word, words.peek().is_none());
                    }
                }
            };
        }
        if content.ends_with('\u{200B}') {
            content.pop();
        }
        if content.ends_with(' ') {
            content.pop();
        }
        (content, map, anchors, max_word_index + 1)
    }

    /// Removes private Pagefind sentinel values from content that would otherwise leak.
    /// This should probably be handled better by not inserting these flags here in the first place,
    /// though there's a chance we do want to process them when we arrive at indexing metadata.
    fn tidy_meta_and_filters(&mut self) {
        if let Some(data) = self.data.as_mut() {
            for filter in data.filters.values_mut() {
                for filter_val in filter.iter_mut() {
                    match PRIVATE_PAGEFIND.replace_all(filter_val, "") {
                        std::borrow::Cow::Borrowed(_) => { /* no-op, no replace happened */ }
                        std::borrow::Cow::Owned(s) => *filter_val = s,
                    }
                }
            }

            for meta in data.meta.values_mut() {
                match PRIVATE_PAGEFIND.replace_all(meta, "") {
                    std::borrow::Cow::Borrowed(_) => { /* no-op, no replace happened */ }
                    std::borrow::Cow::Owned(s) => *meta = s,
                }
            }
        }
    }

    async fn fossick_html(&mut self, options: &SearchOptions) {
        if self.synthetic_content.is_some() {
            while self.read_synthetic(options).await.is_err() {
                sleep(Duration::from_millis(1)).await;
            }
        } else {
            while self.read_file(options).await.is_err() {
                sleep(Duration::from_millis(1)).await;
            }
        }
    }

    pub async fn fossick(mut self, options: &SearchOptions) -> Result<FossickedData> {
        if (self.file_path.is_some() || self.synthetic_content.is_some()) && self.data.is_none() {
            self.fossick_html(options).await;
        };

        let (content, word_data, anchors, word_count) = self.parse_digest();
        self.tidy_meta_and_filters();

        let data = self.data.unwrap();
        let url = if let Some(url) = &self.page_url {
            url.clone()
        } else if let Some(path) = &self.file_path {
            if let Some(root) = &self.root_path {
                build_url(path, Some(root), options)
            } else {
                build_url(path, None, options)
            }
        } else {
            options
                .logger
                .error("Tried to index file with no specified URL or file path, ignoring.");
            bail!("Tried to index file with no specified URL or file path, ignoring.");
        };

        Ok(FossickedData {
            url: url.clone(),
            has_custom_body: data.has_custom_body,
            force_inclusion: data.force_inclusion,
            has_html_element: data.has_html_element,
            has_old_bundle_reference: data.has_old_bundle_reference,
            language: data.language,
            fragment: PageFragment {
                page_number: 0, // This page number is updated later once determined
                data: PageFragmentData {
                    url,
                    content,
                    filters: data.filters,
                    meta: data.meta,
                    word_count,
                    anchors: anchors
                        .into_iter()
                        .map(|(element, id, text, location)| PageAnchorData {
                            element,
                            id,
                            location,
                            text,
                        })
                        .collect(),
                },
            },
            word_data,
            sort: data.sort,
        })
    }
}

fn strip_index_html(url: &str) -> &str {
    if url.ends_with("/index.html") {
        &url[..url.len() - 10]
    } else if url == "index.html" {
        ""
    } else {
        url
    }
}

fn build_url(page_url: &Path, relative_to: Option<&Path>, options: &SearchOptions) -> String {
    let prefix = relative_to.unwrap_or(&options.site_source);

    let url = if let Ok(trimmed) = page_url.strip_prefix(prefix) {
        trimmed
    } else if page_url.is_relative() {
        page_url
    } else {
        options.logger.error(format!(
            "Absolute file was found that does not start with the source directory. Source: {:?}\nFile: {:?}",
            prefix,
            page_url
        ));
        return "/unknown/".to_string();
    };

    let final_url: String = if !options.keep_index_url {
        strip_index_html(&url.to_slash_lossy()).to_string()
    } else {
        url.to_slash_lossy().to_owned().to_string()
    };

    format!("/{}", final_url)
}

fn normalize_content(content: &str) -> String {
    let content = html_escape::decode_html_entities(content);
    let content = TRIM_NEWLINES.replace_all(&content, "");
    let content = NEWLINES.replace_all(&content, " ");
    let content = EXTRANEOUS_SPACES.replace_all(&content, " ");

    content.to_string()
}

// TODO: These language codes are duplicated with pagefind_web's Cargo.toml
fn get_stemmer(lang: &str) -> Option<Stemmer> {
    match lang.split('-').next().unwrap() {
        "ar" => Some(Stemmer::create(Algorithm::Arabic)),
        "hy" => Some(Stemmer::create(Algorithm::Armenian)),
        "eu" => Some(Stemmer::create(Algorithm::Basque)),
        "ca" => Some(Stemmer::create(Algorithm::Catalan)),
        "da" => Some(Stemmer::create(Algorithm::Danish)),
        "nl" => Some(Stemmer::create(Algorithm::Dutch)),
        "en" => Some(Stemmer::create(Algorithm::English)),
        "fi" => Some(Stemmer::create(Algorithm::Finnish)),
        "fr" => Some(Stemmer::create(Algorithm::French)),
        "de" => Some(Stemmer::create(Algorithm::German)),
        "el" => Some(Stemmer::create(Algorithm::Greek)),
        "hi" => Some(Stemmer::create(Algorithm::Hindi)),
        "hu" => Some(Stemmer::create(Algorithm::Hungarian)),
        "id" => Some(Stemmer::create(Algorithm::Indonesian)),
        "ga" => Some(Stemmer::create(Algorithm::Irish)),
        "it" => Some(Stemmer::create(Algorithm::Italian)),
        "lt" => Some(Stemmer::create(Algorithm::Lithuanian)),
        "ne" => Some(Stemmer::create(Algorithm::Nepali)),
        "no" => Some(Stemmer::create(Algorithm::Norwegian)),
        "pt" => Some(Stemmer::create(Algorithm::Portuguese)),
        "ro" => Some(Stemmer::create(Algorithm::Romanian)),
        "ru" => Some(Stemmer::create(Algorithm::Russian)),
        "sr" => Some(Stemmer::create(Algorithm::Serbian)),
        "es" => Some(Stemmer::create(Algorithm::Spanish)),
        "sv" => Some(Stemmer::create(Algorithm::Swedish)),
        "ta" => Some(Stemmer::create(Algorithm::Tamil)),
        "tr" => Some(Stemmer::create(Algorithm::Turkish)),
        "yi" => Some(Stemmer::create(Algorithm::Yiddish)),
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use crate::PagefindInboundConfig;
    use twelf::Layer;

    use super::*;

    #[test]
    fn normalizing_content() {
        let input = "\nHello  Wor\n ld? \n \n";
        let output = normalize_content(input);

        assert_eq!(&output, "Hello Wor ld?");
    }

    async fn test_fossick(s: String) -> Fossicker {
        std::env::set_var("PAGEFIND_SOURCE", "somewhere");
        let config =
            PagefindInboundConfig::with_layers(&[Layer::Env(Some("PAGEFIND_".into()))]).unwrap();
        let opts = SearchOptions::load(config).unwrap();

        let mut f = Fossicker {
            file_path: Some("test/index.html".into()),
            root_path: None,
            page_url: Some("/test/".into()),
            synthetic_content: Some(s),
            data: None,
        };

        _ = f.read_synthetic(&opts).await;

        f
    }

    #[tokio::test]
    async fn parse_file() {
        let mut f =
            test_fossick(["<html><body>", "<p>Hello World!</p>", "</body></html>"].concat()).await;

        let (digest, words, _, _) = f.parse_digest();

        assert_eq!(digest, "Hello World!".to_string());
        assert_eq!(
            words,
            HashMap::from_iter([
                (
                    "hello".to_string(),
                    vec![FossickedWord {
                        position: 0,
                        weight: 1 * 24
                    }]
                ),
                (
                    "world".to_string(),
                    vec![FossickedWord {
                        position: 1,
                        weight: 1 * 24
                    }]
                )
            ])
        );
    }

    #[tokio::test]
    async fn parse_weighted_file() {
        let mut f = test_fossick(
            [
                "<html><body>",
                "<div>The",
                "<p data-pagefind-weight='2'>Quick Brown</p>",
                "Fox",
                "<p data-pagefind-weight='0.5'>Jumps Over</p>",
                "<p data-pagefind-weight='0.00001'>Ryan</p></div>",
                "</body></html>",
            ]
            .concat(),
        )
        .await;

        let (digest, words, _, _) = f.parse_digest();

        assert_eq!(digest, "The Quick Brown. Fox Jumps Over. Ryan.".to_string());
        assert_eq!(
            words,
            HashMap::from_iter([
                (
                    "the".to_string(),
                    vec![FossickedWord {
                        position: 0,
                        weight: 1 * 24
                    }]
                ),
                (
                    "quick".to_string(),
                    vec![FossickedWord {
                        position: 1,
                        weight: 2 * 24
                    }]
                ),
                (
                    "brown".to_string(),
                    vec![FossickedWord {
                        position: 2,
                        weight: 2 * 24
                    }]
                ),
                (
                    "fox".to_string(),
                    vec![FossickedWord {
                        position: 3,
                        weight: 1 * 24
                    }]
                ),
                (
                    "jumps".to_string(),
                    vec![FossickedWord {
                        position: 4,
                        weight: 12
                    }]
                ),
                (
                    "over".to_string(),
                    vec![FossickedWord {
                        position: 5,
                        weight: 12
                    }]
                ),
                (
                    "ryan".to_string(),
                    vec![FossickedWord {
                        position: 6,
                        weight: 1
                    }]
                )
            ])
        );
    }

    #[tokio::test]
    async fn parse_auto_weighted_file() {
        let mut f = test_fossick(
            [
                "<html><body>",
                "<h1>Pagefind</h1>",
                "<h2>Pagefind</h2>",
                "<h3>Pagefind</h3>",
                "<h4>Pagefind</h4>",
                "<h5>Pagefind</h5>",
                "<h6>Pagefind</h6>",
                "<p>Pagefind</p>",
                "<div data-pagefind-weight='0'><h1>Pagefind</h1></div>",
                "</body></html>",
            ]
            .concat(),
        )
        .await;

        let (_, words, _, _) = f.parse_digest();

        assert_eq!(
            words,
            HashMap::from_iter([(
                "pagefind".to_string(),
                vec![
                    FossickedWord {
                        position: 0,
                        weight: 7 * 24
                    },
                    FossickedWord {
                        position: 1,
                        weight: 6 * 24
                    },
                    FossickedWord {
                        position: 2,
                        weight: 5 * 24
                    },
                    FossickedWord {
                        position: 3,
                        weight: 4 * 24
                    },
                    FossickedWord {
                        position: 4,
                        weight: 3 * 24
                    },
                    FossickedWord {
                        position: 5,
                        weight: 2 * 24
                    },
                    FossickedWord {
                        position: 6,
                        weight: 1 * 24
                    },
                    FossickedWord {
                        position: 7,
                        weight: 0 * 24
                    }
                ]
            )])
        );
    }
    
    #[tokio::test]
    async fn parse_zero_weighted_compound_words() {
        let mut f = test_fossick(
            [
                "<html><body>",
                "<div data-pagefind-weight='0'>",
                "<p>Simple text and compound.word.with.periods</p>",
                "</div>",
                "</body></html>",
            ]
            .concat(),
        )
        .await;

        let (_, words, _, _) = f.parse_digest();

        for (_, word_positions) in words {
            for position in word_positions {
                assert_eq!(position.weight, 0, "Expected all words to have weight 0");
            }
        }
    }

    #[tokio::test]
    async fn parse_bad_weights() {
        let mut f = test_fossick(
            [
                "<html><body>",
                "<p data-pagefind-weight='lots'>The</p>",
                "<p data-pagefind-weight='99999999'>Quick</p>",
                "<p data-pagefind-weight='-1234'>Brown</p>",
                "<p data-pagefind-weight='65.4'>Fox</p>",
                "</body></html>",
            ]
            .concat(),
        )
        .await;

        let (_, words, _, _) = f.parse_digest();

        assert_eq!(
            words,
            HashMap::from_iter([
                (
                    "the".to_string(),
                    vec![FossickedWord {
                        position: 0,
                        weight: 24
                    }]
                ),
                (
                    "quick".to_string(),
                    vec![FossickedWord {
                        position: 1,
                        weight: 240
                    }]
                ),
                (
                    "brown".to_string(),
                    vec![FossickedWord {
                        position: 2,
                        weight: 0
                    }]
                ),
                (
                    "fox".to_string(),
                    vec![FossickedWord {
                        position: 3,
                        weight: 240
                    }]
                )
            ])
        );
    }

    #[tokio::test]
    async fn parse_nbsp() {
        let mut f = test_fossick(
            [
                "<html lang='ja'><body>",
                "<p>Hello&nbsp;👋</p>",
                "</body></html>",
            ]
            .concat(),
        )
        .await;

        let (_, words, _, _) = f.parse_digest();

        let mut words = words.keys().collect::<Vec<_>>();
        words.sort();
        assert_eq!(words, vec!["hello", "👋"]);
    }

    #[cfg(feature = "extended")]
    #[tokio::test]
    async fn parse_weights_through_segmentation() {
        let mut f = test_fossick(
            [
                "<html lang='zh'><body>",
                "<h1 id='my-title'>哎呀！ 我的错。</h1>",
                "</body></html>",
            ]
            .concat(),
        )
        .await;

        let (content, words, _, _) = f.parse_digest();

        let mut words = words.keys().collect::<Vec<_>>();
        words.sort();
        assert_eq!(words, vec!["哎呀", "我", "的", "错"]);

        assert_eq!(
            content,
            "哎呀\u{200b}！ \u{200b}我\u{200b}的\u{200b}错\u{200b}。"
        );
    }

    #[cfg(feature = "extended")]
    #[tokio::test]
    async fn segmentation_parity_when_presplitting() {
        fn get_comparison_segmentations(full_input: &'static str) -> (Vec<String>, Vec<String>) {
            let chunked_input = full_input
                .split_whitespace()
                .filter(|w| !w.starts_with("___"))
                .collect::<Vec<_>>();
            let clean_input = chunked_input.join(" ");

            let mut legitimate_output = clean_input
                .as_str()
                .segment_str()
                .filter(|w| w.chars().any(|c| !c.is_whitespace()))
                .map(Into::into)
                .collect::<Vec<_>>();
            let mut chunked_output = chunked_input
                .into_iter()
                .flat_map(|inp| {
                    inp.segment_str()
                        .filter(|w| w.chars().any(|c| !c.is_whitespace()))
                        .collect::<Vec<_>>()
                })
                .map(Into::into)
                .collect::<Vec<_>>();

            legitimate_output.sort();
            chunked_output.sort();
            (legitimate_output, chunked_output)
        }
        {
            let full_zh_input = "___PAGEFIND_AUTO_WEIGHT___7 擁有遠端帳號權限 ___END_PAGEFIND_WEIGHT___

        我們建議大多數具有遠端帳號權限的使用者，採用 ___PAGEFIND_ANCHOR___a:0:my-link Certbot 這個 ACME 客戶端。它可以自動執行憑證的頒發、安裝，甚至不需要停止你的伺服器；Certbot 也提供專家模式，給不想要自動設定的使用者。Certbot 操作簡單，適用於許多系統；並且具有完善的文檔。參考 Certbot 官網，以獲取對於不同系統和網頁伺服器的操作說明。

        如果 Certbot 不能滿足你的需求，或是你想嘗試別的客戶端，還有很多 ACME 用戶端可供選擇。在你選定 ACME 客戶端軟體後，請參閱該客戶端的文檔。
        ___PAGEFIND_WEIGHT___44
        如果你正在嘗試使用不同的 ACME 用戶端，請使用我們的測試環境以免超過憑證頒發與更新的速率限制。
        沒有遠端帳號權限

        在沒有遠端帳號權限的情況下，最好的辦法是使用服務業者所提供的現有支援。如果你的業者支援 ___PAGEFIND_ANCHOR___a:1:my-second-link Let’s Encrypt，那麼他們就能幫助你申請免費憑證；安裝並設定自動更新。某些業者會需要你在控制介面或聯繫客服以開啟 Let’s Encrypt 服務。也有些業者會為所有客戶自動設定並安裝憑證。

        查看支援 Let’s Encrypt 的業者列表，確認你提供商的是否有出現在列表上。如果有的話，請按照他們的文檔設定 Let’s Encrypt 憑證。 ___END_PAGEFIND_WEIGHT___";

            let (legitimate_zh_output, chunked_zh_output) =
                get_comparison_segmentations(full_zh_input);
            assert_eq!(legitimate_zh_output, chunked_zh_output);
        }

        {
            let full_zh_cn_input = "没有命令行访问权限

        在没有命令行访问权限的情况下，___PAGEFIND_AUTO_WEIGHT___7 最好的办法是使用您托管服务提供商提供的内置功能。 支持 Let’s Encrypt 的服务商能替您自动完成免费证书的申请、安装、续期步骤。 某些服务商可能需要您在控制面板中开启相关选项， 也有一些服务商会自动为所有客户申请并安装证书。

        如果您的服务商存在于我们的服务商列表中， 参照其文档设置 Let’s Encrypt ___END_PAGEFIND_WEIGHT___ 证书即可。

        如果您的托管服务提供商不支持 ___PAGEFIND_ANCHOR___a:0:my-link Let’s Encrypt，您可以与他们联系请求支持。 我们尽力使添加 Let’s Encrypt 支持变得非常容易，提供商（注：非中国国内提供商）通常很乐意听取客户的建议！

        如果您的托管服务提供商不想集成 Let’s Encrypt，但支持上传自定义证书，您可以在自己的计算机上安装 Certbot 并使用手动模式（Manual Mode）。 在手动模式下，您需要将指定文件上传到您的网站以证明您的控制权。 然后，Certbot 将获取您可以上传到提供商的证书。 我们不建议使用此选项，因为它非常耗时，并且您需要在证书过期时重复此步骤。 对于大多数人来说，最好从提供商处请求 Let’s Encrypt 支持。若您的提供商不打算兼容，建议您更换提供商。
        获取帮助

        如果您对选择 ACME 客户端，使用特定客户端或与 Let’s Encrypt 相关的任何其他内容有疑问，请前往我们的社区论坛获取帮助。";

            let (legitimate_zh_cn_output, chunked_zh_cn_output) =
                get_comparison_segmentations(full_zh_cn_input);
            assert_eq!(legitimate_zh_cn_output, chunked_zh_cn_output);
        }

        {
            let full_ja_input = "___PAGEFIND_AUTO_WEIGHT___7 シェルへのアクセス権を持っている場合

            シェルアクセスができるほとんどの人には、Certbot という ACME クライアントを使うのがおすすめです。 ___END_PAGEFIND_WEIGHT___ 証明書の発行とインストールを、ダウンタイムゼロで自動化できます。 自動設定を使いたくない人のために、エキスパートモードも用意されています。 とても簡単に使え、多数のオペレーティングシステムで動作し、たくさんのドキュメントもあります。 Certbot のウェブサイトでは、各オペレーティングシステムやウェブサーバーごとの個別の設定方法について解説されています。

            Certbot があなたの要件を満たさない場合や、他のクライアントを試してみたい場合には、Certbot の他にもたくさんの ACME クライアントが利用できます。 ACME クライアントを自分で選んだ場合は、そのクライアントのドキュメントを参照してください。

            別の ACME クライアントを使って実験を行う場合は、 ___PAGEFIND_ANCHOR___a:0:my-link 私たちが用意したステージング環境を利用して、レート・リミットの制限を受けないように気をつけてください。
            シェルへのアクセス権を持っていない場合

            シェルアクセスができない場合に Let’s Encrypt を利用する一番良い方法は、ホスティング・プロバイダが用意したサポートを利用することです。 もし、あなたが利用するホスティング・プロバイダが Let’s Encrypt をサポートしている場合、あなたの代わりに無料の証明書をリクエスト、インストールし、自動的に最新の状態に更新してくれます。 一部のホスティング・プロバイダでは、この機能は自分で設定から有効にする必要がある場合があります。 それ以外のプロバイダでは、すべてのユーザーのために、自動で証明書が発行・インストールされるようになっています。

            あなたが利用しているホスティング・プロバイダが Let’s Encrypt をサポートしているかどうかは、 ホスティング・プロバイダのリストで確認してください。 もしサポートされている場合は、ホスティング・プロバイダのドキュメンに書かれている Let’s Encrypt の設定方法に従ってください。";

            let (legitimate_ja_output, chunked_ja_output) =
                get_comparison_segmentations(full_ja_input);
            assert_eq!(legitimate_ja_output, chunked_ja_output);
        }
    }

    #[cfg(not(target_os = "windows"))]
    #[test]
    fn building_url() {
        std::env::set_var("PAGEFIND_SITE", "hello/world");
        let config =
            PagefindInboundConfig::with_layers(&[Layer::Env(Some("PAGEFIND_".into()))]).unwrap();
        let opts = SearchOptions::load(config).unwrap();

        let cwd = std::env::current_dir().unwrap();

        let p: PathBuf = cwd.join::<PathBuf>("hello/world/index.html".into());
        assert_eq!(&build_url(&p, None, &opts), "/");

        let p: PathBuf = cwd.join::<PathBuf>("hello/world/about/index.html".into());
        assert_eq!(&build_url(&p, None, &opts), "/about/");

        let p: PathBuf = cwd.join::<PathBuf>("hello/world/about.html".into());
        assert_eq!(&build_url(&p, None, &opts), "/about.html");

        let p: PathBuf = cwd.join::<PathBuf>("hello/world/about/index.htm".into());
        assert_eq!(&build_url(&p, None, &opts), "/about/index.htm");

        let p: PathBuf = cwd.join::<PathBuf>("hello/world/index.html".into());
        let root: PathBuf = cwd.join::<PathBuf>("hello".into());
        assert_eq!(&build_url(&p, Some(&root), &opts), "/world/");
    }

    #[cfg(target_os = "windows")]
    #[test]
    fn building_windows_urls() {
        std::env::set_var("PAGEFIND_SITE", "C:\\hello\\world");
        let config =
            PagefindInboundConfig::with_layers(&[Layer::Env(Some("PAGEFIND_".into()))]).unwrap();
        let opts = SearchOptions::load(config).unwrap();

        let p: PathBuf = "C:\\hello\\world\\index.html".into();
        assert_eq!(&build_url(&p, None, &opts), "/");

        let p: PathBuf = "C:\\hello\\world\\about\\index.html".into();
        assert_eq!(&build_url(&p, None, &opts), "/about/");

        let p: PathBuf = "C:\\hello\\world\\about\\index.htm".into();
        assert_eq!(&build_url(&p, None, &opts), "/about/index.htm");
    }
}
