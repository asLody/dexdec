use regex::{Regex, RegexBuilder};
use schemars::JsonSchema;
use serde::{Deserialize, Serialize};

const DEFAULT_RESULT_LIMIT: usize = 10_000;
const MAX_RESULT_LIMIT: usize = 50_000;
const RESULT_BATCH_SIZE: usize = 64;
const EXCERPT_WIDTH: usize = 240;
const EXCERPT_LEFT_CONTEXT: usize = 72;

#[derive(Debug, Clone, Deserialize, JsonSchema)]
#[serde(rename_all = "camelCase")]
pub struct CodeSearchRequestDto {
    pub query: String,
    #[serde(default)]
    pub match_case: bool,
    #[serde(default)]
    pub whole_word: bool,
    #[serde(default)]
    pub use_regex: bool,
    #[serde(default = "default_result_limit")]
    pub max_results: usize,
}

#[derive(Debug, Clone, Serialize, JsonSchema)]
#[serde(rename_all = "camelCase")]
pub struct CodeSearchMatchDto {
    pub class_descriptor: String,
    pub source_path: String,
    pub line: usize,
    pub column: usize,
    pub match_length: usize,
    pub excerpt: String,
    pub excerpt_match_start: usize,
}

#[derive(Debug, Clone, Serialize, JsonSchema)]
#[serde(
    tag = "type",
    rename_all = "camelCase",
    rename_all_fields = "camelCase"
)]
pub enum CodeSearchEventDto {
    Results {
        items: Vec<CodeSearchMatchDto>,
    },
    Progress {
        scanned_classes: usize,
        total_classes: usize,
        failed_classes: usize,
        matches: usize,
    },
}

#[derive(Debug, Clone, Serialize, JsonSchema)]
#[serde(rename_all = "camelCase")]
pub struct CodeSearchSummaryDto {
    pub scanned_classes: usize,
    pub total_classes: usize,
    pub failed_classes: usize,
    pub matches: usize,
    pub truncated: bool,
    pub elapsed_ms: u64,
}

pub trait CodeSearchObserver {
    /// Returns false when the consumer has gone away and scanning should stop.
    fn emit(&mut self, event: CodeSearchEventDto) -> bool;
}

pub struct CodeSearchDocument<'a> {
    pub class_descriptor: &'a str,
    pub source_path: &'a str,
    pub source: &'a str,
}

pub struct CodeSearchEngine {
    matcher: Regex,
    whole_word: bool,
    result_limit: usize,
    matches: usize,
    pending: Vec<CodeSearchMatchDto>,
    truncated: bool,
}

impl CodeSearchEngine {
    pub fn new(request: &CodeSearchRequestDto) -> Result<Self, CodeSearchError> {
        if request.query.is_empty() {
            return Err(CodeSearchError::EmptyQuery);
        }
        let pattern = if request.use_regex {
            request.query.clone()
        } else {
            regex::escape(&request.query)
        };
        let matcher = RegexBuilder::new(&pattern)
            .case_insensitive(!request.match_case)
            .multi_line(false)
            .build()
            .map_err(|error| CodeSearchError::InvalidPattern(error.to_string()))?;
        Ok(Self {
            matcher,
            whole_word: request.whole_word,
            result_limit: request.max_results.clamp(1, MAX_RESULT_LIMIT),
            matches: 0,
            pending: Vec::with_capacity(RESULT_BATCH_SIZE),
            truncated: false,
        })
    }

    pub fn scan(
        &mut self,
        document: CodeSearchDocument<'_>,
        observer: &mut dyn CodeSearchObserver,
    ) -> Result<(), CodeSearchError> {
        for (line_index, line) in document.source.lines().enumerate() {
            let ranges = self
                .matcher
                .find_iter(line)
                .filter(|matched| {
                    !matched.is_empty()
                        && self.accepts_word_boundary(line, matched.start(), matched.end())
                })
                .map(|matched| (matched.start(), matched.end()))
                .collect::<Vec<_>>();
            for (start, end) in ranges {
                if self.matches == self.result_limit {
                    self.truncated = true;
                    return Ok(());
                }
                self.pending.push(materialize_match(
                    &document,
                    line,
                    line_index + 1,
                    start,
                    end,
                ));
                self.matches += 1;
                if self.pending.len() == RESULT_BATCH_SIZE {
                    self.flush(observer)?;
                }
            }
        }
        Ok(())
    }

    pub fn finish(&mut self, observer: &mut dyn CodeSearchObserver) -> Result<(), CodeSearchError> {
        self.flush(observer)
    }

    pub fn matches(&self) -> usize {
        self.matches
    }

    pub fn truncated(&self) -> bool {
        self.truncated
    }

    fn accepts_word_boundary(&self, line: &str, start: usize, end: usize) -> bool {
        if !self.whole_word {
            return true;
        }
        let before = line[..start].chars().next_back();
        let after = line[end..].chars().next();
        !before.is_some_and(is_identifier_part) && !after.is_some_and(is_identifier_part)
    }

    fn flush(&mut self, observer: &mut dyn CodeSearchObserver) -> Result<(), CodeSearchError> {
        if self.pending.is_empty() {
            return Ok(());
        }
        let items = std::mem::replace(&mut self.pending, Vec::with_capacity(RESULT_BATCH_SIZE));
        observer
            .emit(CodeSearchEventDto::Results { items })
            .then_some(())
            .ok_or(CodeSearchError::ObserverClosed)
    }
}

fn materialize_match(
    document: &CodeSearchDocument<'_>,
    line: &str,
    line_number: usize,
    start: usize,
    end: usize,
) -> CodeSearchMatchDto {
    let characters = line.chars().collect::<Vec<_>>();
    let match_start = line[..start].chars().count();
    let match_end = match_start + line[start..end].chars().count();
    let mut excerpt_start = match_start.saturating_sub(EXCERPT_LEFT_CONTEXT);
    let mut excerpt_end = (excerpt_start + EXCERPT_WIDTH).min(characters.len());
    if excerpt_end < match_end {
        excerpt_end = match_end.min(characters.len());
        excerpt_start = excerpt_end.saturating_sub(EXCERPT_WIDTH);
    }
    let excerpt = characters[excerpt_start..excerpt_end].iter().collect();
    CodeSearchMatchDto {
        class_descriptor: document.class_descriptor.to_string(),
        source_path: document.source_path.to_string(),
        line: line_number,
        column: match_start + 1,
        match_length: match_end - match_start,
        excerpt,
        excerpt_match_start: match_start - excerpt_start,
    }
}

fn is_identifier_part(character: char) -> bool {
    character == '_' || character == '$' || character.is_alphanumeric()
}

const fn default_result_limit() -> usize {
    DEFAULT_RESULT_LIMIT
}

#[derive(Debug, thiserror::Error)]
pub enum CodeSearchError {
    #[error("the search query is empty")]
    EmptyQuery,
    #[error("invalid regular expression: {0}")]
    InvalidPattern(String),
    #[error("the search result consumer was closed")]
    ObserverClosed,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[derive(Default)]
    struct Collector(Vec<CodeSearchMatchDto>);

    impl CodeSearchObserver for Collector {
        fn emit(&mut self, event: CodeSearchEventDto) -> bool {
            if let CodeSearchEventDto::Results { items } = event {
                self.0.extend(items);
            }
            true
        }
    }

    fn request(query: &str) -> CodeSearchRequestDto {
        CodeSearchRequestDto {
            query: query.to_string(),
            match_case: false,
            whole_word: false,
            use_regex: false,
            max_results: 100,
        }
    }

    fn search(source: &str, request: CodeSearchRequestDto) -> Vec<CodeSearchMatchDto> {
        let mut engine = CodeSearchEngine::new(&request).unwrap();
        let mut collector = Collector::default();
        engine
            .scan(
                CodeSearchDocument {
                    class_descriptor: "Ltest/Search;",
                    source_path: "test/Search.java",
                    source,
                },
                &mut collector,
            )
            .unwrap();
        engine.finish(&mut collector).unwrap();
        collector.0
    }

    #[test]
    fn literal_search_is_case_insensitive_and_reports_source_coordinates() {
        let results = search("class Demo {\n    String Value;\n}", request("value"));
        assert_eq!(results.len(), 1);
        assert_eq!(results[0].line, 2);
        assert_eq!(results[0].column, 12);
        assert_eq!(results[0].excerpt_match_start, 11);
        assert_eq!(results[0].match_length, 5);
    }

    #[test]
    fn whole_word_uses_source_identifier_boundaries() {
        let mut query = request("task");
        query.whole_word = true;
        let results = search("task taskId $task task_value", query);
        assert_eq!(results.len(), 1);
        assert_eq!(results[0].column, 1);
    }

    #[test]
    fn regular_expression_and_result_limit_are_enforced() {
        let mut query = request(r"condition\d+");
        query.use_regex = true;
        query.max_results = 2;
        let mut engine = CodeSearchEngine::new(&query).unwrap();
        let mut collector = Collector::default();
        engine
            .scan(
                CodeSearchDocument {
                    class_descriptor: "Ltest/Search;",
                    source_path: "test/Search.java",
                    source: "condition1 condition2 condition3",
                },
                &mut collector,
            )
            .unwrap();
        engine.finish(&mut collector).unwrap();
        assert_eq!(collector.0.len(), 2);
        assert!(engine.truncated());
    }
}
