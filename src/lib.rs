//! # Ansi-cut
//!
//! A library which provides a set of methods to work with colored strings (by ansi sequences).
//!
//! Its a library agnostic library.
//! Therefore it can be used with any ansi color library. (e.g. [owo-colors](https://crates.io/crates/owo-colors), [nu-ansi-term ](https://crates.io/crates/nu-ansi-term)).
//!
//! # Example
//!
//! ```
//! use owo_colors::*;
//! use ansi_str::AnsiStr;
//! let hello = "Hello World!".red().to_string();
//! let (hello, world) = hello.ansi_split_at(6);
//! println!("{}", hello);
//! println!("{}", world);
//! ```
//!
//! ## Note
//!
//! The library doesn't guarantee to keep style of usage of ansi sequences.
//!  
//! For example if your string is `"\u{1b}[31;40mTEXT\u{1b}[0m"` and you will call get method.
//! It may not use `"\u{1b}[31;40m"` but it use it as `"\u{1b}[31m"` and `"\u{1b}[40m"`.
//!
//! Why that matters is because for example the following code example is not guaranteed to be true.
//!
//! ```,ignore
//! let hello1 = "Hello World!".red();
//! let hello2 = hello.ansi_get(..).unwrap();
//! assert_eq!(hello1, hello2)
//! ```

// todo: refactoring to use an iterator over chars and it hold a state for each of the chars?
// todo: Maybe it's worth to create some type like AnsiString which would not necessarily allocate String underthehood

// todo: Quickcheck tests
// todo: README.md

use ansi_parser::{AnsiParseIterator, AnsiParser, AnsiSequence, Output};
use std::borrow::Cow;
use std::fmt::Write;
use std::ops::{Bound, RangeBounds};

/// AnsiStr represents a list of functions to work with colored strings
/// defined as ANSI control sequences.
pub trait AnsiStr {
    /// Returns a substring of a string.
    ///
    /// It preserves accurate style of a substring.
    ///
    /// Range is defined in terms of `byte`s of the string not containing ANSI control sequences
    /// (If the string is stripped).
    ///
    /// This is the non-panicking alternative to `[Self::ansi_cut]`.
    /// Returns `None` whenever equivalent indexing operation would panic.
    ///
    /// Exceeding the boundaries of the string results in the
    /// same result if the upper boundary to be equal to the string length.
    ///
    /// If the text doesn't contains any ansi sequences the function must return result  if `[str::get]` was called.  
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use owo_colors::*;
    /// use ansi_str::AnsiStr;
    /// let v = "🗻 on the 🌏".red().to_string();
    ///
    /// assert_eq!(Some("🗻 on".red().to_string()), v.ansi_get(0..7));
    ///
    /// // indices not on UTF-8 sequence boundaries
    /// assert!(v.ansi_get(1..).is_none());
    /// assert!(v.ansi_get(..13).is_none());
    ///
    /// // going over boundries doesn't panic
    /// assert!(v.ansi_get(..std::usize::MAX).is_some());
    /// assert!(v.ansi_get(std::usize::MAX..).is_some());
    /// ```
    ///
    /// Text doesn't contain ansi sequences
    ///
    /// ```
    /// use ansi_str::AnsiStr;
    /// let v = "🗻 on the 🌏";
    ///
    /// assert_eq!(Some("on the 🌏".to_owned()), v.ansi_get(5..));
    /// ```
    fn ansi_get<I>(&self, i: I) -> Option<String>
    where
        I: RangeBounds<usize>;

    /// Cut makes a sub string, keeping the colors in the substring.
    ///
    /// The ANSI escape sequences are ignored when calculating the positions within the string.
    ///
    /// Range is defined in terms of `byte`s of the string not containing ANSI control sequences
    /// (If the string is stripped).
    ///
    /// Exceeding an upper bound does not panic.
    ///
    /// # Panics
    ///
    /// Panics if a start or end indexes are not on a UTF-8 code point boundary.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use owo_colors::*;
    /// use ansi_str::AnsiStr;
    /// let v = "🗻 on the 🌏".red().on_black().to_string();
    /// assert_eq!("🗻", v.ansi_cut(0..4).ansi_strip());
    /// assert_eq!("🗻 on", v.ansi_cut(..7).ansi_strip());
    /// assert_eq!("the 🌏", v.ansi_cut(8..).ansi_strip());
    /// ```
    ///
    /// Panics when index is not a valud UTF-8 char
    ///
    /// ```should_panic
    /// use owo_colors::*;
    /// use ansi_str::AnsiStr;
    /// let v = "🗻 on the 🌏".yellow().to_string();
    /// v.ansi_cut(1..);
    /// ```
    fn ansi_cut<I>(&self, i: I) -> String
    where
        I: RangeBounds<usize>;

    /// Checks that index-th byte is the first byte in a UTF-8 code point sequence or the end of the string.
    ///
    /// The index is determined in a string if it would be stripped.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use owo_colors::*;
    /// use ansi_str::AnsiStr;
    /// let s = "Löwe 老虎 Léopard".blue().to_string();
    /// assert!(s.ansi_is_char_boundary(0));
    /// // start of `老`
    /// assert!(s.ansi_is_char_boundary(6));
    /// assert!(s.ansi_is_char_boundary(s.ansi_strip().len()));
    ///
    /// // second byte of `ö`
    /// assert!(!s.ansi_is_char_boundary(2));
    ///
    /// // third byte of `老`
    /// assert!(!s.ansi_is_char_boundary(8));
    /// ```
    fn ansi_is_char_boundary(&self, index: usize) -> bool;

    /// Returns the byte index of the first character of this string slice that matches the pattern,
    /// considering the ansi sequences.
    ///
    /// Returns None if the pattern doesn’t match.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use owo_colors::*;
    /// use ansi_str::AnsiStr;
    /// let s = "Löwe 老虎 Léopard Gepardi".red().on_black().to_string();
    ///
    /// assert_eq!(s.ansi_find("L"), Some(0));
    /// assert_eq!(s.ansi_find("é"), Some(14));
    /// assert_eq!(s.ansi_find("pard"), Some(17));
    /// ```
    fn ansi_find(&self, pat: &str) -> Option<usize>;

    /// Returns a string with the prefix removed,
    /// considering the ansi sequences.
    ///
    /// If the string starts with the pattern prefix, returns substring after the prefix, wrapped in Some.
    ///
    /// If the string does not start with prefix, returns None.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use owo_colors::*;
    /// use ansi_str::AnsiStr;
    /// assert_eq!("foo:bar".red().to_string().ansi_strip_prefix("foo:"), Some("bar".red().to_string()));
    /// assert_eq!("foo:bar".red().to_string().ansi_strip_prefix("bar"), None);
    /// assert_eq!("foofoo".red().to_string().ansi_strip_prefix("foo"), Some("foo".red().to_string()));
    /// ```
    fn ansi_strip_prefix(&self, prefix: &str) -> Option<String>;

    /// Returns a string slice with the suffix removed,
    /// considering the ansi sequences.
    ///
    /// If the string ends with the pattern suffix, returns the substring before the suffix, wrapped in Some. Unlike trim_end_matches, this method removes the suffix exactly once.
    ///
    /// If the string does not end with suffix, returns None.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use owo_colors::*;
    /// use ansi_str::AnsiStr;
    /// assert_eq!("bar:foo".red().to_string().ansi_strip_suffix(":foo"), Some("bar".red().to_string()));
    /// assert_eq!("bar:foo".red().to_string().ansi_strip_suffix("bar"), None);
    /// assert_eq!("foofoo".red().to_string().ansi_strip_suffix("foo"), Some("foo".red().to_string()));
    /// ```
    fn ansi_strip_suffix(&self, pat: &str) -> Option<String>;

    /// An iterator over substrings of the string, separated by characters matched by a pattern.
    /// While keeping colors in substrings.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use owo_colors::*;
    /// use ansi_str::AnsiStr;
    ///
    /// let text = "Mary had a little lamb".red().to_string();
    ///
    /// let v: Vec<_> = text
    ///     .ansi_split(" ")
    ///     .collect();
    ///
    /// assert_eq!(
    ///     v,
    ///     [
    ///         "Mary".red().to_string(),
    ///         "had".red().to_string(),
    ///         "a".red().to_string(),
    ///         "little".red().to_string(),
    ///         "lamb".red().to_string(),
    ///     ]
    /// );
    ///
    /// let v: Vec<_> = "".ansi_split("X").collect();
    /// assert_eq!(v, [""]);
    ///
    /// let text = "lionXXtigerXleopard".red().to_string();
    /// let v: Vec<_> = text.ansi_split("X").collect();
    /// assert_eq!(v, ["lion".red().to_string(), "".to_string(), "tiger".red().to_string(), "leopard".red().to_string()]);
    ///
    /// let text = "lion::tiger::leopard".red().to_string();
    /// let v: Vec<_> = text.ansi_split("::").collect();
    /// assert_eq!(v, ["lion".red().to_string(), "tiger".red().to_string(), "leopard".red().to_string()]);
    /// ```
    fn ansi_split<'a>(&'a self, pat: &'a str) -> AnsiSplit<'a>;

    /// Divide one string into two at an index.
    /// While considering colors.
    ///
    /// The argument, mid, should be a byte offset from the start of the string.
    /// It must also be on the boundary of a UTF-8 code point.
    ///
    /// The two strings returned go from the start of the string to mid, and from mid to the end of the string.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use owo_colors::*;
    /// use ansi_str::AnsiStr;
    /// let s = "Per Martin-Löf".red().on_black().to_string();
    ///
    /// let (first, last) = s.ansi_split_at(3);
    ///
    /// assert_eq!("Per", first.ansi_strip());
    /// assert_eq!(" Martin-Löf", last.ansi_strip());
    /// ```
    fn ansi_split_at(&self, mid: usize) -> (String, String);

    /// Returns true if the given pattern matches a prefix of this string slice.
    /// Ignoring the ansi sequences.
    ///
    /// Returns false if it does not.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use owo_colors::*;
    /// use ansi_str::AnsiStr;
    /// let bananas = "bananas".red().on_black().to_string();
    ///
    /// assert!(bananas.ansi_starts_with("bana"));
    /// assert!(!bananas.ansi_starts_with("nana"));
    /// ```
    fn ansi_starts_with(&self, pat: &str) -> bool;

    /// Returns true if the given pattern matches a suffix of this string slice.
    /// Ignoring the ansi sequences.
    ///
    /// Returns false if it does not.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use owo_colors::*;
    /// use ansi_str::AnsiStr;
    /// let bananas = "bananas".red().on_black().to_string();
    ///
    /// assert!(bananas.ansi_ends_with("anas"));
    /// assert!(!bananas.ansi_ends_with("nana"));
    /// ```
    fn ansi_ends_with(&self, pat: &str) -> bool;

    /// Returns a string slice with leading and trailing whitespace removed.
    /// Ignoring the ansi sequences.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use owo_colors::*;
    /// use ansi_str::AnsiStr;
    /// let s = " Hello\tworld\t".red().to_string();
    ///
    /// assert_eq!("Hello\tworld".red().to_string(), s.ansi_trim());
    /// ```
    fn ansi_trim(&self) -> String;

    /// Returns a string with all ANSI sequences removed.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use owo_colors::*;
    /// use ansi_str::AnsiStr;
    /// let hello = "Hello World!".red().on_black().to_string();
    ///
    /// assert_eq!(hello.ansi_strip(), "Hello World!");
    /// ```
    fn ansi_strip(&self) -> String;

    /// Returns true if a string contains any ansi sequences.
    ///
    /// Returns false if it does not.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use owo_colors::*;
    /// use ansi_str::AnsiStr;
    ///
    /// assert!(!"Hi".ansi_has_any());
    /// assert!("Hi".red().to_string().ansi_has_any());
    /// ```
    fn ansi_has_any(&self) -> bool;
}

impl AnsiStr for str {
    fn ansi_get<I>(&self, i: I) -> Option<String>
    where
        I: RangeBounds<usize>,
    {
        let (lower, upper) = bounds_to_usize(i.start_bound(), i.end_bound());
        self::get(self, Some(lower), upper)
    }

    fn ansi_cut<I>(&self, i: I) -> String
    where
        I: RangeBounds<usize>,
    {
        self::cut(self, i)
    }

    fn ansi_is_char_boundary(&self, index: usize) -> bool {
        str::is_char_boundary(&self.ansi_strip(), index)
    }

    fn ansi_find(&self, pat: &str) -> Option<usize> {
        self::find(self, pat)
    }

    fn ansi_strip_prefix(&self, prefix: &str) -> Option<String> {
        self::strip_prefix(self, prefix)
    }

    fn ansi_strip_suffix(&self, suffix: &str) -> Option<String> {
        self::strip_suffix(self, suffix)
    }

    fn ansi_split_at(&self, mid: usize) -> (String, String) {
        self::split_at(self, mid)
    }

    fn ansi_starts_with(&self, pat: &str) -> bool {
        self::starts_with(self, pat)
    }

    fn ansi_ends_with(&self, pat: &str) -> bool {
        self::ends_with(self, pat)
    }

    fn ansi_trim(&self) -> String {
        self::trim(self)
    }

    fn ansi_strip(&self) -> String {
        strip_ansi_sequences(self)
    }

    fn ansi_has_any(&self) -> bool {
        self::has_any(self)
    }

    fn ansi_split<'a>(&'a self, pat: &'a str) -> AnsiSplit<'a> {
        AnsiSplit::new(pat, self)
    }
}

impl AnsiStr for String {
    fn ansi_get<I>(&self, i: I) -> Option<String>
    where
        I: RangeBounds<usize>,
    {
        AnsiStr::ansi_get(self.as_str(), i)
    }

    fn ansi_cut<I>(&self, i: I) -> String
    where
        I: RangeBounds<usize>,
    {
        AnsiStr::ansi_cut(self.as_str(), i)
    }

    fn ansi_is_char_boundary(&self, index: usize) -> bool {
        AnsiStr::ansi_is_char_boundary(self.as_str(), index)
    }

    fn ansi_find(&self, pat: &str) -> Option<usize> {
        AnsiStr::ansi_find(self.as_str(), pat)
    }

    fn ansi_strip_prefix(&self, prefix: &str) -> Option<String> {
        AnsiStr::ansi_strip_prefix(self.as_str(), prefix)
    }

    fn ansi_strip_suffix(&self, suffix: &str) -> Option<String> {
        AnsiStr::ansi_strip_suffix(self.as_str(), suffix)
    }

    fn ansi_split_at(&self, mid: usize) -> (String, String) {
        AnsiStr::ansi_split_at(self.as_str(), mid)
    }

    fn ansi_starts_with(&self, pat: &str) -> bool {
        AnsiStr::ansi_starts_with(self.as_str(), pat)
    }

    fn ansi_ends_with(&self, pat: &str) -> bool {
        AnsiStr::ansi_ends_with(self.as_str(), pat)
    }

    fn ansi_trim(&self) -> String {
        AnsiStr::ansi_trim(self.as_str())
    }

    fn ansi_strip(&self) -> String {
        AnsiStr::ansi_strip(self.as_str())
    }

    fn ansi_has_any(&self) -> bool {
        AnsiStr::ansi_has_any(self.as_str())
    }

    fn ansi_split<'a>(&'a self, pat: &'a str) -> AnsiSplit<'a> {
        AnsiStr::ansi_split(self.as_str(), pat)
    }
}

macro_rules! write_list {
    ($b:expr, $($c:tt)*) => {{
        $(
            let result = write!($b, "{}", $c);
            debug_assert!(result.is_ok());
        )*
    }};
}

fn cut<S, R>(string: S, bounds: R) -> String
where
    S: AsRef<str>,
    R: RangeBounds<usize>,
{
    let string = string.as_ref();
    let (start, end) = bounds_to_usize(bounds.start_bound(), bounds.end_bound());

    cut_str(string, start, end)
}

fn cut_str(string: &str, lower_bound: usize, upper_bound: Option<usize>) -> String {
    let mut ansi_state = AnsiState::default();
    let tokens = string.ansi_parse();
    let mut buf = String::new();
    let mut index = 0;

    '_tokens_loop: for token in tokens {
        match token {
            Output::TextBlock(text) => {
                let block_end_index = index + text.len();
                if lower_bound > block_end_index {
                    index += text.len();
                    continue;
                };

                let mut start = 0;
                if lower_bound > index {
                    start = lower_bound - index;
                }

                let mut end = text.len();
                let mut done = false;
                if let Some(upper_bound) = upper_bound {
                    if upper_bound >= index && upper_bound < block_end_index {
                        end = upper_bound - index;
                        done = true;
                    }
                }

                index += text.len();

                match text.get(start..end) {
                    Some(text) => {
                        buf.push_str(text);
                        if done {
                            break '_tokens_loop;
                        }
                    }
                    None => {
                        panic!("One of indexes are not on a UTF-8 code point boundary");
                    }
                }
            }
            Output::Escape(seq) => {
                write_list!(buf, seq);
                if let AnsiSequence::SetGraphicsMode(v) = seq {
                    update_ansi_state(&mut ansi_state, v.as_ref());
                }
            }
        }
    }

    complete_ansi_sequences(&ansi_state, &mut buf);

    buf
}

fn get(string: &str, lower_bound: Option<usize>, upper_bound: Option<usize>) -> Option<String> {
    let mut ansi_state = AnsiState::default();
    let tokens = string.ansi_parse();
    let mut buf = String::new();
    let mut index = 0;

    '_tokens_loop: for token in tokens {
        match token {
            Output::TextBlock(text) => {
                let block_end_index = index + text.len();
                let mut start = 0;
                if let Some(lower_bound) = lower_bound {
                    if lower_bound > block_end_index {
                        index += text.len();
                        continue;
                    }

                    if lower_bound > index {
                        start = lower_bound - index;
                    }
                }

                let mut end = text.len();
                let mut done = false;
                if let Some(upper_bound) = upper_bound {
                    if upper_bound >= index && upper_bound < block_end_index {
                        end = upper_bound - index;
                        done = true;
                    }
                }

                index += text.len();

                let text = text.get(start..end)?;
                buf.push_str(text);
                if done {
                    break '_tokens_loop;
                }
            }
            Output::Escape(seq) => {
                write_list!(buf, seq);
                if let AnsiSequence::SetGraphicsMode(v) = seq {
                    update_ansi_state(&mut ansi_state, v.as_ref());
                }
            }
        }
    }

    complete_ansi_sequences(&ansi_state, &mut buf);

    Some(buf)
}

fn split_at(string: &str, mid: usize) -> (String, String) {
    let mut ansi_state = AnsiState::default();
    let mut lhs = String::new();
    let mut rhs = String::new();
    let mut index = 0;

    let tokens = string.ansi_parse();
    '_tokens_loop: for token in tokens {
        match token {
            Output::TextBlock(text) => {
                let mut left = None;
                let mut right = None;

                if index <= mid && index + text.len() > mid {
                    let need = mid - index;
                    left = Some(&text[..need]);
                    right = Some(&text[need..]);
                } else if index <= mid {
                    left = Some(text);
                } else {
                    right = Some(text);
                }

                if let Some(text) = left {
                    if !text.is_empty() {
                        begin_ansi_sequences(&ansi_state, &mut lhs);
                        lhs.push_str(text);
                        complete_ansi_sequences(&ansi_state, &mut lhs);
                    }
                }

                if let Some(text) = right {
                    if !text.is_empty() {
                        begin_ansi_sequences(&ansi_state, &mut rhs);
                        rhs.push_str(text);
                        complete_ansi_sequences(&ansi_state, &mut rhs);
                    }
                }

                index += text.len();
            }
            Output::Escape(seq) => {
                if let AnsiSequence::SetGraphicsMode(v) = seq {
                    update_ansi_state(&mut ansi_state, v.as_ref());
                } else if index <= mid {
                    write_list!(lhs, seq);
                } else if index > mid {
                    write_list!(rhs, seq);
                }
            }
        }
    }

    (lhs, rhs)
}

fn strip_prefix(text: &str, mut pat: &str) -> Option<String> {
    let mut buf = String::new();

    for token in text.ansi_parse() {
        match token {
            Output::TextBlock(text) => {
                let is_stripped = pat.is_empty();
                if is_stripped {
                    buf.push_str(text);
                    continue;
                }

                if pat.len() <= text.len() {
                    match text.strip_prefix(pat) {
                        Some(text) => {
                            buf.push_str(text);
                            pat = "";
                        }
                        None => return None,
                    }
                } else {
                    match pat.get(..text.len()) {
                        Some(p) => {
                            match text.strip_prefix(p) {
                                Some(text) => {
                                    buf.push_str(text);
                                }
                                None => return None,
                            }

                            // its safe to use index because we already checked the split point
                            pat = &pat[text.len()..];
                        }
                        None => return None,
                    }
                }
            }
            Output::Escape(seq) => write_list!(buf, seq),
        }
    }

    Some(buf)
}

fn strip_suffix(text: &str, mut pat: &str) -> Option<String> {
    #[allow(clippy::needless_collect)]
    let tokens = text.ansi_parse().collect::<Vec<_>>();

    let mut buf = String::new();

    for token in tokens.into_iter().rev() {
        match token {
            Output::TextBlock(text) => {
                let is_stripped = pat.is_empty();
                if is_stripped {
                    buf.insert_str(0, text);
                    continue;
                }

                if pat.len() <= text.len() {
                    let text = text.strip_suffix(pat)?;
                    buf.insert_str(0, text);
                    pat = "";
                } else {
                    let split_index = pat.len() - text.len();
                    let p = pat.get(split_index..)?;
                    match text.strip_suffix(p) {
                        Some(text) => {
                            buf.insert_str(0, text);
                        }
                        None => return None,
                    }

                    // its safe to use index because we already checked the split point
                    pat = &pat[..split_index];
                }
            }
            Output::Escape(seq) => buf.insert_str(0, &seq.to_string()),
        }
    }

    Some(buf)
}

fn starts_with(text: &str, mut pat: &str) -> bool {
    for token in text.ansi_parse() {
        match token {
            Output::TextBlock(text) => {
                if pat.is_empty() {
                    return true;
                }

                if pat.len() <= text.len() {
                    return text.starts_with(pat);
                }

                // We take all the text here so nothing is dropped
                match pat.get(..text.len()) {
                    Some(p) => {
                        if !text.starts_with(p) {
                            return false;
                        }

                        // its safe to use index because we already checked the split point
                        pat = &pat[text.len()..];
                    }
                    None => return false,
                }
            }
            Output::Escape(_) => {}
        }
    }

    #[allow(clippy::let_and_return)]
    let pattern_checked = pat.is_empty();
    pattern_checked
}

fn ends_with(text: &str, pat: &str) -> bool {
    // Use strip because the manual implementaion would not be much faster
    text.ansi_strip().ends_with(pat)
}

fn trim(text: &str) -> String {
    let mut buf = String::new();
    let mut buf_ansi = String::new();
    let mut trimmed = false;

    for token in text.ansi_parse() {
        match token {
            Output::TextBlock(mut text) => {
                if !buf_ansi.is_empty() {
                    buf.push_str(&buf_ansi);
                    buf_ansi.clear();
                }

                if !trimmed {
                    text = text.trim_start();
                    if !text.is_empty() {
                        trimmed = true;
                    }
                }

                buf.push_str(text);
            }
            Output::Escape(seq) => {
                write_list!(buf_ansi, seq);
            }
        }
    }

    // probably we could check the lengh difference and reuse buf string
    let mut buf = buf.trim_end().to_owned();

    if !buf_ansi.is_empty() {
        buf.push_str(&buf_ansi);
    }

    buf
}

fn find(text: &str, pat: &str) -> Option<usize> {
    // Can we improve the algorithm?
    text.ansi_strip().find(pat)
}

fn has_any(text: &str) -> bool {
    for token in text.ansi_parse() {
        if matches!(token, Output::Escape(AnsiSequence::SetGraphicsMode(_))) {
            return true;
        }
    }

    false
}

pub struct AnsiSplit<'a> {
    split_iter: std::str::Split<'a, &'a str>,
    ansi_state: AnsiState,
}

impl<'a> AnsiSplit<'a> {
    fn new(pat: &'a str, text: &'a str) -> Self {
        Self {
            ansi_state: AnsiState::default(),
            split_iter: text.split(pat),
        }
    }
}

impl<'a> Iterator for AnsiSplit<'a> {
    type Item = Cow<'a, str>;

    fn next(&mut self) -> Option<Self::Item> {
        let mut part = Cow::Borrowed(self.split_iter.next()?);
        if part.is_empty() {
            return Some(part);
        }

        if is_ansi_state_set(&self.ansi_state) {
            let mut part_o = String::new();
            begin_ansi_sequences(&self.ansi_state, &mut part_o);
            part_o.push_str(&part);

            part = Cow::Owned(part_o);
        }

        let tokens = part.ansi_parse();
        for token in tokens {
            if let Output::Escape(AnsiSequence::SetGraphicsMode(v)) = token {
                update_ansi_state(&mut self.ansi_state, v.as_ref())
            }
        }

        if is_ansi_state_set(&self.ansi_state) {
            let mut part_o = part.into_owned();
            complete_ansi_sequences(&self.ansi_state, &mut part_o);

            part = Cow::Owned(part_o);
        }

        Some(part)
    }
}

/// This function returns a [Iterator] which produces a [AnsiBlock].
///
/// [AnsiBlock] represents a string with a consisten style.
///
/// # Example
///
/// ```
/// use owo_colors::*;
/// use ansi_str::get_blocks;
///
/// let message = format!("{} {}", "Hello".red(), "World".blue());
///
/// for block in get_blocks(&message) {
///     println!("{:?}", block.text());
/// }
/// ```
pub fn get_blocks(s: &str) -> AnsiBlockIter<'_> {
    AnsiBlockIter {
        buf: None,
        state: AnsiState::default(),
        tokens: s.ansi_parse(),
    }
}

/// An [Iterator] which produces a [AnsiBlock].
pub struct AnsiBlockIter<'a> {
    buf: Option<String>,
    tokens: AnsiParseIterator<'a>,
    state: AnsiState,
}

impl<'a> Iterator for AnsiBlockIter<'a> {
    type Item = AnsiBlock<'a>;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            match self.tokens.next()? {
                Output::TextBlock(text) => {
                    // todo: fix the clone to borrowing.
                    let text = match self.buf.take() {
                        Some(mut buf) => {
                            buf.push_str(text);
                            Cow::Owned(buf)
                        }
                        None => Cow::Borrowed(text),
                    };

                    return Some(AnsiBlock::new(text, self.state.clone()));
                }
                Output::Escape(seq) => match seq {
                    AnsiSequence::SetGraphicsMode(v) => update_ansi_state(&mut self.state, &v),
                    _ => {
                        let buf = match self.buf.as_mut() {
                            Some(buf) => buf,
                            None => {
                                self.buf = Some(String::new());
                                self.buf.as_mut().unwrap()
                            }
                        };

                        write_list!(buf, seq);
                    }
                },
            }
        }
    }
}

/// An structure which represents a text and it's grafic settings.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AnsiBlock<'a> {
    text: Cow<'a, str>,
    state: AnsiState,
}

impl<'a> AnsiBlock<'a> {
    fn new(text: Cow<'a, str>, state: AnsiState) -> Self {
        Self { text, state }
    }

    /// Text returns a text which is used in the [AnsiBlock].
    pub fn text(&self) -> &str {
        self.text.as_ref()
    }

    /// Has_ansi checks wheather any grafic sequences are set in the [AnsiBlock].
    pub fn has_ansi(&self) -> bool {
        is_ansi_state_set(&self.state)
    }

    /// Returns a [AnsiSequenceStart] object which can be used to produce a ansi sequences which sets the grafic mode.
    pub fn start(&self) -> AnsiSequenceStart<'_> {
        AnsiSequenceStart(&self.state)
    }

    /// Returns a [AnsiSequenceEnd] object which can be used to produce a ansi sequences which ends the grafic mode.
    pub fn end(&self) -> AnsiSequenceEnd<'_> {
        AnsiSequenceEnd(&self.state)
    }

    // todo: Add is_* methods
}

/// An object which can be used to produce a ansi sequences which sets the grafic mode,
/// through the [std::fmt::Display].
pub struct AnsiSequenceStart<'a>(&'a AnsiState);

impl std::fmt::Display for AnsiSequenceStart<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if !is_ansi_state_set(self.0) {
            return Ok(());
        }

        let mut b = String::new();
        begin_ansi_sequences(self.0, &mut b);
        b.fmt(f)?;
        Ok(())
    }
}

/// An object which can be used to produce a ansi sequences which ends the grafic mode,
/// through the [std::fmt::Display].
pub struct AnsiSequenceEnd<'a>(&'a AnsiState);

impl std::fmt::Display for AnsiSequenceEnd<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if !is_ansi_state_set(self.0) {
            return Ok(());
        }

        let mut b = String::new();
        complete_ansi_sequences(self.0, &mut b);
        b.fmt(f)?;
        Ok(())
    }
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
struct AnsiState {
    fg_color: Option<AnsiColor>,
    bg_color: Option<AnsiColor>,
    undr_color: Option<AnsiColor>,
    bold: bool,
    faint: bool,
    italic: bool,
    underline: bool,
    double_underline: bool,
    slow_blink: bool,
    rapid_blink: bool,
    inverse: bool,
    hide: bool,
    crossedout: bool,
    reset: bool,
    framed: bool,
    encircled: bool,
    font: Option<u8>,
    fraktur: bool,
    proportional_spacing: bool,
    overlined: bool,
    igrm_underline: bool,
    igrm_double_underline: bool,
    igrm_overline: bool,
    igrm_double_overline: bool,
    igrm_stress_marking: bool,
    superscript: bool,
    subscript: bool,
    unknown: bool,
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum AnsiColor {
    Bit4 { index: u8 },
    Bit8 { index: u8 },
    Bit24 { r: u8, g: u8, b: u8 },
}

fn is_ansi_state_set(state: &AnsiState) -> bool {
    state.fg_color.is_some()
        || state.bg_color.is_some()
        || state.undr_color.is_some()
        || state.bold
        || state.crossedout
        || state.double_underline
        || state.encircled
        || state.faint
        || state.fraktur
        || state.framed
        || state.hide
        || state.inverse
        || state.italic
        || state.overlined
        || state.proportional_spacing
        || state.rapid_blink
        || state.slow_blink
        || state.underline
        || state.subscript
        || state.superscript
        || state.igrm_double_overline
        || state.igrm_double_underline
        || state.igrm_overline
        || state.igrm_stress_marking
        || state.igrm_underline
        || (state.reset && state.unknown)
}

fn update_ansi_state(state: &mut AnsiState, mode: &[u8]) {
    let mut ptr = mode;
    loop {
        if ptr.is_empty() {
            break;
        }

        let tag = ptr[0];

        match tag {
            0 => {
                *state = AnsiState::default();
                state.reset = true;
            }
            1 => state.bold = true,
            2 => state.faint = true,
            3 => state.italic = true,
            4 => state.underline = true,
            5 => state.slow_blink = true,
            6 => state.rapid_blink = true,
            7 => state.inverse = true,
            8 => state.hide = true,
            9 => state.crossedout = true,
            10 => state.font = None,
            n @ 11..=19 => state.font = Some(n),
            20 => state.fraktur = true,
            21 => state.double_underline = true,
            22 => {
                state.faint = false;
                state.bold = false;
            }
            23 => {
                state.italic = false;
            }
            24 => {
                state.underline = false;
                state.double_underline = false;
            }
            25 => {
                state.slow_blink = false;
                state.rapid_blink = false;
            }
            26 => {
                state.proportional_spacing = true;
            }
            27 => {
                state.inverse = false;
            }
            28 => {
                state.hide = false;
            }
            29 => {
                state.crossedout = false;
            }
            n @ 30..=37 | n @ 90..=97 => {
                state.fg_color = Some(AnsiColor::Bit4 { index: n });
            }
            38 => {
                if ptr.len() > 2 {
                    if let Some((color, n)) = parse_ansi_color(&ptr[1..]) {
                        state.fg_color = Some(color);
                        ptr = &ptr[n..];
                    }
                }

                // fixme: if connditions are not meat we must set unknown
            }
            39 => {
                state.fg_color = None;
            }
            n @ 40..=47 | n @ 100..=107 => {
                state.bg_color = Some(AnsiColor::Bit4 { index: n });
            }
            48 => {
                if ptr.len() > 2 {
                    if let Some((color, n)) = parse_ansi_color(&ptr[1..]) {
                        state.bg_color = Some(color);
                        ptr = &ptr[n..];
                    }
                }
            }
            49 => {
                state.bg_color = None;
            }
            50 => {
                state.proportional_spacing = false;
            }
            51 => {
                state.framed = true;
            }
            52 => {
                state.encircled = true;
            }
            53 => {
                state.overlined = true;
            }
            54 => {
                state.encircled = false;
                state.framed = false;
            }
            55 => {
                state.overlined = false;
            }
            58 => {
                if ptr.len() > 2 {
                    if let Some((color, n)) = parse_ansi_color(&ptr[1..]) {
                        state.undr_color = Some(color);
                        ptr = &ptr[n..];
                    }
                }
            }
            59 => {
                state.undr_color = None;
            }
            60 => {
                state.igrm_underline = true;
            }
            61 => {
                state.igrm_double_underline = true;
            }
            62 => {
                state.igrm_overline = true;
            }
            63 => {
                state.igrm_double_overline = true;
            }
            64 => {
                state.igrm_stress_marking = true;
            }
            65 => {
                state.igrm_underline = false;
                state.igrm_double_underline = false;
                state.igrm_overline = false;
                state.igrm_double_overline = false;
                state.igrm_stress_marking = false;
            }
            73 => {
                state.superscript = true;
            }
            74 => {
                state.subscript = true;
            }
            75 => {
                state.subscript = false;
                state.superscript = false;
            }
            _ => {
                state.unknown = true;
            }
        }

        ptr = &ptr[1..];
    }
}

// ansi parser skips `;` chars
//
// todo: open issue in ansi parse
// because it provides not bytes as they appear but bytes as parsed ints
fn parse_ansi_color(buf: &[u8]) -> Option<(AnsiColor, usize)> {
    match buf {
        [5, index, ..] => Some((AnsiColor::Bit8 { index: *index }, 2)),
        [2, r, g, b, ..] => Some((
            AnsiColor::Bit24 {
                r: *r,
                g: *g,
                b: *b,
            },
            4,
        )),
        _ => None,
    }
}

enum ColorType {
    Bg,
    Fg,
    Undr,
}

fn complete_ansi_sequences(state: &AnsiState, buf: &mut String) {
    macro_rules! emit_static {
        ($s:expr) => {
            buf.push_str(concat!("\u{1b}[", $s, "m"))
        };
    }

    if state.unknown && state.reset {
        emit_static!("0");
    }

    if state.font.is_some() {
        emit_static!("10");
    }

    if state.bold || state.faint {
        emit_static!("22");
    }

    if state.italic {
        emit_static!("23");
    }

    if state.underline || state.double_underline {
        emit_static!("24");
    }

    if state.slow_blink || state.rapid_blink {
        emit_static!("25");
    }

    if state.inverse {
        emit_static!("28");
    }

    if state.crossedout {
        emit_static!("29");
    }

    if state.fg_color.is_some() {
        emit_static!("39");
    }

    if state.bg_color.is_some() {
        emit_static!("49");
    }

    if state.proportional_spacing {
        emit_static!("50");
    }

    if state.encircled || state.framed {
        emit_static!("54");
    }

    if state.overlined {
        emit_static!("55");
    }

    if state.igrm_underline
        || state.igrm_double_underline
        || state.igrm_overline
        || state.igrm_double_overline
        || state.igrm_stress_marking
    {
        emit_static!("65");
    }

    if state.undr_color.is_some() {
        emit_static!("59");
    }

    if state.subscript || state.superscript {
        emit_static!("75");
    }

    if state.unknown {
        emit_static!("0");
    }
}

fn begin_ansi_sequences(state: &AnsiState, buf: &mut String) {
    macro_rules! emit_char {
        ($s:expr) => {
            buf.push('\u{1b}');
            buf.push('[');
            buf.push($s);
            buf.push('m');
        };
    }

    macro_rules! emit_str {
        ($s:expr) => {
            buf.push('\u{1b}');
            buf.push('[');
            buf.push_str($s);
            buf.push('m');
        };
    }

    macro_rules! emit_color {
        ($color:expr, $t:expr) => {{
            buf.push('\u{1b}');
            buf.push('[');

            emit_ansi_color($color, $t, buf);

            buf.push('m');
        }};
    }

    macro_rules! emit_byte {
        ($b:expr) => {{
            buf.push('\u{1b}');
            buf.push('[');
            buf.push(char::from($b));
            buf.push('m');
        }};
    }

    if state.bold {
        emit_char!('1');
    }

    if state.faint {
        emit_char!('2');
    }

    if state.italic {
        emit_char!('3');
    }

    if state.underline {
        emit_char!('4');
    }

    if state.slow_blink {
        emit_char!('5');
    }

    if state.rapid_blink {
        emit_char!('6');
    }

    if state.inverse {
        emit_char!('7');
    }

    if state.hide {
        emit_char!('8');
    }

    if state.crossedout {
        emit_char!('9');
    }

    if let Some(font) = state.font {
        emit_byte!(font);
    }

    if state.fraktur {
        emit_str!("20");
    }

    if state.double_underline {
        emit_str!("21");
    }

    if state.proportional_spacing {
        emit_str!("26");
    }

    if let Some(color) = &state.fg_color {
        emit_color!(color, ColorType::Fg);
    }

    if let Some(color) = &state.bg_color {
        emit_color!(color, ColorType::Bg);
    }

    if let Some(color) = &state.undr_color {
        emit_color!(color, ColorType::Undr);
    }

    if state.framed {
        emit_str!("51");
    }

    if state.encircled {
        emit_str!("52");
    }

    if state.overlined {
        emit_str!("53");
    }

    if state.igrm_underline {
        emit_str!("60");
    }

    if state.igrm_double_underline {
        emit_str!("61");
    }

    if state.igrm_overline {
        emit_str!("62");
    }

    if state.igrm_double_overline {
        emit_str!("63");
    }

    if state.igrm_stress_marking {
        emit_str!("64");
    }

    if state.superscript {
        emit_str!("73");
    }

    if state.subscript {
        emit_str!("74");
    }
}

fn emit_ansi_color(color: &AnsiColor, color_type: ColorType, buf: &mut String) {
    let first_byte = match color_type {
        ColorType::Bg => 48,
        ColorType::Fg => 38,
        ColorType::Undr => 58,
    };

    match *color {
        AnsiColor::Bit4 { index } => write_list!(buf, index),
        AnsiColor::Bit8 { index } => {
            write_list!(buf, first_byte);
            buf.push(';');
            buf.push('5');
            buf.push(';');
            write_list!(buf, index);
        }
        AnsiColor::Bit24 { r, g, b } => {
            write_list!(buf, first_byte);
            buf.push(';');
            buf.push('2');
            buf.push(';');
            write_list!(buf, r);
            buf.push(';');
            write_list!(buf, g);
            buf.push(';');
            write_list!(buf, b);
        }
    }
}

fn bounds_to_usize(left: Bound<&usize>, right: Bound<&usize>) -> (usize, Option<usize>) {
    match (left, right) {
        (Bound::Included(x), Bound::Included(y)) => (*x, Some(y + 1)),
        (Bound::Included(x), Bound::Excluded(y)) => (*x, Some(*y)),
        (Bound::Included(x), Bound::Unbounded) => (*x, None),
        (Bound::Unbounded, Bound::Unbounded) => (0, None),
        (Bound::Unbounded, Bound::Included(y)) => (0, Some(y + 1)),
        (Bound::Unbounded, Bound::Excluded(y)) => (0, Some(*y)),
        (Bound::Excluded(_), Bound::Unbounded)
        | (Bound::Excluded(_), Bound::Included(_))
        | (Bound::Excluded(_), Bound::Excluded(_)) => {
            unreachable!("A start bound can't be excluded")
        }
    }
}

fn strip_ansi_sequences(string: &str) -> String {
    let tokens = string.ansi_parse();
    let mut buf = String::new();
    for token in tokens {
        match token {
            Output::TextBlock(text) => {
                buf.push_str(text);
            }
            Output::Escape(_) => {}
        }
    }

    buf
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parse_ansi_color_test() {
        let tests: Vec<(&[u8], _)> = vec![
            (&[5, 200], Some(AnsiColor::Bit8 { index: 200 })),
            (&[5, 100, 123, 39], Some(AnsiColor::Bit8 { index: 100 })),
            (&[5, 100, 1, 2, 3], Some(AnsiColor::Bit8 { index: 100 })),
            (&[5, 1, 2, 3], Some(AnsiColor::Bit8 { index: 1 })),
            (&[5], None),
            (
                &[2, 100, 123, 39],
                Some(AnsiColor::Bit24 {
                    r: 100,
                    g: 123,
                    b: 39,
                }),
            ),
            (
                &[2, 100, 123, 39, 1, 2, 3],
                Some(AnsiColor::Bit24 {
                    r: 100,
                    g: 123,
                    b: 39,
                }),
            ),
            (
                &[2, 100, 123, 39, 1, 2, 3],
                Some(AnsiColor::Bit24 {
                    r: 100,
                    g: 123,
                    b: 39,
                }),
            ),
            (&[2, 100, 123], None),
            (&[2, 100], None),
            (&[2], None),
            (&[], None),
        ];

        for (i, (bytes, expected)) in tests.into_iter().enumerate() {
            assert_eq!(parse_ansi_color(bytes).map(|a| a.0), expected, "test={}", i);
        }
    }

    #[test]
    fn cut_colored_fg_test() {
        let colored_s = "\u{1b}[30mTEXT\u{1b}[39m";
        assert_eq!(colored_s, colored_s.ansi_cut(..));
        assert_eq!(colored_s, colored_s.ansi_cut(0..4));
        assert_eq!("\u{1b}[30mEXT\u{1b}[39m", colored_s.ansi_cut(1..));
        assert_eq!("\u{1b}[30mTEX\u{1b}[39m", colored_s.ansi_cut(..3));
        assert_eq!("\u{1b}[30mEX\u{1b}[39m", colored_s.ansi_cut(1..3));

        assert_eq!("TEXT", strip_ansi_sequences(&colored_s.ansi_cut(..)));
        assert_eq!("TEX", strip_ansi_sequences(&colored_s.ansi_cut(..3)));
        assert_eq!("EX", strip_ansi_sequences(&colored_s.ansi_cut(1..3)));

        let colored_s = "\u{1b}[30mTEXT\u{1b}[39m \u{1b}[31mTEXT\u{1b}[39m";
        assert_eq!(colored_s, colored_s.ansi_cut(..));
        assert_eq!(colored_s, colored_s.ansi_cut(0..9));
        assert_eq!(
            "\u{1b}[30mXT\u{1b}[39m \u{1b}[31mTEXT\u{1b}[39m",
            colored_s.ansi_cut(2..)
        );
        assert_eq!(
            "\u{1b}[30mTEXT\u{1b}[39m \u{1b}[31mT\u{1b}[39m",
            colored_s.ansi_cut(..6)
        );
        assert_eq!(
            "\u{1b}[30mXT\u{1b}[39m \u{1b}[31mT\u{1b}[39m",
            colored_s.ansi_cut(2..6)
        );

        assert_eq!("TEXT TEXT", strip_ansi_sequences(&colored_s.ansi_cut(..)));
        assert_eq!("TEXT T", strip_ansi_sequences(&colored_s.ansi_cut(..6)));
        assert_eq!("XT T", strip_ansi_sequences(&colored_s.ansi_cut(2..6)));

        assert_eq!("\u{1b}[30m\u{1b}[39m", cut("\u{1b}[30m\u{1b}[39m", ..));
    }

    #[test]
    fn cut_colored_bg_test() {
        let colored_s = "\u{1b}[40mTEXT\u{1b}[49m";
        assert_eq!(colored_s, colored_s.ansi_cut(..));
        assert_eq!(colored_s, colored_s.ansi_cut(0..4));
        assert_eq!("\u{1b}[40mEXT\u{1b}[49m", colored_s.ansi_cut(1..));
        assert_eq!("\u{1b}[40mTEX\u{1b}[49m", colored_s.ansi_cut(..3));
        assert_eq!("\u{1b}[40mEX\u{1b}[49m", colored_s.ansi_cut(1..3));

        // todo: determine if this is the right behaviour
        assert_eq!("\u{1b}[40m\u{1b}[49m", colored_s.ansi_cut(3..3));

        assert_eq!("TEXT", strip_ansi_sequences(&colored_s.ansi_cut(..)));
        assert_eq!("TEX", strip_ansi_sequences(&colored_s.ansi_cut(..3)));
        assert_eq!("EX", strip_ansi_sequences(&colored_s.ansi_cut(1..3)));

        let colored_s = "\u{1b}[40mTEXT\u{1b}[49m \u{1b}[41mTEXT\u{1b}[49m";
        assert_eq!(colored_s, colored_s.ansi_cut(..));
        assert_eq!(colored_s, colored_s.ansi_cut(0..9));
        assert_eq!(
            "\u{1b}[40mXT\u{1b}[49m \u{1b}[41mTEXT\u{1b}[49m",
            colored_s.ansi_cut(2..)
        );
        assert_eq!(
            "\u{1b}[40mTEXT\u{1b}[49m \u{1b}[41mT\u{1b}[49m",
            colored_s.ansi_cut(..6)
        );
        assert_eq!(
            "\u{1b}[40mXT\u{1b}[49m \u{1b}[41mT\u{1b}[49m",
            colored_s.ansi_cut(2..6)
        );

        assert_eq!("TEXT TEXT", strip_ansi_sequences(&colored_s.ansi_cut(..)));
        assert_eq!("TEXT T", strip_ansi_sequences(&colored_s.ansi_cut(..6)));
        assert_eq!("XT T", strip_ansi_sequences(&colored_s.ansi_cut(2..6)));

        assert_eq!("\u{1b}[40m\u{1b}[49m", cut("\u{1b}[40m\u{1b}[49m", ..));
    }

    #[test]
    fn cut_colored_bg_fg_test() {
        let colored_s = "\u{1b}[31;40mTEXT\u{1b}[0m";
        assert_eq!(
            "\u{1b}[31;40m\u{1b}[39m\u{1b}[49m",
            colored_s.ansi_cut(0..0)
        );
        assert_eq!(colored_s, colored_s.ansi_cut(..));
        assert_eq!(colored_s, colored_s.ansi_cut(0..4));
        assert_eq!("\u{1b}[31;40mEXT\u{1b}[0m", colored_s.ansi_cut(1..));
        assert_eq!(
            "\u{1b}[31;40mTEX\u{1b}[39m\u{1b}[49m",
            colored_s.ansi_cut(..3)
        );
        assert_eq!(
            "\u{1b}[31;40mEX\u{1b}[39m\u{1b}[49m",
            colored_s.ansi_cut(1..3)
        );

        assert_eq!("TEXT", strip_ansi_sequences(&colored_s.ansi_cut(..)));
        assert_eq!("TEX", strip_ansi_sequences(&colored_s.ansi_cut(..3)));
        assert_eq!("EX", strip_ansi_sequences(&colored_s.ansi_cut(1..3)));

        let colored_s = "\u{1b}[31;40mTEXT\u{1b}[0m \u{1b}[34;42mTEXT\u{1b}[0m";
        assert_eq!(colored_s, colored_s.ansi_cut(..));
        assert_eq!(colored_s, colored_s.ansi_cut(0..9));
        assert_eq!(
            "\u{1b}[31;40mXT\u{1b}[0m \u{1b}[34;42mTEXT\u{1b}[0m",
            colored_s.ansi_cut(2..)
        );
        assert_eq!(
            "\u{1b}[31;40mTEXT\u{1b}[0m \u{1b}[34;42mT\u{1b}[39m\u{1b}[49m",
            colored_s.ansi_cut(..6)
        );
        assert_eq!(
            "\u{1b}[31;40mXT\u{1b}[0m \u{1b}[34;42mT\u{1b}[39m\u{1b}[49m",
            colored_s.ansi_cut(2..6)
        );

        assert_eq!("TEXT TEXT", strip_ansi_sequences(&colored_s.ansi_cut(..)));
        assert_eq!("TEXT T", strip_ansi_sequences(&colored_s.ansi_cut(..6)));
        assert_eq!("XT T", strip_ansi_sequences(&colored_s.ansi_cut(2..6)));

        assert_eq!("\u{1b}[40m\u{1b}[49m", cut("\u{1b}[40m\u{1b}[49m", ..));
    }

    #[test]
    fn cut_keep_general_color_test() {
        assert_eq!(
            "\u{1b}[41m\u{1b}[30m\u{1b}[39m \u{1b}[34m12\u{1b}[39m\u{1b}[49m",
            "\u{1b}[41m\u{1b}[30msomething\u{1b}[39m \u{1b}[34m123123\u{1b}[39m\u{1b}[49m"
                .ansi_cut(9..12)
        );
    }

    #[test]
    fn cut_no_colored_str() {
        assert_eq!("something", cut("something", ..));
        assert_eq!("som", cut("something", ..3));
        assert_eq!("some", cut("something", ..=3));
        assert_eq!("et", cut("something", 3..5));
        assert_eq!("eth", cut("something", 3..=5));
        assert_eq!("ething", cut("something", 3..));
        assert_eq!("something", cut("something", ..));
        assert_eq!("", cut("", ..));
    }

    #[test]
    fn cut_dont_panic_on_exceeding_upper_bound() {
        assert_eq!("TEXT", cut("TEXT", ..50));
        assert_eq!("EXT", cut("TEXT", 1..50));
        assert_eq!(
            "\u{1b}[31;40mTEXT\u{1b}[0m",
            cut("\u{1b}[31;40mTEXT\u{1b}[0m", ..50)
        );
        assert_eq!(
            "\u{1b}[31;40mEXT\u{1b}[0m",
            cut("\u{1b}[31;40mTEXT\u{1b}[0m", 1..50)
        );
    }

    #[test]
    fn cut_dont_panic_on_exceeding_lower_bound() {
        assert_eq!("", cut("TEXT", 10..));
        assert_eq!("", cut("TEXT", 10..50));
    }

    #[test]
    #[should_panic = "One of indexes are not on a UTF-8 code point boundary"]
    fn cut_a_mid_of_emojie_2_test() {
        cut("😀", 1..2);
    }

    #[test]
    #[should_panic = "One of indexes are not on a UTF-8 code point boundary"]
    fn cut_a_mid_of_emojie_1_test() {
        cut("😀", 1..);
    }

    #[test]
    #[should_panic = "One of indexes are not on a UTF-8 code point boundary"]
    fn cut_a_mid_of_emojie_0_test() {
        cut("😀", ..1);
    }

    #[test]
    fn cut_emojies_test() {
        let emojes = "😀😃😄😁😆😅😂🤣🥲😊";
        assert_eq!(emojes, emojes.ansi_cut(..));
        assert_eq!("😀", emojes.ansi_cut(..4));
        assert_eq!("😃😄", emojes.ansi_cut(4..12));
        assert_eq!("🤣🥲😊", emojes.ansi_cut(emojes.find('🤣').unwrap()..));
    }

    #[test]
    // todo: We probably need to fix it.
    fn cut_colored_x_x_test() {
        assert_ne!("", cut("\u{1b}[31;40mTEXT\u{1b}[0m", 3..3));
        assert_ne!(
            "",
            cut(
                "\u{1b}[31;40mTEXT\u{1b}[0m \u{1b}[34;42mTEXT\u{1b}[0m",
                1..1
            )
        );
        assert_ne!("", cut("\u{1b}[31;40mTEXT\u{1b}[0m", ..0));

        assert_eq!("", cut("123", 0..0));
        assert_eq!(
            "\u{1b}[31;40m\u{1b}[39m\u{1b}[49m",
            "\u{1b}[31;40mTEXT\u{1b}[0m".ansi_cut(0..0)
        );
    }

    #[test]
    fn cut_partially_colored_str_test() {
        let s = "zxc_\u{1b}[31;40mTEXT\u{1b}[0m_qwe";
        assert_eq!("zxc", s.ansi_cut(..3));
        assert_eq!("zxc_\u{1b}[31;40mT\u{1b}[39m\u{1b}[49m", s.ansi_cut(..5));
        assert_eq!("\u{1b}[31;40mEXT\u{1b}[0m_q", s.ansi_cut(5..10));
        assert_eq!("\u{1b}[31;40m\u{1b}[0m", s.ansi_cut(12..));
    }

    #[test]
    fn ansi_get_test() {
        let text = "TEXT";
        assert_eq!(text.get(0..0).map(str::to_string), text.ansi_get(0..0));
        assert_eq!(Some("".to_owned()), text.ansi_get(0..0));
        assert_eq!(text.get(0..1).map(str::to_string), text.ansi_get(0..1));

        let text = "\u{1b}[30m123:456\u{1b}[39m";
        assert_eq!(Some("\u{1b}[30m\u{1b}[39m".to_owned()), text.ansi_get(0..0));
    }

    #[test]
    fn split_at_test() {
        {
            let colored_s = "\u{1b}[30mTEXT\u{1b}[39m";
            assert_eq!(
                ("".to_owned(), colored_s.to_owned()),
                colored_s.ansi_split_at(0)
            );
            assert_eq!(
                (
                    "\u{1b}[30mTE\u{1b}[39m".to_owned(),
                    "\u{1b}[30mXT\u{1b}[39m".to_owned()
                ),
                colored_s.ansi_split_at(2)
            );
            assert_eq!(
                ("\u{1b}[30mTEXT\u{1b}[39m".to_owned(), "".to_owned()),
                colored_s.ansi_split_at(4)
            );
        }

        {
            for colored_s in [
                "\u{1b}[41m\u{1b}[30msomething\u{1b}[39m \u{1b}[34m123123\u{1b}[39m\u{1b}[49m",
                "\u{1b}[41;30msomething\u{1b}[39m \u{1b}[34m123123\u{1b}[39;49m",
            ] {
                assert_eq!(
                    ("".to_owned(), "\u{1b}[30m\u{1b}[41msomething\u{1b}[39m\u{1b}[49m\u{1b}[41m \u{1b}[49m\u{1b}[34m\u{1b}[41m123123\u{1b}[39m\u{1b}[49m".to_owned()),
                    colored_s.ansi_split_at(0)
                );
                assert_eq!(
                    ("\u{1b}[30m\u{1b}[41mso\u{1b}[39m\u{1b}[49m".to_owned(), "\u{1b}[30m\u{1b}[41mmething\u{1b}[39m\u{1b}[49m\u{1b}[41m \u{1b}[49m\u{1b}[34m\u{1b}[41m123123\u{1b}[39m\u{1b}[49m".to_owned()),
                    colored_s.ansi_split_at(2)
                );
                assert_eq!(
                    (
                        "\u{1b}[30m\u{1b}[41msomethi\u{1b}[39m\u{1b}[49m".to_owned(),
                        "\u{1b}[30m\u{1b}[41mng\u{1b}[39m\u{1b}[49m\u{1b}[41m \u{1b}[49m\u{1b}[34m\u{1b}[41m123123\u{1b}[39m\u{1b}[49m".to_owned(),
                    ),
                    colored_s.ansi_split_at(7)
                );
            }
        }

        {
            let colored_s = "\u{1b}[30mTEXT\u{1b}[39m";
            assert_eq!(
                ("\u{1b}[30mTEXT\u{1b}[39m".to_owned(), "".to_owned()),
                colored_s.ansi_split_at(10)
            );
        }
    }

    #[test]
    fn split_dont_panic_on_exceeding_mid() {
        assert_eq!(
            ("TEXT".to_owned(), "".to_owned()),
            "TEXT".ansi_split_at(100)
        );
        assert_eq!(
            ("\u{1b}[30mTEXT\u{1b}[39m".to_owned(), "".to_owned()),
            "\u{1b}[30mTEXT\u{1b}[39m".ansi_split_at(100)
        );
    }

    #[test]
    #[should_panic]
    fn split_of_emojie_test() {
        "😀".ansi_split_at(1);
    }

    #[test]
    fn starts_with_test() {
        let text = "\u{1b}[30mTEXT\u{1b}[39m";
        assert!(text.ansi_starts_with(""));
        assert!(text.ansi_starts_with("T"));
        assert!(text.ansi_starts_with("TE"));
        assert!(text.ansi_starts_with("TEX"));
        assert!(text.ansi_starts_with("TEXT"));
        assert!(!text.ansi_starts_with("123"));
        assert!(!text.ansi_starts_with("TEX+"));
        assert!(!text.ansi_starts_with("TEXT NOT STARTED WITH"));
        assert!(!text.ansi_starts_with("EXT"));

        let texts = [
            "\u{1b}[41m\u{1b}[30mTEXT\u{1b}[39m \u{1b}[34m123\u{1b}[39m\u{1b}[49m",
            "\u{1b}[41;30mTEXT\u{1b}[39m \u{1b}[34m123\u{1b}[39;49m",
        ];
        for text in texts {
            assert!(text.ansi_starts_with(""));
            assert!(text.ansi_starts_with("T"));
            assert!(text.ansi_starts_with("TE"));
            assert!(text.ansi_starts_with("TEX"));
            assert!(text.ansi_starts_with("TEXT"));
            assert!(text.ansi_starts_with("TEXT "));
            assert!(text.ansi_starts_with("TEXT 1"));
            assert!(text.ansi_starts_with("TEXT 12"));
            assert!(text.ansi_starts_with("TEXT 123"));
            assert!(!text.ansi_starts_with("TEXT+"));
            assert!(!text.ansi_starts_with("TEXT +"));
            assert!(!text.ansi_starts_with("TEXT 12+"));
            assert!(!text.ansi_starts_with("TEXT 12NOT THERE"));
            assert!(!text.ansi_starts_with("NOT THERE"));
            assert!(!text.ansi_starts_with("EXT 123"));
        }
    }

    #[test]
    fn starts_with_uses_chars_so_dont_panic_test() {
        assert!(!"TE".ansi_starts_with("😀"));
        assert!(!"T".ansi_starts_with("Щ"));
    }

    #[test]
    fn ends_with_test() {
        let text = "\u{1b}[30mTEXT\u{1b}[39m";
        assert!(text.ansi_ends_with(""));
        assert!(text.ansi_ends_with("T"));
        assert!(text.ansi_ends_with("XT"));
        assert!(text.ansi_ends_with("EXT"));
        assert!(text.ansi_ends_with("TEXT"));
        assert!(!text.ansi_ends_with("123"));
        assert!(!text.ansi_ends_with("TEXT NOT STARTED WITH"));
        assert!(!text.ansi_ends_with("EXT+"));
        assert!(!text.ansi_ends_with("+EXT"));
        assert!(!text.ansi_ends_with("TEX"));

        let texts = [
            "\u{1b}[41m\u{1b}[30mTEXT\u{1b}[39m \u{1b}[34m123\u{1b}[39m\u{1b}[49m",
            "\u{1b}[41;30mTEXT\u{1b}[39m \u{1b}[34m123\u{1b}[39;49m",
        ];
        for text in texts {
            assert!(text.ansi_ends_with(""));
            assert!(text.ansi_ends_with("3"));
            assert!(text.ansi_ends_with("23"));
            assert!(text.ansi_ends_with("123"));
            assert!(text.ansi_ends_with(" 123"));
            assert!(text.ansi_ends_with("T 123"));
            assert!(text.ansi_ends_with("XT 123"));
            assert!(text.ansi_ends_with("EXT 123"));
            assert!(text.ansi_ends_with("TEXT 123"));
            assert!(!text.ansi_ends_with("123+"));
            assert!(!text.ansi_ends_with("+123"));
            assert!(!text.ansi_ends_with(" +123"));
            assert!(!text.ansi_ends_with("+ 123"));
            assert!(!text.ansi_ends_with("TEXT 12NOT THERE"));
            assert!(!text.ansi_ends_with("NOT THERE"));
            assert!(!text.ansi_ends_with("TEXT 12"));
        }
    }

    #[test]
    fn ends_with_uses_chars_so_dont_panic_test() {
        assert!(!"TE".ansi_ends_with("😀"));
        assert!(!"T".ansi_ends_with("Щ"));
    }

    #[test]
    fn trim_test() {
        assert_eq!("", "".ansi_trim());
        assert_eq!("", " ".ansi_trim());
        assert_eq!("TEXT", "TEXT".ansi_trim());
        assert_eq!("TEXT", " TEXT".ansi_trim());
        assert_eq!("TEXT", "TEXT ".ansi_trim());
        assert_eq!("TEXT", " TEXT ".ansi_trim());

        let texts = [
            "\u{1b}[41m\u{1b}[30mTEXT\u{1b}[39m \u{1b}[34m123\u{1b}[39m\u{1b}[49m",
            "\u{1b}[41m\u{1b}[30m TEXT\u{1b}[39m \u{1b}[34m123\u{1b}[39m\u{1b}[49m",
            "\u{1b}[41m\u{1b}[30m  TEXT\u{1b}[39m \u{1b}[34m123\u{1b}[39m\u{1b}[49m",
            "\u{1b}[41m\u{1b}[30m   TEXT\u{1b}[39m \u{1b}[34m123\u{1b}[39m\u{1b}[49m",
            "\u{1b}[41m\u{1b}[30mTEXT\u{1b}[39m \u{1b}[34m123 \u{1b}[39m\u{1b}[49m",
            "\u{1b}[41m\u{1b}[30mTEXT\u{1b}[39m \u{1b}[34m123  \u{1b}[39m\u{1b}[49m",
            "\u{1b}[41m\u{1b}[30mTEXT\u{1b}[39m \u{1b}[34m123   \u{1b}[39m\u{1b}[49m",
            "\u{1b}[41m\u{1b}[30m TEXT\u{1b}[39m \u{1b}[34m123 \u{1b}[39m\u{1b}[49m",
            "\u{1b}[41m\u{1b}[30m  TEXT\u{1b}[39m \u{1b}[34m123  \u{1b}[39m\u{1b}[49m",
            "\u{1b}[41m\u{1b}[30m   TEXT\u{1b}[39m \u{1b}[34m123   \u{1b}[39m\u{1b}[49m",
        ];
        for text in texts {
            assert_eq!(
                "\u{1b}[41m\u{1b}[30mTEXT\u{1b}[39m \u{1b}[34m123\u{1b}[39m\u{1b}[49m",
                text.ansi_trim()
            );
        }

        let texts = [
            "\u{1b}[41;30mTEXT\u{1b}[39m \u{1b}[34m123\u{1b}[39;49m",
            "\u{1b}[41;30m TEXT\u{1b}[39m \u{1b}[34m123\u{1b}[39;49m",
            "\u{1b}[41;30m  TEXT\u{1b}[39m \u{1b}[34m123\u{1b}[39;49m",
            "\u{1b}[41;30m   TEXT\u{1b}[39m \u{1b}[34m123\u{1b}[39;49m",
            "\u{1b}[41;30mTEXT\u{1b}[39m \u{1b}[34m123 \u{1b}[39;49m",
            "\u{1b}[41;30mTEXT\u{1b}[39m \u{1b}[34m123  \u{1b}[39;49m",
            "\u{1b}[41;30mTEXT\u{1b}[39m \u{1b}[34m123   \u{1b}[39;49m",
            "\u{1b}[41;30m TEXT\u{1b}[39m \u{1b}[34m123 \u{1b}[39;49m",
            "\u{1b}[41;30m  TEXT\u{1b}[39m \u{1b}[34m123  \u{1b}[39;49m",
            "\u{1b}[41;30m   TEXT\u{1b}[39m \u{1b}[34m123   \u{1b}[39;49m",
        ];
        for text in texts {
            assert_eq!(
                "\u{1b}[41;30mTEXT\u{1b}[39m \u{1b}[34m123\u{1b}[39;49m",
                text.ansi_trim()
            );
        }
    }

    #[test]
    fn strip_prefix_test() {
        macro_rules! test_prefix {
            ($text:expr, $prefix:expr, $expected:expr $(,)? ) => {
                assert_eq!(
                    $expected.map(str::to_string),
                    $text.ansi_strip_prefix($prefix),
                );
            };
        }

        test_prefix!("", "", Some(""));
        test_prefix!("qwe:TEXT", "", Some("qwe:TEXT"));
        test_prefix!("qwe:TEXT", "qwe:TEXT", Some(""));
        test_prefix!("qwe:TEXT", "qwe:", Some("TEXT"));
        test_prefix!("qwe:TEXT", "we:", None);
        test_prefix!("qwe:TEXT", "T", None);
        test_prefix!(
            "\u{1b}[41m\u{1b}[30mqwe:TEXT\u{1b}[39m \u{1b}[34mQWE\u{1b}[39m\u{1b}[49m",
            "",
            Some("\u{1b}[41m\u{1b}[30mqwe:TEXT\u{1b}[39m \u{1b}[34mQWE\u{1b}[39m\u{1b}[49m"),
        );
        test_prefix!(
            "\u{1b}[41m\u{1b}[30mqwe:TEXT\u{1b}[39m \u{1b}[34mQWE\u{1b}[39m\u{1b}[49m",
            "qwe:TEXT QWE",
            Some("\u{1b}[41m\u{1b}[30m\u{1b}[39m\u{1b}[34m\u{1b}[39m\u{1b}[49m"),
        );
        test_prefix!(
            "\u{1b}[41m\u{1b}[30mqwe:TEXT\u{1b}[39m \u{1b}[34mQWE\u{1b}[39m\u{1b}[49m",
            "qwe:",
            Some("\u{1b}[41m\u{1b}[30mTEXT\u{1b}[39m \u{1b}[34mQWE\u{1b}[39m\u{1b}[49m"),
        );
        test_prefix!(
            "\u{1b}[41m\u{1b}[30mqwe:TEXT\u{1b}[39m \u{1b}[34mQWE\u{1b}[39m\u{1b}[49m",
            "qwe:TEXT",
            Some("\u{1b}[41m\u{1b}[30m\u{1b}[39m \u{1b}[34mQWE\u{1b}[39m\u{1b}[49m"),
        );
        test_prefix!(
            "\u{1b}[41m\u{1b}[30mqwe:TEXT\u{1b}[39m \u{1b}[34mQWE\u{1b}[39m\u{1b}[49m",
            "qwe:TEXT ",
            Some("\u{1b}[41m\u{1b}[30m\u{1b}[39m\u{1b}[34mQWE\u{1b}[39m\u{1b}[49m"),
        );
        test_prefix!(
            "\u{1b}[41m\u{1b}[30mqwe:TEXT\u{1b}[39m \u{1b}[34mQWE\u{1b}[39m\u{1b}[49m",
            "qwe:TEXT ",
            Some("\u{1b}[41m\u{1b}[30m\u{1b}[39m\u{1b}[34mQWE\u{1b}[39m\u{1b}[49m"),
        );
        test_prefix!(
            "\u{1b}[41m\u{1b}[30mqwe:TEXT\u{1b}[39m \u{1b}[34mQWE\u{1b}[39m\u{1b}[49m",
            "qwe:TEXT ",
            Some("\u{1b}[41m\u{1b}[30m\u{1b}[39m\u{1b}[34mQWE\u{1b}[39m\u{1b}[49m"),
        );
        test_prefix!(
            "\u{1b}[41m\u{1b}[30mqwe:TEXT\u{1b}[39m \u{1b}[34mQWE\u{1b}[39m\u{1b}[49m",
            "qwe:TEXT QW",
            Some("\u{1b}[41m\u{1b}[30m\u{1b}[39m\u{1b}[34mE\u{1b}[39m\u{1b}[49m"),
        );
        test_prefix!(
            "\u{1b}[41m\u{1b}[30mqwe:TEXT\u{1b}[39m \u{1b}[34mQWE\u{1b}[39m\u{1b}[49m",
            "we:",
            None,
        );
        test_prefix!(
            "\u{1b}[41m\u{1b}[30mqwe:TEXT\u{1b}[39m \u{1b}[34mQWE\u{1b}[39m\u{1b}[49m",
            ":",
            None,
        );
        test_prefix!(
            "\u{1b}[41m\u{1b}[30mqwe:TEXT\u{1b}[39m \u{1b}[34mQWE\u{1b}[39m\u{1b}[49m",
            "QWE",
            None,
        );
        test_prefix!(
            "\u{1b}[41;30mqwe:TEXT\u{1b}[39m \u{1b}[34m123\u{1b}[39;49m",
            "",
            Some("\u{1b}[41;30mqwe:TEXT\u{1b}[39m \u{1b}[34m123\u{1b}[39;49m"),
        );
        test_prefix!(
            "\u{1b}[41;30mqwe:TEXT\u{1b}[39m \u{1b}[34m123\u{1b}[39;49m",
            "qwe:TEXT 123",
            Some("\u{1b}[41;30m\u{1b}[39m\u{1b}[34m\u{1b}[39;49m"),
        );
        test_prefix!(
            "\u{1b}[41;30mqwe:TEXT\u{1b}[39m \u{1b}[34m123\u{1b}[39;49m",
            "qwe:",
            Some("\u{1b}[41;30mTEXT\u{1b}[39m \u{1b}[34m123\u{1b}[39;49m"),
        );
        test_prefix!(
            "\u{1b}[41;30mqwe:TEXT\u{1b}[39m \u{1b}[34m123\u{1b}[39;49m",
            "qwe:TEXT",
            Some("\u{1b}[41;30m\u{1b}[39m \u{1b}[34m123\u{1b}[39;49m"),
        );
        test_prefix!(
            "\u{1b}[41;30mqwe:TEXT\u{1b}[39m \u{1b}[34m123\u{1b}[39;49m",
            "qwe:TEXT ",
            Some("\u{1b}[41;30m\u{1b}[39m\u{1b}[34m123\u{1b}[39;49m"),
        );
        test_prefix!(
            "\u{1b}[41;30mqwe:TEXT\u{1b}[39m \u{1b}[34m123\u{1b}[39;49m",
            "qwe:TEXT 12",
            Some("\u{1b}[41;30m\u{1b}[39m\u{1b}[34m3\u{1b}[39;49m"),
        );
        test_prefix!(
            "\u{1b}[41;30mqwe:TEXT\u{1b}[39m \u{1b}[34m123\u{1b}[39;49m",
            "qwe:TEXT 123",
            Some("\u{1b}[41;30m\u{1b}[39m\u{1b}[34m\u{1b}[39;49m"),
        );
        test_prefix!(
            "\u{1b}[41;30mqwe:TEXT\u{1b}[39m \u{1b}[34m123\u{1b}[39;49m",
            "we:",
            None,
        );
        test_prefix!(
            "\u{1b}[41;30mqwe:TEXT\u{1b}[39m \u{1b}[34m123\u{1b}[39;49m",
            ":",
            None,
        );
        test_prefix!(
            "\u{1b}[41;30mqwe:TEXT\u{1b}[39m \u{1b}[34m123\u{1b}[39;49m",
            "QWE",
            None,
        );
    }

    #[test]
    fn strip_suffix_test() {
        assert_eq!(Some("".to_owned()), "".ansi_strip_suffix(""));

        let text = "qwe:TEXT";
        assert_eq!(Some(text.to_owned()), text.ansi_strip_suffix(""));
        assert_eq!(Some("".to_owned()), text.ansi_strip_suffix(text));
        assert_eq!(Some("qwe:TEX".to_owned()), text.ansi_strip_suffix("T"));
        assert_eq!(Some("qwe".to_owned()), text.ansi_strip_suffix(":TEXT"));
        assert_eq!(None, text.ansi_strip_suffix("qwe:"));
        assert_eq!(None, text.ansi_strip_suffix(":"));

        let text = "\u{1b}[41m\u{1b}[30mqwe:TEXT\u{1b}[39m \u{1b}[34mQWE\u{1b}[39m\u{1b}[49m";
        assert_eq!(Some(text.to_owned()), text.ansi_strip_suffix(""));
        assert_eq!(None, text.ansi_strip_suffix(text));
        assert_eq!(
            Some(
                "\u{1b}[41m\u{1b}[30mqwe:TEXT\u{1b}[39m \u{1b}[34mQW\u{1b}[39m\u{1b}[49m"
                    .to_owned()
            ),
            text.ansi_strip_suffix("E")
        );
        assert_eq!(
            Some(
                "\u{1b}[41m\u{1b}[30mqwe:TEXT\u{1b}[39m \u{1b}[34mQ\u{1b}[39m\u{1b}[49m".to_owned()
            ),
            text.ansi_strip_suffix("WE")
        );
        assert_eq!(
            Some(
                "\u{1b}[41m\u{1b}[30mqwe:TEXT\u{1b}[39m \u{1b}[34m\u{1b}[39m\u{1b}[49m".to_owned()
            ),
            text.ansi_strip_suffix("QWE")
        );
        assert_eq!(
            Some("\u{1b}[41m\u{1b}[30mqwe:TEXT\u{1b}[39m\u{1b}[34m\u{1b}[39m\u{1b}[49m".to_owned()),
            text.ansi_strip_suffix(" QWE")
        );
        assert_eq!(
            Some("\u{1b}[41m\u{1b}[30mqwe:TEX\u{1b}[39m\u{1b}[34m\u{1b}[39m\u{1b}[49m".to_owned()),
            text.ansi_strip_suffix("T QWE")
        );
        assert_eq!(
            Some("\u{1b}[41m\u{1b}[30mqwe:TE\u{1b}[39m\u{1b}[34m\u{1b}[39m\u{1b}[49m".to_owned()),
            text.ansi_strip_suffix("XT QWE")
        );
        assert_eq!(
            Some("\u{1b}[41m\u{1b}[30mqwe:T\u{1b}[39m\u{1b}[34m\u{1b}[39m\u{1b}[49m".to_owned()),
            text.ansi_strip_suffix("EXT QWE")
        );
        assert_eq!(
            Some("\u{1b}[41m\u{1b}[30mqwe:\u{1b}[39m\u{1b}[34m\u{1b}[39m\u{1b}[49m".to_owned()),
            text.ansi_strip_suffix("TEXT QWE")
        );
        assert_eq!(
            Some("\u{1b}[41m\u{1b}[30mqwe\u{1b}[39m\u{1b}[34m\u{1b}[39m\u{1b}[49m".to_owned()),
            text.ansi_strip_suffix(":TEXT QWE")
        );
        assert_eq!(
            Some("\u{1b}[41m\u{1b}[30mqw\u{1b}[39m\u{1b}[34m\u{1b}[39m\u{1b}[49m".to_owned()),
            text.ansi_strip_suffix("e:TEXT QWE")
        );
        assert_eq!(
            Some("\u{1b}[41m\u{1b}[30mq\u{1b}[39m\u{1b}[34m\u{1b}[39m\u{1b}[49m".to_owned()),
            text.ansi_strip_suffix("we:TEXT QWE")
        );
        assert_eq!(
            Some("\u{1b}[41m\u{1b}[30m\u{1b}[39m\u{1b}[34m\u{1b}[39m\u{1b}[49m".to_owned()),
            text.ansi_strip_suffix("qwe:TEXT QWE")
        );
        assert_eq!(None, text.ansi_strip_suffix("qwe:TEXT QW"));
        assert_eq!(None, text.ansi_strip_suffix("qwe:"));
        assert_eq!(None, text.ansi_strip_suffix("QW"));

        let text = "\u{1b}[41;30mqwe:TEXT\u{1b}[39m \u{1b}[34m123\u{1b}[39;49m";
        assert_eq!(Some(text.to_owned()), text.ansi_strip_suffix(""));
        assert_eq!(None, text.ansi_strip_suffix(text));
        assert_eq!(
            Some("\u{1b}[41;30mqwe:TEXT\u{1b}[39m \u{1b}[34m12\u{1b}[39;49m".to_owned()),
            text.ansi_strip_suffix("3")
        );
        assert_eq!(
            Some("\u{1b}[41;30mqwe:TEXT\u{1b}[39m \u{1b}[34m1\u{1b}[39;49m".to_owned()),
            text.ansi_strip_suffix("23")
        );
        assert_eq!(
            Some("\u{1b}[41;30mqwe:TEXT\u{1b}[39m \u{1b}[34m\u{1b}[39;49m".to_owned()),
            text.ansi_strip_suffix("123")
        );
        assert_eq!(
            Some("\u{1b}[41;30mqwe:TEXT\u{1b}[39m\u{1b}[34m\u{1b}[39;49m".to_owned()),
            text.ansi_strip_suffix(" 123")
        );
        assert_eq!(
            Some("\u{1b}[41;30mqwe:TEX\u{1b}[39m\u{1b}[34m\u{1b}[39;49m".to_owned()),
            text.ansi_strip_suffix("T 123")
        );
        assert_eq!(
            Some("\u{1b}[41;30mqwe:TE\u{1b}[39m\u{1b}[34m\u{1b}[39;49m".to_owned()),
            text.ansi_strip_suffix("XT 123")
        );
        assert_eq!(
            Some("\u{1b}[41;30mqwe:T\u{1b}[39m\u{1b}[34m\u{1b}[39;49m".to_owned()),
            text.ansi_strip_suffix("EXT 123")
        );
        assert_eq!(
            Some("\u{1b}[41;30mqwe:\u{1b}[39m\u{1b}[34m\u{1b}[39;49m".to_owned()),
            text.ansi_strip_suffix("TEXT 123")
        );
        assert_eq!(
            Some("\u{1b}[41;30mqwe\u{1b}[39m\u{1b}[34m\u{1b}[39;49m".to_owned()),
            text.ansi_strip_suffix(":TEXT 123")
        );
        assert_eq!(
            Some("\u{1b}[41;30mqw\u{1b}[39m\u{1b}[34m\u{1b}[39;49m".to_owned()),
            text.ansi_strip_suffix("e:TEXT 123")
        );
        assert_eq!(
            Some("\u{1b}[41;30mq\u{1b}[39m\u{1b}[34m\u{1b}[39;49m".to_owned()),
            text.ansi_strip_suffix("we:TEXT 123")
        );
        assert_eq!(
            Some("\u{1b}[41;30m\u{1b}[39m\u{1b}[34m\u{1b}[39;49m".to_owned()),
            text.ansi_strip_suffix("qwe:TEXT 123")
        );
        assert_eq!(None, text.ansi_strip_suffix("qwe:TEXT 12"));
        assert_eq!(None, text.ansi_strip_suffix("qwe:"));
        assert_eq!(None, text.ansi_strip_suffix("2"));
    }

    #[test]
    fn find_test() {
        assert_eq!("".find(""), "".ansi_find(""));

        let text = "qwe:TEXT";
        assert_eq!(Some(0), text.ansi_find("q"));
        assert_eq!(Some(0), text.ansi_find("qwe"));
        assert_eq!(Some(1), text.ansi_find("we"));
        assert_eq!(Some(3), text.ansi_find(":"));
        assert_eq!(Some(4), text.ansi_find("TEXT"));

        let text = "\u{1b}[30mqwe:TEXT\u{1b}[39m";
        assert_eq!(Some(0), text.ansi_find("q"));
        assert_eq!(Some(0), text.ansi_find("qwe"));
        assert_eq!(Some(1), text.ansi_find("we"));
        assert_eq!(Some(3), text.ansi_find(":"));
        assert_eq!(Some(4), text.ansi_find("TEXT"));

        let text = "\u{1b}[41m\u{1b}[30mqwe:TEXT\u{1b}[39m \u{1b}[34mQWE\u{1b}[39m\u{1b}[49m";
        assert_eq!(Some(0), text.ansi_find("q"));
        assert_eq!(Some(0), text.ansi_find("qwe"));
        assert_eq!(Some(1), text.ansi_find("we"));
        assert_eq!(Some(3), text.ansi_find(":"));
        assert_eq!(Some(4), text.ansi_find("TEXT"));
        assert_eq!(Some(5), text.ansi_find("E"));
        assert_eq!(Some(8), text.ansi_find(" "));
        assert_eq!(Some(9), text.ansi_find("QWE"));

        let text = "\u{1b}[41;30mqwe:TEXT\u{1b}[39m \u{1b}[34mQWE\u{1b}[39;49m";
        assert_eq!(Some(0), text.ansi_find("q"));
        assert_eq!(Some(0), text.ansi_find("qwe"));
        assert_eq!(Some(1), text.ansi_find("we"));
        assert_eq!(Some(3), text.ansi_find(":"));
        assert_eq!(Some(4), text.ansi_find("TEXT"));
        assert_eq!(Some(5), text.ansi_find("E"));
        assert_eq!(Some(8), text.ansi_find(" "));
        assert_eq!(Some(9), text.ansi_find("QWE"));
    }

    #[test]
    fn split_test() {
        assert_eq!(
            "213".split("").collect::<Vec<_>>(),
            "213".ansi_split("").collect::<Vec<_>>()
        );
        assert_eq!(
            "".split("").collect::<Vec<_>>(),
            "".ansi_split("").collect::<Vec<_>>()
        );

        let text = "123:456";
        assert_eq!(
            text.split(':').collect::<Vec<_>>(),
            text.ansi_split(":").collect::<Vec<_>>()
        );
        assert_eq!(
            text.split("").collect::<Vec<_>>(),
            text.ansi_split("").collect::<Vec<_>>()
        );
        assert_eq!(
            text.split("TEXT").collect::<Vec<_>>(),
            text.ansi_split("TEXT").collect::<Vec<_>>()
        );
        assert_eq!(
            text.split("123").collect::<Vec<_>>(),
            text.ansi_split("123").collect::<Vec<_>>()
        );
        assert_eq!(
            text.split("456").collect::<Vec<_>>(),
            text.ansi_split("456").collect::<Vec<_>>()
        );

        let text = "123:456:789";
        assert_eq!(
            text.split(':').collect::<Vec<_>>(),
            text.ansi_split(":").collect::<Vec<_>>()
        );
        assert_eq!(
            text.split("").collect::<Vec<_>>(),
            text.ansi_split("").collect::<Vec<_>>()
        );
        assert_eq!(
            text.split("TEXT").collect::<Vec<_>>(),
            text.ansi_split("TEXT").collect::<Vec<_>>()
        );
        assert_eq!(
            text.split("123").collect::<Vec<_>>(),
            text.ansi_split("123").collect::<Vec<_>>()
        );
        assert_eq!(
            text.split("456").collect::<Vec<_>>(),
            text.ansi_split("456").collect::<Vec<_>>()
        );
        assert_eq!(
            text.split("789").collect::<Vec<_>>(),
            text.ansi_split("789").collect::<Vec<_>>()
        );

        assert_eq!(
            ":123:456:789".split(':').collect::<Vec<_>>(),
            ":123:456:789".ansi_split(":").collect::<Vec<_>>()
        );
        assert_eq!(
            "123:456:789:".split(':').collect::<Vec<_>>(),
            "123:456:789:".ansi_split(":").collect::<Vec<_>>()
        );
        assert_eq!(
            ":123:456:789:".split(':').collect::<Vec<_>>(),
            ":123:456:789:".ansi_split(":").collect::<Vec<_>>()
        );

        let text = "\u{1b}[30m123:456\u{1b}[39m";
        assert_eq!(
            vec!["\u{1b}[30m123\u{1b}[39m", "\u{1b}[30m456\u{1b}[39m"],
            text.ansi_split(":").collect::<Vec<_>>()
        );
        assert_eq!(
            vec!["\u{1b}[30m123:\u{1b}[39m", "\u{1b}[30m\u{1b}[39m"],
            text.ansi_split("456").collect::<Vec<_>>()
        );

        let text = "\u{1b}[41m\u{1b}[30mqwe:TEXT\u{1b}[39m \u{1b}[34mQWE\u{1b}[39m\u{1b}[49m";
        assert_eq!(
            vec![
                "\u{1b}[41m\u{1b}[30mqwe\u{1b}[39m\u{1b}[49m",
                "\u{1b}[30m\u{1b}[41mTEXT\u{1b}[39m \u{1b}[34mQWE\u{1b}[39m\u{1b}[49m"
            ],
            text.ansi_split(":").collect::<Vec<_>>()
        );
        assert_eq!(vec![text], text.ansi_split("456").collect::<Vec<_>>());
        assert_eq!(
            vec![text.to_owned()],
            text.ansi_split("NOT FOUND").collect::<Vec<_>>()
        );

        let text = "\u{1b}[41;30mqwe:TEXT\u{1b}[39m \u{1b}[34mQWE\u{1b}[39;49m";
        assert_eq!(
            vec![
                "\u{1b}[41;30mqwe\u{1b}[39m\u{1b}[49m",
                "\u{1b}[30m\u{1b}[41mTEXT\u{1b}[39m \u{1b}[34mQWE\u{1b}[39;49m"
            ],
            text.ansi_split(":").collect::<Vec<_>>()
        );
        assert_eq!(
            vec!["\u{1b}[41;30mqwe:TEXT\u{1b}[39m \u{1b}[34mQWE\u{1b}[39;49m"],
            text.ansi_split("456").collect::<Vec<_>>()
        );
        assert_eq!(
            vec![text.to_owned()],
            text.ansi_split("NOT FOUND").collect::<Vec<_>>()
        );

        assert_eq!(
            "\u{1b}[31mlionXXtigerXleopard\u{1b}[39m"
                .ansi_split("X")
                .collect::<Vec<_>>(),
            [
                "\u{1b}[31mlion\u{1b}[39m",
                "",
                "\u{1b}[31mtiger\u{1b}[39m",
                "\u{1b}[31mleopard\u{1b}[39m"
            ],
        );
    }

    #[test]
    fn split_at_color_preservation_test() {
        assert_eq!(
            "\u{1b}[30mTEXT\u{1b}[39m".ansi_split_at(2),
            (
                "\u{1b}[30mTE\u{1b}[39m".to_owned(),
                "\u{1b}[30mXT\u{1b}[39m".to_owned()
            ),
        );
        assert_eq!(
            "\u{1b}[38;5;12mTEXT\u{1b}[39m".ansi_split_at(2),
            (
                "\u{1b}[38;5;12mTE\u{1b}[39m".to_owned(),
                "\u{1b}[38;5;12mXT\u{1b}[39m".to_owned()
            ),
        );
        assert_eq!(
            "\u{1b}[38;2;100;123;1mTEXT\u{1b}[39m".ansi_split_at(2),
            (
                "\u{1b}[38;2;100;123;1mTE\u{1b}[39m".to_owned(),
                "\u{1b}[38;2;100;123;1mXT\u{1b}[39m".to_owned()
            ),
        );
        assert_eq!(
            "\u{1b}[38;5;30mTEXT\u{1b}[39m".ansi_split_at(2),
            (
                "\u{1b}[38;5;30mTE\u{1b}[39m".to_owned(),
                "\u{1b}[38;5;30mXT\u{1b}[39m".to_owned()
            ),
        );
        assert_eq!(
            "\u{1b}[48;2;023;011;100m\u{1b}[31mHello\u{1b}[39m\u{1b}[49m \u{1b}[32;43mWorld\u{1b}[0m".ansi_split_at(6),
            ("\u{1b}[31m\u{1b}[48;2;23;11;100mHello\u{1b}[39m\u{1b}[49m ".to_owned(), "\u{1b}[32m\u{1b}[43mWorld\u{1b}[39m\u{1b}[49m".to_owned()),
        );
    }

    #[test]
    fn get_blocks_test() {
        macro_rules! test_blocks {
            ([$($string:expr),* $(,)?], $expected:expr) => {
                $(
                    assert_eq!(
                        get_blocks($string).collect::<Vec<_>>(),
                        $expected,
                    );
                )*
            };
        }

        test_blocks!([""], []);

        test_blocks!(
            ["213"],
            [AnsiBlock::new(Cow::Borrowed("213"), AnsiState::default())]
        );

        test_blocks!(
            ["213\n456"],
            [AnsiBlock::new(
                Cow::Borrowed("213\n456"),
                AnsiState::default()
            )]
        );

        test_blocks!(
            [
                "\u{1b}[30m123:456\u{1b}[39m",
                "\u{1b}[30m123:456\u{1b}[0m",
                "\u{1b}[30m123:456",
            ],
            [AnsiBlock::new(
                Cow::Borrowed("123:456"),
                AnsiState {
                    fg_color: Some(AnsiColor::Bit4 { index: 30 }),
                    ..Default::default()
                }
            )]
        );

        test_blocks!(
            [
                "\u{1b}[30m123\n:\n456\u{1b}[39m",
                "\u{1b}[30m123\n:\n456\u{1b}[0m",
                "\u{1b}[30m123\n:\n456",
            ],
            [AnsiBlock::new(
                Cow::Borrowed("123\n:\n456"),
                AnsiState {
                    fg_color: Some(AnsiColor::Bit4 { index: 30 }),
                    ..Default::default()
                }
            )]
        );

        test_blocks!(
            [
                "\u{1b}[41m\u{1b}[30mqwe:TEXT\u{1b}[39m \u{1b}[34mQWE\u{1b}[39m\u{1b}[49m",
                "\u{1b}[41;30mqwe:TEXT\u{1b}[39m \u{1b}[34mQWE\u{1b}[39;49m",
                "\u{1b}[41m\u{1b}[30mqwe:TEXT\u{1b}[39m \u{1b}[34mQWE\u{1b}[0m",
                "\u{1b}[41m\u{1b}[30mqwe:TEXT\u{1b}[39m \u{1b}[34mQWE",
            ],
            [
                AnsiBlock::new(
                    Cow::Borrowed("qwe:TEXT"),
                    AnsiState {
                        fg_color: Some(AnsiColor::Bit4 { index: 30 }),
                        bg_color: Some(AnsiColor::Bit4 { index: 41 }),
                        ..Default::default()
                    }
                ),
                AnsiBlock::new(
                    Cow::Borrowed(" "),
                    AnsiState {
                        bg_color: Some(AnsiColor::Bit4 { index: 41 }),
                        ..Default::default()
                    }
                ),
                AnsiBlock::new(
                    Cow::Borrowed("QWE"),
                    AnsiState {
                        fg_color: Some(AnsiColor::Bit4 { index: 34 }),
                        bg_color: Some(AnsiColor::Bit4 { index: 41 }),
                        ..Default::default()
                    }
                ),
            ]
        );

        test_blocks!(
            ["\u{1b}[31mlionXXtigerXleopard\u{1b}[39m"],
            [AnsiBlock::new(
                Cow::Borrowed("lionXXtigerXleopard"),
                AnsiState {
                    fg_color: Some(AnsiColor::Bit4 { index: 31 }),
                    ..Default::default()
                },
            )]
        );

        test_blocks!(
            ["\u{1b}[41;30m Hello \u{1b}[0m \t \u{1b}[43;32m World \u{1b}[0m",],
            [
                AnsiBlock::new(
                    Cow::Borrowed(" Hello "),
                    AnsiState {
                        fg_color: Some(AnsiColor::Bit4 { index: 30 }),
                        bg_color: Some(AnsiColor::Bit4 { index: 41 }),
                        ..Default::default()
                    }
                ),
                AnsiBlock::new(
                    Cow::Borrowed(" \t "),
                    AnsiState {
                        reset: true,
                        ..Default::default()
                    },
                ),
                AnsiBlock::new(
                    Cow::Borrowed(" World "),
                    AnsiState {
                        fg_color: Some(AnsiColor::Bit4 { index: 32 }),
                        bg_color: Some(AnsiColor::Bit4 { index: 43 }),
                        reset: true,
                        ..Default::default()
                    },
                ),
            ]
        );
    }
}
