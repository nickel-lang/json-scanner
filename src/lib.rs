#![allow(clippy::unusual_byte_groupings)]

use memchr::memchr;
use std::borrow::Cow;

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum ErrorKind {
    InvalidUtf8,
    NumberWithLeadingZero,
    UnterminatedString,
    UnescapedControl(u8),
    UnmatchedSurrogate,
    InvalidEscape(u8),
    InvalidHex(u8),
    ExpectedComma,
    ExpectedDigit,
    ExpectedFalse,
    ExpectedTrue,
    ExpectedNull,
    ExpectedNumber,
    ExpectedExponentStart,
    ExpectedValue,
    ExpectedString,
    ExpectedEos,
    ExpectedColon,
    ExpectedFirstObjectEntry,
    ExpectedNextObjectEntry,
    ExpectedFirstArrayEntry,
    ExpectedNextArrayEntry,
}

#[derive(Copy, Clone, Debug)]
pub struct ParseError {
    pub byte_offset: usize,
    pub kind: ErrorKind,
}

enum Container {
    Object,
    Array,
}

enum State {
    Init,
    ObjectStart,
    ObjectAfterKey,
    ObjectAfterValue,
    ArrayStart,
    ArrayAfterValue,
    Done,
}

/// A simple JSON parser that delivers event streams in "pull" mode.
pub struct Parser<'input> {
    /// The current offset in the input, for reporting spans and errors.
    offset: usize,
    /// The remaining input left to process.
    ///
    /// The next byte to process is `input[0]`: we have advanced past `offset`
    /// bytes already.
    input: &'input [u8],
    /// The current state of the parser.
    state: State,
    /// The stack of "old" containers. The current container isn't
    /// on this stack, because it can be deduced from `state`.
    ///
    /// For example, consider the input
    /// ```json
    ///  { "foo": [1, 2] }`
    /// ^0 ^1      ^2
    /// ```
    ///
    /// At position `^0`, the state will be `Init` and the stack
    /// will be empty. At position `^1`, the state will be `ObjectStart`
    /// and the stack will be empty. At position `^2`, the state will
    /// be `ArrayStart` and the stack will have an object on it.
    container_stack: Vec<Container>,
}

#[derive(Debug, PartialEq, Eq)]
pub enum Event<'input> {
    /// The parser has entered an object (i.e., it has encountered a `{`).
    ///
    /// The next event will either be `EndObject`, or else a `String` containing
    /// an object key.
    BeginObject,
    /// The parser has left an object (i.e., it has encountered a `}`).
    EndObject,
    /// The parser has entered an array (i.e., it has encountered a `[`).
    BeginArray,
    /// The parser has left an array (i.e., it has encountered a `]`).
    EndArray,
    /// The parser has encountered a number. The number has not been
    /// parsed.
    Number(&'input str),
    /// The parser has encountered a string.
    String(Cow<'input, str>),
    /// The parser has encountered a boolean.
    Boolean(bool),
    /// The parser has encountered a JSON `null` literal.
    Null,
}

#[derive(Debug, PartialEq, Eq)]
pub struct SpannedEvent<'input> {
    pub start: usize,
    pub end: usize,
    pub event: Event<'input>,
}

/// Does JSON consider `c` an ASCII control character?
///
/// This is different from Rust's `u8::is_ascii_control`.
///
/// https://datatracker.ietf.org/doc/html/rfc8259#section-7
fn is_ascii_control(c: u8) -> bool {
    c <= 0x1F
}

fn is_high_surrogate(c: u16) -> bool {
    (0xD800..=0xDBFF).contains(&c)
}

fn is_low_surrogate(c: u16) -> bool {
    (0xDC00..=0xDFFF).contains(&c)
}

impl<'input> Parser<'input> {
    pub fn new(input: &'input [u8]) -> Self {
        Parser {
            input,
            offset: 0,
            container_stack: Vec::new(),
            state: State::Init,
        }
    }

    pub fn next_event(&mut self) -> Result<Option<SpannedEvent<'input>>, ParseError> {
        self.skip_whitespace();

        let ev = match self.state {
            State::Init => self.expect_value(State::Done)?,
            State::ObjectStart => {
                let c = self.peek(ErrorKind::ExpectedFirstObjectEntry)?;
                if c == b'}' {
                    self.pop_container(Event::EndObject)
                } else {
                    let s = self.expect_string()?;
                    self.state = State::ObjectAfterKey;
                    s
                }
            }
            State::ObjectAfterKey => {
                self.expect_byte(b':', self.err(ErrorKind::ExpectedColon))?;
                self.skip_whitespace();
                self.expect_value(State::ObjectAfterValue)?
            }
            State::ObjectAfterValue => {
                let c = self.peek(ErrorKind::ExpectedNextObjectEntry)?;
                if c == b'}' {
                    self.pop_container(Event::EndObject)
                } else {
                    self.expect_byte(b',', self.err(ErrorKind::ExpectedComma))?;
                    self.skip_whitespace();
                    let k = self.expect_string()?;
                    self.state = State::ObjectAfterKey;
                    k
                }
            }
            State::ArrayStart => {
                let c = self.peek(ErrorKind::ExpectedFirstArrayEntry)?;
                if c == b']' {
                    self.pop_container(Event::EndArray)
                } else {
                    self.expect_value(State::ArrayAfterValue)?
                }
            }
            State::ArrayAfterValue => {
                let c = self.peek(ErrorKind::ExpectedNextArrayEntry)?;
                if c == b']' {
                    self.pop_container(Event::EndArray)
                } else {
                    self.expect_byte(b',', self.err(ErrorKind::ExpectedComma))?;
                    self.expect_value(State::ArrayAfterValue)?
                }
            }
            State::Done => {
                if self.peek(ErrorKind::ExpectedEos).is_ok() {
                    return Err(self.err(ErrorKind::ExpectedEos));
                } else {
                    return Ok(None);
                }
            }
        };

        Ok(Some(ev))
    }

    fn pop_container(&mut self, event: Event<'input>) -> SpannedEvent<'input> {
        #[cfg(debug_assertions)]
        {
            let c = self.peek(ErrorKind::ExpectedEos).unwrap();
            assert!(c == b'}' || c == b']');
        }
        self.state = match self.container_stack.pop() {
            Some(Container::Object) => State::ObjectAfterValue,
            Some(Container::Array) => State::ArrayAfterValue,
            None => State::Done,
        };
        self.advance(1);
        SpannedEvent {
            start: self.offset - 1,
            end: self.offset,
            event,
        }
    }

    fn expect_literal(&mut self, literal: &[u8], error: ErrorKind) -> Result<(), ParseError> {
        if self.input.starts_with(literal) {
            self.advance(literal.len());
            Ok(())
        } else {
            Err(self.err(error))
        }
    }

    fn expect_string(&mut self) -> Result<SpannedEvent<'input>, ParseError> {
        let start = self.offset;
        self.expect_byte(b'"', self.err(ErrorKind::ExpectedString))?;
        let s = self.parse_str_tail()?;
        let ev = SpannedEvent {
            start,
            end: self.offset,
            event: Event::String(s),
        };
        Ok(ev)
    }

    fn remember_container(&mut self) {
        match self.state {
            State::Init | State::Done => {}
            State::ObjectStart | State::ObjectAfterKey | State::ObjectAfterValue => {
                self.container_stack.push(Container::Object)
            }
            State::ArrayStart | State::ArrayAfterValue => {
                self.container_stack.push(Container::Array)
            }
        }
    }

    fn expect_value(&mut self, next_state: State) -> Result<SpannedEvent<'input>, ParseError> {
        self.skip_whitespace();
        let c = self.peek(ErrorKind::ExpectedValue)?;

        let (ev, state) = match c {
            b'{' => {
                let ev = SpannedEvent {
                    start: self.offset,
                    end: self.offset + 1,
                    event: Event::BeginObject,
                };
                self.remember_container();
                self.advance(1);
                (ev, State::ObjectStart)
            }
            b'[' => {
                let ev = SpannedEvent {
                    start: self.offset,
                    end: self.offset + 1,
                    event: Event::BeginArray,
                };
                self.remember_container();
                self.advance(1);
                (ev, State::ArrayStart)
            }
            b'f' => {
                let ev = SpannedEvent {
                    start: self.offset,
                    end: self.offset + b"false".len(),
                    event: Event::Boolean(false),
                };
                self.expect_literal(b"false", ErrorKind::ExpectedFalse)?;
                (ev, next_state)
            }
            b't' => {
                let ev = SpannedEvent {
                    start: self.offset,
                    end: self.offset + b"true".len(),
                    event: Event::Boolean(true),
                };
                self.expect_literal(b"true", ErrorKind::ExpectedTrue)?;
                (ev, next_state)
            }
            b'n' => {
                let ev = SpannedEvent {
                    start: self.offset,
                    end: self.offset + b"null".len(),
                    event: Event::Null,
                };
                self.expect_literal(b"null", ErrorKind::ExpectedNull)?;
                (ev, next_state)
            }
            b'"' => (self.expect_string()?, next_state),
            b'-' | b'0'..=b'9' => {
                let start = self.offset;
                let n = self.consume_number()?;
                let ev = SpannedEvent {
                    start,
                    end: self.offset,
                    event: Event::Number(n),
                };
                (ev, next_state)
            }
            _ => {
                self.advance(1);
                return Err(self.err(ErrorKind::ExpectedValue));
            }
        };

        self.state = state;
        Ok(ev)
    }

    fn skip_whitespace(&mut self) {
        let not_ws = |c: u8| !(c == b' ' || c == b'\t' || c == b'\n' || c == b'\r');
        match self.input.iter().copied().position(not_ws) {
            Some(offset) => {
                self.advance(offset);
            }
            None => {
                self.advance(self.input.len());
            }
        }
    }

    fn peek(&self, expecting: ErrorKind) -> Result<u8, ParseError> {
        self.input
            .first()
            .copied()
            .ok_or_else(|| self.err(expecting))
    }

    fn err(&self, kind: ErrorKind) -> ParseError {
        ParseError {
            byte_offset: self.offset.saturating_sub(1),
            kind,
        }
    }

    fn advance(&mut self, count: usize) {
        self.offset += count;
        self.input = &self.input[count..];
    }

    fn next_byte(&mut self, expecting: ErrorKind) -> Result<u8, ParseError> {
        let b = self.peek(expecting)?;
        self.advance(1);
        Ok(b)
    }

    fn expect_byte(&mut self, b: u8, err: ParseError) -> Result<(), ParseError> {
        if self.next_byte(err.kind).is_ok_and(|x| x == b) {
            Ok(())
        } else {
            Err(err)
        }
    }

    fn next_hex(&mut self, eos_error: ParseError) -> Result<u16, ParseError> {
        let c = self.next_byte(eos_error.kind).map_err(|_| eos_error)?;
        match c {
            b'0'..=b'9' => Ok((c - b'0') as u16),
            b'a'..=b'f' => Ok((c - b'a' + 10) as u16),
            b'A'..=b'F' => Ok((c - b'A' + 10) as u16),
            _ => Err(self.err(ErrorKind::InvalidHex(c))),
        }
    }

    fn four_hex(&mut self, eos_error: ParseError) -> Result<u16, ParseError> {
        let mut code = 0;
        code += self.next_hex(eos_error)? << 12;
        code += self.next_hex(eos_error)? << 8;
        code += self.next_hex(eos_error)? << 4;
        code += self.next_hex(eos_error)?;
        Ok(code)
    }

    fn parse_str_tail_slow(&mut self, capacity: usize) -> Result<Cow<'input, str>, ParseError> {
        let mut s = Vec::with_capacity(capacity);
        let string_start_offset = self.offset.saturating_sub(1);
        let unterminated = ParseError {
            byte_offset: string_start_offset,
            kind: ErrorKind::UnterminatedString,
        };

        loop {
            let b = self
                .next_byte(ErrorKind::UnterminatedString)
                .map_err(|_| unterminated)?;

            if b == b'\\' {
                let b = self
                    .next_byte(ErrorKind::UnterminatedString)
                    .map_err(|_| unterminated)?;

                match b {
                    b'"' | b'\\' | b'/' => s.push(b),
                    b'n' => s.push(b'\n'),
                    b'r' => s.push(b'\r'),
                    b't' => s.push(b'\t'),
                    b'b' => s.push(0x08),
                    b'f' => s.push(0x0c),
                    b'u' => {
                        let hi = self.four_hex(unterminated)?;

                        let c = match char::from_u32(hi as u32) {
                            Some(c) => c,
                            None => {
                                let err = ParseError {
                                    byte_offset: self.offset,
                                    kind: ErrorKind::UnmatchedSurrogate,
                                };
                                self.expect_byte(b'\\', err)?;
                                self.expect_byte(b'u', err)?;

                                let lo = self.four_hex(err)?;

                                if !(is_high_surrogate(hi) && is_low_surrogate(lo)) {
                                    return Err(err);
                                }

                                let w = (hi & 0b000000_1111_000000) >> 6;
                                let x_hi = (hi & 0b000000_0000_111111) << 10;
                                let x_lo = lo & 0b000000_1111_111111;
                                let x = (x_hi | x_lo) as u32;
                                let code = (((w + 1) as u32) << 16) | x;
                                char::from_u32(code).unwrap()
                            }
                        };
                        let mut buf = [0u8; 4];
                        c.encode_utf8(&mut buf);
                        s.extend_from_slice(&buf[..c.len_utf8()]);
                    }
                    _ => {
                        return Err(self.err(ErrorKind::InvalidEscape(b)));
                    }
                };
            } else if b == b'"' {
                let s = String::from_utf8(s).map_err(|e| ParseError {
                    byte_offset: string_start_offset + 1 + e.utf8_error().valid_up_to(),
                    kind: ErrorKind::InvalidUtf8,
                })?;
                return Ok(s.into());
            } else if b <= 0x1F {
                // We don't check b.is_ascii_control(), because JSON has different rules.
                return Err(self.err(ErrorKind::UnescapedControl(b)));
            } else {
                s.push(b);
            }
        }
    }

    fn parse_str_tail(&mut self) -> Result<Cow<'input, str>, ParseError> {
        let Some(close) = memchr(b'"', self.input) else {
            return Err(self.err(ErrorKind::UnterminatedString));
        };

        if close == 0 {
            self.advance(1);
            Ok(Cow::Borrowed(""))
        } else if memchr(b'\\', &self.input[..close]).is_none() {
            if let Some(idx) = self.input[..close]
                .iter()
                .copied()
                .position(is_ascii_control)
            {
                return Err(ParseError {
                    byte_offset: self.offset + idx,
                    kind: ErrorKind::UnescapedControl(self.input[idx]),
                });
            }
            let s = std::str::from_utf8(&self.input[..close]).map_err(|e| ParseError {
                byte_offset: self.offset + e.valid_up_to(),
                kind: ErrorKind::InvalidUtf8,
            })?;
            self.advance(close + 1);
            Ok(Cow::Borrowed(s))
        } else {
            self.parse_str_tail_slow(close)
        }
    }

    fn consume_number(&mut self) -> Result<&'input str, ParseError> {
        let mut number_state = NumberParser {
            input: self.input,
            offset: 0,
        };
        let n = number_state.consume().map_err(|mut e| {
            e.byte_offset += self.offset;
            e
        })?;
        self.advance(n.len());
        Ok(str::from_utf8(n).unwrap())
    }
}

struct NumberParser<'input> {
    input: &'input [u8],
    offset: usize,
}

impl<'input> NumberParser<'input> {
    fn err(&self, kind: ErrorKind) -> ParseError {
        ParseError {
            byte_offset: self.offset.saturating_sub(1),
            kind,
        }
    }

    fn skip_digits(&mut self) {
        match self.input[self.offset..]
            .iter()
            .position(|c| !c.is_ascii_digit())
        {
            Some(offset) => self.offset += offset,
            None => self.offset = self.input.len(),
        }
    }

    fn skip_digits_at_least_one(&mut self) -> Result<(), ParseError> {
        let prev_offset = self.offset;
        self.skip_digits();
        if self.offset == prev_offset {
            Err(ParseError {
                byte_offset: self.offset,
                kind: ErrorKind::ExpectedDigit,
            })
        } else {
            Ok(())
        }
    }

    fn number_so_far(&self) -> &'input [u8] {
        &self.input[..self.offset]
    }

    fn next_byte(&mut self) -> Option<u8> {
        if self.offset < self.input.len() {
            let c = self.input[self.offset];
            self.offset += 1;
            Some(c)
        } else {
            None
        }
    }

    fn next_byte_or(&mut self, expecting: ErrorKind) -> Result<u8, ParseError> {
        if self.offset < self.input.len() {
            let c = self.input[self.offset];
            self.offset += 1;
            Ok(c)
        } else {
            Err(ParseError {
                byte_offset: self.input.len(),
                kind: expecting,
            })
        }
    }

    fn consume(&mut self) -> Result<&'input [u8], ParseError> {
        let mut c = self.next_byte_or(ErrorKind::ExpectedNumber)?;
        if c == b'-' {
            c = self.next_byte_or(ErrorKind::ExpectedDigit)?;
        } else if !c.is_ascii_digit() {
            return Err(self.err(ErrorKind::ExpectedNumber));
        }

        if c == b'0' {
            let Some(next) = self.next_byte() else {
                return Ok(self.number_so_far());
            };
            c = next;
            if c.is_ascii_digit() {
                return Err(self.err(ErrorKind::NumberWithLeadingZero));
            }
        } else if (b'1'..=b'9').contains(&c) {
            self.skip_digits();
            let Some(next) = self.next_byte() else {
                return Ok(self.number_so_far());
            };
            c = next;
        } else {
            return Err(self.err(ErrorKind::ExpectedDigit));
        }

        if c == b'.' {
            self.skip_digits_at_least_one()?;
            let Some(next) = self.next_byte() else {
                return Ok(self.number_so_far());
            };
            c = next;
        }

        if c == b'e' || c == b'E' {
            c = self.next_byte_or(ErrorKind::ExpectedExponentStart)?;
            if c == b'+' || c == b'-' {
                c = self.next_byte_or(ErrorKind::ExpectedDigit)?;
            }
            if !c.is_ascii_digit() {
                return Err(self.err(ErrorKind::ExpectedDigit));
            }
            self.skip_digits();

            // All the other branches consume one byte past the end of the
            // number, so make sure to match that.
            if self.next_byte().is_none() {
                return Ok(self.number_so_far());
            };
        }
        debug_assert!(self.offset > 0);
        Ok(&self.input[..self.offset - 1])
    }
}

#[cfg(test)]
mod tests {
    use crate::{ErrorKind, Event, NumberParser, Parser};

    fn parse_all(input: &[u8]) -> Vec<Event<'_>> {
        let mut parser = Parser::new(input);
        let mut ret = Vec::new();
        while let Some(ev) = parser.next_event().unwrap() {
            ret.push(ev.event);
        }
        ret
    }

    #[test]
    fn string() {
        let successes = [
            (r#""foo""#, "foo", 5),
            (r#""foo" trailing"#, "foo", 5),
            (r#""foo\n""#, "foo\n", 7),
            (r#""foo\n\n""#, "foo\n\n", 9),
            (r#""foo\u000a""#, "foo\n", 11),
            (r#""\uD834\uDD1E""#, "𝄞", 14),
        ];

        let failures: [(&[u8], _, _); _] = [
            (br#""foo"#, ErrorKind::UnterminatedString, 0),
            (br#""foo\"#, ErrorKind::UnterminatedString, 0),
            (br#""foo\u000""#, ErrorKind::InvalidHex(b'"'), 9),
            (br#""foo\x""#, ErrorKind::InvalidEscape(b'x'), 5),
            (b"\"foo\n\"", ErrorKind::UnescapedControl(b'\n'), 4),
            (b"\"foo\xff\xff\"", ErrorKind::InvalidUtf8, 4),
        ];

        for (input, expected, position) in successes {
            dbg!(input);
            let mut parser = Parser::new(input.as_bytes());
            parser.advance(1);

            let result = parser.parse_str_tail().unwrap();
            assert_eq!(&result, expected);
            assert_eq!(parser.offset, position);

            let mut parser = Parser::new(input.as_bytes());
            parser.advance(1);
            let result = parser.parse_str_tail_slow(0).unwrap();
            assert_eq!(&result, expected);
            assert_eq!(parser.offset, position);
        }

        for (input, expected, position) in failures {
            dbg!(input);

            let mut parser = Parser::new(input);
            parser.advance(1);
            let result = parser.parse_str_tail().unwrap_err();
            assert_eq!(result.kind, expected);
            assert_eq!(result.byte_offset, position);

            let mut parser = Parser::new(input);
            parser.advance(1);
            let result = parser.parse_str_tail_slow(0).unwrap_err();
            assert_eq!(result.kind, expected);
            assert_eq!(result.byte_offset, position);
        }
    }

    #[test]
    fn number() {
        let successes = [
            ("0", "0"),
            ("0.1", "0.1"),
            ("0,", "0"),
            ("-1", "-1"),
            ("1e-3", "1e-3"),
            ("1e-3,", "1e-3"),
            ("1e3", "1e3"),
            ("1e33", "1e33"),
            ("1.0e33", "1.0e33"),
        ];

        let failures = [
            ("01", ErrorKind::NumberWithLeadingZero, 1),
            ("+1", ErrorKind::ExpectedNumber, 0),
            ("--1", ErrorKind::ExpectedDigit, 1),
            ("0.", ErrorKind::ExpectedDigit, 2),
            ("0.,", ErrorKind::ExpectedDigit, 2),
            ("1e-", ErrorKind::ExpectedDigit, 3),
        ];

        for (input, expected) in successes {
            dbg!(input);
            let mut np = NumberParser {
                input: input.as_bytes(),
                offset: 0,
            };
            let n = np.consume().unwrap();
            let n = str::from_utf8(n).unwrap();

            assert_eq!(n, expected);
        }

        for (input, expected, position) in failures {
            dbg!(input);
            let mut np = NumberParser {
                input: input.as_bytes(),
                offset: 0,
            };
            let e = np.consume().unwrap_err();

            assert_eq!(e.kind, expected);
            assert_eq!(e.byte_offset, position);
        }
    }

    #[test]
    fn basic() {
        let successes: [(&str, &[Event<'_>]); _] = [
            ("[]", &[Event::BeginArray, Event::EndArray]),
            ("[] ", &[Event::BeginArray, Event::EndArray]),
            (" [ ] ", &[Event::BeginArray, Event::EndArray]),
            (
                " [ 1, 2 ] ",
                &[
                    Event::BeginArray,
                    Event::Number("1"),
                    Event::Number("2"),
                    Event::EndArray,
                ],
            ),
            (
                r#" [ 1, { "foo": "bar" } ] "#,
                &[
                    Event::BeginArray,
                    Event::Number("1"),
                    Event::BeginObject,
                    Event::String("foo".into()),
                    Event::String("bar".into()),
                    Event::EndObject,
                    Event::EndArray,
                ],
            ),
        ];

        for (input, expected) in successes {
            dbg!(input);

            let result = parse_all(input.as_bytes());
            assert_eq!(&result, expected);
        }
    }
}
