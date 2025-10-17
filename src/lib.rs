#![allow(clippy::unusual_byte_groupings)]

use memchr::memchr;
use std::borrow::Cow;

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum ErrorKind {
    InvalidUtf8,
    UnexpectedEos,
    UnterminatedString,
    UnescapedControl(u8),
    UnmatchedSurrogate,
    InvalidEscape(u8),
    InvalidHex(u8),
}

#[derive(Copy, Clone, Debug)]
pub struct ParseError {
    pub byte_offset: usize,
    pub kind: ErrorKind,
}

pub struct Parser<'input> {
    offset: usize,
    input: &'input [u8],
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
    (0xD00..=0xDBFF).contains(&c)
}

fn is_low_surrogate(c: u16) -> bool {
    (0xDC0..=0xDFFF).contains(&c)
}

impl<'input> Parser<'input> {
    fn peek(&self) -> Result<u8, ParseError> {
        self.input
            .first()
            .copied()
            .ok_or_else(|| self.err(ErrorKind::UnexpectedEos))
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

    fn next_byte(&mut self) -> Result<u8, ParseError> {
        let b = self.peek()?;
        self.advance(1);
        Ok(b)
    }

    fn expect(&mut self, b: u8, err: ParseError) -> Result<(), ParseError> {
        if self.next_byte().is_ok_and(|x| x == b) {
            Ok(())
        } else {
            Err(err)
        }
    }

    fn next_hex(&mut self, eos_error: ParseError) -> Result<u16, ParseError> {
        let c = self.next_byte().map_err(|_| eos_error)?;
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
            let b = self.next_byte().map_err(|_| unterminated)?;

            if b == b'\\' {
                let b = self.next_byte().map_err(|_| unterminated)?;

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
                                self.expect(b'\\', err)?;
                                self.expect(b'u', err)?;

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
}

#[cfg(test)]
mod tests {
    use crate::{ErrorKind, Parser};

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
            let mut parser = Parser {
                input: &input.as_bytes()[1..],
                offset: 1,
            };

            let result = parser.parse_str_tail().unwrap();
            assert_eq!(&result, expected);
            assert_eq!(parser.offset, position);

            let mut parser = Parser {
                input: &input.as_bytes()[1..],
                offset: 1,
            };
            let result = parser.parse_str_tail_slow(0).unwrap();
            assert_eq!(&result, expected);
            assert_eq!(parser.offset, position);
        }

        for (input, expected, position) in failures {
            dbg!(input);
            let mut parser = Parser {
                input: &input[1..],
                offset: 1,
            };

            let result = parser.parse_str_tail().unwrap_err();
            assert_eq!(result.kind, expected);
            assert_eq!(result.byte_offset, position);

            let mut parser = Parser {
                input: &input[1..],
                offset: 1,
            };
            let result = parser.parse_str_tail_slow(0).unwrap_err();
            assert_eq!(result.kind, expected);
            assert_eq!(result.byte_offset, position);
        }
    }
}
