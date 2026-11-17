use std::io::{ErrorKind, Read};

use crate::error::{Fault, ParseError};

const BUFFER_BYTES: usize = 1 << 20;
const FIRST_LINE: u64 = 1;
const DECIMAL: u8 = 10;
pub const MAX_VARIABLE: i32 = (1 << 30) - 1;

const NEW_LINE: u8 = b'\n';
const CARRIAGE_RETURN: u8 = b'\r';
const SPACE: u8 = b' ';
const TAB: u8 = b'\t';
const COMMENT: u8 = b'c';
const PROBLEM: u8 = b'p';
const MINUS: u8 = b'-';
const ZERO: u8 = b'0';

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Strictness {
    Relaxed,
    Normal,
    Pedantic,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Header {
    pub variables: i32,
    pub clauses: u64,
}

#[derive(Debug)]
pub struct Dimacs<R> {
    input: R,
    buffer: Vec<u8>,
    pos: usize,
    end: usize,
    line: u64,
    strictness: Strictness,
}

impl<R: Read> Dimacs<R> {
    pub fn new(input: R, strictness: Strictness) -> Dimacs<R> {
        Dimacs {
            input,
            buffer: vec![0; BUFFER_BYTES],
            pos: 0,
            end: 0,
            line: FIRST_LINE,
            strictness,
        }
    }

    pub fn header(&mut self) -> Result<Header, ParseError> {
        let mut first = true;
        loop {
            let ch = self.next()?;
            match ch {
                Some(PROBLEM) => break,
                None if first => return Err(self.fail(Fault::Empty)),
                None => return Err(self.fail(Fault::EofBeforeHeader)),
                Some(CARRIAGE_RETURN) => {
                    let after = self.next()?;
                    if after != Some(NEW_LINE) {
                        return Err(self.fail(Fault::CarriageReturn));
                    }
                    if self.strictness == Strictness::Pedantic {
                        return Err(self.at(after, Fault::EmptyLine));
                    }
                }
                Some(NEW_LINE) if self.strictness == Strictness::Pedantic => {
                    return Err(self.at(ch, Fault::EmptyLine));
                }
                Some(NEW_LINE) => {}
                Some(COMMENT) => self.skip_header_comment()?,
                Some(_) => return Err(self.fail(Fault::LineStart)),
            }
            first = false;
        }
        let ch = self.next()?;
        if ch != Some(SPACE) {
            return Err(self.at(ch, Fault::SpaceAfterP));
        }
        let ch = self.next_lenient()?;
        self.expect(ch, b'c', Fault::CAfterP)?;
        let ch = self.next()?;
        self.expect(ch, b'n', Fault::NAfterPC)?;
        let ch = self.next()?;
        self.expect(ch, b'f', Fault::FAfterPCn)?;
        let ch = self.next()?;
        self.expect(ch, SPACE, Fault::SpaceAfterCnf)?;
        let ch = self.next_lenient()?;
        let Some(first_digit) = digit(ch) else {
            return Err(self.at(ch, Fault::DigitAfterCnf));
        };
        let (variables, mut ch) = self.number(first_digit, Fault::MaxVariableTooLarge)?;
        let Some(after) = ch else {
            return Err(self.fail(Fault::EofInMaxVariable));
        };
        if after == CARRIAGE_RETURN {
            ch = self.next()?;
            if ch != Some(NEW_LINE) {
                return Err(self.fail(Fault::CarriageReturn));
            }
        }
        if ch == Some(NEW_LINE) {
            return Err(self.at(ch, Fault::NewLineAfterMaxVariable));
        }
        if ch != Some(SPACE) {
            return Err(self.fail(Fault::SpaceAfterMaxVariable));
        }
        let ch = self.next_lenient()?;
        let first_digit = digit(ch).ok_or_else(|| self.fail(Fault::ClausesAfterMaxVariable))?;
        let (clauses, ch) = self.count(first_digit)?;
        if ch.is_none() {
            return Err(self.fail(Fault::EofInClauses));
        }
        let mut ch = self.blanks(ch)?;
        if ch == Some(CARRIAGE_RETURN) {
            ch = self.next()?;
            if ch != Some(NEW_LINE) {
                return Err(self.fail(Fault::CarriageReturn));
            }
        }
        match ch {
            None => Err(self.fail(Fault::EofAfterClauses)),
            Some(NEW_LINE) => Ok(Header { variables, clauses }),
            Some(_) => Err(self.fail(Fault::NewLineAfterClauses)),
        }
    }

    pub fn clauses(&mut self, header: Header, mut add: impl FnMut(i32)) -> Result<(), ParseError> {
        let relaxed = self.strictness == Strictness::Relaxed;
        let pedantic = self.strictness == Strictness::Pedantic;
        let mut parsed: u64 = 0;
        let mut lit: i32 = 0;
        loop {
            let ch = match self.next()? {
                None => break,
                Some(SPACE | TAB | NEW_LINE) => continue,
                Some(CARRIAGE_RETURN) => {
                    self.line_feed()?;
                    continue;
                }
                Some(COMMENT) => {
                    if self.skip_comment(Fault::EofInCommentAfterHeader)? {
                        continue;
                    }
                    break;
                }
                Some(ch) => ch,
            };
            let (negative, first) = if ch == MINUS {
                let after = self.next()?;
                match after {
                    None => return Err(self.fail(Fault::EofAfterMinus)),
                    Some(NEW_LINE) => return Err(self.at(after, Fault::NewLineAfterMinus)),
                    Some(ZERO) => return Err(self.fail(Fault::NonZeroAfterMinus)),
                    Some(_) => (
                        true,
                        digit(after).ok_or_else(|| self.fail(Fault::DigitAfterMinus))?,
                    ),
                }
            } else {
                (
                    false,
                    digit(Some(ch)).ok_or_else(|| self.fail(Fault::DigitOrMinus))?,
                )
            };
            let (index, ch) = self.number(first, Fault::IndexTooLarge)?;
            let ch = match ch {
                None if pedantic && index != 0 => return Err(self.fail(Fault::EofAfterLiteral)),
                None if pedantic => return Err(self.fail(Fault::EofAfterZero)),
                None => None,
                Some(CARRIAGE_RETURN) => {
                    self.line_feed()?;
                    Some(NEW_LINE)
                }
                Some(COMMENT) => self
                    .skip_comment(Fault::EofInCommentAfterLiteral)?
                    .then_some(NEW_LINE),
                Some(SPACE | TAB | NEW_LINE) => ch,
                Some(_) => return Err(self.fail(Fault::SpaceAfterLiteral)),
            };
            if !relaxed && index > header.variables {
                return Err(self.at(ch, Fault::IndexExceeded));
            }
            if index == 0 {
                if !relaxed && parsed == header.clauses {
                    return Err(self.at(ch, Fault::TooManyClauses));
                }
                parsed += 1;
                lit = 0;
            } else {
                lit = if negative { -index } else { index };
            }
            add(lit);
        }
        if lit != 0 {
            return Err(self.fail(Fault::TrailingZero));
        }
        if !relaxed && parsed < header.clauses {
            return Err(self.fail(if parsed + 1 == header.clauses {
                Fault::OneClauseMissing
            } else {
                Fault::ClausesMissing
            }));
        }
        Ok(())
    }

    fn next(&mut self) -> Result<Option<u8>, ParseError> {
        if self.pos == self.end {
            self.pos = 0;
            self.end = loop {
                match self.input.read(&mut self.buffer) {
                    Ok(read) => break read,
                    Err(error) if error.kind() == ErrorKind::Interrupted => {}
                    Err(error) => {
                        return Err(ParseError {
                            line: self.line,
                            fault: Fault::Read(error),
                        })
                    }
                }
            };
        }
        let Some(&ch) = self.buffer.get(self.pos).filter(|_| self.pos < self.end) else {
            return Ok(None);
        };
        self.pos += 1;
        if ch == NEW_LINE {
            self.line += 1;
        }
        Ok(Some(ch))
    }

    fn next_lenient(&mut self) -> Result<Option<u8>, ParseError> {
        let ch = self.next()?;
        if self.strictness == Strictness::Pedantic {
            Ok(ch)
        } else {
            self.blanks(ch)
        }
    }

    fn blanks(&mut self, mut ch: Option<u8>) -> Result<Option<u8>, ParseError> {
        if self.strictness != Strictness::Pedantic {
            while matches!(ch, Some(SPACE | TAB)) {
                ch = self.next()?;
            }
        }
        Ok(ch)
    }

    fn expect(&self, ch: Option<u8>, wanted: u8, fault: Fault) -> Result<(), ParseError> {
        if ch == Some(wanted) {
            Ok(())
        } else {
            Err(self.at(ch, fault))
        }
    }

    fn line_feed(&mut self) -> Result<(), ParseError> {
        if self.next()? == Some(NEW_LINE) {
            Ok(())
        } else {
            Err(self.fail(Fault::CarriageReturn))
        }
    }

    fn skip_header_comment(&mut self) -> Result<(), ParseError> {
        loop {
            match self.next()? {
                Some(NEW_LINE) => return Ok(()),
                Some(CARRIAGE_RETURN) => return self.line_feed(),
                None => return Err(self.fail(Fault::EofInHeaderComment)),
                Some(_) => {}
            }
        }
    }

    fn skip_comment(&mut self, eof: Fault) -> Result<bool, ParseError> {
        loop {
            match self.next()? {
                Some(NEW_LINE) => return Ok(true),
                None if self.strictness == Strictness::Pedantic => return Err(self.fail(eof)),
                None => return Ok(false),
                Some(_) => {}
            }
        }
    }

    fn number(&mut self, first: u8, overflow: Fault) -> Result<(i32, Option<u8>), ParseError> {
        let mut value = i32::from(first);
        loop {
            let ch = self.next()?;
            let Some(next) = digit(ch) else {
                return Ok((value, ch));
            };
            match value
                .checked_mul(i32::from(DECIMAL))
                .and_then(|value| value.checked_add(i32::from(next)))
                .filter(|value| *value <= MAX_VARIABLE)
            {
                Some(grown) => value = grown,
                None => return Err(self.fail(overflow)),
            }
        }
    }

    fn count(&mut self, first: u8) -> Result<(u64, Option<u8>), ParseError> {
        let mut value = u64::from(first);
        loop {
            let ch = self.next()?;
            let Some(next) = digit(ch) else {
                return Ok((value, ch));
            };
            value = value
                .checked_mul(u64::from(DECIMAL))
                .and_then(|value| value.checked_add(u64::from(next)))
                .ok_or_else(|| self.fail(Fault::ClausesTooLarge))?;
        }
    }

    fn fail(&self, fault: Fault) -> ParseError {
        ParseError {
            line: self.line,
            fault,
        }
    }

    fn at(&self, ch: Option<u8>, fault: Fault) -> ParseError {
        let line = if ch == Some(NEW_LINE) {
            self.line - 1
        } else {
            self.line
        };
        ParseError { line, fault }
    }
}

fn digit(ch: Option<u8>) -> Option<u8> {
    ch.filter(u8::is_ascii_digit).map(|ch| ch - ZERO)
}
