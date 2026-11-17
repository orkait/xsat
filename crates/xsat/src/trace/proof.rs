use std::io::{self, Write};

use crate::trace::statistics::{Counter, Shown};

const BINARY_ADD: u8 = b'a';
const DELETE: u8 = b'd';
const SEVEN_BITS: u32 = 0x7f;
const CONTINUATION: u8 = 0x80;
const SHIFT: u32 = 7;

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Format {
    Binary,
    Ascii,
    Idrup,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(crate) enum Step {
    Add,
    Delete,
    Input,
    Restore,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(crate) enum Conclusion<'a> {
    Query(&'a [i32]),
    Satisfiable(&'a [i32]),
    Unsatisfiable(&'a [i32]),
    Unknown,
}

pub struct Proof {
    out: Box<dyn Write + Send>,
    format: Format,
    line: Vec<i32>,
    failed: Option<io::Error>,
    added: u64,
    deleted: u64,
    lines: u64,
    literals: u64,
    flush: bool,
}

impl std::fmt::Debug for Proof {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter
            .debug_struct("Proof")
            .field("format", &self.format)
            .field("lines", &self.lines)
            .finish_non_exhaustive()
    }
}

impl Proof {
    #[must_use]
    pub fn new(out: Box<dyn Write + Send>, format: Format) -> Proof {
        Proof {
            out,
            format,
            line: Vec::new(),
            failed: None,
            added: 0,
            deleted: 0,
            lines: 0,
            literals: 0,
            flush: false,
        }
    }

    pub(crate) fn flush_every_line(&mut self) {
        self.flush = true;
    }

    fn write(&mut self, bytes: &[u8]) {
        if self.failed.is_none() {
            if let Err(error) = self.out.write_all(bytes) {
                self.failed = Some(error);
            }
        }
    }

    pub(crate) fn line(&mut self, step: Step, elits: impl IntoIterator<Item = i32>) {
        let prefix: &[u8] = match (step, self.format) {
            (Step::Input, Format::Binary | Format::Ascii) => return,
            (Step::Add | Step::Restore, Format::Binary) => &[BINARY_ADD],
            (Step::Add | Step::Restore, Format::Ascii) => &[],
            (Step::Delete, Format::Binary) => &[DELETE],
            (Step::Delete, Format::Ascii) => b"d ",
            (Step::Add, Format::Idrup) => b"l ",
            (Step::Delete, Format::Idrup) => b"w ",
            (Step::Input, Format::Idrup) => b"i ",
            (Step::Restore, Format::Idrup) => b"r ",
        };
        self.line.extend(elits);
        self.literals += u64::try_from(self.line.len()).unwrap_or(u64::MAX);
        self.write(prefix);
        match step {
            Step::Add | Step::Restore => self.added += 1,
            Step::Delete => self.deleted += 1,
            Step::Input => {}
        }
        self.print_line();
    }

    pub(crate) fn conclude(&mut self, conclusion: Conclusion<'_>) {
        if self.format != Format::Idrup {
            return;
        }
        let (status, letter, lits): (&[u8], &[u8], &[i32]) = match conclusion {
            Conclusion::Query(assumptions) => (b"", b"q ", assumptions),
            Conclusion::Satisfiable(model) => (b"s SATISFIABLE\n", b"m ", model),
            Conclusion::Unsatisfiable(core) => (b"s UNSATISFIABLE\n", b"u ", core),
            Conclusion::Unknown => {
                self.write(b"s UNKNOWN\n");
                return;
            }
        };
        self.write(status);
        self.write(letter);
        self.line.extend_from_slice(lits);
        self.print_line();
    }

    fn print_line(&mut self) {
        self.lines += 1;
        let mut text = Vec::new();
        for &elit in &self.line {
            match self.format {
                Format::Binary => {
                    let mut x = 2 * elit.unsigned_abs() + u32::from(elit < 0);
                    while x & !SEVEN_BITS != 0 {
                        text.push(low_byte(x) | CONTINUATION);
                        x >>= SHIFT;
                    }
                    text.push(low_byte(x));
                }
                Format::Ascii | Format::Idrup => {
                    text.extend_from_slice(elit.to_string().as_bytes());
                    text.push(b' ');
                }
            }
        }
        match self.format {
            Format::Binary => text.push(0),
            Format::Ascii | Format::Idrup => text.extend_from_slice(b"0\n"),
        }
        self.write(&text);
        self.line.clear();
        if self.flush && self.failed.is_none() {
            if let Err(error) = self.out.flush() {
                self.failed = Some(error);
            }
        }
    }

    #[must_use]
    pub fn counters(&self) -> Vec<Counter> {
        [
            ("proof_added", self.added, Shown::Always),
            ("proof_deleted", self.deleted, Shown::Always),
            ("proof_lines", self.lines, Shown::Verbose),
            ("proof_literals", self.literals, Shown::Verbose),
        ]
        .into_iter()
        .map(|(name, value, shown)| Counter { name, value, shown })
        .collect()
    }

    pub(crate) fn incremental(&self) -> bool {
        self.format == Format::Idrup
    }

    pub fn finish(mut self) -> io::Result<()> {
        if let Some(error) = self.failed.take() {
            return Err(error);
        }
        self.out.flush()
    }
}

fn low_byte(x: u32) -> u8 {
    u8::try_from(x & SEVEN_BITS).unwrap_or(0)
}
