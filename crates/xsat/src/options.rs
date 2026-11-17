mod table;

pub use table::{Opt, COUNT, SPECS};

use crate::error::OptionError;

const OFF: i32 = 0;
const ON: i32 = 1;
const STABLE_ALWAYS: i32 = 2;
const STABLE_UNSAT: i32 = 0;
const TARGET_SAT: i32 = 2;
const RESTARTINT_SAT: i32 = 50;
const TRUE_WORD: &str = "true";
const FALSE_WORD: &str = "false";
const LONG_PREFIX: &str = "--";
const NEGATION: &str = "no-";
const ASSIGN: char = '=';
const END: u8 = 0;
const MINUS: u8 = b'-';
const EXPONENT: u8 = b'e';
const POWER: u8 = b'^';
const DECIMAL: u64 = 10;
const SMALLEST_BASE: u64 = 2;

const UNRANGED: [Opt; 5] = [
    Opt::Quiet,
    Opt::Reduce,
    Opt::Reluctant,
    Opt::Rephase,
    Opt::Restart,
];

const PLAIN: [(Opt, i32); 13] = [
    (Opt::Bumpreasons, OFF),
    (Opt::Chrono, OFF),
    (Opt::Compact, OFF),
    (Opt::Eagersubsume, OFF),
    (Opt::Jumpreasons, OFF),
    (Opt::Otfs, OFF),
    (Opt::Preprocess, OFF),
    (Opt::Reorder, OFF),
    (Opt::Rephase, OFF),
    (Opt::Restartreusetrail, OFF),
    (Opt::Simplify, OFF),
    (Opt::Stable, STABLE_ALWAYS),
    (Opt::Tumble, OFF),
];
const BASIC: [(Opt, i32); 3] = [
    (Opt::Restart, OFF),
    (Opt::Reduce, OFF),
    (Opt::Minimize, OFF),
];
const SAT: [(Opt, i32); 2] = [(Opt::Target, TARGET_SAT), (Opt::Restartint, RESTARTINT_SAT)];
const UNSAT: [(Opt, i32); 1] = [(Opt::Stable, STABLE_UNSAT)];

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Spec {
    pub opt: Opt,
    pub name: &'static str,
    pub low: i32,
    pub value: i32,
    pub high: i32,
    pub help: &'static str,
}

impl Opt {
    #[expect(
        clippy::as_conversions,
        reason = "an Opt discriminant is its row in SPECS"
    )]
    const fn row(self) -> usize {
        self as usize
    }

    #[must_use]
    pub fn spec(self) -> Spec {
        SPECS[self.row()]
    }

    #[must_use]
    pub fn named(name: &str) -> Option<Opt> {
        SPECS
            .iter()
            .find(|spec| spec.name == name)
            .map(|spec| spec.opt)
    }

    #[must_use]
    pub fn ranged(self) -> bool {
        !UNRANGED.contains(&self)
    }
}

const _: () = {
    let mut row = 0;
    while row < COUNT {
        assert!(
            SPECS[row].opt.row() == row,
            "SPECS lists the options in Opt order"
        );
        row += 1;
    }
};

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Options {
    values: [i32; COUNT],
}

impl Default for Options {
    fn default() -> Options {
        Options {
            values: SPECS.map(|spec| spec.value),
        }
    }
}

impl Options {
    #[must_use]
    pub fn get(&self, opt: Opt) -> i32 {
        self.values[opt.row()]
    }

    pub fn set(&mut self, opt: Opt, value: i32) -> Result<(), OptionError> {
        let spec = opt.spec();
        if !(spec.low..=spec.high).contains(&value) {
            return Err(OptionError::Range {
                name: spec.name,
                value,
            });
        }
        self.values[opt.row()] = value;
        Ok(())
    }

    pub fn configure(&mut self, configuration: Configuration) {
        match configuration {
            Configuration::Basic => {
                self.assign(&PLAIN);
                self.assign(&BASIC);
            }
            Configuration::Default => {}
            Configuration::Plain => self.assign(&PLAIN),
            Configuration::Sat => self.assign(&SAT),
            Configuration::Unsat => self.assign(&UNSAT),
        }
    }

    fn assign(&mut self, settings: &[(Opt, i32)]) {
        for &(opt, value) in settings {
            self.values[opt.row()] = value;
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Configuration {
    Basic,
    Default,
    Plain,
    Sat,
    Unsat,
}

impl Configuration {
    pub const ALL: [Configuration; 5] = [
        Configuration::Basic,
        Configuration::Default,
        Configuration::Plain,
        Configuration::Sat,
        Configuration::Unsat,
    ];

    #[must_use]
    pub fn name(self) -> &'static str {
        match self {
            Configuration::Basic => "basic",
            Configuration::Default => "default",
            Configuration::Plain => "plain",
            Configuration::Sat => "sat",
            Configuration::Unsat => "unsat",
        }
    }

    #[must_use]
    pub fn help(self) -> &'static str {
        match self {
            Configuration::Basic => {
                "basic CDCL solving ('--plain' but no restarts, minimize, reduce)"
            }
            Configuration::Default => "default configuration",
            Configuration::Plain => "plain CDCL solving without advanced techniques",
            Configuration::Sat => "target satisfiable instances ('--target=2 --restartint=50')",
            Configuration::Unsat => "target unsatisfiable instances ('--stable=0')",
        }
    }

    #[must_use]
    pub fn named(name: &str) -> Option<Configuration> {
        Configuration::ALL
            .into_iter()
            .find(|configuration| configuration.name() == name)
    }
}

#[must_use]
pub fn parse_arg(arg: &str) -> Option<(Opt, i32)> {
    let body = arg.strip_prefix(LONG_PREFIX)?;
    if let Some((name, value)) = body.split_once(ASSIGN) {
        Some((Opt::named(name)?, parse_value(value)?))
    } else if let Some(name) = body.strip_prefix(NEGATION) {
        Some((Opt::named(name)?, OFF))
    } else {
        Some((Opt::named(body)?, ON))
    }
}

#[must_use]
pub fn parse_value(text: &str) -> Option<i32> {
    match text {
        TRUE_WORD => return Some(ON),
        FALSE_WORD => return Some(OFF),
        _ => {}
    }
    let mut digits = Digits::new(text);
    let limit = u64::from(i32::MIN.unsigned_abs());
    let mut ch = digits.next();
    let negative = ch == MINUS;
    if negative {
        ch = digits.next();
    }
    let mut res = Digits::value(ch)?;
    loop {
        ch = digits.next();
        let Some(digit) = Digits::value(ch) else {
            break;
        };
        res = res * DECIMAL + digit;
        if res > limit || res == 0 {
            return None;
        }
    }
    if ch == EXPONENT {
        let first = Digits::value(digits.next())?;
        if res == 0 {
            digits.rest_are_digits()?;
        } else {
            if !digits.at_end() {
                return None;
            }
            for _ in 0..first {
                res *= DECIMAL;
                if res > limit {
                    return None;
                }
            }
        }
    } else if ch == POWER {
        let base = res;
        let mut exponent = Digits::value(digits.next())?;
        if base < SMALLEST_BASE {
            digits.rest_are_digits()?;
        } else {
            let next = digits.next();
            if let Some(digit) = Digits::value(next) {
                if !digits.at_end() {
                    return None;
                }
                exponent = exponent * DECIMAL + digit;
                if exponent == 0 {
                    return None;
                }
            } else if next != END {
                return None;
            }
        }
        if exponent > 0 {
            for _ in 1..exponent {
                res *= base;
                if res > limit {
                    return None;
                }
            }
        } else if base > 0 {
            res = 1;
        } else {
            return None;
        }
    } else if ch != END {
        return None;
    }
    if !negative && res == limit {
        return None;
    }
    let magnitude = i64::try_from(res).ok()?;
    i32::try_from(if negative { -magnitude } else { magnitude }).ok()
}

struct Digits<'a> {
    bytes: &'a [u8],
    at: usize,
}

impl<'a> Digits<'a> {
    fn new(text: &'a str) -> Digits<'a> {
        Digits {
            bytes: text.as_bytes(),
            at: 0,
        }
    }

    fn next(&mut self) -> u8 {
        let ch = self.bytes.get(self.at).copied().unwrap_or(END);
        self.at += 1;
        ch
    }

    fn at_end(&self) -> bool {
        self.bytes.get(self.at).is_none()
    }

    fn rest_are_digits(&mut self) -> Option<()> {
        loop {
            let ch = self.next();
            if Digits::value(ch).is_none() {
                return (ch == END).then_some(());
            }
        }
    }

    fn value(ch: u8) -> Option<u64> {
        ch.is_ascii_digit().then(|| u64::from(ch - b'0'))
    }
}
