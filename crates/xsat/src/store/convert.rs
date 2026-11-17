pub(crate) fn widen(index: u32) -> usize {
    usize::try_from(index).unwrap_or(usize::MAX)
}

pub(crate) fn narrow(index: usize) -> u32 {
    u32::try_from(index).unwrap_or(u32::MAX)
}

#[expect(
    clippy::as_conversions,
    clippy::cast_possible_truncation,
    clippy::cast_sign_loss,
    reason = "Kissat converts doubles to counters by truncation and the port must match it"
)]
pub(crate) fn truncate(value: f64) -> u64 {
    value as u64
}

#[expect(
    clippy::as_conversions,
    clippy::cast_precision_loss,
    reason = "Kissat converts 64-bit counters to double and the port must match it"
)]
pub(crate) fn real(value: u64) -> f64 {
    value as f64
}

pub(crate) const PER_MILLE: f64 = 1000.0;
pub(crate) const PERCENT: f64 = 100.0;

pub(crate) fn average(a: f64, b: f64) -> f64 {
    if b == 0.0 {
        0.0
    } else {
        a / b
    }
}

pub(crate) fn percent(a: u64, b: u64) -> f64 {
    average(PERCENT * real(a), real(b))
}
