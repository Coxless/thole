//! The affine map from `[-1, 1]` to `[a, b]`, shared by the rules.

/// The midpoint `c` of `[a, b]` and the half-length `h = (b - a) / 2`, so
/// that `x ↦ c + h x` maps `[-1, 1]` onto `[a, b]`.
///
/// Each end is halved before it is added or subtracted, so that neither
/// overflows. Halving is exact unless the result is subnormal, so `c` is
/// `(a + b) / 2` correctly rounded, like `f64::midpoint`, but by a sequence
/// of operations that the oracle repeats.
pub(crate) fn center_and_half(a: f64, b: f64) -> (f64, f64) {
    (a / 2.0 + b / 2.0, b / 2.0 - a / 2.0)
}
