/// An error tolerance with an absolute and a relative part.
///
/// A quantity of size `x` is accepted when its error is at most
/// `abs + rel * |x|` (see [`Tolerance::bound`]). The absolute part matters
/// near zero, where a relative error is meaningless; the relative part
/// matters for large values, where an absolute error below the spacing of
/// floating-point numbers can never be reached.
///
/// There is no default: sensible values depend on the algorithm, so each
/// algorithm's options provide their own.
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct Tolerance {
    /// Absolute tolerance. Must be non-negative.
    pub abs: f64,
    /// Relative tolerance. Must be non-negative.
    pub rel: f64,
}

impl Tolerance {
    /// Creates a tolerance from its absolute and relative parts.
    pub const fn new(abs: f64, rel: f64) -> Self {
        Self { abs, rel }
    }

    /// The largest accepted error for a quantity of size `x`:
    /// `abs + rel * |x|`.
    pub fn bound(&self, x: f64) -> f64 {
        self.abs + self.rel * x.abs()
    }

    /// Whether both parts are non-negative numbers (not NaN).
    pub fn is_valid(&self) -> bool {
        self.abs >= 0.0 && self.rel >= 0.0
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn bound_adds_absolute_and_relative_parts() {
        let tol = Tolerance::new(0.5, 0.25);
        assert_eq!(tol.bound(0.0), 0.5);
        assert_eq!(tol.bound(4.0), 1.5);
        assert_eq!(tol.bound(-4.0), 1.5);
    }

    #[test]
    fn validity() {
        assert!(Tolerance::new(0.0, 0.0).is_valid());
        assert!(Tolerance::new(1e-12, 1e-15).is_valid());
        assert!(!Tolerance::new(-1e-12, 0.0).is_valid());
        assert!(!Tolerance::new(0.0, -1e-15).is_valid());
        assert!(!Tolerance::new(f64::NAN, 0.0).is_valid());
        assert!(!Tolerance::new(0.0, f64::NAN).is_valid());
    }
}
