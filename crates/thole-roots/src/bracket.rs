//! What the bracketing methods share.

use crate::{Error, Options};

/// A root located by a bracketing method.
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct Root {
    /// The approximation of the root. It lies in the final bracket.
    pub x: f64,
    /// Lower end of the final bracket.
    pub lo: f64,
    /// Upper end of the final bracket.
    pub hi: f64,
    /// Number of steps taken.
    pub iterations: usize,
}

/// Checks the arguments that every bracketing method takes.
pub(crate) fn check_arguments(a: f64, b: f64, options: &Options) -> Result<(), Error> {
    if !(a.is_finite() && b.is_finite() && a <= b) {
        return Err(Error::InvalidBracket { a, b });
    }
    let tol = options.tol;
    if !tol.is_valid() {
        return Err(Error::InvalidTolerance {
            abs: tol.abs,
            rel: tol.rel,
        });
    }
    Ok(())
}

/// Evaluates `f` at `x`. A NaN value is an error.
pub(crate) fn eval(f: &mut impl FnMut(f64) -> f64, x: f64) -> Result<f64, Error> {
    let fx = f(x);
    if fx.is_nan() {
        Err(Error::NanValue { x })
    } else {
        Ok(fx)
    }
}

/// Whether `u` and `v` have opposite signs or one of them is zero.
///
/// Over the real numbers this is `u * v <= 0`, the form used in the Lean
/// definition `SignChange`, which the oracle evaluates exactly. The product is avoided here because it can
/// underflow to zero for two small values of the same sign.
pub(crate) fn sign_change(u: f64, v: f64) -> bool {
    u == 0.0 || v == 0.0 || (u < 0.0) != (v < 0.0)
}

#[cfg(test)]
mod tests {
    use super::sign_change;

    #[test]
    fn sign_change_matches_the_sign_of_the_product() {
        let values = [-2.0, -1e-300, -0.0, 0.0, 1e-300, 2.0, f64::INFINITY];
        for u in values {
            for v in values {
                let expected = match (u == 0.0, v == 0.0) {
                    (false, false) => (u < 0.0) != (v < 0.0),
                    _ => true,
                };
                assert_eq!(sign_change(u, v), expected, "u = {u}, v = {v}");
            }
        }
    }

    #[test]
    fn sign_change_does_not_underflow() {
        // The product of these underflows to 0, which would look like a sign change.
        assert_eq!(1e-200 * 1e-200, 0.0);
        assert!(!sign_change(1e-200, 1e-200));
    }
}
