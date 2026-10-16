use std::fmt;

/// The ways an integration can fail.
#[derive(Debug, Clone, Copy, PartialEq)]
#[non_exhaustive]
pub enum Error {
    /// An end of the interval is not finite.
    InvalidInterval {
        /// Lower end as given.
        a: f64,
        /// Upper end as given.
        b: f64,
    },
    /// A rule with no points was asked for.
    InvalidOrder {
        /// The number of points as given.
        n: usize,
    },
    /// A tolerance is negative or NaN.
    InvalidTolerance {
        /// Absolute tolerance as given.
        abs: f64,
        /// Relative tolerance as given.
        rel: f64,
    },
    /// The function returned NaN or an infinity.
    NonFiniteValue {
        /// The point at which the function was evaluated.
        x: f64,
        /// The value it returned.
        fx: f64,
    },
    /// The limit on the number of subintervals is zero.
    InvalidLimit {
        /// The limit as given.
        max_subintervals: usize,
    },
    /// The tolerance was not reached with the allowed number of
    /// subintervals.
    MaxSubintervals {
        /// The limit that was hit.
        max_subintervals: usize,
        /// The estimate of the integral at that point.
        value: f64,
        /// The estimate of its error, which exceeds the tolerance.
        error: f64,
    },
}

impl fmt::Display for Error {
    fn fmt(&self, out: &mut fmt::Formatter<'_>) -> fmt::Result {
        match *self {
            Self::InvalidInterval { a, b } => {
                write!(out, "invalid interval [{a}, {b}]: need finite ends")
            }
            Self::InvalidOrder { n } => {
                write!(out, "invalid number of points {n}: need at least one")
            }
            Self::InvalidTolerance { abs, rel } => write!(
                out,
                "invalid tolerance (abs = {abs}, rel = {rel}): both must be non-negative"
            ),
            Self::NonFiniteValue { x, fx } => {
                write!(out, "the function returned {fx} at x = {x}")
            }
            Self::InvalidLimit { max_subintervals } => write!(
                out,
                "invalid limit of {max_subintervals} subintervals: need at least one"
            ),
            Self::MaxSubintervals {
                max_subintervals,
                value,
                error,
            } => write!(
                out,
                "tolerance not reached with {max_subintervals} subintervals; \
                 estimate {value} with error estimate {error}"
            ),
        }
    }
}

impl std::error::Error for Error {}

/// Checks that both ends of the interval are finite.
pub(crate) fn check_interval(a: f64, b: f64) -> Result<(), Error> {
    if a.is_finite() && b.is_finite() {
        Ok(())
    } else {
        Err(Error::InvalidInterval { a, b })
    }
}

/// Evaluates `f` at `x`. A value that is not finite is an error.
pub(crate) fn eval(f: &mut impl FnMut(f64) -> f64, x: f64) -> Result<f64, Error> {
    let fx = f(x);
    if fx.is_finite() {
        Ok(fx)
    } else {
        Err(Error::NonFiniteValue { x, fx })
    }
}
