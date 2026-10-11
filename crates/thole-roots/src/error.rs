use std::fmt;

/// The ways a root finder can fail.
#[derive(Debug, Clone, Copy, PartialEq)]
#[non_exhaustive]
pub enum Error {
    /// The bracket `[a, b]` is not a finite interval with `a <= b`.
    InvalidBracket {
        /// Lower end as given.
        a: f64,
        /// Upper end as given.
        b: f64,
    },
    /// A tolerance is negative or NaN.
    InvalidTolerance {
        /// Absolute tolerance as given.
        abs: f64,
        /// Relative tolerance as given.
        rel: f64,
    },
    /// `f(a)` and `f(b)` have the same strict sign, so the bracket is not
    /// known to contain a root.
    NoSignChange {
        /// `f(a)`.
        fa: f64,
        /// `f(b)`.
        fb: f64,
    },
    /// The function returned NaN.
    NanValue {
        /// The point at which the function was evaluated.
        x: f64,
    },
    /// The tolerance was not reached within the allowed number of iterations.
    MaxIterations {
        /// The iteration limit that was hit.
        max_iter: usize,
        /// Lower end of the last bracket. It still contains a root.
        lo: f64,
        /// Upper end of the last bracket.
        hi: f64,
    },
}

impl fmt::Display for Error {
    fn fmt(&self, out: &mut fmt::Formatter<'_>) -> fmt::Result {
        match *self {
            Self::InvalidBracket { a, b } => {
                write!(out, "invalid bracket [{a}, {b}]: need finite a <= b")
            }
            Self::InvalidTolerance { abs, rel } => write!(
                out,
                "invalid tolerance (abs = {abs}, rel = {rel}): both must be non-negative"
            ),
            Self::NoSignChange { fa, fb } => write!(
                out,
                "no sign change over the bracket: f(a) = {fa}, f(b) = {fb}"
            ),
            Self::NanValue { x } => write!(out, "the function returned NaN at x = {x}"),
            Self::MaxIterations { max_iter, lo, hi } => write!(
                out,
                "tolerance not reached after {max_iter} iterations; last bracket [{lo}, {hi}]"
            ),
        }
    }
}

impl std::error::Error for Error {}
