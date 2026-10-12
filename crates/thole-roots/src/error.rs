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
    /// The starting point of an iteration is not finite.
    InvalidStart {
        /// The starting point as given.
        x0: f64,
    },
    /// The function returned NaN.
    NanValue {
        /// The point at which the function was evaluated.
        x: f64,
    },
    /// The derivative returned NaN.
    NanDerivative {
        /// The point at which the derivative was evaluated.
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
    /// The derivative is zero at an approximation where the function is not,
    /// so the next Newton step is undefined.
    ZeroDerivative {
        /// The approximation.
        x: f64,
    },
    /// The Newton step from an approximation leaves the finite numbers: the
    /// function or its derivative is infinite there, or the derivative is so
    /// small that the next approximation overflows.
    NonFiniteStep {
        /// The approximation the step was taken from.
        x: f64,
    },
    /// An iteration without a bracket did not reach the tolerance within the
    /// allowed number of iterations.
    NotConverged {
        /// The iteration limit that was hit.
        max_iter: usize,
        /// The last approximation. Nothing is known about its error.
        x: f64,
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
            Self::InvalidStart { x0 } => {
                write!(out, "invalid starting point {x0}: need a finite number")
            }
            Self::NanValue { x } => write!(out, "the function returned NaN at x = {x}"),
            Self::NanDerivative { x } => {
                write!(out, "the derivative returned NaN at x = {x}")
            }
            Self::MaxIterations { max_iter, lo, hi } => write!(
                out,
                "tolerance not reached after {max_iter} iterations; last bracket [{lo}, {hi}]"
            ),
            Self::ZeroDerivative { x } => {
                write!(out, "the derivative is zero at x = {x}, where f is not")
            }
            Self::NonFiniteStep { x } => {
                write!(out, "the Newton step from x = {x} is not finite")
            }
            Self::NotConverged { max_iter, x } => write!(
                out,
                "tolerance not reached after {max_iter} iterations; last approximation {x}"
            ),
        }
    }
}

impl std::error::Error for Error {}
