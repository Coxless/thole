use thole_core::Tolerance;

/// Stopping criteria shared by the root finders.
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct Options {
    /// Tolerance on the position of the root.
    pub tol: Tolerance,
    /// Maximum number of iterations.
    pub max_iter: usize,
}

impl Default for Options {
    /// `tol.abs = 2e-12`, `tol.rel = 4 * f64::EPSILON`, `max_iter = 100`.
    ///
    /// These are the defaults of SciPy's bracketing root finders
    /// (`scipy.optimize.bisect`, `brentq`).
    fn default() -> Self {
        Self {
            tol: Tolerance::new(2e-12, 4.0 * f64::EPSILON),
            max_iter: 100,
        }
    }
}
