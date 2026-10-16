use thole_core::Tolerance;

/// Stopping criteria of the adaptive integrators.
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct Options {
    /// Tolerance on the integral. The iteration stops when the error
    /// estimate is at most `tol.bound(value)`.
    pub tol: Tolerance,
    /// Maximum number of subintervals. Must be at least one.
    pub max_subintervals: usize,
}

impl Default for Options {
    /// `tol.abs = 1.49e-8`, `tol.rel = 1.49e-8`, `max_subintervals = 50`.
    ///
    /// These are the defaults of `scipy.integrate.quad`.
    fn default() -> Self {
        Self {
            tol: Tolerance::new(1.49e-8, 1.49e-8),
            max_subintervals: 50,
        }
    }
}
