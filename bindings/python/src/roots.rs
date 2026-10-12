//! Bindings for `thole-roots`.

use pyo3::create_exception;
use pyo3::exceptions::{PyRuntimeError, PyValueError};
use pyo3::prelude::*;
use thole::core::Tolerance;
use thole::roots::{self, Error, Options};

create_exception!(
    thole.roots,
    ConvergenceError,
    PyRuntimeError,
    "The tolerance was not reached within the allowed number of iterations."
);

/// A root located by a bracketing method.
#[pyclass(frozen, get_all, module = "thole.roots")]
struct Root {
    /// The approximation of the root. It lies in the final bracket.
    x: f64,
    /// Lower end of the final bracket.
    lo: f64,
    /// Upper end of the final bracket.
    hi: f64,
    /// Number of steps taken.
    iterations: usize,
}

#[pymethods]
impl Root {
    fn __repr__(&self) -> String {
        format!(
            // `{:?}` prints floats the way Python does (`1.0`, not `1`).
            "Root(x={:?}, lo={:?}, hi={:?}, iterations={})",
            self.x, self.lo, self.hi, self.iterations
        )
    }
}

impl From<roots::Root> for Root {
    fn from(root: roots::Root) -> Self {
        Self {
            x: root.x,
            lo: root.lo,
            hi: root.hi,
            iterations: root.iterations,
        }
    }
}

/// Invalid input is a `ValueError`; running out of iterations is a
/// `ConvergenceError`.
fn to_py_err(error: Error) -> PyErr {
    match error {
        Error::MaxIterations { .. } => ConvergenceError::new_err(error.to_string()),
        _ => PyValueError::new_err(error.to_string()),
    }
}

/// Builds the options from keyword arguments, falling back to the Rust defaults.
fn options(xtol: Option<f64>, rtol: Option<f64>, max_iter: Option<usize>) -> Options {
    let default = Options::default();
    Options {
        tol: Tolerance::new(
            xtol.unwrap_or(default.tol.abs),
            rtol.unwrap_or(default.tol.rel),
        ),
        max_iter: max_iter.unwrap_or(default.max_iter),
    }
}

/// Runs a root finder on the Python function `f`.
fn solve(
    f: &Bound<'_, PyAny>,
    method: impl FnOnce(&mut dyn FnMut(f64) -> f64) -> Result<roots::Root, Error>,
) -> PyResult<Root> {
    // An exception raised by `f` is kept here; NaN then stops the iteration.
    let mut raised = None;
    let result = method(
        &mut |x| match f.call1((x,)).and_then(|y| y.extract::<f64>()) {
            Ok(y) => y,
            Err(error) => {
                raised.get_or_insert(error);
                f64::NAN
            }
        },
    );
    match (raised, result) {
        (Some(error), _) => Err(error),
        (None, Ok(root)) => Ok(root.into()),
        (None, Err(error)) => Err(to_py_err(error)),
    }
}

/// Find a root of `f` in `[a, b]` by bisection.
///
/// `f` must be continuous on `[a, b]`, and `f(a)` and `f(b)` must not have
/// the same strict sign. The iteration stops when half the width of the
/// bracket is at most `xtol + rtol * abs(x)`, where `x` is its midpoint.
///
/// Defaults: `xtol=2e-12`, `rtol=4 * sys.float_info.epsilon`, `max_iter=100`.
///
/// Raises `ValueError` for an invalid bracket or tolerance, when there is no
/// sign change, or when `f` returns NaN, and `ConvergenceError` when the
/// tolerance is not reached within `max_iter` steps. An exception raised by
/// `f` propagates unchanged.
#[pyfunction]
#[pyo3(signature = (f, a, b, *, xtol=None, rtol=None, max_iter=None))]
fn bisect(
    f: &Bound<'_, PyAny>,
    a: f64,
    b: f64,
    xtol: Option<f64>,
    rtol: Option<f64>,
    max_iter: Option<usize>,
) -> PyResult<Root> {
    let options = options(xtol, rtol, max_iter);
    solve(f, |f| roots::bisect(f, a, b, &options))
}

/// Find a root of `f` in `[a, b]` by Brent's method.
///
/// `f` must be continuous on `[a, b]`, and `f(a)` and `f(b)` must not have
/// the same strict sign. Each step is an interpolation step when that is
/// safe and a bisection otherwise, which takes far fewer steps than `bisect`
/// for a smooth function. The iteration stops when `f` is zero at the
/// approximation `x`, or when the root is known to be within
/// `xtol + rtol * abs(x)` of it. `x` is an end of the final bracket.
///
/// Defaults: `xtol=2e-12`, `rtol=4 * sys.float_info.epsilon`, `max_iter=100`.
///
/// Raises `ValueError` for an invalid bracket or tolerance, when there is no
/// sign change, or when `f` returns NaN, and `ConvergenceError` when the
/// tolerance is not reached within `max_iter` steps. An exception raised by
/// `f` propagates unchanged.
#[pyfunction]
#[pyo3(signature = (f, a, b, *, xtol=None, rtol=None, max_iter=None))]
fn brent(
    f: &Bound<'_, PyAny>,
    a: f64,
    b: f64,
    xtol: Option<f64>,
    rtol: Option<f64>,
    max_iter: Option<usize>,
) -> PyResult<Root> {
    let options = options(xtol, rtol, max_iter);
    solve(f, |f| roots::brent(f, a, b, &options))
}

pub(crate) fn register(parent: &Bound<'_, PyModule>) -> PyResult<()> {
    let m = PyModule::new(parent.py(), "roots")?;
    m.add_function(wrap_pyfunction!(bisect, &m)?)?;
    m.add_function(wrap_pyfunction!(brent, &m)?)?;
    m.add_class::<Root>()?;
    m.add(
        "ConvergenceError",
        parent.py().get_type::<ConvergenceError>(),
    )?;
    parent.add_submodule(&m)
}
