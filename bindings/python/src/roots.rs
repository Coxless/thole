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

/// A root located by Newton's method.
#[pyclass(frozen, get_all, module = "thole.roots")]
struct NewtonRoot {
    /// The approximation of the root.
    x: f64,
    /// The last step taken: `x` is the previous approximation minus `step`.
    /// Zero if no step was taken.
    step: f64,
    /// Number of steps taken.
    iterations: usize,
}

#[pymethods]
impl NewtonRoot {
    fn __repr__(&self) -> String {
        format!(
            "NewtonRoot(x={:?}, step={:?}, iterations={})",
            self.x, self.step, self.iterations
        )
    }
}

impl From<roots::NewtonRoot> for NewtonRoot {
    fn from(root: roots::NewtonRoot) -> Self {
        Self {
            x: root.x,
            step: root.step,
            iterations: root.iterations,
        }
    }
}

/// Invalid input is a `ValueError`; an iteration that fails to converge is a
/// `ConvergenceError`.
fn to_py_err(error: Error) -> PyErr {
    match error {
        Error::MaxIterations { .. }
        | Error::NotConverged { .. }
        | Error::ZeroDerivative { .. }
        | Error::NonFiniteStep { .. } => ConvergenceError::new_err(error.to_string()),
        _ => PyValueError::new_err(error.to_string()),
    }
}

/// Calls the Python function `f` at `x`. An exception raised by `f` is kept
/// in `raised` and the value is NaN, which stops the iteration.
fn call(f: &Bound<'_, PyAny>, x: f64, raised: &mut Option<PyErr>) -> f64 {
    match f.call1((x,)).and_then(|y| y.extract::<f64>()) {
        Ok(y) => y,
        Err(error) => {
            raised.get_or_insert(error);
            f64::NAN
        }
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
    let mut raised = None;
    let result = method(&mut |x| call(f, x, &mut raised));
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

/// Find a root of `f` near `x0` by Newton's method, given the derivative
/// `fprime` of `f`.
///
/// Each step moves the approximation `x` to `x - f(x) / fprime(x)`. The
/// iteration stops when `f` is zero at the approximation, or when the step
/// that led to it is at most `xtol + rtol * abs(x)` long. Near a simple root
/// convergence is quadratic; elsewhere nothing is guaranteed, and a short
/// step does not by itself mean that a root is near.
///
/// Defaults: `xtol=2e-12`, `rtol=4 * sys.float_info.epsilon`, `max_iter=100`.
///
/// Raises `ValueError` for a starting point that is not finite, an invalid
/// tolerance, or when `f` or `fprime` returns NaN, and `ConvergenceError`
/// when the derivative is zero, a step is not finite, or the tolerance is not
/// reached within `max_iter` steps. An exception raised by `f` or `fprime`
/// propagates unchanged.
#[pyfunction]
#[pyo3(signature = (f, fprime, x0, *, xtol=None, rtol=None, max_iter=None))]
fn newton(
    f: &Bound<'_, PyAny>,
    fprime: &Bound<'_, PyAny>,
    x0: f64,
    xtol: Option<f64>,
    rtol: Option<f64>,
    max_iter: Option<usize>,
) -> PyResult<NewtonRoot> {
    let options = options(xtol, rtol, max_iter);
    // The two closures cannot share one place for an exception, so each has
    // its own; at most one of them is set, because NaN stops the iteration.
    let (mut raised, mut raised_by_fprime) = (None, None);
    let result = roots::newton(
        |x| call(f, x, &mut raised),
        |x| call(fprime, x, &mut raised_by_fprime),
        x0,
        &options,
    );
    match (raised.or(raised_by_fprime), result) {
        (Some(error), _) => Err(error),
        (None, Ok(root)) => Ok(root.into()),
        (None, Err(error)) => Err(to_py_err(error)),
    }
}

pub(crate) fn register(parent: &Bound<'_, PyModule>) -> PyResult<()> {
    let m = PyModule::new(parent.py(), "roots")?;
    m.add_function(wrap_pyfunction!(bisect, &m)?)?;
    m.add_function(wrap_pyfunction!(brent, &m)?)?;
    m.add_function(wrap_pyfunction!(newton, &m)?)?;
    m.add_class::<Root>()?;
    m.add_class::<NewtonRoot>()?;
    m.add(
        "ConvergenceError",
        parent.py().get_type::<ConvergenceError>(),
    )?;
    parent.add_submodule(&m)
}
