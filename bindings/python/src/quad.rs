//! Bindings for `thole-quad`.

use pyo3::create_exception;
use pyo3::exceptions::{PyRuntimeError, PyValueError};
use pyo3::prelude::*;
use thole::core::Tolerance;
use thole::quad::{self, Error, Options};

create_exception!(
    thole.quad,
    ConvergenceError,
    PyRuntimeError,
    "The tolerance was not reached with the allowed number of subintervals."
);

/// An integral computed by an adaptive method.
#[pyclass(frozen, get_all, module = "thole.quad")]
struct Integral {
    /// The estimate of the integral.
    value: f64,
    /// The estimate of its absolute error. It is not a bound.
    error: f64,
    /// The number of subintervals in the final partition of the interval.
    subintervals: usize,
    /// The number of evaluations of the function.
    evaluations: usize,
}

#[pymethods]
impl Integral {
    fn __repr__(&self) -> String {
        format!(
            "Integral(value={:?}, error={:?}, subintervals={}, evaluations={})",
            self.value, self.error, self.subintervals, self.evaluations
        )
    }
}

impl From<quad::Integral> for Integral {
    fn from(integral: quad::Integral) -> Self {
        Self {
            value: integral.value,
            error: integral.error,
            subintervals: integral.subintervals,
            evaluations: integral.evaluations,
        }
    }
}

/// Invalid input is a `ValueError`; running out of subintervals is a
/// `ConvergenceError`.
fn to_py_err(error: Error) -> PyErr {
    match error {
        Error::MaxSubintervals { .. } => ConvergenceError::new_err(error.to_string()),
        _ => PyValueError::new_err(error.to_string()),
    }
}

/// Runs an integrator on the Python function `f`.
fn run<T>(
    f: &Bound<'_, PyAny>,
    method: impl FnOnce(&mut dyn FnMut(f64) -> f64) -> Result<T, Error>,
) -> PyResult<T> {
    // An exception raised by `f` is kept here; NaN then stops the integration.
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
        (None, Ok(value)) => Ok(value),
        (None, Err(error)) => Err(to_py_err(error)),
    }
}

/// The `n`-point Gauss-Legendre rule: its nodes and weights on `[-1, 1]`.
///
/// The rule is exact for polynomials of degree at most `2n - 1`. The nodes
/// are the roots of the Legendre polynomial `P_n`, computed by Newton's
/// method, in increasing order. Raises `ValueError` if `n` is zero.
#[pyclass(frozen, module = "thole.quad")]
struct GaussLegendre(quad::GaussLegendre);

#[pymethods]
impl GaussLegendre {
    #[new]
    fn new(n: usize) -> PyResult<Self> {
        quad::GaussLegendre::new(n).map(Self).map_err(to_py_err)
    }

    /// The number of nodes.
    #[getter]
    fn order(&self) -> usize {
        self.0.order()
    }

    /// The nodes on `[-1, 1]`, in increasing order.
    #[getter]
    fn nodes(&self) -> Vec<f64> {
        self.0.nodes().to_vec()
    }

    /// The weights, in the order of the nodes.
    #[getter]
    fn weights(&self) -> Vec<f64> {
        self.0.weights().to_vec()
    }

    /// Approximate the integral of `f` over `[a, b]` by the rule.
    ///
    /// Raises `ValueError` for an end that is not finite, or when `f`
    /// returns NaN or an infinity. An exception raised by `f` propagates
    /// unchanged.
    fn integrate(&self, f: &Bound<'_, PyAny>, a: f64, b: f64) -> PyResult<f64> {
        run(f, |f| self.0.integrate(f, a, b))
    }

    fn __repr__(&self) -> String {
        format!("GaussLegendre({})", self.0.order())
    }
}

/// Approximate the integral of `f` over `[a, b]` by the `n`-point
/// Gauss-Legendre rule.
///
/// Exact, up to rounding, for polynomials of degree at most `2n - 1`. There
/// is no error estimate. `a > b` is allowed.
///
/// Raises `ValueError` if `n` is zero, for an end that is not finite, or when
/// `f` returns NaN or an infinity. An exception raised by `f` propagates
/// unchanged.
#[pyfunction]
fn gauss_legendre(f: &Bound<'_, PyAny>, a: f64, b: f64, n: usize) -> PyResult<f64> {
    let rule = quad::GaussLegendre::new(n).map_err(to_py_err)?;
    run(f, |f| rule.integrate(f, a, b))
}

/// Approximate the integral of `f` over `[a, b]` by adaptive Gauss-Kronrod
/// quadrature.
///
/// On each subinterval the 15-point Kronrod rule estimates the integral and
/// its difference from the 7-point Gauss rule the error. The subinterval with
/// the largest error estimate is halved until the total error estimate is at
/// most `atol + rtol * abs(value)`. The error estimate is not a bound.
///
/// Defaults: `atol=1.49e-8`, `rtol=1.49e-8`, `max_subintervals=50`, those of
/// `scipy.integrate.quad`.
///
/// Raises `ValueError` for an end that is not finite, an invalid tolerance or
/// limit, or when `f` returns NaN or an infinity, and `ConvergenceError` when
/// the tolerance is not reached with `max_subintervals` subintervals. An
/// exception raised by `f` propagates unchanged.
#[pyfunction]
#[pyo3(signature = (f, a, b, *, atol=None, rtol=None, max_subintervals=None))]
fn gauss_kronrod(
    f: &Bound<'_, PyAny>,
    a: f64,
    b: f64,
    atol: Option<f64>,
    rtol: Option<f64>,
    max_subintervals: Option<usize>,
) -> PyResult<Integral> {
    let default = Options::default();
    let options = Options {
        tol: Tolerance::new(
            atol.unwrap_or(default.tol.abs),
            rtol.unwrap_or(default.tol.rel),
        ),
        max_subintervals: max_subintervals.unwrap_or(default.max_subintervals),
    };
    run(f, |f| quad::gauss_kronrod(f, a, b, &options)).map(Integral::from)
}

pub(crate) fn register(parent: &Bound<'_, PyModule>) -> PyResult<()> {
    let m = PyModule::new(parent.py(), "quad")?;
    m.add_function(wrap_pyfunction!(gauss_legendre, &m)?)?;
    m.add_function(wrap_pyfunction!(gauss_kronrod, &m)?)?;
    m.add_class::<GaussLegendre>()?;
    m.add_class::<Integral>()?;
    m.add(
        "ConvergenceError",
        parent.py().get_type::<ConvergenceError>(),
    )?;
    parent.add_submodule(&m)
}
