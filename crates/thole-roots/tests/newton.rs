//! Tests of `newton` against reference values and on hard inputs.

use thole_core::Tolerance;
use thole_roots::{Error, NewtonRoot, Options, newton};

/// Options with an absolute tolerance only.
fn abs_tol(abs: f64) -> Options {
    Options {
        tol: Tolerance::new(abs, 0.0),
        ..Options::default()
    }
}

// ---- Reference values -----------------------------------------------------

/// Roots computed with mpmath at 50 digits by `python/reference_values.py`.
#[test]
fn matches_mpmath_reference_roots() {
    type Problem = (fn(f64) -> f64, fn(f64) -> f64, f64, f64);
    let problems: [Problem; 3] = [
        (
            |x| x * x * x - x - 2.0,
            |x| 3.0 * x * x - 1.0,
            1.5,
            1.5213797068045676,
        ),
        (|x| x.cos() - x, |x| -x.sin() - 1.0, 0.5, 0.7390851332151607),
        (
            |x| x * x.exp() - 1.0,
            |x| (x + 1.0) * x.exp(),
            0.5,
            0.5671432904097838,
        ),
    ];
    let options = Options::default();
    for (f, df, x0, expected) in problems {
        let root = newton(f, df, x0, &options).unwrap();
        assert!(
            (root.x - expected).abs() <= options.tol.bound(root.x),
            "got {}, expected {expected}",
            root.x
        );
    }
}

/// Roots known in closed form.
#[test]
fn matches_analytic_roots() {
    let options = Options::default();

    let root = newton(|x| x * x - 2.0, |x| 2.0 * x, 1.0, &options).unwrap();
    assert!((root.x - 2.0_f64.sqrt()).abs() <= options.tol.bound(root.x));

    let root = newton(f64::cos, |x| -x.sin(), 1.0, &options).unwrap();
    assert!((root.x - std::f64::consts::FRAC_PI_2).abs() <= options.tol.bound(root.x));

    // From the other side of the root.
    let root = newton(|x| x * x - 2.0, |x| 2.0 * x, -1.0, &options).unwrap();
    assert!((root.x + 2.0_f64.sqrt()).abs() <= options.tol.bound(root.x));
}

/// Results of `scipy.optimize.newton` (SciPy 1.18.1) with `tol=1.48e-8`, its
/// default, and the derivative, printed by `python/reference_values.py`.
/// SciPy takes the same steps, so the result and the number of steps are the
/// same.
#[test]
fn matches_scipy_newton() {
    type Problem = (fn(f64) -> f64, fn(f64) -> f64, f64, f64, usize);
    let problems: [Problem; 3] = [
        (
            |x| x * x * x - x - 2.0,
            |x| 3.0 * x * x - 1.0,
            1.5,
            1.5213797068045676,
            4,
        ),
        (
            |x| x * x - 2.0,
            |x| 2.0 * x,
            1.0,
            std::f64::consts::SQRT_2,
            5,
        ),
        (
            |x| x * x - 2.0,
            |x| 2.0 * x,
            1000.0,
            std::f64::consts::SQRT_2,
            14,
        ),
    ];
    for (f, df, x0, x, iterations) in problems {
        let root = newton(f, df, x0, &abs_tol(1.48e-8)).unwrap();
        assert_eq!((root.x, root.iterations), (x, iterations));
    }
}

/// Newton's method for a linear function lands on the root in one step, and
/// the next step is zero.
#[test]
fn linear_function_takes_one_step() {
    let root = newton(|x| 2.0 * x - 1.0, |_| 2.0, 4.0, &Options::default()).unwrap();
    assert_eq!(root.x, 0.5);
    assert_eq!(root.iterations, 1);
    assert_eq!(root.step, 3.5);
}

// ---- Agreement with the Lean theorems -------------------------------------

/// `newtonStep_error`: near a simple root, each step squares the error, up
/// to the factor `L / |df(x)|`. For `x^2 - 2`, `L = 2` and `df(x) = 2x`, so
/// the error after a step is at most `e^2 / x`.
#[test]
fn error_is_squared_by_every_step() {
    let root_of_two = 2.0_f64.sqrt();
    let mut x: f64 = 3.0;
    for _ in 0..4 {
        let next = x - (x * x - 2.0) / (2.0 * x);
        let e = (x - root_of_two).abs();
        assert!((next - root_of_two).abs() <= e * e / x + 4.0 * f64::EPSILON);
        x = next;
    }
}

/// `newton_error`: close enough to a simple root, the error at least halves
/// every step, so `n` steps reach an error of `|x0 - r| / 2^n`.
#[test]
fn error_halves_close_to_a_simple_root() {
    let root_of_two = 2.0_f64.sqrt();
    for steps in 1..=4 {
        let options = Options {
            max_iter: steps,
            ..abs_tol(0.0)
        };
        let x = match newton(|x| x * x - 2.0, |x| 2.0 * x, 2.0, &options) {
            Err(Error::NotConverged { x, .. }) => x,
            Ok(root) => root.x,
            other => panic!("{other:?}"),
        };
        let bound = (2.0 - root_of_two) / 2.0_f64.powi(steps as i32);
        assert!(
            (x - root_of_two).abs() <= bound + f64::EPSILON,
            "{steps} steps"
        );
    }
}

/// `newton_error_of_done`: the last step bounds the error from above, close
/// to a simple root.
#[test]
fn error_is_within_the_last_step() {
    let root_of_two = 2.0_f64.sqrt();
    for t in [0.5, 0.1, 1e-2, 1e-3, 1e-6] {
        let root = newton(|x| x * x - 2.0, |x| 2.0 * x, 2.0, &abs_tol(t)).unwrap();
        assert!(root.step.abs() <= t, "t = {t}");
        assert!((root.x - root_of_two).abs() <= root.step.abs(), "t = {t}");
    }
}

/// Convergence is quadratic: from a good start, few steps reach full
/// precision.
#[test]
fn converges_in_few_steps() {
    let root = newton(|x| x * x - 2.0, |x| 2.0 * x, 1.0, &Options::default()).unwrap();
    assert!(root.iterations <= 6, "{} steps", root.iterations);
}

/// At a double root convergence is only linear: the error halves each step.
#[test]
fn double_root_converges_linearly() {
    let f = |x: f64| (x - 1.0) * (x - 1.0);
    let df = |x: f64| 2.0 * (x - 1.0);
    let root = newton(f, df, 2.0, &abs_tol(1e-6)).unwrap();
    assert!((root.x - 1.0).abs() <= 2e-6);
    assert!(root.iterations >= 18, "{} steps", root.iterations);
}

// ---- Hard inputs ----------------------------------------------------------

#[test]
fn root_at_the_starting_point_takes_no_step() {
    let root = newton(|x| x - 1.0, |_| 1.0, 1.0, &Options::default()).unwrap();
    assert_eq!(
        root,
        NewtonRoot {
            x: 1.0,
            step: 0.0,
            iterations: 0
        }
    );
}

#[test]
fn large_root_is_reached_through_the_relative_tolerance() {
    let options = Options::default();
    let root = newton(|x| x - 1.234e15, |_| 1.0, 0.0, &options).unwrap();
    assert!((root.x - 1.234e15).abs() <= options.tol.bound(root.x));
}

/// A short step far from any root: `x^2 + 1e-8` has no real root, but its
/// steps are shorter than a coarse tolerance near zero. The guarantee needs
/// the derivative to be bounded away from zero, which fails here.
#[test]
fn a_short_step_without_a_root() {
    let root = newton(|x| x * x + 1e-8, |x| 2.0 * x, 1.0, &abs_tol(1e-3)).unwrap();
    assert!(root.x * root.x + 1e-8 > 0.0);
}

/// The classic cycle: for `x^3 - 2x + 2` from 0 the iteration alternates
/// between 0 and 1.
#[test]
fn a_cycle_hits_the_iteration_limit() {
    let err = newton(
        |x| x * x * x - 2.0 * x + 2.0,
        |x| 3.0 * x * x - 2.0,
        0.0,
        &Options::default(),
    )
    .unwrap_err();
    assert!(matches!(
        err,
        Error::NotConverged {
            max_iter: 100,
            x: 0.0
        }
    ));
}

#[test]
fn zero_derivative() {
    let err = newton(|x| x * x - 2.0, |x| 2.0 * x, 0.0, &Options::default()).unwrap_err();
    assert_eq!(err, Error::ZeroDerivative { x: 0.0 });
}

#[test]
fn non_finite_steps() {
    let options = Options::default();
    // A tiny derivative: the step overflows.
    let err = newton(|_| 1.0, |_| 1e-310, 0.0, &options).unwrap_err();
    assert_eq!(err, Error::NonFiniteStep { x: 0.0 });
    // An infinite value of f.
    let err = newton(|_| f64::INFINITY, |_| 1.0, 0.0, &options).unwrap_err();
    assert_eq!(err, Error::NonFiniteStep { x: 0.0 });
    // An infinite derivative would give a zero step.
    let err = newton(|x| x - 1.0, |_| f64::INFINITY, 0.0, &options).unwrap_err();
    assert_eq!(err, Error::NonFiniteStep { x: 0.0 });
}

/// For `atan` from too far out, every step overshoots further on the other
/// side, until the derivative underflows to zero.
#[test]
fn a_runaway_iteration_ends_in_an_error() {
    let err = newton(
        f64::atan,
        |x| 1.0 / (1.0 + x * x),
        10.0,
        &Options::default(),
    )
    .unwrap_err();
    assert!(
        matches!(err, Error::ZeroDerivative { x } if x.abs() > 1e150),
        "{err:?}"
    );
}

// ---- Errors ---------------------------------------------------------------

#[test]
fn invalid_starting_points() {
    let options = Options::default();
    for x0 in [f64::NAN, f64::INFINITY, f64::NEG_INFINITY] {
        match newton(|x| x, |_| 1.0, x0, &options) {
            Err(Error::InvalidStart { .. }) => {}
            other => panic!("{x0}: {other:?}"),
        }
    }
}

#[test]
fn invalid_tolerances() {
    for tol in [
        Tolerance::new(-1e-12, 0.0),
        Tolerance::new(0.0, -1e-12),
        Tolerance::new(f64::NAN, 0.0),
    ] {
        let options = Options {
            tol,
            ..Options::default()
        };
        match newton(|x| x, |_| 1.0, 1.0, &options) {
            Err(Error::InvalidTolerance { .. }) => {}
            other => panic!("{tol:?}: {other:?}"),
        }
    }
}

#[test]
fn nan_values() {
    let options = Options::default();
    assert_eq!(
        newton(|_| f64::NAN, |_| 1.0, 0.5, &options),
        Err(Error::NanValue { x: 0.5 })
    );
    assert_eq!(
        newton(|x| x - 1.0, |_| f64::NAN, 0.5, &options),
        Err(Error::NanDerivative { x: 0.5 })
    );
}

#[test]
fn iteration_limit() {
    let options = Options {
        max_iter: 2,
        ..abs_tol(1e-12)
    };
    let err = newton(|x| x * x - 2.0, |x| 2.0 * x, 1.0, &options).unwrap_err();
    // 1 -> 1.5 -> 1.41666...
    assert_eq!(
        err,
        Error::NotConverged {
            max_iter: 2,
            x: 1.5 - 0.25 / 3.0
        }
    );
    let options = Options {
        max_iter: 0,
        ..Options::default()
    };
    let err = newton(|x| x * x - 2.0, |x| 2.0 * x, 1.0, &options).unwrap_err();
    assert_eq!(
        err,
        Error::NotConverged {
            max_iter: 0,
            x: 1.0
        }
    );
}

/// A zero tolerance is met only when a step is exactly zero or `f` is
/// exactly zero at an approximation.
#[test]
fn zero_tolerance() {
    let options = Options {
        max_iter: 50,
        ..abs_tol(0.0)
    };
    let root = newton(|x| x - 0.5, |_| 1.0, 2.0, &options).unwrap();
    assert_eq!(root.x, 0.5);
}

#[test]
fn counts_function_evaluations() {
    let (mut calls, mut derivative_calls) = (0, 0);
    let root = newton(
        |x| {
            calls += 1;
            x * x * x - x - 2.0
        },
        |x| {
            derivative_calls += 1;
            3.0 * x * x - 1.0
        },
        1.5,
        &Options::default(),
    )
    .unwrap();
    assert!(root.iterations > 0);
    assert_eq!(derivative_calls, root.iterations);
    assert_eq!(calls, root.iterations);
}
