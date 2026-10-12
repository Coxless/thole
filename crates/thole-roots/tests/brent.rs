//! Tests of `brent` against reference values and on hard inputs.

use thole_core::Tolerance;
use thole_roots::{Error, Options, bisect, brent};

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
    type Problem = (fn(f64) -> f64, f64, f64, f64);
    let problems: [Problem; 3] = [
        (|x| x * x * x - x - 2.0, 1.0, 2.0, 1.5213797068045676),
        (|x| x.cos() - x, 0.0, 1.0, 0.7390851332151607),
        (|x| x * x.exp() - 1.0, 0.0, 1.0, 0.5671432904097838),
    ];
    let options = Options::default();
    for (f, a, b, expected) in problems {
        let root = brent(f, a, b, &options).unwrap();
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

    let root = brent(|x| x * x - 2.0, 0.0, 2.0, &options).unwrap();
    assert!((root.x - 2.0_f64.sqrt()).abs() <= options.tol.bound(root.x));

    let root = brent(f64::cos, 0.0, 2.0, &options).unwrap();
    assert!((root.x - std::f64::consts::FRAC_PI_2).abs() <= options.tol.bound(root.x));

    // Decreasing function: the sign change is from positive to negative.
    let root = brent(|x| 1.0 - x, -3.0, 5.0, &options).unwrap();
    assert!((root.x - 1.0).abs() <= options.tol.bound(root.x));
}

/// Results of `scipy.optimize.brentq` (SciPy 1.18.1) with its default
/// tolerances, which are those of `Options::default()`, printed by
/// `python/reference_values.py`. SciPy takes the same steps on these
/// problems, so the result and the number of evaluations are the same.
#[test]
fn matches_scipy_brentq() {
    type Problem = (fn(f64) -> f64, f64, f64, f64, usize);
    let problems: [Problem; 3] = [
        (|x| x * x * x - x - 2.0, 1.0, 2.0, 1.5213797068045676, 9),
        (|x| x * x - 2.0, 0.0, 2.0, 1.4142135623731364, 9),
        (
            |x| if x < 0.7 { -1.0 } else { 1e-3 },
            0.0,
            1.0,
            0.7000000000005636,
            62,
        ),
    ];
    for (f, a, b, x, evaluations) in problems {
        let root = brent(f, a, b, &Options::default()).unwrap();
        assert_eq!((root.x, root.iterations + 2), (x, evaluations));
    }
}

/// The secant through the ends of the bracket is the function itself, so the
/// first step lands on the root.
#[test]
fn linear_function_takes_one_step() {
    let root = brent(|x| 2.0 * x - 1.0, 0.0, 4.0, &Options::default()).unwrap();
    assert_eq!((root.x, root.iterations), (0.5, 1));
}

/// The reason to prefer Brent's method: on smooth functions with a simple
/// root it needs far fewer evaluations than bisection.
#[test]
fn takes_fewer_steps_than_bisection_on_smooth_functions() {
    type Problem = (fn(f64) -> f64, f64, f64);
    let problems: [Problem; 4] = [
        (|x| x * x * x - x - 2.0, 1.0, 2.0),
        (|x| x.cos() - x, 0.0, 1.0),
        (|x| x * x.exp() - 1.0, 0.0, 1.0),
        (|x| x * x - 2.0, 0.0, 2.0),
    ];
    let options = Options::default();
    for (f, a, b) in problems {
        let by_brent = brent(f, a, b, &options).unwrap().iterations;
        let by_bisection = bisect(f, a, b, &options).unwrap().iterations;
        assert!(by_brent <= 10, "{by_brent} steps");
        assert!(by_bisection >= 3 * by_brent);
    }
}

// ---- Agreement with the Lean theorems -------------------------------------

/// `brent_mem` and `brent_signChange`: the returned bracket lies in the
/// initial bracket, has `x` at one end, and has the sign change.
#[test]
fn final_bracket_is_nested_and_has_a_sign_change() {
    let f = |x: f64| x * x * x - x - 2.0;
    let root = brent(f, 1.0, 2.0, &Options::default()).unwrap();
    assert!(1.0 <= root.lo && root.lo <= root.hi && root.hi <= 2.0);
    assert!(root.x == root.lo || root.x == root.hi);
    assert!(f(root.lo) <= 0.0 && f(root.hi) >= 0.0);
}

/// `brent_error_of_done`: with a coarse tolerance the result is still within
/// the tolerance of the root, and the final bracket is at most twice as wide.
#[test]
fn error_is_within_a_coarse_tolerance() {
    let root_of_two = 2.0_f64.sqrt();
    for t in [0.5, 0.1, 1e-2, 1e-3, 1e-6] {
        let root = brent(|x| x * x - 2.0, 0.0, 2.0, &abs_tol(t)).unwrap();
        assert!((root.x - root_of_two).abs() <= t, "t = {t}");
        assert!(root.hi - root.lo <= t, "t = {t}");
    }
}

/// `brent_done_of_le`: with an absolute tolerance `t`, the iteration stops
/// after `n` steps as soon as `(n + 2) * t / 2 >= b - a`. The functions are
/// chosen to defeat the interpolation.
#[test]
fn step_count_is_within_the_proved_bound() {
    type Problem = (fn(f64) -> f64, f64, f64);
    let problems: [Problem; 4] = [
        // A root of multiplicity nine.
        (|x| (x - 0.3).powi(9), 0.0, 1.0),
        // Flat, then very steep.
        (|x| (20.0 * (x - 0.9)).exp() - 1.0, 0.0, 1.0),
        // A jump across zero.
        (|x| if x < 0.7 { -1.0 } else { 1e-3 }, 0.0, 1.0),
        (|x| x.cbrt() + 0.1, -1.0, 1.0),
    ];
    for t in [0.25, 0.1, 1e-2] {
        for (i, (f, a, b)) in problems.into_iter().enumerate() {
            let root = brent(f, a, b, &abs_tol(t)).unwrap();
            let bound = (2.0 * (b - a) / t - 2.0).ceil().max(0.0) as usize;
            assert!(
                root.iterations <= bound,
                "problem {i}, t = {t}: {} steps, bound {bound}",
                root.iterations
            );
        }
    }
}

/// Functions on which the interpolation is of little use still converge, to
/// the tolerance. The root of multiplicity nine takes more steps than the
/// default limit allows, and about three times as many as bisection.
#[test]
fn converges_on_functions_that_defeat_the_interpolation() {
    type Problem = (fn(f64) -> f64, f64, f64, f64);
    let problems: [Problem; 4] = [
        (|x| (x - 0.3).powi(9), 0.0, 1.0, 0.3),
        (|x| (20.0 * (x - 0.9)).exp() - 1.0, 0.0, 1.0, 0.9),
        (|x| if x < 0.7 { -1.0 } else { 1e-3 }, 0.0, 1.0, 0.7),
        (|x| x.cbrt() + 0.1, -1.0, 1.0, -1e-3),
    ];
    let options = Options {
        max_iter: 200,
        ..Options::default()
    };
    for (i, (f, a, b, expected)) in problems.into_iter().enumerate() {
        let root = brent(f, a, b, &options).unwrap();
        assert!(
            (root.x - expected).abs() <= 2.0 * options.tol.bound(root.x),
            "problem {i}: got {}, expected {expected}",
            root.x
        );
    }
}

// ---- Hard inputs ----------------------------------------------------------

/// A root at an end of the bracket is found without a step.
#[test]
fn root_at_an_endpoint() {
    let options = Options::default();
    let root = brent(|x| x - 1.0, 1.0, 3.0, &options).unwrap();
    assert_eq!((root.x, root.iterations), (1.0, 0));
    let root = brent(|x| x - 3.0, 1.0, 3.0, &options).unwrap();
    assert_eq!((root.x, root.iterations), (3.0, 0));
    // Zero at both ends.
    let root = brent(|x| (x - 1.0) * (x - 3.0), 1.0, 3.0, &options).unwrap();
    assert_eq!((root.x, root.iterations), (3.0, 0));
}

#[test]
fn degenerate_bracket() {
    let root = brent(|x| x - 1.0, 1.0, 1.0, &Options::default()).unwrap();
    assert_eq!((root.x, root.iterations), (1.0, 0));

    let err = brent(|x| x - 1.0, 2.0, 2.0, &Options::default()).unwrap_err();
    assert_eq!(err, Error::NoSignChange { fa: 1.0, fb: 1.0 });
}

#[test]
fn several_roots_in_the_bracket() {
    // Roots at -1, 0 and 1. Which one is found is unspecified; it must be one of them.
    let options = Options::default();
    let root = brent(|x| x * (x - 1.0) * (x + 1.0), -1.5, 1.7, &options).unwrap();
    let nearest = root.x.round();
    assert!((-1.0..=1.0).contains(&nearest));
    assert!((root.x - nearest).abs() <= options.tol.bound(root.x));
}

#[test]
fn tiny_function_values_do_not_fake_a_sign_change() {
    // f > 0 everywhere, but f(a) * f(b) underflows to zero.
    let err = brent(|_| 1e-200, 0.0, 1.0, &Options::default()).unwrap_err();
    assert_eq!(
        err,
        Error::NoSignChange {
            fa: 1e-200,
            fb: 1e-200
        }
    );

    // A genuine root of a function whose values are all tiny.
    let root = brent(|x| 1e-200 * (x - 0.3), 0.0, 1.0, &Options::default()).unwrap();
    assert!((root.x - 0.3).abs() <= 1e-11);
}

#[test]
fn huge_bracket_does_not_overflow() {
    let options = Options::default();
    let root = brent(|x| x - 1.0, -f64::MAX, f64::MAX, &options).unwrap();
    assert!((root.x - 1.0).abs() <= options.tol.bound(root.x));

    // Not linear, so that the interpolation is put to work on huge steps.
    let options = Options {
        max_iter: 2000,
        ..Options::default()
    };
    let root = brent(|x| x.cbrt() - 1.0, -f64::MAX, f64::MAX, &options).unwrap();
    assert!((root.x - 1.0).abs() <= options.tol.bound(root.x));
    let root = brent(|x| x.atan() + 1.0, -f64::MAX, f64::MAX / 2.0, &options).unwrap();
    assert!((root.x + 1.0_f64.tan()).abs() <= options.tol.bound(root.x));
}

#[test]
fn large_root_is_reached_through_the_relative_tolerance() {
    let options = Options::default();
    let root = brent(|x| x - 1.234e15, 0.0, 1e16, &options).unwrap();
    assert!((root.x - 1.234e15).abs() <= options.tol.bound(root.x));
}

/// Infinite values make the interpolation produce NaN. The step is then a
/// bisection.
#[test]
fn infinite_function_values_still_have_a_sign() {
    let f = |x: f64| if x < 0.25 { f64::NEG_INFINITY } else { x - 0.5 };
    let root = brent(f, 0.0, 1.0, &Options::default()).unwrap();
    assert!((root.x - 0.5).abs() <= 1e-11);

    let f = |x: f64| {
        if x < 0.4 {
            f64::NEG_INFINITY
        } else if x > 0.6 {
            f64::INFINITY
        } else {
            x - 0.5
        }
    };
    let root = brent(f, 0.0, 1.0, &Options::default()).unwrap();
    assert!((root.x - 0.5).abs() <= 1e-11);
}

/// Continuity is a precondition that cannot be checked: for `1 / x` the
/// method converges to the pole, which is not a root.
#[test]
fn discontinuity_is_reported_as_a_root() {
    let root = brent(|x| 1.0 / x, -1.0, 2.0, &Options::default()).unwrap();
    assert!(root.x.abs() <= 1e-11);
}

// ---- Errors ---------------------------------------------------------------

#[test]
fn invalid_brackets() {
    let options = Options::default();
    let f = |x: f64| x;
    for (a, b) in [
        (1.0, -1.0),
        (f64::NAN, 1.0),
        (-1.0, f64::NAN),
        (f64::NEG_INFINITY, 1.0),
        (-1.0, f64::INFINITY),
    ] {
        match brent(f, a, b, &options) {
            Err(Error::InvalidBracket { .. }) => {}
            other => panic!("[{a}, {b}]: {other:?}"),
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
        match brent(|x| x, -1.0, 1.0, &options) {
            Err(Error::InvalidTolerance { .. }) => {}
            other => panic!("{tol:?}: {other:?}"),
        }
    }
}

#[test]
fn no_sign_change() {
    let err = brent(|x| x * x + 1.0, -1.0, 2.0, &Options::default()).unwrap_err();
    assert_eq!(err, Error::NoSignChange { fa: 2.0, fb: 5.0 });
}

#[test]
fn nan_function_value() {
    let options = Options::default();
    assert_eq!(
        brent(|_| f64::NAN, 0.0, 1.0, &options),
        Err(Error::NanValue { x: 0.0 })
    );
    // NaN away from the ends of the bracket only.
    let f = |x: f64| {
        if x > 0.0 && x < 1.0 {
            f64::NAN
        } else {
            x - 0.3
        }
    };
    match brent(f, 0.0, 1.0, &options) {
        Err(Error::NanValue { x }) => assert!(x > 0.0 && x < 1.0),
        other => panic!("{other:?}"),
    }
}

#[test]
fn iteration_limit() {
    let options = Options {
        max_iter: 3,
        ..abs_tol(1e-12)
    };
    let root_of_two = 2.0_f64.sqrt();
    let err = brent(|x| x * x - 2.0, 0.0, 2.0, &options).unwrap_err();
    match err {
        Error::MaxIterations { max_iter, lo, hi } => {
            assert_eq!(max_iter, 3);
            assert!(0.0 <= lo && lo <= root_of_two && root_of_two <= hi && hi <= 2.0);
            assert!(hi - lo < 2.0);
        }
        other => panic!("{other:?}"),
    }
}

/// A zero tolerance cannot be met unless the function is exactly zero at an
/// approximation: the bracket stops shrinking once its ends are adjacent
/// floating-point numbers.
#[test]
fn zero_tolerance_hits_the_iteration_limit() {
    let options = Options {
        max_iter: 200,
        ..abs_tol(0.0)
    };
    match brent(|x| x * x - 2.0, 0.0, 2.0, &options) {
        Err(Error::MaxIterations { lo, hi, .. }) => {
            assert!(lo < hi && hi - lo <= 2.0 * f64::EPSILON);
        }
        other => panic!("{other:?}"),
    }

    // Here the function is zero at the root, which is found exactly.
    let root = brent(|x| x - 0.5, 0.0, 2.0, &options).unwrap();
    assert_eq!(root.x, 0.5);
}

#[test]
fn counts_function_evaluations() {
    let mut calls = 0;
    let root = brent(
        |x| {
            calls += 1;
            x * x * x - x - 2.0
        },
        1.0,
        2.0,
        &Options::default(),
    )
    .unwrap();
    assert!(root.iterations > 0);
    assert_eq!(calls, root.iterations + 2);
}
