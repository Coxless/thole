//! Tests of `bisect` against reference values and on hard inputs.

use thole_core::Tolerance;
use thole_roots::{Error, Options, bisect};

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
        let root = bisect(f, a, b, &options).unwrap();
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

    let root = bisect(|x| x * x - 2.0, 0.0, 2.0, &options).unwrap();
    assert!((root.x - 2.0_f64.sqrt()).abs() <= options.tol.bound(root.x));

    let root = bisect(f64::cos, 0.0, 2.0, &options).unwrap();
    assert!((root.x - std::f64::consts::FRAC_PI_2).abs() <= options.tol.bound(root.x));

    // Decreasing function: the sign change is from positive to negative.
    let root = bisect(|x| 1.0 - x, -3.0, 5.0, &options).unwrap();
    assert!((root.x - 1.0).abs() <= options.tol.bound(root.x));
}

// ---- Agreement with the Lean theorems -------------------------------------

/// `bisect_exists_root`: the returned bracket has the sign change and lies in
/// the initial bracket.
#[test]
fn final_bracket_is_nested_and_has_a_sign_change() {
    let f = |x: f64| x * x * x - x - 2.0;
    let root = bisect(f, 1.0, 2.0, &Options::default()).unwrap();
    assert!(1.0 <= root.lo && root.lo <= root.x && root.x <= root.hi && root.hi <= 2.0);
    assert!(f(root.lo) <= 0.0 && f(root.hi) >= 0.0);
}

/// `bisectMid_error`: with a purely absolute tolerance `t`, the number of
/// steps is the smallest `n` with `(b - a) / 2^(n + 1) <= t`.
#[test]
fn step_count_matches_the_error_bound() {
    // (b - a, t, n): 1 / 2^10 <= 1e-3 < 1 / 2^9, and so on.
    let cases = [(1.0, 1e-3, 9), (1.0, 0.5, 0), (1.0, 0.25, 1), (8.0, 1.0, 2)];
    for (width, t, n) in cases {
        // Root at an irrational point so that no midpoint hits it exactly.
        let shift = 2.0_f64.sqrt() / 2.0 * width;
        let root = bisect(|x| x - shift, 0.0, width, &abs_tol(t)).unwrap();
        assert_eq!(root.iterations, n, "width = {width}, t = {t}");
        assert_eq!(root.hi - root.lo, width / 2.0_f64.powi(n as i32));
        assert!((root.x - shift).abs() <= t);
    }
}

// ---- Hard inputs ----------------------------------------------------------

#[test]
fn root_at_an_endpoint() {
    let options = Options::default();
    let root = bisect(|x| x - 1.0, 1.0, 3.0, &options).unwrap();
    assert!((root.x - 1.0).abs() <= options.tol.bound(root.x));
    let root = bisect(|x| x - 3.0, 1.0, 3.0, &options).unwrap();
    assert!((root.x - 3.0).abs() <= options.tol.bound(root.x));
}

#[test]
fn degenerate_bracket() {
    let root = bisect(|x| x - 1.0, 1.0, 1.0, &Options::default()).unwrap();
    assert_eq!((root.x, root.iterations), (1.0, 0));

    let err = bisect(|x| x - 1.0, 2.0, 2.0, &Options::default()).unwrap_err();
    assert_eq!(err, Error::NoSignChange { fa: 1.0, fb: 1.0 });
}

#[test]
fn several_roots_in_the_bracket() {
    // Roots at -1, 0 and 1. Which one is found is unspecified; it must be one of them.
    let options = Options::default();
    let root = bisect(|x| x * (x - 1.0) * (x + 1.0), -1.5, 1.7, &options).unwrap();
    let nearest = root.x.round();
    assert!((-1.0..=1.0).contains(&nearest));
    assert!((root.x - nearest).abs() <= options.tol.bound(root.x));
}

#[test]
fn tiny_function_values_do_not_fake_a_sign_change() {
    // f > 0 everywhere, but f(a) * f(b) underflows to zero.
    let err = bisect(|_| 1e-200, 0.0, 1.0, &Options::default()).unwrap_err();
    assert_eq!(
        err,
        Error::NoSignChange {
            fa: 1e-200,
            fb: 1e-200
        }
    );

    // A genuine root of a function whose values are all tiny.
    let root = bisect(|x| 1e-200 * (x - 0.3), 0.0, 1.0, &Options::default()).unwrap();
    assert!((root.x - 0.3).abs() <= 1e-11);
}

#[test]
fn huge_bracket_does_not_overflow() {
    let options = Options {
        max_iter: 2000,
        ..Options::default()
    };
    let root = bisect(|x| x - 1.0, -f64::MAX, f64::MAX, &options).unwrap();
    assert!((root.x - 1.0).abs() <= options.tol.bound(root.x));
}

#[test]
fn large_root_is_reached_through_the_relative_tolerance() {
    let options = Options::default();
    let root = bisect(|x| x - 1.234e15, 0.0, 1e16, &options).unwrap();
    assert!((root.x - 1.234e15).abs() <= options.tol.bound(root.x));
}

#[test]
fn infinite_function_values_still_have_a_sign() {
    let f = |x: f64| if x < 0.25 { f64::NEG_INFINITY } else { x - 0.5 };
    let root = bisect(f, 0.0, 1.0, &Options::default()).unwrap();
    assert!((root.x - 0.5).abs() <= 1e-11);
}

/// Continuity is a precondition that cannot be checked: for `1 / x` the
/// method converges to the pole, which is not a root.
#[test]
fn discontinuity_is_reported_as_a_root() {
    let root = bisect(|x| 1.0 / x, -1.0, 2.0, &Options::default()).unwrap();
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
        match bisect(f, a, b, &options) {
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
        match bisect(|x| x, -1.0, 1.0, &options) {
            Err(Error::InvalidTolerance { .. }) => {}
            other => panic!("{tol:?}: {other:?}"),
        }
    }
}

#[test]
fn no_sign_change() {
    let err = bisect(|x| x * x + 1.0, -1.0, 2.0, &Options::default()).unwrap_err();
    assert_eq!(err, Error::NoSignChange { fa: 2.0, fb: 5.0 });
}

#[test]
fn nan_function_value() {
    let options = Options::default();
    assert_eq!(
        bisect(|_| f64::NAN, 0.0, 1.0, &options),
        Err(Error::NanValue { x: 0.0 })
    );
    // NaN at the first midpoint only.
    let f = |x: f64| if x == 0.5 { f64::NAN } else { x - 0.3 };
    assert_eq!(
        bisect(f, 0.0, 1.0, &options),
        Err(Error::NanValue { x: 0.5 })
    );
}

#[test]
fn iteration_limit() {
    let options = Options {
        max_iter: 5,
        ..abs_tol(1e-9)
    };
    let err = bisect(|x| x - 0.3, 0.0, 1.0, &options).unwrap_err();
    // Five steps were taken: the bracket has width 1 / 2^5 and still contains the root.
    match err {
        Error::MaxIterations { max_iter, lo, hi } => {
            assert_eq!(max_iter, 5);
            assert_eq!(hi - lo, 1.0 / 32.0);
            assert!(lo <= 0.3 && 0.3 <= hi);
        }
        other => panic!("{other:?}"),
    }
}

/// A zero tolerance cannot be met: the bracket stops shrinking once its ends
/// are adjacent floating-point numbers.
#[test]
fn zero_tolerance_hits_the_iteration_limit() {
    let options = Options {
        max_iter: 200,
        ..abs_tol(0.0)
    };
    match bisect(|x| x * x - 2.0, 0.0, 2.0, &options) {
        Err(Error::MaxIterations { lo, hi, .. }) => {
            assert!(lo < hi && hi - lo <= 2.0 * f64::EPSILON);
        }
        other => panic!("{other:?}"),
    }
}

#[test]
fn counts_function_evaluations() {
    let mut calls = 0;
    let root = bisect(
        |x| {
            calls += 1;
            x - 0.3
        },
        0.0,
        1.0,
        &Options::default(),
    )
    .unwrap();
    assert_eq!(calls, root.iterations + 2);
}

#[test]
fn error_messages() {
    let message = Error::NoSignChange { fa: 2.0, fb: 5.0 }.to_string();
    assert_eq!(
        message,
        "no sign change over the bracket: f(a) = 2, f(b) = 5"
    );
}
