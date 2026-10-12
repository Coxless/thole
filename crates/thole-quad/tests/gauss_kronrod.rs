//! Tests of `gauss_kronrod` against reference values and on hard inputs.

use thole_core::Tolerance;
use thole_quad::{Error, Integral, Options, gauss_kronrod, gauss_kronrod_rule};

fn tight() -> Options {
    Options {
        tol: Tolerance::new(1e-14, 1e-14),
        max_subintervals: 1000,
    }
}

type Problem = (fn(f64) -> f64, f64, f64, f64);

/// Integrals computed with mpmath at 50 digits by
/// `python/reference_values.py`: smooth integrands, and integrands with a
/// singularity at an end, a kink, a narrow peak and oscillations.
const PROBLEMS: [Problem; 9] = [
    (f64::exp, 0.0, 1.0, 1.7182818284590453),
    (f64::sin, 0.0, std::f64::consts::PI, 2.0),
    (
        |x| 1.0 / (1.0 + x * x),
        0.0,
        1.0,
        std::f64::consts::FRAC_PI_4,
    ),
    (f64::sqrt, 0.0, 1.0, 0.6666666666666666),
    (|x| -x.ln(), 0.0, 1.0, 1.0),
    (|x| (x - 1.0 / 3.0).abs(), -1.0, 1.0, 1.1111111111111112),
    (
        |x| 1.0 / (1e-4 + (x - 0.3) * (x - 0.3)),
        0.0,
        1.0,
        309.3986915124149,
    ),
    (|x| (30.0 * x).cos(), 0.0, 1.0, -0.03293438746976206),
    (|x| (-x * x).exp(), -5.0, 5.0, 1.772453850902791),
];

// ---- Reference values -----------------------------------------------------

/// With the default tolerance, the error is within the tolerance, and the
/// error estimate is not below the actual error.
#[test]
fn matches_mpmath_reference_integrals() {
    let options = Options::default();
    for (i, (f, a, b, expected)) in PROBLEMS.into_iter().enumerate() {
        let integral = gauss_kronrod(f, a, b, &options).unwrap();
        let error = (integral.value - expected).abs();
        assert!(
            error <= options.tol.bound(expected),
            "problem {i}: {integral:?}"
        );
        assert!(
            error <= integral.error + 4.0 * f64::EPSILON * expected.abs(),
            "problem {i}: {integral:?}"
        );
        assert!(integral.error <= options.tol.bound(integral.value));
    }
}

/// With a tolerance near the precision of `f64`, the error is within a few
/// units in the last place, up to the narrow peak.
#[test]
fn reaches_full_precision() {
    for (i, (f, a, b, expected)) in PROBLEMS.into_iter().enumerate() {
        let integral = gauss_kronrod(f, a, b, &tight()).unwrap();
        let error = (integral.value - expected).abs();
        assert!(
            error <= 1e-13 * expected.abs().max(1.0),
            "problem {i}: {integral:?}"
        );
    }
}

/// Smooth integrands are done with the first 15 evaluations.
#[test]
fn smooth_integrands_take_one_interval() {
    let integral = gauss_kronrod(f64::exp, 0.0, 1.0, &Options::default()).unwrap();
    assert_eq!((integral.subintervals, integral.evaluations), (1, 15));
    let integral = gauss_kronrod(|x| 1.0 / (1.0 + x * x), 0.0, 1.0, &Options::default()).unwrap();
    assert_eq!((integral.subintervals, integral.evaluations), (1, 15));
}

// ---- Agreement with the constants and the Lean theorems -------------------

/// The Kronrod rule is exact for degree 22 and the Gauss rule for degree 13,
/// and not beyond: for every monomial up to degree 22 the error estimate,
/// the difference of the two, vanishes exactly when the Gauss rule is exact.
#[test]
fn the_rules_are_exact_for_their_degrees() {
    let (nodes, kronrod, gauss) = gauss_kronrod_rule();
    for degree in 0..=24 {
        let exact = if degree % 2 == 0 {
            2.0 / (degree as f64 + 1.0)
        } else {
            0.0
        };
        let rule =
            |w: &[f64; 15]| -> f64 { nodes.iter().zip(w).map(|(x, w)| w * x.powi(degree)).sum() };
        let (k, g) = (rule(&kronrod), rule(&gauss));
        if degree <= 22 {
            assert!((k - exact).abs() <= 1e-15, "Kronrod, degree {degree}: {k}");
        } else if degree % 2 == 0 {
            assert!((k - exact).abs() > 1e-10, "Kronrod, degree {degree}: {k}");
        }
        if degree <= 13 {
            assert!((g - exact).abs() <= 1e-15, "Gauss, degree {degree}: {g}");
        } else if degree % 2 == 0 {
            assert!((g - exact).abs() > 1e-6, "Gauss, degree {degree}: {g}");
        }
    }
}

#[test]
fn the_constants_are_symmetric_and_sorted() {
    let (nodes, kronrod, gauss) = gauss_kronrod_rule();
    assert!(nodes.windows(2).all(|p| p[0] < p[1]));
    for i in 0..15 {
        assert_eq!(nodes[i], -nodes[14 - i]);
        assert_eq!(kronrod[i], kronrod[14 - i]);
        assert_eq!(gauss[i], gauss[14 - i]);
        assert!(kronrod[i] > 0.0);
        assert_eq!(gauss[i] > 0.0, i % 2 == 1);
    }
    assert!((kronrod.iter().sum::<f64>() - 2.0).abs() <= 4.0 * f64::EPSILON);
    assert!((gauss.iter().sum::<f64>() - 2.0).abs() <= 4.0 * f64::EPSILON);
}

/// A polynomial of degree 13 is integrated exactly on every subinterval by
/// both rules, so the error estimate is zero up to rounding, and one
/// interval does.
#[test]
fn polynomials_of_degree_13_take_one_interval() {
    let f = |x: f64| x.powi(13) - 3.0 * x.powi(6) + 1.0;
    let integral = gauss_kronrod(f, -1.0, 2.0, &tight()).unwrap();
    let exact = (2.0_f64.powi(14) - 1.0) / 14.0 - 3.0 * (2.0_f64.powi(7) + 1.0) / 7.0 + 3.0;
    assert_eq!(integral.subintervals, 1);
    assert!((integral.value - exact).abs() <= 1e-12 * exact.abs());
}

/// `gk_error_le`: the returned error estimate is the sum of the estimates
/// over a partition, so it does not shrink when the tolerance is tightened.
#[test]
fn error_estimate_bounds_the_error() {
    for (i, (f, a, b, expected)) in PROBLEMS.into_iter().enumerate() {
        for t in [1e-3, 1e-6, 1e-9] {
            let options = Options {
                tol: Tolerance::new(t, 0.0),
                max_subintervals: 1000,
            };
            let integral = gauss_kronrod(f, a, b, &options).unwrap();
            assert!(integral.error <= t, "problem {i}, t = {t}");
            assert!(
                (integral.value - expected).abs() <= integral.error + 1e-14 * expected.abs(),
                "problem {i}, t = {t}: {integral:?}"
            );
        }
    }
}

// ---- Hard inputs ----------------------------------------------------------

/// A narrow peak between the nodes of the first estimate is missed: both
/// rules see a smooth function, and agree. The error estimate is an
/// estimate, not a bound.
#[test]
fn a_peak_between_the_nodes_is_missed() {
    let f = |x: f64| 1.0 + if (x - 0.5).abs() < 1e-6 { 1e6 } else { 0.0 };
    let integral = gauss_kronrod(f, 0.0, 1.0, &Options::default()).unwrap();
    assert_eq!(integral.value, 1.0);
    assert_eq!(integral.error, 0.0);
    // The true integral is about 3.
}

#[test]
fn reversed_and_empty_intervals() {
    let options = Options::default();
    let forward = gauss_kronrod(f64::sqrt, 0.0, 1.0, &options).unwrap();
    let backward = gauss_kronrod(f64::sqrt, 1.0, 0.0, &options).unwrap();
    // The nodes are visited in the other order, so the sums can differ in
    // the last place.
    assert!((forward.value + backward.value).abs() <= 4.0 * f64::EPSILON);
    assert_eq!(forward.subintervals, backward.subintervals);
    let empty = gauss_kronrod(f64::sqrt, 2.0, 2.0, &options).unwrap();
    assert_eq!(
        empty,
        Integral {
            value: 0.0,
            error: 0.0,
            subintervals: 1,
            evaluations: 15
        }
    );
}

#[test]
fn huge_interval_does_not_overflow() {
    let integral = gauss_kronrod(|_| 1e-300, -f64::MAX, f64::MAX, &Options::default()).unwrap();
    let expected = 2.0 * (f64::MAX * 1e-300);
    assert!((integral.value - expected).abs() <= 1e-14 * expected);
}

#[test]
fn counts_function_evaluations() {
    let mut calls = 0;
    let integral = gauss_kronrod(
        |x: f64| {
            calls += 1;
            x.sqrt()
        },
        0.0,
        1.0,
        &Options::default(),
    )
    .unwrap();
    assert!(integral.subintervals > 1);
    assert_eq!(calls, integral.evaluations);
    assert_eq!(calls, 15 * (2 * integral.subintervals - 1));
}

// ---- Errors ---------------------------------------------------------------

#[test]
fn invalid_arguments() {
    let options = Options::default();
    for (a, b) in [(f64::NAN, 1.0), (0.0, f64::INFINITY)] {
        match gauss_kronrod(f64::exp, a, b, &options) {
            Err(Error::InvalidInterval { .. }) => {}
            other => panic!("[{a}, {b}]: {other:?}"),
        }
    }
    for tol in [Tolerance::new(-1.0, 0.0), Tolerance::new(0.0, f64::NAN)] {
        let options = Options {
            tol,
            ..Options::default()
        };
        match gauss_kronrod(f64::exp, 0.0, 1.0, &options) {
            Err(Error::InvalidTolerance { .. }) => {}
            other => panic!("{tol:?}: {other:?}"),
        }
    }
    let options = Options {
        max_subintervals: 0,
        ..Options::default()
    };
    assert_eq!(
        gauss_kronrod(f64::exp, 0.0, 1.0, &options),
        Err(Error::InvalidLimit {
            max_subintervals: 0
        })
    );
}

#[test]
fn non_finite_values() {
    match gauss_kronrod(|x| 1.0 / x, -1.0, 1.0, &Options::default()) {
        Err(Error::NonFiniteValue { x, fx }) => {
            assert_eq!(x, 0.0);
            assert!(fx.is_infinite());
        }
        other => panic!("{other:?}"),
    }
}

#[test]
fn subinterval_limit() {
    let options = Options {
        tol: Tolerance::new(1e-14, 0.0),
        max_subintervals: 3,
    };
    match gauss_kronrod(f64::sqrt, 0.0, 1.0, &options) {
        Err(Error::MaxSubintervals {
            max_subintervals: 3,
            value,
            error,
        }) => {
            assert!((value - 2.0 / 3.0).abs() < 1e-4);
            assert!(error > 1e-14);
        }
        other => panic!("{other:?}"),
    }
    // A zero tolerance is met only where both rules agree exactly.
    let options = Options {
        tol: Tolerance::new(0.0, 0.0),
        max_subintervals: 1,
    };
    assert!(gauss_kronrod(|x| 2.0 * x, 0.0, 1.0, &options).is_ok());
}
