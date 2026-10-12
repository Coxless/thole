//! Tests of `GaussLegendre` and `gauss_legendre` against reference values and
//! on hard inputs.

use thole_quad::{Error, GaussLegendre, gauss_legendre};

/// `|x - y|` in units of `2^-53`, the spacing of `f64` values just below 1.
fn units(x: f64, y: f64) -> f64 {
    (x - y).abs() / 2.0_f64.powi(-53)
}

// ---- Reference values -----------------------------------------------------

/// The nodes and weights of the 20-point rule, the positive half from the
/// largest node, computed with mpmath at 50 digits by
/// `python/reference_values.py`.
#[test]
fn matches_mpmath_nodes_and_weights() {
    let nodes = [
        0.9931285991850949,
        0.9639719272779138,
        0.912234428251326,
        0.8391169718222188,
        0.7463319064601508,
        0.636053680726515,
        0.5108670019508271,
        0.37370608871541955,
        0.22778585114164507,
        0.07652652113349734,
    ];
    let weights = [
        0.017614007139152118,
        0.04060142980038694,
        0.06267204833410907,
        0.08327674157670475,
        0.10193011981724044,
        0.11819453196151841,
        0.13168863844917664,
        0.14209610931838204,
        0.14917298647260374,
        0.15275338713072584,
    ];
    let rule = GaussLegendre::new(20).unwrap();
    for i in 0..10 {
        let (x, w) = (rule.nodes()[19 - i], rule.weights()[19 - i]);
        assert!(units(x, nodes[i]) <= 1.0, "node {i}: {x} vs {}", nodes[i]);
        assert!(
            units(w, weights[i]) <= 4.0,
            "weight {i}: {w} vs {}",
            weights[i]
        );
    }
}

/// Closed forms of the rules with up to 5 points (Abramowitz and Stegun,
/// table 25.4).
#[test]
fn matches_closed_forms() {
    let check = |n: usize, nodes: &[f64], weights: &[f64]| {
        let rule = GaussLegendre::new(n).unwrap();
        assert_eq!(rule.order(), n);
        for i in 0..n {
            assert!(units(rule.nodes()[i], nodes[i]) <= 2.0, "n = {n}, node {i}");
            assert!(
                units(rule.weights()[i], weights[i]) <= 4.0,
                "n = {n}, weight {i}"
            );
        }
    };
    check(1, &[0.0], &[2.0]);
    let x = 1.0 / 3.0_f64.sqrt();
    check(2, &[-x, x], &[1.0, 1.0]);
    let x = 0.6_f64.sqrt();
    check(3, &[-x, 0.0, x], &[5.0 / 9.0, 8.0 / 9.0, 5.0 / 9.0]);
    let r = (6.0 / 5.0_f64).sqrt() * 2.0 / 7.0;
    let (x1, x2) = ((3.0 / 7.0 - r).sqrt(), (3.0 / 7.0 + r).sqrt());
    let s = 30.0_f64.sqrt() / 36.0;
    check(
        4,
        &[-x2, -x1, x1, x2],
        &[0.5 - s, 0.5 + s, 0.5 + s, 0.5 - s],
    );
    let r = 2.0 * (10.0 / 7.0_f64).sqrt();
    let (x1, x2) = ((5.0 - r).sqrt() / 3.0, (5.0 + r).sqrt() / 3.0);
    let (w1, w2) = (
        (322.0 + 13.0 * 70.0_f64.sqrt()) / 900.0,
        (322.0 - 13.0 * 70.0_f64.sqrt()) / 900.0,
    );
    check(
        5,
        &[-x2, -x1, 0.0, x1, x2],
        &[w2, w1, 128.0 / 225.0, w1, w2],
    );
}

/// Integrals computed with mpmath at 50 digits by
/// `python/reference_values.py`, for smooth functions, which the rule with
/// 20 points gets to within a few units in the last place.
#[test]
fn matches_mpmath_reference_integrals() {
    type Problem = (fn(f64) -> f64, f64, f64, f64);
    let problems: [Problem; 5] = [
        (f64::exp, 0.0, 1.0, 1.7182818284590453),
        (f64::sin, 0.0, std::f64::consts::PI, 2.0),
        (
            |x| 1.0 / (1.0 + x * x),
            0.0,
            1.0,
            std::f64::consts::FRAC_PI_4,
        ),
        (|x| (30.0 * x).cos(), 0.0, 1.0, -0.03293438746976206),
        (|x| (-x * x).exp(), -5.0, 5.0, 1.772453850902791),
    ];
    let rule = GaussLegendre::new(40).unwrap();
    for (f, a, b, expected) in problems {
        let value = rule.integrate(f, a, b).unwrap();
        assert!(
            (value - expected).abs() <= 1e-14 * expected.abs().max(1.0),
            "got {value}, expected {expected}"
        );
    }
}

// ---- Agreement with the Lean theorems -------------------------------------

/// `gauss_exact` and `rule_exact_of_exact`: the rule with `n` points is
/// exact for every polynomial of degree at most `2n - 1`, on any interval,
/// and not for degree `2n`.
#[test]
fn exact_for_polynomials_of_degree_2n_minus_1() {
    for n in 1..=12 {
        let rule = GaussLegendre::new(n).unwrap();
        for (a, b) in [(-1.0_f64, 1.0_f64), (0.0, 1.0), (-3.0, 2.0)] {
            for degree in 0..=2 * n {
                let f = |x: f64| x.powi(degree as i32);
                let exact =
                    (b.powi(degree as i32 + 1) - a.powi(degree as i32 + 1)) / (degree as f64 + 1.0);
                let value = rule.integrate(f, a, b).unwrap();
                let scale = a.abs().max(b.abs()).powi(degree as i32) * (b - a);
                let error = (value - exact).abs() / scale;
                if degree < 2 * n {
                    assert!(
                        error <= 1e-14,
                        "n = {n}, degree {degree} on [{a}, {b}]: {error}"
                    );
                } else if a == -1.0 {
                    // The error for x^(2n) on [-1, 1] is
                    // 2^(2n+1) (n!)^4 / ((2n+1) ((2n)!)^2), above 1e-7 for n <= 12.
                    assert!(
                        error > 1e-8,
                        "n = {n}, degree {degree} on [{a}, {b}]: {error}"
                    );
                }
            }
        }
    }
}

/// `legendre_neg`: the rule is symmetric.
#[test]
fn nodes_and_weights_are_symmetric_and_sorted() {
    for n in [1, 2, 7, 20, 101, 1000] {
        let rule = GaussLegendre::new(n).unwrap();
        let (x, w) = (rule.nodes(), rule.weights());
        for i in 0..n {
            assert_eq!(x[i], -x[n - 1 - i]);
            assert_eq!(w[i], w[n - 1 - i]);
            assert!(w[i] > 0.0);
            assert!(-1.0 < x[i] && x[i] < 1.0);
        }
        assert!(x.windows(2).all(|p| p[0] < p[1]), "n = {n}");
        let total: f64 = w.iter().sum();
        assert!((total - 2.0).abs() <= 1e-14, "n = {n}: {total}");
    }
}

/// The 7-point rule is the Gauss part of the 7-15 Gauss-Kronrod pair, whose
/// constants come from QUADPACK.
#[test]
fn matches_the_gauss_part_of_the_kronrod_constants() {
    let (nodes, _, gauss) = thole_quad::gauss_kronrod_rule();
    let rule = GaussLegendre::new(7).unwrap();
    let pairs: Vec<(f64, f64)> = nodes
        .iter()
        .zip(&gauss)
        .filter(|(_, w)| **w != 0.0)
        .map(|(&x, &w)| (x, w))
        .collect();
    for (i, (x, w)) in pairs.into_iter().enumerate() {
        assert_eq!(rule.nodes()[i], x);
        assert!(units(rule.weights()[i], w) <= 1.0);
    }
}

// ---- Hard inputs ----------------------------------------------------------

#[test]
fn reversed_and_empty_intervals() {
    let rule = GaussLegendre::new(5).unwrap();
    let forward = rule.integrate(f64::exp, 0.0, 1.0).unwrap();
    let backward = rule.integrate(f64::exp, 1.0, 0.0).unwrap();
    assert_eq!(forward, -backward);
    assert_eq!(rule.integrate(f64::exp, 2.0, 2.0).unwrap(), 0.0);
}

#[test]
fn huge_interval_does_not_overflow() {
    let value = gauss_legendre(|_| 1e-300, -f64::MAX, f64::MAX, 3).unwrap();
    let expected = 2.0 * (f64::MAX * 1e-300);
    assert!((value - expected).abs() <= 1e-14 * expected);
}

/// An endpoint singularity: the nodes avoid the ends, so the rule gives a
/// finite but inaccurate value.
#[test]
fn endpoint_singularity_converges_slowly() {
    let error = |n| (gauss_legendre(|x| -x.ln(), 0.0, 1.0, n).unwrap() - 1.0).abs();
    assert!(error(10) > 1e-3);
    assert!(error(1000) < error(10) / 100.0);
}

#[test]
fn large_orders() {
    let rule = GaussLegendre::new(2000).unwrap();
    let value = rule.integrate(|x| (100.0 * x).cos(), -1.0, 1.0).unwrap();
    let expected = 2.0 * 100.0_f64.sin() / 100.0;
    assert!((value - expected).abs() <= 1e-14);
}

#[test]
fn counts_function_evaluations() {
    let mut calls = 0;
    gauss_legendre(
        |x| {
            calls += 1;
            x
        },
        0.0,
        1.0,
        9,
    )
    .unwrap();
    assert_eq!(calls, 9);
}

// ---- Errors ---------------------------------------------------------------

#[test]
fn zero_points() {
    assert_eq!(GaussLegendre::new(0), Err(Error::InvalidOrder { n: 0 }));
    assert_eq!(
        gauss_legendre(f64::exp, 0.0, 1.0, 0),
        Err(Error::InvalidOrder { n: 0 })
    );
}

#[test]
fn invalid_intervals() {
    let rule = GaussLegendre::new(3).unwrap();
    for (a, b) in [
        (f64::NAN, 1.0),
        (0.0, f64::NAN),
        (f64::NEG_INFINITY, 1.0),
        (0.0, f64::INFINITY),
    ] {
        match rule.integrate(f64::exp, a, b) {
            Err(Error::InvalidInterval { .. }) => {}
            other => panic!("[{a}, {b}]: {other:?}"),
        }
    }
}

#[test]
fn non_finite_values() {
    let rule = GaussLegendre::new(3).unwrap();
    // NaN is not equal to itself, so the error is taken apart.
    match rule.integrate(|_| f64::NAN, -1.0, 1.0) {
        Err(Error::NonFiniteValue { x, fx }) => {
            assert_eq!(x, rule.nodes()[0]);
            assert!(fx.is_nan());
        }
        other => panic!("{other:?}"),
    }
    match rule.integrate(|x| 1.0 / x, -1.0, 1.0) {
        Err(Error::NonFiniteValue { x, fx }) => {
            assert_eq!(x, 0.0);
            assert!(fx.is_infinite());
        }
        other => panic!("{other:?}"),
    }
}
