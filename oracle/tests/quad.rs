//! `thole_quad` against the Lean oracle.
//!
//! Lean counterpart: `oracle/lean/Thole/Oracle/Quad.lean`.

use proptest::prelude::*;
use proptest::test_runner::FileFailurePersistence;
use thole_core::Tolerance;
use thole_oracle::quad::{
    Check, GaussCall, KronrodCall, RuleCheck, kronrod_rule_request, rule_request,
};
use thole_oracle::{Poly, Verdict, ask, bits};
use thole_quad::{Error, GaussLegendre, Integral, Options, gauss_kronrod_rule};

fn config(cases: u32) -> ProptestConfig {
    ProptestConfig {
        cases,
        // Failing inputs are saved next to this file and tried first from then on.
        failure_persistence: Some(Box::new(FileFailurePersistence::WithSource(
            "proptest-regressions",
        ))),
        ..ProptestConfig::default()
    }
}

fn is_ok(verdict: &Verdict) -> bool {
    *verdict == Verdict::Ok
}

fn is_fail(verdict: &Verdict) -> bool {
    matches!(verdict, Verdict::Fail(_))
}

fn is_skip(verdict: &Verdict) -> bool {
    matches!(verdict, Verdict::Skip(_))
}

fn assert_verdict(request: &str, expected: fn(&Verdict) -> bool) {
    let verdict = ask(request);
    assert!(expected(&verdict), "{request}: {verdict:?}");
}

/// The request for a rule with the given nodes and weights.
fn raw_rule_request(check: RuleCheck, nodes: &[f64], weights: &[f64]) -> String {
    let name = match check {
        RuleCheck::Spec => "quad.gauss.rule.spec",
        RuleCheck::Bound => "quad.gauss.rule.bound",
    };
    let mut line = format!("{name} {}", nodes.len());
    for &x in nodes.iter().chain(weights) {
        line.push(' ');
        line.push_str(&bits(x));
    }
    line
}

// ---- The oracle tells right from wrong ------------------------------------

#[test]
fn a_gauss_rule_is_accepted_and_wrong_rules_are_rejected() {
    let rule = GaussLegendre::new(6).unwrap();
    for check in [RuleCheck::Spec, RuleCheck::Bound] {
        assert_verdict(&rule_request(check, &rule), is_ok);
    }
    let (x, w) = (rule.nodes().to_vec(), rule.weights().to_vec());

    // One unit in the last place: as good as far as the roots go.
    let mut nearby = x.clone();
    nearby[0] = nearby[0].next_down();
    nearby[5] = nearby[5].next_up();
    assert_verdict(&raw_rule_request(RuleCheck::Spec, &nearby, &w), is_fail);
    assert_verdict(&raw_rule_request(RuleCheck::Bound, &nearby, &w), is_ok);

    let mut far = x.clone();
    far[1] -= 1e-9;
    far[4] += 1e-9;
    let mut heavy = w.clone();
    heavy[2] *= 1.0 + 1e-9;
    heavy[3] *= 1.0 + 1e-9;
    let reversed: Vec<f64> = x.iter().rev().copied().collect();
    let wrong = [
        (far.clone(), w.clone()),
        (x.clone(), heavy),
        (reversed, w.clone()),
        // The rule with 7 points is not the rule with 6.
        (
            GaussLegendre::new(7).unwrap().nodes()[..6].to_vec(),
            GaussLegendre::new(7).unwrap().weights()[..6].to_vec(),
        ),
    ];
    for (nodes, weights) in wrong {
        for check in [RuleCheck::Spec, RuleCheck::Bound] {
            assert_verdict(&raw_rule_request(check, &nodes, &weights), is_fail);
        }
    }
}

#[test]
fn the_kronrod_constants_are_accepted_and_wrong_ones_are_rejected() {
    assert_verdict(&kronrod_rule_request(), is_ok);
    let (mut nodes, kronrod, gauss) = gauss_kronrod_rule();
    nodes[3] = nodes[3].next_up();
    let mut line = "quad.kronrod.rule".to_owned();
    for &x in nodes.iter().chain(&kronrod).chain(&gauss) {
        line.push(' ');
        line.push_str(&bits(x));
    }
    assert_verdict(&line, is_fail);
}

#[test]
fn a_gauss_integral_is_accepted_and_wrong_ones_are_rejected() {
    // Degree 9 = 2n - 1 for n = 5.
    let call = GaussCall {
        poly: Poly(vec![1.0, -2.0, 0.5, 3.0, 0.0, 0.0, -1.0, 0.25, 0.0, 2.0]),
        n: 5,
        a: -1.5,
        b: 2.25,
    };
    let result = call.integrate();
    let value = *result.as_ref().unwrap();
    for check in [Check::Spec, Check::Bound] {
        assert_verdict(&call.request(check, &result), is_ok);
        assert_verdict(&call.request(check, &Ok(value * (1.0 + 1e-9))), is_fail);
    }
    assert_verdict(&call.request(Check::Spec, &Ok(value.next_up())), is_fail);
    assert_verdict(&call.request(Check::Bound, &Ok(value.next_up())), is_ok);

    // Degree 10 is beyond the exactness of the rule.
    let higher = GaussCall {
        poly: Poly([call.poly.0.clone(), vec![1.0]].concat()),
        ..call
    };
    let result = higher.integrate();
    assert_verdict(&higher.request(Check::Spec, &result), is_ok);
    assert_verdict(&higher.request(Check::Bound, &result), is_skip);
}

#[test]
fn a_kronrod_integral_is_accepted_and_wrong_ones_are_rejected() {
    // x^20 - x^3 on [0, 1.5]: exact for the Kronrod rule, not for the Gauss
    // rule, so the error estimate forces some halvings.
    let mut coeffs = vec![0.0; 21];
    coeffs[20] = 1.0;
    coeffs[3] = -1.0;
    let call = KronrodCall {
        poly: Poly(coeffs),
        a: 0.0,
        b: 1.5,
        options: Options {
            tol: Tolerance::new(1e-12, 0.0),
            max_subintervals: 100,
        },
    };
    let result = call.integrate();
    let integral = result.unwrap();
    assert!(integral.subintervals > 1, "{integral:?}");
    for check in [Check::Spec, Check::Bound] {
        assert_verdict(&call.request(check, &result), is_ok);
    }
    let wrong_for_both = [
        Ok(Integral {
            value: integral.value * (1.0 + 1e-9),
            ..integral
        }),
        Ok(Integral {
            evaluations: integral.evaluations + 15,
            ..integral
        }),
        Ok(Integral {
            error: 1e-3,
            ..integral
        }),
        Err(Error::MaxSubintervals {
            max_subintervals: 100,
            value: integral.value,
            error: integral.error,
        }),
    ];
    for wrong in wrong_for_both {
        for check in [Check::Spec, Check::Bound] {
            assert_verdict(&call.request(check, &wrong), is_fail);
        }
    }
    let wrong_for_spec = [
        Ok(Integral {
            value: integral.value.next_up(),
            ..integral
        }),
        Ok(Integral {
            error: integral.error * 0.5,
            ..integral
        }),
    ];
    for wrong in wrong_for_spec {
        assert_verdict(&call.request(Check::Spec, &wrong), is_fail);
        assert_verdict(&call.request(Check::Bound, &wrong), is_ok);
    }

    // The limit, with the estimates where it was hit.
    let limited = KronrodCall {
        options: Options {
            max_subintervals: 2,
            ..call.options
        },
        ..call.clone()
    };
    let result = limited.integrate();
    assert!(
        matches!(result, Err(Error::MaxSubintervals { .. })),
        "{result:?}"
    );
    for check in [Check::Spec, Check::Bound] {
        assert_verdict(&limited.request(check, &result), is_ok);
    }
}

// ---- Random calls ---------------------------------------------------------

/// `n / 2^shift` for an integer `n` with `|n| <= limit`.
fn dyadic(limit: i32, shift: i32) -> impl Strategy<Value = f64> {
    (-limit..=limit).prop_map(move |n| f64::from(n) * 2.0_f64.powi(-shift))
}

/// A finite number at one of several scales, or zero.
fn scaled() -> impl Strategy<Value = f64> {
    prop_oneof![Just(0.0), -1e3..1e3, -1.0..1.0, -1e-3..1e-3, dyadic(64, 3)]
}

/// The ends of an interval: anything from a point to a long interval.
fn interval() -> impl Strategy<Value = (f64, f64)> {
    (scaled(), scaled())
}

/// Calls of the Gauss-Legendre rule on polynomials of degree up to `2n + 1`.
fn gauss_call() -> impl Strategy<Value = GaussCall> {
    (1..=16_usize)
        .prop_flat_map(|n| {
            (
                Just(n),
                prop::collection::vec(scaled(), 1..=2 * n + 2),
                interval(),
            )
        })
        .prop_map(|(n, coeffs, (a, b))| GaussCall {
            poly: Poly(coeffs),
            n,
            a,
            b,
        })
}

/// Calls of the adaptive integrator on polynomials of degree up to 30, with
/// any tolerance and limit.
fn kronrod_call() -> impl Strategy<Value = KronrodCall> {
    let default = Options::default();
    (
        prop::collection::vec(scaled(), 1..=31),
        interval(),
        prop_oneof![Just(0.0), Just(default.tol.abs), 1e-15..1e-3],
        prop_oneof![Just(0.0), Just(default.tol.rel), 1e-16..1e-6],
        prop_oneof![Just(default.max_subintervals), 1..=60_usize],
    )
        .prop_map(|(coeffs, (a, b), abs, rel, max_subintervals)| KronrodCall {
            poly: Poly(coeffs),
            a,
            b,
            options: Options {
                tol: Tolerance::new(abs, rel),
                max_subintervals,
            },
        })
}

proptest! {
    #![proptest_config(config(200))]

    /// The nodes and weights of every rule up to 64 points are exactly what
    /// the Lean program computes in the model of `f64` arithmetic, and are
    /// within `2^-50` and a relative `2^-40` of the roots of `P_n` and the
    /// Gauss weights.
    #[test]
    fn gauss_rules_agree_with_the_specification(n in 1..=64_usize) {
        let rule = GaussLegendre::new(n).unwrap();
        for check in [RuleCheck::Spec, RuleCheck::Bound] {
            let verdict = ask(&rule_request(check, &rule));
            prop_assert_eq!(verdict, Verdict::Ok, "{:?}", check);
        }
    }
}

proptest! {
    #![proptest_config(config(1000))]

    /// For any finite arguments, the integral of a polynomial by the
    /// Gauss-Legendre rule is exactly what the Lean program computes in the
    /// model of `f64` arithmetic.
    #[test]
    fn gauss_integrals_agree_with_the_specification(call in gauss_call()) {
        let result = call.integrate();
        let verdict = ask(&call.request(Check::Spec, &result));
        prop_assert_eq!(verdict, Verdict::Ok, "{:?}", result);
    }

    /// For any finite arguments, the integral of a polynomial of degree at
    /// most `2n - 1` is exact up to rounding.
    #[test]
    fn gauss_integrals_are_exact_for_degree_2n_minus_1(call in gauss_call()) {
        let result = call.integrate();
        match ask(&call.request(Check::Bound, &result)) {
            Verdict::Ok => {}
            Verdict::Skip(reason) => return Err(TestCaseError::reject(reason)),
            Verdict::Fail(reason) => prop_assert!(false, "{reason}: {result:?}"),
        }
    }

    /// For any finite arguments, `gauss_kronrod` returns exactly what the Lean
    /// definitions compute in the model of `f64` arithmetic: the same
    /// outcome, with the same estimates and the same number of subintervals.
    #[test]
    fn gauss_kronrod_agrees_with_the_specification(call in kronrod_call()) {
        let result = call.integrate();
        let verdict = ask(&call.request(Check::Spec, &result));
        prop_assert_eq!(verdict, Verdict::Ok, "{:?}", result);
    }

    /// For any finite arguments, the result of `gauss_kronrod` has the
    /// properties that the Lean definitions and theorems give, up to rounding.
    #[test]
    fn gauss_kronrod_result_has_the_proved_properties(call in kronrod_call()) {
        let result = call.integrate();
        let verdict = ask(&call.request(Check::Bound, &result));
        prop_assert_eq!(verdict, Verdict::Ok, "{:?}", result);
    }
}
