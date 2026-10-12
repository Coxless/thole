//! `thole_roots` against the Lean oracle.
//!
//! Lean counterpart: `oracle/lean/Thole/Oracle/Roots.lean`.

use proptest::prelude::*;
use proptest::test_runner::FileFailurePersistence;
use thole_core::Tolerance;
use thole_oracle::roots::{BracketCall, Check, NewtonCall};
use thole_oracle::{Poly, Verdict, ask};
use thole_roots::{Error, NewtonRoot, Options, Root};

fn call(coeffs: &[f64], a: f64, b: f64, abs: f64, rel: f64, max_iter: usize) -> BracketCall {
    BracketCall {
        poly: Poly(coeffs.to_vec()),
        a,
        b,
        options: Options {
            tol: Tolerance::new(abs, rel),
            max_iter,
        },
    }
}

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

// ---- The oracle tells right from wrong ------------------------------------
//
// A check that accepts everything would let the tests below pass. These take
// one call of each kind, and require the oracle to accept what the method
// returned and to reject results that are wrong in one respect.

/// `x^2 - 2` on `[0, 2]`: an irrational root, so no midpoint hits it.
fn sqrt_two() -> BracketCall {
    call(&[-2.0, 0.0, 1.0], 0.0, 2.0, 2.0_f64.powi(-10), 0.0, 100)
}

fn unwrap_root(result: Result<Root, Error>) -> Root {
    result.expect("the call finds a root")
}

#[test]
fn a_root_is_accepted_and_wrong_roots_are_rejected() {
    let call = sqrt_two();
    let root = unwrap_root(call.bisect());
    for check in [Check::BisectSpec, Check::BisectBound] {
        assert_eq!(ask(&call.request(check, &Ok(root))), Verdict::Ok);
    }

    let width = root.hi - root.lo;
    let wrong_for_both = [
        // The bracket next to the right one: no sign change.
        Root {
            x: root.x + width,
            lo: root.lo + width,
            hi: root.hi + width,
            ..root
        },
        // An end of the bracket instead of its midpoint.
        Root { x: root.lo, ..root },
        // Stopped one step early: the bracket is too wide.
        Root {
            lo: root.lo - width,
            x: root.lo,
            iterations: root.iterations - 1,
            ..root
        },
        // A bracket that leaves the initial one.
        Root {
            lo: -1.0,
            hi: 3.0,
            x: 1.0,
            ..root
        },
    ];
    for wrong in wrong_for_both {
        for check in [Check::BisectSpec, Check::BisectBound] {
            let verdict = ask(&call.request(check, &Ok(wrong)));
            assert!(
                matches!(verdict, Verdict::Fail(_)),
                "{check:?} {wrong:?}: {verdict:?}"
            );
        }
    }

    // Only the comparison with the specification sees these.
    let wrong_for_spec = [
        Ok(Root {
            iterations: root.iterations + 1,
            ..root
        }),
        // One step too many: a valid bracket, but not where bisection stops.
        Ok(Root {
            hi: root.x,
            x: f64::midpoint(root.lo, root.x),
            iterations: root.iterations + 1,
            ..root
        }),
        Err(Error::MaxIterations {
            max_iter: 100,
            lo: root.lo,
            hi: root.hi,
        }),
    ];
    for wrong in wrong_for_spec {
        let verdict = ask(&call.request(Check::BisectSpec, &wrong));
        assert!(
            matches!(verdict, Verdict::Fail(_)),
            "{wrong:?}: {verdict:?}"
        );
    }

    let no_sign_change = Err(Error::NoSignChange { fa: -2.0, fb: 2.0 });
    for check in [Check::BisectSpec, Check::BisectBound] {
        let verdict = ask(&call.request(check, &no_sign_change));
        assert!(
            matches!(verdict, Verdict::Fail(_)),
            "{check:?}: {verdict:?}"
        );
    }
}

#[test]
fn a_missing_sign_change_is_accepted_and_a_root_is_rejected() {
    // x^2 + 1 has no real root.
    let call = call(&[1.0, 0.0, 1.0], -1.0, 2.0, 2.0_f64.powi(-10), 0.0, 100);
    let result = call.bisect();
    assert!(matches!(result, Err(Error::NoSignChange { .. })));
    let invented = Ok(Root {
        x: 0.5,
        lo: 0.5 - 2.0_f64.powi(-10),
        hi: 0.5 + 2.0_f64.powi(-10),
        iterations: 11,
    });
    for check in [Check::BisectSpec, Check::BisectBound] {
        assert_eq!(ask(&call.request(check, &result)), Verdict::Ok);
        let verdict = ask(&call.request(check, &invented));
        assert!(
            matches!(verdict, Verdict::Fail(_)),
            "{check:?}: {verdict:?}"
        );
    }
}

#[test]
fn the_iteration_limit_is_accepted_and_wrong_brackets_are_rejected() {
    let call = BracketCall {
        options: Options {
            max_iter: 3,
            ..sqrt_two().options
        },
        ..sqrt_two()
    };
    let result = call.bisect();
    let Err(Error::MaxIterations { max_iter, lo, hi }) = result else {
        panic!("{result:?}");
    };
    for check in [Check::BisectSpec, Check::BisectBound] {
        assert_eq!(ask(&call.request(check, &result)), Verdict::Ok);
    }

    // The other half of the previous bracket: no sign change.
    let other_half = Err(Error::MaxIterations {
        max_iter,
        lo: hi,
        hi: hi + (hi - lo),
    });
    for check in [Check::BisectSpec, Check::BisectBound] {
        let verdict = ask(&call.request(check, &other_half));
        assert!(
            matches!(verdict, Verdict::Fail(_)),
            "{check:?}: {verdict:?}"
        );
    }
    // The limit is reported although the tolerance was reached, with room to
    // spare: the bracket is four times shorter than it has to be.
    let finer = BracketCall {
        options: Options {
            tol: Tolerance::new(2.0_f64.powi(-12), 0.0),
            ..sqrt_two().options
        },
        ..sqrt_two()
    };
    let reached = unwrap_root(finer.bisect());
    let too_late = Err(Error::MaxIterations {
        max_iter,
        lo: reached.lo,
        hi: reached.hi,
    });
    for check in [Check::BisectSpec, Check::BisectBound] {
        let verdict = ask(&call.request(check, &too_late));
        assert!(
            matches!(verdict, Verdict::Fail(_)),
            "{check:?}: {verdict:?}"
        );
    }
}

/// When a midpoint is the root itself, rounding decides which half is kept.
/// The comparison with the specification says so instead of guessing.
#[test]
fn a_root_at_a_midpoint_is_skipped_by_the_exact_comparison() {
    let call = call(&[-0.5, 1.0], 0.0, 1.0, 2.0_f64.powi(-10), 0.0, 100);
    let result = call.bisect();
    let verdict = ask(&call.request(Check::BisectSpec, &result));
    assert!(matches!(verdict, Verdict::Skip(_)), "{verdict:?}");
    assert_eq!(ask(&call.request(Check::BisectBound, &result)), Verdict::Ok);
}

// ---- The same, for Brent's method -----------------------------------------

const BRENT_CHECKS: [Check; 2] = [Check::BrentSpec, Check::BrentBound];

/// Requires each of the checks to answer `fail`.
fn assert_rejected(call: &BracketCall, checks: &[Check], wrong: &Result<Root, Error>) {
    for &check in checks {
        let verdict = ask(&call.request(check, wrong));
        assert!(
            matches!(verdict, Verdict::Fail(_)),
            "{check:?} {wrong:?}: {verdict:?}"
        );
    }
}

/// Requires each of the checks to answer `ok`.
fn assert_accepted(call: &BracketCall, checks: &[Check], result: &Result<Root, Error>) {
    for &check in checks {
        let verdict = ask(&call.request(check, result));
        assert_eq!(verdict, Verdict::Ok, "{check:?} {result:?}");
    }
}

#[test]
fn a_brent_root_is_accepted_and_wrong_roots_are_rejected() {
    let call = sqrt_two();
    let root = unwrap_root(call.brent());
    assert!(root.iterations > 1 && root.lo < root.hi);
    assert_accepted(&call, &BRENT_CHECKS, &Ok(root));

    let width = root.hi - root.lo;
    let wrong_for_both = [
        // The bracket next to the right one: no sign change.
        Ok(Root {
            x: root.x + width,
            lo: root.lo + width,
            hi: root.hi + width,
            ..root
        }),
        // The midpoint of the bracket instead of one of its ends.
        Ok(Root {
            x: f64::midpoint(root.lo, root.hi),
            ..root
        }),
        // Stopped early: the bracket is too wide.
        Ok(Root {
            x: 1.0,
            lo: 1.0,
            hi: 1.5,
            ..root
        }),
        // A bracket that leaves the initial one.
        Ok(Root {
            x: 3.0,
            lo: -1.0,
            hi: 3.0,
            ..root
        }),
        // More steps than the limit allows.
        Ok(Root {
            iterations: 101,
            ..root
        }),
        Err(Error::NoSignChange { fa: -2.0, fb: 2.0 }),
        // The limit is reported although the tolerance was reached.
        Err(Error::MaxIterations {
            max_iter: 100,
            lo: root.lo,
            hi: root.hi,
        }),
    ];
    for wrong in wrong_for_both {
        assert_rejected(&call, &BRENT_CHECKS, &wrong);
    }

    // Only the comparison with the specification sees these. As far as the
    // theorems go, they are as good an answer.
    let x_is_lo = root.x == root.lo;
    let wrong_for_spec = [
        // The other end of the bracket.
        Root {
            x: if x_is_lo { root.hi } else { root.lo },
            ..root
        },
        // One step more or less than were taken.
        Root {
            iterations: root.iterations + 1,
            ..root
        },
        Root {
            iterations: root.iterations - 1,
            ..root
        },
        // The neighbouring `f64`, away from the root: an operation rounded
        // the other way.
        if x_is_lo {
            Root {
                x: root.x.next_down(),
                lo: root.lo.next_down(),
                ..root
            }
        } else {
            Root {
                x: root.x.next_up(),
                hi: root.hi.next_up(),
                ..root
            }
        },
        // The other end of the bracket moved by one `f64`.
        if x_is_lo {
            Root {
                hi: root.hi.next_up(),
                ..root
            }
        } else {
            Root {
                lo: root.lo.next_down(),
                ..root
            }
        },
    ];
    for wrong in wrong_for_spec {
        assert_accepted(&call, &[Check::BrentBound], &Ok(wrong));
        assert_rejected(&call, &[Check::BrentSpec], &Ok(wrong));
    }
}

/// What bisection returns for the same call is not what Brent's method
/// returns.
#[test]
fn the_result_of_bisection_is_rejected_for_brent() {
    let call = sqrt_two();
    assert_rejected(&call, &BRENT_CHECKS, &call.bisect());
}

/// When the value at the approximation is zero, the iteration stops however
/// long the bracket is. The oracle accepts that only at a root.
#[test]
fn a_brent_root_with_a_long_bracket_is_accepted_only_at_a_zero() {
    // 2x - 1 on [0, 4]: the first step lands on the root.
    let call = call(&[-1.0, 2.0], 0.0, 4.0, 2.0_f64.powi(-10), 0.0, 100);
    let root = unwrap_root(call.brent());
    assert_eq!((root.x, root.lo, root.hi), (0.5, 0.5, 4.0));
    assert_accepted(&call, &BRENT_CHECKS, &Ok(root));

    let not_a_zero = Ok(Root {
        x: 4.0,
        lo: 0.5,
        hi: 4.0,
        ..root
    });
    assert_rejected(&call, &BRENT_CHECKS, &not_a_zero);
}

#[test]
fn a_missing_sign_change_is_accepted_and_a_brent_root_is_rejected() {
    // x^2 + 1 has no real root.
    let call = call(&[1.0, 0.0, 1.0], -1.0, 2.0, 2.0_f64.powi(-10), 0.0, 100);
    let result = call.brent();
    assert!(matches!(result, Err(Error::NoSignChange { .. })));
    assert_accepted(&call, &BRENT_CHECKS, &result);
    let invented = Ok(Root {
        x: 0.5,
        lo: 0.5,
        hi: 0.5 + 2.0_f64.powi(-10),
        iterations: 5,
    });
    assert_rejected(&call, &BRENT_CHECKS, &invented);
}

#[test]
fn the_brent_iteration_limit_is_accepted_and_wrong_brackets_are_rejected() {
    let call = BracketCall {
        options: Options {
            max_iter: 2,
            ..sqrt_two().options
        },
        ..sqrt_two()
    };
    let result = call.brent();
    let Err(Error::MaxIterations { max_iter, lo, hi }) = result else {
        panic!("{result:?}");
    };
    assert_accepted(&call, &BRENT_CHECKS, &result);

    let wrong_for_both = [
        // A bracket next to the right one: no sign change.
        Err(Error::MaxIterations {
            max_iter,
            lo: hi,
            hi: hi + (hi - lo),
        }),
        // A bracket that leaves the initial one.
        Err(Error::MaxIterations {
            max_iter,
            lo: -1.0,
            hi,
        }),
    ];
    for wrong in wrong_for_both {
        assert_rejected(&call, &BRENT_CHECKS, &wrong);
    }

    // Only the comparison with the specification sees these: the bracket one
    // step earlier, and a root where the limit was hit.
    let earlier = BracketCall {
        options: Options {
            max_iter: max_iter - 1,
            ..call.options
        },
        ..call.clone()
    };
    let wrong_for_spec = [
        earlier.brent(),
        Ok(Root {
            x: lo,
            lo,
            hi,
            iterations: max_iter,
        }),
    ];
    for wrong in wrong_for_spec {
        assert_rejected(&call, &[Check::BrentSpec], &wrong);
    }
}

// ---- The same, for Newton's method ----------------------------------------

const NEWTON_CHECKS: [Check; 2] = [Check::NewtonSpec, Check::NewtonBound];

fn newton_call(coeffs: &[f64], x0: f64, abs: f64, max_iter: usize) -> NewtonCall {
    NewtonCall::with_derivative(
        Poly(coeffs.to_vec()),
        x0,
        Options {
            tol: Tolerance::new(abs, 0.0),
            max_iter,
        },
    )
}

fn assert_newton_verdict(
    call: &NewtonCall,
    checks: &[Check],
    result: &Result<NewtonRoot, Error>,
    expected: fn(&Verdict) -> bool,
) {
    for &check in checks {
        let verdict = ask(&call.request(check, result));
        assert!(expected(&verdict), "{check:?} {result:?}: {verdict:?}");
    }
}

fn is_ok(verdict: &Verdict) -> bool {
    *verdict == Verdict::Ok
}

fn is_fail(verdict: &Verdict) -> bool {
    matches!(verdict, Verdict::Fail(_))
}

#[test]
fn a_newton_root_is_accepted_and_wrong_roots_are_rejected() {
    // x^2 - 2 from 1, to full precision.
    let call = newton_call(&[-2.0, 0.0, 1.0], 1.0, 1e-15, 100);
    let root = call.newton().expect("the call finds a root");
    assert!(root.iterations > 2);
    assert_newton_verdict(&call, &NEWTON_CHECKS, &Ok(root), is_ok);

    let wrong_for_both = [
        // A short step far from the root.
        Ok(NewtonRoot {
            x: 1.5,
            step: 1e-15,
            ..root
        }),
        // A step longer than the tolerance, at a point where f is not zero.
        // (At the root itself the result would be fine: f is zero there.)
        Ok(NewtonRoot {
            x: 1.4,
            step: 1e-3,
            ..root
        }),
        // More steps than the limit allows.
        Ok(NewtonRoot {
            iterations: 101,
            ..root
        }),
        // No step taken, but not at the starting point.
        Ok(NewtonRoot {
            step: 0.0,
            iterations: 0,
            ..root
        }),
        // The derivative is not zero there.
        Err(Error::ZeroDerivative { x: 1.0 }),
    ];
    for wrong in wrong_for_both {
        assert_newton_verdict(&call, &NEWTON_CHECKS, &wrong, is_fail);
    }

    // Only the comparison with the specification sees these.
    let wrong_for_spec = [
        Ok(NewtonRoot {
            x: root.x.next_up(),
            ..root
        }),
        Ok(NewtonRoot {
            step: root.step * 2.0,
            ..root
        }),
        Ok(NewtonRoot {
            iterations: root.iterations - 1,
            ..root
        }),
        Err(Error::NotConverged {
            max_iter: 100,
            x: root.x,
        }),
    ];
    for wrong in wrong_for_spec {
        assert_newton_verdict(&call, &[Check::NewtonBound], &wrong, is_ok);
        assert_newton_verdict(&call, &[Check::NewtonSpec], &wrong, is_fail);
    }
}

#[test]
fn newton_errors_are_accepted_and_wrong_errors_are_rejected() {
    // A zero derivative at the start.
    let call = newton_call(&[-2.0, 0.0, 1.0], 0.0, 1e-15, 100);
    let result = call.newton();
    assert_eq!(result, Err(Error::ZeroDerivative { x: 0.0 }));
    assert_newton_verdict(&call, &NEWTON_CHECKS, &result, is_ok);

    // The cycle between 0 and 1 of x^3 - 2x + 2.
    let call = newton_call(&[2.0, -2.0, 0.0, 1.0], 0.0, 1e-15, 7);
    let result = call.newton();
    assert_eq!(
        result,
        Err(Error::NotConverged {
            max_iter: 7,
            x: 1.0
        })
    );
    assert_newton_verdict(&call, &NEWTON_CHECKS, &result, is_ok);
    let wrong = [
        Err(Error::NotConverged {
            max_iter: 7,
            x: 0.0,
        }),
        Ok(NewtonRoot {
            x: 1.0,
            step: -1.0,
            iterations: 7,
        }),
    ];
    for wrong in wrong {
        assert_newton_verdict(&call, &[Check::NewtonSpec], &wrong, is_fail);
    }
}

/// The guarantee is about the derivative of `f`. A call with another
/// derivative is not decided by the comparison with the theorems.
#[test]
fn a_wrong_derivative_is_skipped_by_the_bound_check() {
    let call = NewtonCall {
        deriv: Poly(vec![0.0, 3.0]),
        ..newton_call(&[-2.0, 0.0, 1.0], 1.0, 1e-15, 100)
    };
    let result = call.newton();
    assert!(result.is_ok(), "{result:?}");
    assert_newton_verdict(&call, &[Check::NewtonSpec], &result, is_ok);
    assert_newton_verdict(&call, &[Check::NewtonBound], &result, |v| {
        matches!(v, Verdict::Skip(_))
    });
}

/// At a double root the derivative vanishes, and the guarantee cannot be
/// established.
#[test]
fn a_double_root_is_skipped_by_the_bound_check() {
    let call = newton_call(&[1.0, -2.0, 1.0], 2.0, 1e-6, 100);
    let result = call.newton();
    assert!(result.is_ok(), "{result:?}");
    assert_newton_verdict(&call, &[Check::NewtonSpec], &result, is_ok);
    assert_newton_verdict(&call, &[Check::NewtonBound], &result, |v| {
        matches!(v, Verdict::Skip(_))
    });
}

// ---- Random calls ---------------------------------------------------------

/// `n / 2^shift` for an integer `n` with `|n| <= limit`.
fn dyadic(limit: i32, shift: i32) -> impl Strategy<Value = f64> {
    (-limit..=limit).prop_map(move |n| f64::from(n) * 2.0_f64.powi(-shift))
}

/// Where the constant term puts the values at the ends of the bracket.
///
/// A polynomial drawn at random changes sign over a bracket drawn at random
/// about one time in three, and the other calls end at once with
/// `NoSignChange`. Most calls are therefore given a constant term that makes
/// the two values `(1 - t) * d` and `-t * d` for some `d`, which have
/// opposite signs. `None` keeps the constant term as drawn.
fn sign_change() -> impl Strategy<Value = Option<f64>> {
    prop::option::weighted(0.8, 0.05..0.95)
}

/// Builds the call. `grid` is the spacing the constant term is rounded to
/// when it is replaced; zero for none.
fn build(
    mut coeffs: Vec<f64>,
    a: f64,
    b: f64,
    t: Option<f64>,
    grid: f64,
    options: Options,
) -> BracketCall {
    let (a, b) = (a.min(b), a.max(b));
    if let Some(t) = t {
        coeffs[0] = 0.0;
        let poly = Poly(coeffs.clone());
        let constant = -(t * poly.eval(a) + (1.0 - t) * poly.eval(b));
        coeffs[0] = if grid > 0.0 {
            (constant / grid).round() * grid
        } else {
            constant
        };
    }
    BracketCall {
        poly: Poly(coeffs),
        a,
        b,
        options,
    }
}

/// Calls in which `f64` arithmetic is exact: the ends of the bracket are
/// multiples of `2^-7` in `[-64, 64]`, and the tolerance is absolute and at
/// least `2^-30`. A bracket then needs at most 38 steps, and every midpoint
/// on the way has at most 51 significant bits. The coefficients are multiples
/// of `2^-3`.
fn exact_call() -> impl Strategy<Value = BracketCall> {
    (
        prop::collection::vec(dyadic(64, 3), 2..=6),
        dyadic(1 << 13, 7),
        dyadic(1 << 13, 7),
        sign_change(),
        (1..=16_i32, 0..=26_i32).prop_map(|(m, e)| f64::from(m) * 2.0_f64.powi(-e)),
        0..=45_usize,
    )
        .prop_map(|(coeffs, a, b, t, abs, max_iter)| {
            let options = Options {
                tol: Tolerance::new(abs, 0.0),
                max_iter,
            };
            build(coeffs, a, b, t, 0.125, options)
        })
}

/// A finite number at one of several scales, or zero.
fn scaled() -> impl Strategy<Value = f64> {
    prop_oneof![Just(0.0), -1e6..1e6, -1.0..1.0, -1e-6..1e-6, dyadic(64, 3),]
}

/// Calls with any finite arguments that cannot overflow: polynomials of
/// degree at most 6 with coefficients and brackets up to `1e6`, any
/// tolerance (including zero, and the default) and any iteration limit.
fn any_call() -> impl Strategy<Value = BracketCall> {
    let default = Options::default();
    (
        prop::collection::vec(scaled(), 2..=7),
        scaled(),
        scaled(),
        sign_change(),
        prop_oneof![Just(0.0), Just(default.tol.abs), 1e-15..1e-3],
        prop_oneof![Just(0.0), Just(default.tol.rel), 1e-16..1e-6],
        prop_oneof![Just(default.max_iter), 0..=200_usize],
    )
        .prop_map(|(coeffs, a, b, t, abs, rel, max_iter)| {
            let options = Options {
                tol: Tolerance::new(abs, rel),
                max_iter,
            };
            build(coeffs, a, b, t, 0.0, options)
        })
}

/// A number with at most 44 significant bits, so that multiplying it by an
/// integer up to 7 is exact.
fn short(x: f64) -> f64 {
    f64::from_bits(x.to_bits() & !0x1ff)
}

/// Calls of [`thole_roots::newton`] with any finite arguments that cannot
/// overflow, and the exact derivative. Most polynomials are given a constant
/// term that puts a root near the starting point.
fn newton_any_call() -> impl Strategy<Value = NewtonCall> {
    let default = Options::default();
    (
        prop::collection::vec(scaled(), 2..=7),
        scaled(),
        prop::option::weighted(0.8, -1.0..1.0),
        prop_oneof![Just(0.0), Just(default.tol.abs), 1e-15..1e-3],
        prop_oneof![Just(0.0), Just(default.tol.rel), 1e-16..1e-6],
        prop_oneof![Just(default.max_iter), 0..=60_usize],
    )
        .prop_map(|(coeffs, x0, offset, abs, rel, max_iter)| {
            let mut coeffs: Vec<f64> = coeffs.into_iter().map(short).collect();
            if let Some(offset) = offset {
                coeffs[0] = 0.0;
                let constant = -Poly(coeffs.clone()).eval(x0 + offset);
                coeffs[0] = short(constant);
            }
            let options = Options {
                tol: Tolerance::new(abs, rel),
                max_iter,
            };
            NewtonCall::with_derivative(Poly(coeffs), short(x0), options)
        })
}

proptest! {
    #![proptest_config(config(2000))]

    /// For any finite arguments, `newton` returns exactly what the Lean
    /// definitions compute in the model of `f64` arithmetic: the same
    /// outcome, after the same number of steps, with the same approximation
    /// and the same last step.
    #[test]
    fn newton_agrees_with_the_specification(call in newton_any_call()) {
        let result = call.newton();
        let verdict = ask(&call.request(Check::NewtonSpec, &result));
        prop_assert_eq!(verdict, Verdict::Ok, "{:?}", result);
    }

    /// For any finite arguments, the result of `newton` has the properties
    /// that the Lean theorems give, up to rounding, wherever the oracle can
    /// establish their hypotheses.
    #[test]
    fn newton_result_has_the_proved_properties(call in newton_any_call()) {
        let result = call.newton();
        match ask(&call.request(Check::NewtonBound, &result)) {
            Verdict::Ok => {}
            Verdict::Skip(reason) => return Err(TestCaseError::reject(reason)),
            Verdict::Fail(reason) => prop_assert!(false, "{reason}: {result:?}"),
        }
    }

    /// Where `f64` arithmetic is exact, `bisect` returns exactly what the
    /// Lean definitions compute: the same outcome, after the same number of
    /// steps, with the same bracket.
    #[test]
    fn bisect_agrees_with_the_specification(call in exact_call()) {
        let result = call.bisect();
        match ask(&call.request(Check::BisectSpec, &result)) {
            Verdict::Ok => {}
            Verdict::Skip(reason) => return Err(TestCaseError::reject(reason)),
            Verdict::Fail(reason) => prop_assert!(false, "{reason}: {result:?}"),
        }
    }

    /// For any finite arguments, the result of `bisect` has the properties
    /// that the Lean theorems give, up to rounding.
    #[test]
    fn bisect_result_has_the_proved_properties(call in any_call()) {
        let result = call.bisect();
        let verdict = ask(&call.request(Check::BisectBound, &result));
        prop_assert_eq!(verdict, Verdict::Ok, "{:?}", result);
    }

    /// For any finite arguments, `brent` returns exactly what the Lean
    /// definitions compute in the model of `f64` arithmetic: the same
    /// outcome, after the same number of steps, with the same approximation
    /// and the same bracket.
    #[test]
    fn brent_agrees_with_the_specification(call in any_call()) {
        let result = call.brent();
        let verdict = ask(&call.request(Check::BrentSpec, &result));
        prop_assert_eq!(verdict, Verdict::Ok, "{:?}", result);
    }

    /// For any finite arguments, the result of `brent` has the properties
    /// that the Lean theorems give, up to rounding.
    #[test]
    fn brent_result_has_the_proved_properties(call in any_call()) {
        let result = call.brent();
        let verdict = ask(&call.request(Check::BrentBound, &result));
        prop_assert_eq!(verdict, Verdict::Ok, "{:?}", result);
    }
}
