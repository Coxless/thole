//! `thole_roots` against the Lean oracle.
//!
//! Lean counterpart: `oracle/lean/Thole/Oracle/Roots.lean`.

use proptest::prelude::*;
use proptest::test_runner::FileFailurePersistence;
use thole_core::Tolerance;
use thole_oracle::roots::{BracketCall, Check};
use thole_oracle::{Poly, Verdict, ask};
use thole_roots::{Error, Options, Root};

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

#[test]
fn a_brent_root_is_accepted_and_wrong_roots_are_rejected() {
    let call = sqrt_two();
    let root = unwrap_root(call.brent());
    assert!(root.iterations > 1 && root.lo < root.hi);
    assert_eq!(
        ask(&call.request(Check::BrentBound, &Ok(root))),
        Verdict::Ok
    );

    let width = root.hi - root.lo;
    let other_end = if root.x == root.lo { root.hi } else { root.lo };
    let wrong = [
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
    for wrong in wrong {
        let verdict = ask(&call.request(Check::BrentBound, &wrong));
        assert!(
            matches!(verdict, Verdict::Fail(_)),
            "{wrong:?}: {verdict:?}"
        );
    }

    // The other end of the bracket is as good an answer, as far as the
    // theorems go: they do not say which end is the approximation.
    let swapped = Ok(Root {
        x: other_end,
        ..root
    });
    assert_eq!(ask(&call.request(Check::BrentBound, &swapped)), Verdict::Ok);
}

/// When the value at the approximation is zero, the iteration stops however
/// long the bracket is. The oracle accepts that only at a root.
#[test]
fn a_brent_root_with_a_long_bracket_is_accepted_only_at_a_zero() {
    // 2x - 1 on [0, 4]: the first step lands on the root.
    let call = call(&[-1.0, 2.0], 0.0, 4.0, 2.0_f64.powi(-10), 0.0, 100);
    let root = unwrap_root(call.brent());
    assert_eq!((root.x, root.lo, root.hi), (0.5, 0.5, 4.0));
    assert_eq!(
        ask(&call.request(Check::BrentBound, &Ok(root))),
        Verdict::Ok
    );

    let not_a_zero = Ok(Root {
        x: 4.0,
        lo: 0.5,
        hi: 4.0,
        ..root
    });
    let verdict = ask(&call.request(Check::BrentBound, &not_a_zero));
    assert!(matches!(verdict, Verdict::Fail(_)), "{verdict:?}");
}

#[test]
fn a_missing_sign_change_is_accepted_and_a_brent_root_is_rejected() {
    // x^2 + 1 has no real root.
    let call = call(&[1.0, 0.0, 1.0], -1.0, 2.0, 2.0_f64.powi(-10), 0.0, 100);
    let result = call.brent();
    assert!(matches!(result, Err(Error::NoSignChange { .. })));
    assert_eq!(ask(&call.request(Check::BrentBound, &result)), Verdict::Ok);
    let invented = Ok(Root {
        x: 0.5,
        lo: 0.5,
        hi: 0.5 + 2.0_f64.powi(-10),
        iterations: 5,
    });
    let verdict = ask(&call.request(Check::BrentBound, &invented));
    assert!(matches!(verdict, Verdict::Fail(_)), "{verdict:?}");
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
    assert_eq!(ask(&call.request(Check::BrentBound, &result)), Verdict::Ok);

    let wrong = [
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
    for wrong in wrong {
        let verdict = ask(&call.request(Check::BrentBound, &wrong));
        assert!(
            matches!(verdict, Verdict::Fail(_)),
            "{wrong:?}: {verdict:?}"
        );
    }
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

proptest! {
    #![proptest_config(config(2000))]

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

    /// For any finite arguments, the result of `brent` has the properties
    /// that the Lean theorems give, up to rounding.
    #[test]
    fn brent_result_has_the_proved_properties(call in any_call()) {
        let result = call.brent();
        let verdict = ask(&call.request(Check::BrentBound, &result));
        prop_assert_eq!(verdict, Verdict::Ok, "{:?}", result);
    }
}
