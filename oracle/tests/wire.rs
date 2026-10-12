//! Both sides must read the same number from the same request, and the model
//! of `f64` arithmetic that the oracle computes with must be `f64` arithmetic.

use std::sync::{LazyLock, Mutex};

use proptest::prelude::*;
use proptest::test_runner::FileFailurePersistence;
use thole_oracle::{Oracle, bits};

/// `2^k` in decimal.
fn pow2(k: u32) -> String {
    // Digits, least significant first.
    let mut digits = vec![1u8];
    for _ in 0..k {
        let mut carry = 0;
        for d in &mut digits {
            let doubled = *d * 2 + carry;
            *d = doubled % 10;
            carry = doubled / 10;
        }
        if carry > 0 {
            digits.push(carry);
        }
    }
    digits.iter().rev().map(|d| char::from(b'0' + d)).collect()
}

#[test]
fn the_oracle_reads_f64_values_exactly() {
    let cases = [
        (0.0, "0/1".to_owned()),
        (-0.0, "0/1".to_owned()),
        (-2.0, "-2/1".to_owned()),
        (0.1, "3602879701896397/36028797018963968".to_owned()),
        (
            1.0 + f64::EPSILON,
            "4503599627370497/4503599627370496".to_owned(),
        ),
        (2.0_f64.powi(1023), format!("{}/1", pow2(1023))),
        (f64::MIN_POSITIVE, format!("1/{}", pow2(1022))),
        // Subnormal numbers: the largest and the smallest.
        (
            f64::from_bits(0x000f_ffff_ffff_ffff),
            format!("4503599627370495/{}", pow2(1074)),
        ),
        (-f64::from_bits(1), format!("-1/{}", pow2(1074))),
    ];
    let mut oracle = Oracle::start();
    for (x, expected) in cases {
        assert_eq!(
            oracle.ask_raw(&format!("f64 {}", bits(x))),
            expected,
            "{x:e}"
        );
    }
}

#[test]
fn the_oracle_refuses_what_it_cannot_read() {
    let mut oracle = Oracle::start();
    for request in [
        format!("f64 {}", bits(f64::INFINITY)),
        format!("f64 {}", bits(f64::NAN)),
        "f64 12".to_owned(),
        "no.such.request".to_owned(),
        "roots.bisect.spec".to_owned(),
        "roots.brent.spec".to_owned(),
        "roots.brent.bound".to_owned(),
        format!("f64.add {} {}", bits(1.0), bits(f64::NAN)),
    ] {
        let answer = oracle.ask_raw(&request);
        assert!(answer.starts_with("error "), "{request}: {answer}");
    }
}

// ---- The model of `f64` arithmetic ----------------------------------------
//
// Lean counterpart: `F64` in `oracle/lean/Thole/Oracle/Arith.lean`.

/// What the oracle answers for an operation whose result in Rust is `x`.
fn answer_for(oracle: &mut Oracle, x: f64) -> String {
    if x.is_nan() {
        "nan".to_owned()
    } else if x.is_infinite() {
        if x > 0.0 { "inf" } else { "-inf" }.to_owned()
    } else {
        oracle.ask_raw(&format!("f64 {}", bits(x)))
    }
}

/// Requires each operation of the model to give what Rust gives for `x` and
/// `y`.
fn check_operations(x: f64, y: f64) -> Result<(), TestCaseError> {
    static SHARED: LazyLock<Mutex<Oracle>> = LazyLock::new(|| Mutex::new(Oracle::start()));
    let mut oracle = SHARED.lock().expect("an earlier request failed");
    let results = [
        ("add", x + y),
        ("sub", x - y),
        ("mul", x * y),
        ("div", x / y),
    ];
    for (name, result) in results {
        // Not modelled: a non-zero number divided by zero.
        if name == "div" && y == 0.0 && x != 0.0 {
            continue;
        }
        let model = oracle.ask_raw(&format!("f64.{name} {} {}", bits(x), bits(y)));
        let expected = answer_for(&mut oracle, result);
        prop_assert_eq!(model, expected, "{:e} {} {:e}", x, name, y);
    }
    Ok(())
}

/// Any finite `f64`, including the subnormal ones.
fn finite() -> impl Strategy<Value = f64> {
    any::<u64>()
        .prop_map(f64::from_bits)
        .prop_filter("finite", |x| x.is_finite())
}

/// A finite `f64` of ordinary size, with any significand.
fn ordinary() -> impl Strategy<Value = f64> {
    (any::<u64>(), -60..=60_i32).prop_map(|(significand, exponent)| {
        let x = f64::from_bits(significand & 0x800f_ffff_ffff_ffff | 0x3ff0_0000_0000_0000);
        x * 2.0_f64.powi(exponent)
    })
}

/// Values at which rounding has something to decide.
fn special() -> impl Strategy<Value = f64> {
    prop::sample::select(vec![
        0.0,
        1.0,
        -1.0,
        3.0,
        0.1,
        1.0 + f64::EPSILON,
        1.0 - f64::EPSILON / 2.0,
        f64::EPSILON / 2.0,
        2.0_f64.powi(53),
        2.0_f64.powi(53) + 2.0,
        f64::MAX,
        -f64::MAX,
        f64::MIN_POSITIVE,
        f64::MIN_POSITIVE * 1.5,
        f64::from_bits(1),
        f64::from_bits(3),
        -f64::from_bits(0x000f_ffff_ffff_ffff),
    ])
}

fn operand() -> impl Strategy<Value = f64> {
    prop_oneof![ordinary(), ordinary(), finite(), special()]
}

#[test]
fn the_model_rounds_ties_to_even_and_overflows_to_infinity() {
    let half_ulp = f64::EPSILON / 2.0;
    let cases = [
        // Half way between two values: the even one is taken.
        (1.0, half_ulp),
        (1.0 + f64::EPSILON, half_ulp),
        (2.0_f64.powi(53), 1.0),
        (2.0_f64.powi(53) + 2.0, 1.0),
        // Subnormal results.
        (f64::from_bits(3), 0.5),
        (f64::from_bits(1), 0.5),
        (f64::MIN_POSITIVE, 0.75),
        // Overflow, and the largest value that does not.
        (f64::MAX, f64::MAX),
        (f64::MAX, 2.0_f64.powi(970)),
        (f64::MAX, 2.0_f64.powi(969)),
        (-f64::MAX, 2.0),
        (0.0, 0.0),
    ];
    for (x, y) in cases {
        check_operations(x, y).unwrap();
        check_operations(y, x).unwrap();
        check_operations(-x, y).unwrap();
    }
}

proptest! {
    #![proptest_config(ProptestConfig {
        cases: 2000,
        failure_persistence: Some(Box::new(FileFailurePersistence::WithSource(
            "proptest-regressions",
        ))),
        ..ProptestConfig::default()
    })]

    /// Addition, subtraction, multiplication and division of the model give
    /// the result of Rust, bit for bit, on any finite operands.
    #[test]
    fn the_model_is_f64_arithmetic(x in operand(), y in operand()) {
        check_operations(x, y)?;
    }
}
