//! Both sides must read the same number from the same request.

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
        "roots.brent.bound".to_owned(),
    ] {
        let answer = oracle.ask_raw(&request);
        assert!(answer.starts_with("error "), "{request}: {answer}");
    }
}
