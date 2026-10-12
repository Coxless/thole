/// A polynomial with `f64` coefficients, lowest degree first.
///
/// A closure cannot be sent to the oracle, so the two sides agree on this
/// family of functions instead. Every finite `f64` is a rational number, so
/// the oracle evaluates the same polynomial exactly.
///
/// Lean counterpart: `horner` in `oracle/lean/Thole/Oracle/Poly.lean`.
#[derive(Debug, Clone, PartialEq)]
pub struct Poly(pub Vec<f64>);

impl Poly {
    /// The value at `x`, by Horner's rule.
    ///
    /// The oracle bounds the rounding error of exactly this sequence of
    /// operations (`hornerError`), so it must not be rearranged.
    pub fn eval(&self, x: f64) -> f64 {
        self.0.iter().rev().fold(0.0, |acc, &c| acc * x + c)
    }
}

#[cfg(test)]
mod tests {
    use super::Poly;

    #[test]
    fn eval_is_horner_from_the_highest_degree() {
        let p = Poly(vec![-2.0, 0.0, 1.0]);
        assert_eq!(p.eval(3.0), 7.0);
        assert_eq!(Poly(vec![]).eval(3.0), 0.0);
    }
}
