//! Requests about `thole-quad`.
//!
//! Lean counterpart: `oracle/lean/Thole/Oracle/Quad.lean`.

use std::fmt::Write;

use thole_quad::{Error, GaussLegendre, Integral, Options, gauss_kronrod, gauss_kronrod_rule};

use crate::{Poly, bits};

/// The checks of [`GaussLegendre`] itself.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RuleCheck {
    /// The nodes and weights are exactly those that the Lean program
    /// computes in a model of `f64` arithmetic (`checkGaussRuleSpec`).
    Spec,
    /// The nodes are within `2^-50` of the roots of the Legendre polynomial,
    /// and the weights within a relative `2^-40` of the Gauss weights
    /// (`checkGaussRuleBound`).
    Bound,
}

/// The checks of an integral.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Check {
    /// The result is exactly what the Lean program computes in a model of
    /// `f64` arithmetic (`checkGaussSpec`, `checkKronrodSpec`).
    Spec,
    /// The result has the properties that the Lean definitions and theorems
    /// give, up to rounding (`checkGaussBound`, `checkKronrodBound`).
    Bound,
}

/// The request that asks the oracle about the rule with `n` points.
pub fn rule_request(check: RuleCheck, rule: &GaussLegendre) -> String {
    let name = match check {
        RuleCheck::Spec => "quad.gauss.rule.spec",
        RuleCheck::Bound => "quad.gauss.rule.bound",
    };
    let mut line = format!("{name} {}", rule.order());
    for &x in rule.nodes().iter().chain(rule.weights()) {
        write!(line, " {}", bits(x)).unwrap();
    }
    line
}

/// The request that asks the oracle whether the constants of
/// [`gauss_kronrod_rule`] are QUADPACK's, and exact up to their rounding.
pub fn kronrod_rule_request() -> String {
    let (nodes, kronrod, gauss) = gauss_kronrod_rule();
    let mut line = "quad.kronrod.rule".to_owned();
    for &x in nodes.iter().chain(&kronrod).chain(&gauss) {
        write!(line, " {}", bits(x)).unwrap();
    }
    line
}

/// Writes the coefficients of a polynomial: their number, then each one.
fn write_poly(line: &mut String, poly: &Poly) {
    write!(line, " {}", poly.0.len()).unwrap();
    for &c in &poly.0 {
        write!(line, " {}", bits(c)).unwrap();
    }
}

/// A call of [`GaussLegendre::integrate`] on a polynomial.
#[derive(Debug, Clone, PartialEq)]
pub struct GaussCall {
    /// The function integrated.
    pub poly: Poly,
    /// The number of points of the rule.
    pub n: usize,
    /// Lower end of the interval.
    pub a: f64,
    /// Upper end of the interval.
    pub b: f64,
}

impl GaussCall {
    /// Makes the call.
    ///
    /// # Panics
    ///
    /// If `n` is zero.
    pub fn integrate(&self) -> Result<f64, Error> {
        GaussLegendre::new(self.n)
            .expect("the rule has at least one point")
            .integrate(|x| self.poly.eval(x), self.a, self.b)
    }

    /// The request that asks the oracle whether `result` is right for this
    /// call.
    ///
    /// # Panics
    ///
    /// If `result` is an error about the arguments.
    pub fn request(&self, check: Check, result: &Result<f64, Error>) -> String {
        let name = match check {
            Check::Spec => "quad.gauss.spec",
            Check::Bound => "quad.gauss.bound",
        };
        let mut line = format!("{name} {} {} {}", self.n, bits(self.a), bits(self.b));
        write_poly(&mut line, &self.poly);
        match *result {
            Ok(value) => write!(line, " value {}", bits(value)),
            Err(Error::NonFiniteValue { x, .. }) => write!(line, " non-finite {}", bits(x)),
            Err(err) => panic!("the oracle has no counterpart for this error: {err}"),
        }
        .unwrap();
        line
    }
}

/// A call of [`gauss_kronrod`] on a polynomial.
#[derive(Debug, Clone, PartialEq)]
pub struct KronrodCall {
    /// The function integrated.
    pub poly: Poly,
    /// Lower end of the interval.
    pub a: f64,
    /// Upper end of the interval.
    pub b: f64,
    /// Tolerance and limit.
    pub options: Options,
}

impl KronrodCall {
    /// Makes the call.
    pub fn integrate(&self) -> Result<Integral, Error> {
        gauss_kronrod(|x| self.poly.eval(x), self.a, self.b, &self.options)
    }

    /// The request that asks the oracle whether `result` is right for this
    /// call.
    ///
    /// # Panics
    ///
    /// If `result` is an error about the arguments.
    pub fn request(&self, check: Check, result: &Result<Integral, Error>) -> String {
        let name = match check {
            Check::Spec => "quad.kronrod.spec",
            Check::Bound => "quad.kronrod.bound",
        };
        let tol = self.options.tol;
        let mut line = format!(
            "{name} {} {} {} {} {}",
            bits(self.a),
            bits(self.b),
            bits(tol.abs),
            bits(tol.rel),
            self.options.max_subintervals
        );
        write_poly(&mut line, &self.poly);
        match *result {
            Ok(Integral {
                value,
                error,
                subintervals,
                evaluations,
            }) => write!(
                line,
                " integral {} {} {subintervals} {evaluations}",
                bits(value),
                bits(error)
            ),
            Err(Error::MaxSubintervals { value, error, .. }) => {
                write!(line, " max-subintervals {} {}", bits(value), bits(error))
            }
            Err(Error::NonFiniteValue { x, .. }) => write!(line, " non-finite {}", bits(x)),
            Err(err) => panic!("the oracle has no counterpart for this error: {err}"),
        }
        .unwrap();
        line
    }
}
