//! Requests about `thole-roots`.
//!
//! Lean counterpart: `oracle/lean/Thole/Oracle/Roots.lean`.

use std::fmt::Write;

use thole_roots::{Error, Options, Root, bisect};

use crate::{Poly, bits};

/// The checks the oracle has for a call of [`bisect`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BisectCheck {
    /// The result is exactly what the Lean definitions compute over the
    /// rational numbers (`checkBisectSpec`). The oracle skips the calls in
    /// which rounding could change a decision.
    Spec,
    /// The result has the properties the Lean theorems give, up to rounding
    /// (`checkBisectBound`). Decided for every call with finite arguments.
    Bound,
}

/// A call of [`bisect`] on a polynomial.
#[derive(Debug, Clone, PartialEq)]
pub struct BisectCall {
    /// The function whose root is sought.
    pub poly: Poly,
    /// Lower end of the bracket.
    pub a: f64,
    /// Upper end of the bracket.
    pub b: f64,
    /// Tolerance and iteration limit.
    pub options: Options,
}

impl BisectCall {
    /// Makes the call.
    pub fn run(&self) -> Result<Root, Error> {
        bisect(|x| self.poly.eval(x), self.a, self.b, &self.options)
    }

    /// The request that asks the oracle whether `result` is right for this
    /// call.
    ///
    /// # Panics
    ///
    /// If `result` is an error about the arguments or about a NaN. The
    /// specification is about real numbers and has no counterpart for those;
    /// the tests of `thole-roots` cover them.
    pub fn request(&self, check: BisectCheck, result: &Result<Root, Error>) -> String {
        let name = match check {
            BisectCheck::Spec => "roots.bisect.spec",
            BisectCheck::Bound => "roots.bisect.bound",
        };
        let tol = self.options.tol;
        let mut line = format!(
            "{name} {} {} {} {} {} {}",
            bits(self.a),
            bits(self.b),
            bits(tol.abs),
            bits(tol.rel),
            self.options.max_iter,
            self.poly.0.len()
        );
        for &c in &self.poly.0 {
            write!(line, " {}", bits(c)).unwrap();
        }
        match *result {
            Ok(Root {
                x,
                lo,
                hi,
                iterations,
            }) => write!(
                line,
                " root {} {} {} {iterations}",
                bits(x),
                bits(lo),
                bits(hi)
            ),
            Err(Error::NoSignChange { .. }) => write!(line, " no-sign-change"),
            Err(Error::MaxIterations { lo, hi, .. }) => {
                write!(line, " max-iterations {} {}", bits(lo), bits(hi))
            }
            Err(err) => panic!("the oracle has no counterpart for this error: {err}"),
        }
        .unwrap();
        line
    }
}
