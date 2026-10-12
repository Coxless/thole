//! Requests about `thole-roots`.
//!
//! Lean counterpart: `oracle/lean/Thole/Oracle/Roots.lean`.

use std::fmt::Write;

use thole_roots::{Error, Options, Root, bisect, brent};

use crate::{Poly, bits};

/// The checks the oracle has.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Check {
    /// The result of [`bisect`] is exactly what the Lean definitions compute
    /// over the rational numbers (`checkBisectSpec`). The oracle skips the
    /// calls in which rounding could change a decision.
    BisectSpec,
    /// The result of [`bisect`] has the properties the Lean theorems give, up
    /// to rounding (`checkBisectBound`). Decided for every call with finite
    /// arguments.
    BisectBound,
    /// The result of [`brent`] has the properties the Lean theorems give, up
    /// to rounding (`checkBrentBound`). Decided for every call with finite
    /// arguments.
    BrentBound,
}

/// A call of a bracketing method on a polynomial.
#[derive(Debug, Clone, PartialEq)]
pub struct BracketCall {
    /// The function whose root is sought.
    pub poly: Poly,
    /// Lower end of the bracket.
    pub a: f64,
    /// Upper end of the bracket.
    pub b: f64,
    /// Tolerance and iteration limit.
    pub options: Options,
}

impl BracketCall {
    /// Makes the call with [`bisect`].
    pub fn bisect(&self) -> Result<Root, Error> {
        bisect(|x| self.poly.eval(x), self.a, self.b, &self.options)
    }

    /// Makes the call with [`brent`].
    pub fn brent(&self) -> Result<Root, Error> {
        brent(|x| self.poly.eval(x), self.a, self.b, &self.options)
    }

    /// The request that asks the oracle whether `result` is right for this
    /// call.
    ///
    /// # Panics
    ///
    /// If `result` is an error about the arguments or about a NaN. The
    /// specification is about real numbers and has no counterpart for those;
    /// the tests of `thole-roots` cover them.
    pub fn request(&self, check: Check, result: &Result<Root, Error>) -> String {
        let name = match check {
            Check::BisectSpec => "roots.bisect.spec",
            Check::BisectBound => "roots.bisect.bound",
            Check::BrentBound => "roots.brent.bound",
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
