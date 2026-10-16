//! Requests about `thole-roots`.
//!
//! Lean counterpart: `oracle/lean/Thole/Oracle/Roots.lean`.

use std::fmt::Write;

use thole_roots::{Error, NewtonRoot, Options, Root, bisect, brent, newton};

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
    /// The result of [`brent`] is exactly what the Lean definitions compute
    /// in a model of `f64` arithmetic (`checkBrentSpec`). Decided for every
    /// call with finite arguments.
    BrentSpec,
    /// The result of [`brent`] has the properties the Lean theorems give, up
    /// to rounding (`checkBrentBound`). Decided for every call with finite
    /// arguments.
    BrentBound,
    /// The result of [`newton`] is exactly what the Lean definitions compute
    /// in a model of `f64` arithmetic (`checkNewtonSpec`). Decided for every
    /// call with finite arguments.
    NewtonSpec,
    /// The result of [`newton`] has the properties the Lean theorems give, up
    /// to rounding (`checkNewtonBound`). The oracle skips the calls in which
    /// it cannot establish the hypotheses of the theorems.
    NewtonBound,
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
            Check::BrentSpec => "roots.brent.spec",
            Check::BrentBound => "roots.brent.bound",
            _ => panic!("{check:?} is not a check of a bracketing method"),
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

/// A call of [`newton`] on a polynomial, with a second polynomial for the
/// derivative.
#[derive(Debug, Clone, PartialEq)]
pub struct NewtonCall {
    /// The function whose root is sought.
    pub poly: Poly,
    /// The derivative that is passed. For [`Check::NewtonBound`] it must be
    /// exactly the derivative of `poly`, or the oracle skips the call.
    pub deriv: Poly,
    /// The starting point.
    pub x0: f64,
    /// Tolerance and iteration limit.
    pub options: Options,
}

impl NewtonCall {
    /// A call with the derivative of `poly` as `deriv`.
    ///
    /// # Panics
    ///
    /// If a coefficient of the derivative cannot be computed exactly in
    /// `f64`.
    pub fn with_derivative(poly: Poly, x0: f64, options: Options) -> Self {
        let deriv = Poly(
            poly.0
                .iter()
                .enumerate()
                .skip(1)
                .map(|(k, &c)| {
                    let d = k as f64 * c;
                    assert_eq!(d / k as f64, c, "the derivative of {poly:?} is not exact");
                    d
                })
                .collect(),
        );
        Self {
            poly,
            deriv,
            x0,
            options,
        }
    }

    /// Makes the call.
    pub fn newton(&self) -> Result<NewtonRoot, Error> {
        newton(
            |x| self.poly.eval(x),
            |x| self.deriv.eval(x),
            self.x0,
            &self.options,
        )
    }

    /// The request that asks the oracle whether `result` is right for this
    /// call.
    ///
    /// # Panics
    ///
    /// If `check` is not a check of [`newton`], or `result` is an error about
    /// the arguments.
    pub fn request(&self, check: Check, result: &Result<NewtonRoot, Error>) -> String {
        let name = match check {
            Check::NewtonSpec => "roots.newton.spec",
            Check::NewtonBound => "roots.newton.bound",
            _ => panic!("{check:?} is not a check of Newton's method"),
        };
        let tol = self.options.tol;
        let mut line = format!(
            "{name} {} {} {} {}",
            bits(self.x0),
            bits(tol.abs),
            bits(tol.rel),
            self.options.max_iter,
        );
        for poly in [&self.poly, &self.deriv] {
            write!(line, " {}", poly.0.len()).unwrap();
            for &c in &poly.0 {
                write!(line, " {}", bits(c)).unwrap();
            }
        }
        match *result {
            Ok(NewtonRoot {
                x,
                step,
                iterations,
            }) => write!(line, " root {} {} {iterations}", bits(x), bits(step)),
            Err(Error::NotConverged { x, .. }) => write!(line, " not-converged {}", bits(x)),
            Err(Error::ZeroDerivative { x }) => write!(line, " zero-derivative {}", bits(x)),
            Err(Error::NonFiniteStep { x }) => write!(line, " non-finite-step {}", bits(x)),
            Err(Error::NanValue { x }) => write!(line, " nan-value {}", bits(x)),
            Err(Error::NanDerivative { x }) => write!(line, " nan-derivative {}", bits(x)),
            Err(err) => panic!("the oracle has no counterpart for this error: {err}"),
        }
        .unwrap();
        line
    }
}
