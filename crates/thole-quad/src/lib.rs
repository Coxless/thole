//! Numerical integration (quadrature): approximating `∫_a^b f(x) dx` for a
//! function of one variable on a finite interval.
//!
//! | Function | Method | Error estimate |
//! |---|---|---|
//! | [`gauss_legendre`], [`GaussLegendre`] | Gauss-Legendre rule with `n` points | none; exact for degree `2n - 1` |
//! | [`gauss_kronrod`] | adaptive Gauss-Kronrod (7 and 15 points) | yes |

mod error;
mod gauss_kronrod;
mod gauss_legendre;
mod options;

pub use error::Error;
pub use gauss_kronrod::{Integral, gauss_kronrod, gauss_kronrod_rule};
pub use gauss_legendre::{GaussLegendre, gauss_legendre};
pub use options::Options;
