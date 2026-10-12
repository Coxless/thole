//! Root finding: solving `f(x) = 0` for a function of one variable.
//!
//! | Function | Method | Needs |
//! |---|---|---|
//! | [`bisect`] | Bisection | a bracket with a sign change |
//! | [`brent`] | Brent's method | a bracket with a sign change |
//! | [`newton`] | Newton's method | a starting point and the derivative |

mod bisection;
mod bracket;
mod brent;
mod error;
mod newton;
mod options;

pub use bisection::bisect;
pub use bracket::Root;
pub use brent::brent;
pub use error::Error;
pub use newton::{NewtonRoot, newton};
pub use options::Options;
