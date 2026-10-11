//! Root finding: solving `f(x) = 0` for a function of one variable.
//!
//! | Function | Method | Needs |
//! |---|---|---|
//! | [`bisect`] | Bisection | a bracket with a sign change |

mod bisection;
mod error;
mod options;

pub use bisection::{Root, bisect};
pub use error::Error;
pub use options::Options;
