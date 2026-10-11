//! Pure Rust, no C/Fortran: scientific computing with every algorithm
//! implemented from scratch.
//!
//! This crate re-exports the individual `thole-*` crates. Each area is behind
//! a feature flag of the same name; all of them are enabled by default.

pub use thole_core as core;
#[cfg(feature = "linalg")]
pub use thole_linalg as linalg;
#[cfg(feature = "ode")]
pub use thole_ode as ode;
#[cfg(feature = "quad")]
pub use thole_quad as quad;
#[cfg(feature = "roots")]
pub use thole_roots as roots;
