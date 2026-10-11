//! Python bindings for thole.
//!
//! This crate is a thin conversion layer: it holds no numerical logic. Every
//! public item of the `thole-*` crates gets a counterpart here (CONCEPT.md
//! section 3.4), in one module per area.

use pyo3::prelude::*;

mod roots;

#[pymodule]
fn _thole(m: &Bound<'_, PyModule>) -> PyResult<()> {
    m.add("__version__", env!("CARGO_PKG_VERSION"))?;
    roots::register(m)?;
    Ok(())
}
