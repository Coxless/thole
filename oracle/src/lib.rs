//! Tests of the thole crates against the Lean oracle.
//!
//! The oracle is the executable `thole-oracle`, built by `lake build` from
//! `oracle/lean/`. It runs the definitions that the Lean theorems are about,
//! with exact rational arithmetic. A test sends it a problem together with
//! what the Rust code returned, and it answers whether the specification
//! allows that result.
//!
//! This crate is the Rust side: the connection to the executable
//! ([`Oracle`]), the functions both sides can evaluate ([`Poly`]), and one
//! module per area that writes the requests. The tests themselves are in
//! `tests/`, one file per area.
//!
//! The executable runs as a separate process, so nothing of Lean is linked
//! into any crate.

mod poly;
pub mod roots;

use std::io::{BufRead, BufReader, Write};
use std::path::PathBuf;
use std::process::{Child, ChildStdin, ChildStdout, Command, Stdio};
use std::sync::{LazyLock, Mutex};

pub use poly::Poly;

/// The answer of the oracle to a request.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Verdict {
    /// The result is what the specification allows.
    Ok,
    /// The request is outside what the check can decide; the reason is given.
    /// Nothing is claimed about the result.
    Skip(String),
    /// The result contradicts the specification; the reason is given.
    Fail(String),
}

/// A running oracle process.
#[derive(Debug)]
pub struct Oracle {
    child: Child,
    stdin: ChildStdin,
    stdout: BufReader<ChildStdout>,
}

impl Oracle {
    /// Starts the oracle.
    ///
    /// The executable is the one named by the environment variable
    /// `THOLE_ORACLE`, or `.lake/build/bin/thole-oracle` in the repository.
    ///
    /// # Panics
    ///
    /// If the executable cannot be started. A missing oracle fails the tests
    /// instead of skipping them, so that they cannot pass without having run.
    pub fn start() -> Self {
        let path = std::env::var_os("THOLE_ORACLE").map_or_else(
            || {
                PathBuf::from(concat!(
                    env!("CARGO_MANIFEST_DIR"),
                    "/../.lake/build/bin/thole-oracle"
                ))
            },
            PathBuf::from,
        );
        let mut child = Command::new(&path)
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .spawn()
            .unwrap_or_else(|err| {
                panic!(
                    "cannot start the oracle {}: {err}\nbuild it with `lake build thole-oracle`",
                    path.display()
                )
            });
        let stdin = child.stdin.take().expect("stdin is piped");
        let stdout = BufReader::new(child.stdout.take().expect("stdout is piped"));
        Self {
            child,
            stdin,
            stdout,
        }
    }

    /// Sends one request line and returns the answer line as it is.
    ///
    /// # Panics
    ///
    /// If the oracle cannot be reached or has stopped.
    pub fn ask_raw(&mut self, request: &str) -> String {
        assert!(!request.contains('\n'), "a request is a single line");
        writeln!(self.stdin, "{request}").expect("the oracle accepts the request");
        self.stdin.flush().expect("the oracle accepts the request");
        let mut answer = String::new();
        let read = self.stdout.read_line(&mut answer);
        assert!(
            matches!(read, Ok(n) if n > 0),
            "the oracle stopped while answering: {request}"
        );
        answer.truncate(answer.trim_end().len());
        answer
    }

    /// Sends one request line and returns the verdict.
    ///
    /// # Panics
    ///
    /// If the oracle cannot read the request. That is a mistake in the test,
    /// not a result of it.
    pub fn ask(&mut self, request: &str) -> Verdict {
        let answer = self.ask_raw(request);
        let (kind, reason) = answer.split_once(' ').unwrap_or((&answer, ""));
        match kind {
            "ok" => Verdict::Ok,
            "skip" => Verdict::Skip(reason.to_owned()),
            "fail" => Verdict::Fail(reason.to_owned()),
            _ => panic!("the oracle answered `{answer}` to `{request}`"),
        }
    }
}

impl Drop for Oracle {
    fn drop(&mut self) {
        let _ = self.child.kill();
        let _ = self.child.wait();
    }
}

/// Sends one request line to an oracle process shared by the whole test
/// binary, and returns the verdict. See [`Oracle::ask`].
pub fn ask(request: &str) -> Verdict {
    static SHARED: LazyLock<Mutex<Oracle>> = LazyLock::new(|| Mutex::new(Oracle::start()));
    // A panic in `Oracle::ask` already fails the test that caused it; the
    // other tests would only repeat it.
    SHARED
        .lock()
        .expect("an earlier request failed")
        .ask(request)
}

/// How an `f64` is written in a request: the 16 hexadecimal digits of its bit
/// pattern. The oracle reads them back as the exact value.
pub fn bits(x: f64) -> String {
    format!("{:016x}", x.to_bits())
}
