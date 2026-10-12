/-
The oracle executable.

It reads one request per line from standard input and writes one answer per
line to standard output, until the input ends. A request is a name followed by
arguments, separated by single spaces. The answer is `ok`, `skip <reason>` or
`fail <reason>` (see `Thole.Oracle.Verdict`), or `error <message>` for a
request that cannot be read.

The request `f64 <bits>` answers with the value of that `f64` as a fraction.
The Rust tests use it to check that both sides read numbers the same way.
-/
import Thole.Oracle.Roots

open Thole.Oracle

/-- The requests of every area. -/
def requests : List (String × (List String → Except String Verdict)) :=
  rootsRequests

/-- The answer to one request line. -/
def respond (line : String) : String :=
  match line.splitOn " " with
  | ["f64", bits] =>
    match parseF64 bits with
    | .ok q => s!"{q.num}/{q.den}"
    | .error message => s!"error {message}"
  | name :: args =>
    match requests.lookup name with
    | some handler =>
      match handler args with
      | .ok verdict => verdict.toLine
      | .error message => s!"error {message}"
    | none => s!"error unknown request: {name}"
  | [] => "error empty request"

def main : IO Unit := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  repeat
    let line ← stdin.getLine
    if line.isEmpty then break
    stdout.putStrLn (respond (line.dropEndWhile (· == '\n')).copy)
    stdout.flush
