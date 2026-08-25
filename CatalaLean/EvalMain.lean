import CatalaLean.Eval

/-!
# `lake exe catala-eval` — entry point for the diff harness

Input (argv[1]): a simple s-expression term encoding.
Output: the evaluated normal form via `Repr`-derived string on stdout.

Term grammar (S-expr, whitespace-separated):
  (int N) | (bool true|false) | unit | none | empty | conflict
  (some T) | (pure T) | (pair T T)
  (+ T T) | (* T T) | (ge T T) | (and T T) | (or T T)
  (if T T T) | (match T T T) | (errorOnEmpty T) | (defaultPure T)
  (app (closure INT T) T)
  (default (T ...) T T)

Usage: lake exe catala-eval '(+ (int 2) (int 3))' [fuel=200]
-/

namespace CatalaLean.EvalMain

open CatalaLean

/-- Parse an s-expression token list into a CataTerm. `fuel` bounds recursion. -/
def parse : Nat → List String → Option (CataTerm × List String)
  | 0, _ => none
  | fuel+1, "(" :: rest =>
    match rest with
    | "int" :: n :: ")" :: r => match n.toInt? with
        | some i => some (.tint i, r)
        | none => none
    | "bool" :: b :: ")" :: r => some (.tbool (b == "true"), r)
    | "unit" :: ")" :: r => some (.tunit, r)
    | "none" :: ")" :: r => some (.tvnone, r)
    | "empty" :: ")" :: r => some (.tempty, r)
    | "conflict" :: ")" :: r => some (.tconflict, r)
    | "some" :: r =>
      match parse fuel r with
      | some (t, ")" :: r') => some (.tvsome t, r')
      | _ => none
    | "pair" :: r =>
      match parse fuel r with
      | some (t1, r1) =>
        match parse fuel r1 with
        | some (t2, ")" :: r2) => some (.tpair t1 t2, r2)
        | _ => none
      | _ => none
    | "if" :: r =>
      match parse fuel r with
      | some (c, r1) =>
        match parse fuel r1 with
        | some (ta, r2) =>
          match parse fuel r2 with
          | some (tb, ")" :: r3) => some (.tif c ta tb, r3)
          | _ => none
        | _ => none
      | _ => none
    | "errorOnEmpty" :: r =>
      match parse fuel r with
      | some (t, ")" :: r') => some (.terrorOnEmpty t, r')
      | _ => none
    | "defaultPure" :: r =>
      match parse fuel r with
      | some (t, ")" :: r') => some (.tdefaultPure t, r')
      | _ => none
    | op :: r =>
      let cop : Option CataOp :=
        if op == "+" then some .add else if op == "*" then some .mul
        else if op == "ge" then some .ge else if op == "and" then some .and
        else if op == "or" then some .or else none
      match cop with
      | none => none
      | some o =>
        match parse fuel r with
        | none => none
        | some (t1, r1) =>
          match parse fuel r1 with
          | none => none
          | some (t2, ")" :: r2) => some (.tbinop o t1 t2, r2)
          | _ => none
    | _ => none
  | _, _ => none

/-- Tokenize an s-expression string. -/
def tokenize (s : String) : List String :=
  (s.replace "(" " ( " |>.replace ")" " ) ").splitOn |>.filter (· ≠ "")

/-- Parse a full term; fails unless tokens are exactly consumed. -/
def parseTop (s : String) : Option CataTerm :=
  match parse 100 (tokenize s) with
  | some (t, []) => some t
  | _ => none

end CatalaLean.EvalMain

def main (args : List String) : IO UInt32 := do
  match args with
  | [] => do
    IO.println "usage: lake exe catala-eval '<sexpr>' [fuel]"
    return 1
  | expr :: rest => do
    let fuel := match rest.head? with
      | some f => (f.toNat?).getD 200
      | none => 200
    match CatalaLean.EvalMain.parseTop expr with
    | none => do IO.println "{\"error\": \"parse failure\"}"; return 1
    | some t =>
      match CatalaLean.evalTerm fuel t with
      | none => do IO.println "{\"error\": \"fuel exhausted\"}"; return 2
      | some r => do IO.println (repr r); return 0
