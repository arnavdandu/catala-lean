import CatalaLean.SmallStep

/-!
# Executable evaluator — L4-04 Differential Testing Harness (Lean side)

A functional, decidable mirror of the `red` relation: `step t` returns
`some t'` when `red t t'` holds (determinism guarantees at most one such
`t'` — see `red_det`), and `none` on a normal form.

`evalTerm` iterates steps to a normal form with a fuel bound. This is the
Lean oracle that the Python fuzzer (`scripts/diff_test.py`) will compare
against the OCaml `catala dcalc` runtime.

Note: `red` itself is a `Prop` and cannot execute; `step` is its verified
computational shadow. A future L5 obligation is to prove
`step t = some t' → red t t'`.
-/

namespace CatalaLean

/-- Is this term a closure value? -/
def isClosureV : CataTerm → Bool
  | .tclosure _ _ => true
  | _ => false

/-- Does the term have a tvsome head? -/
def isTvsome : CataTerm → Bool
  | .tvsome _ => true
  | _ => false

/-- Does the term have a tvpure head? -/
def isTvpure : CataTerm → Bool
  | .tvpure _ => true
  | _ => false

/-- Is this term a value (normal form for head evaluation)? -/
def isValT (t : CataTerm) : Bool :=
  match t with
  | .tunit | .tbool _ | .tint _ | .tvnone | .tconflict => true
  | .tpair t1 t2 => isValT t1 && isValT t2
  | .tclosure _ _ => true
  | .tvsome t' => isValT t'
  | .tvpure t' => isValT t'
  | _ => false

/-- One small-step reduction, executable mirror of `red`. Returns `none` on normal forms. -/
def step : CataTerm → Option CataTerm
  -- Application: beta redex
  | .tapp f a =>
    if isClosureV f && isValT a then
      match f, valOf a with
      | .tclosure k body, some v => some (substValTerm v body k)
      | _, _ => none
    else if !isClosureV f then none  -- non-closure values are stuck in app position per red
    else (step a).map (fun a' => .tapp f a')
  -- Binary operators
  | .tbinop op t1 t2 =>
    if isValT t1 && isValT t2 then
      getOp op t1 t2
    else if !isValT t1 then
      (step t1).map (fun t1' => .tbinop op t1' t2)
    else
      (step t2).map (fun t2' => .tbinop op t1 t2')
  -- Match
  | .tmatch s t1 t2 =>
    if s == .tvnone then some t1
    else if isTvsome s then
      match s with
      | .tvsome inner => (valOf inner).map (fun v => substValTerm v t2 Bruijn.zero)
      | _ => none
    else
      (step s).map (fun s' => .tmatch s' t1 t2)
  -- If
  | .tif c ta tb =>
    if c == .tbool true then some ta
    else if c == .tbool false then some tb
    else
      (step c).map (fun c' => .tif c' ta tb)
  -- Default
  | .tdefault ts tj tc =>
    match ts with
    | [] => if tj == .tbool true then some tc else none
    | .tempty :: rest => some (.tdefault rest tj tc)
    | t :: rest =>
      some (.tdefault rest tj (.tmatch t (.tif tj tc .tempty) (.tvsome (.tvar Bruijn.zero))))
  -- Fold: reduce accumulator while args remain
  | .tfold f ts acc =>
    match ts with
    | [] => some acc
    | _ :: _ =>
      match step acc with
      | some acc' => some (.tfold f ts acc')
      | none => none
  -- errorOnEmpty
  | .terrorOnEmpty t' =>
    if t' == .tvnone then some .tconflict
    else if isTvsome t' then
      match t' with
      | .tvsome inner => some inner
      | _ => none
    else
      (step t').map .terrorOnEmpty
  -- defaultPure
  | .tdefaultPure t' =>
    if isTvpure t' then none
    else if isValT t' then some (.tvpure t')
    else (step t').map .tdefaultPure
  -- Empty
  | .tempty => some .tvnone
  | _ => none

/-- Evaluate to normal form under fuel bound. -/
def evalTerm (fuel : Nat) (t : CataTerm) : Option CataTerm :=
  match fuel with
  | 0 => none
  | Nat.succ f =>
    match step t with
    | none => some t   -- normal form reached
    | some t' => evalTerm f t'

end CatalaLean
