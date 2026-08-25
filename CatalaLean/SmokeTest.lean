import CatalaLean.Syntax

/-!
# Smoke tests — L4-05 Regression Corpus

Hand-curated regression suite covering the most critical substitution,
lifting, free-variable, and environment paths. These run as part of
`lake build` (every test is a compiled theorem — a failure breaks the build).

`substTerm`/`termValid` are `partial` defs (opaque to `simp`), so behavioral
tests use `native_decide` over the `BEq` instances; structural lemmas use
plain proofs.

Populated per `levels/L4-testing/tickets/regression-corpus.md`; new entries
come from diff-harness divergences or manually discovered edge cases.
-/

namespace CatalaLean.Test.Smoke

/-- Bruijn round-trip at zero. -/
theorem smoke_ofNat_zero : Bruijn.ofNat 0 = .zero := rfl

/-- Bruijn round-trip: general induction proof. -/
theorem smoke_bruijn_roundtrip : ∀ n : Nat, Bruijn.toNat (Bruijn.ofNat n) = n := by
  intro n
  induction n with
  | zero => exact smoke_ofNat_zero ▸ rfl
  | succ m ih =>
    have h : Bruijn.ofNat (m + 1) = .succ (Bruijn.ofNat m) := rfl
    simp [h, Bruijn.toNat, ih]

/-! ## Behavioral tests via native_decide (partial defs are opaque) -/

/-- Identity substitution at index 0 on a variable: replaces it. -/
example : substTerm (.tint 42) (.tvar .zero) 0 == .tint 42 := by native_decide

/-- Substitution at a higher index leaves variable 0 untouched. -/
example : substTerm (.tint 42) (.tvar .zero) 1 == .tvar .zero := by native_decide

/-- Substitution into a pair distributes. -/
example : substTerm (.tbool true) (.tpair (.tvar .zero) (.tint 5)) 0 ==
    .tpair (.tbool true) (.tint 5) := by native_decide

/-- filterFV keeps only positive-index variables, decremented. -/
example : filterFV [.zero, .succ .zero] == [.zero] := by native_decide

/-- Free vars of application is concatenation. -/
example : freeVarsTerm (.tapp (.tvar .zero) (.tvar (.succ .zero))) ==
    [.zero, .succ .zero] := by native_decide

/-- envLookup basic case. -/
example : envLookup [("x", .intT), ("y", .boolT)] 1 == some .boolT := by native_decide

/-- envLookup miss on empty env. -/
example : envLookup [] 0 == none := by native_decide

/-! ## Lifting semantics: variable below cutoff d shifts by n; at/above stays. -/

/-- Variable strictly below cutoff gets shifted past n binders. -/
example : liftTerm 2 1 (.tvar .zero) == .tvar (Bruijn.ofNat 2) := by native_decide

/-- Variable at the cutoff is untouched. -/
example : liftTerm 2 0 (.tvar .zero) == .tvar .zero := by native_decide

/-- Lift by zero amount is identity regardless of cutoff. -/
theorem smoke_lift_zero_amount : liftTerm 0 d t = t := by
  unfold liftTerm; rfl

/-- getOp integer arithmetic sanity (guards against oracle mutation). -/
example : getOp .add (.tint 2) (.tint 3) == some (.tint 5) := by native_decide

end CatalaLean.Test.Smoke
