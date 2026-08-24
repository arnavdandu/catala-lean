import CatalaLean.Syntax
import CatalaLean.SmallStep
import Mathlib.Tactic

namespace CatalaLean

/-!
# Typing.lean — Type system for Cata

Maps Coq `typing.v` to Lean 4:
- Type invariants
- Well-typed terms (wellTyped) — unified, no mutual recursion
-/

/- ============================================================
   Section 1: Type Invariants
   ============================================================ -/

/-- A type is "base" — no complex structure -/
inductive typeIsBase : CataType → Prop
  | unit : typeIsBase .unitT
  | int : typeIsBase .intT
  | bool : typeIsBase .boolT

/-- A type has no conflict anywhere -/
inductive typeNoConflict : CataType → Prop
  | unit : typeNoConflict .unitT
  | int : typeNoConflict .intT
  | bool : typeNoConflict .boolT
  | funT {T1 T2} : typeNoConflict T1 → typeNoConflict T2 → typeNoConflict (.funT T1 T2)
  | prodT {T1 T2} : typeNoConflict T1 → typeNoConflict T2 → typeNoConflict (.prodT T1 T2)
  | arrowT {T1 T2} : typeNoConflict T1 → typeNoConflict T2 → typeNoConflict (.arrowT T1 T2)
  | arrowProdT {T1 T2} : typeNoConflict T1 → typeNoConflict T2 → typeNoConflict (.arrowProdT T1 T2)
  | arrowListT {T1 T2} : typeNoConflict T1 → typeNoConflict T2 → typeNoConflict (.arrowListT T1 T2)

theorem typeIsBase_implies_noConflict {T : CataType} :
  typeIsBase T → typeNoConflict T := by
  intro h
  induction h <;> constructor

/- ============================================================
   Section 2: Well-typed terms (unified, no mutual recursion)
   ============================================================ -/

/-- Γ ⊢ t : T — term t has type T in context Γ -/
inductive wellTyped : List CataType → CataTerm → CataType → Prop
  -- Values
  | w_unit {Γ} : wellTyped Γ .tunit .unitT
  | w_bool {Γ b} : wellTyped Γ (.tbool b) .boolT
  | w_int {Γ i} : wellTyped Γ (.tint i) .intT
  | w_vnone {Γ T} : wellTyped Γ .tvnone (.funT T .unitT)
  | w_vsome {Γ v T} : wellTyped Γ v T → wellTyped Γ (.tvsome v) (.funT T .unitT)
  | w_vpure {Γ v T} : wellTyped Γ v T → wellTyped Γ (.tvpure v) T
  | w_empty {Γ T} : wellTyped Γ .tempty (.funT T .unitT)
  | w_closure {Γ k T1 T2 body} :
      wellTyped (T1 :: Γ) body T2 →
      wellTyped Γ (.tclosure k body) (.funT T1 T2)
  -- Lambda
  | w_lam {Γ T1 T2 body} :
      wellTyped (T1 :: Γ) body T2 →
      wellTyped Γ (.tlam T1 body) (.funT T1 T2)
  -- Application
  | w_app {Γ t1 t2 T1 T2} :
      wellTyped Γ t1 (.funT T1 T2) →
      wellTyped Γ t2 T1 →
      wellTyped Γ (.tapp t1 t2) T2
  -- Pair
  | w_pair {Γ t1 t2 T1 T2} :
      wellTyped Γ t1 T1 →
      wellTyped Γ t2 T2 →
      wellTyped Γ (.tpair t1 t2) (.prodT T1 T2)
  -- Projection
  | w_proj1 {Γ t T1 T2} :
      wellTyped Γ t (.prodT T1 T2) →
      wellTyped Γ (.tproj 0 t) T1
  | w_proj2 {Γ t T1 T2} :
      wellTyped Γ t (.prodT T1 T2) →
      wellTyped Γ (.tproj 1 t) T2
  -- If
  | w_if {Γ tb tf T} :
      wellTyped Γ (.tbool true) .boolT →
      wellTyped Γ tb T →
      wellTyped Γ tf T →
      wellTyped Γ (.tif (.tbool true) tb tf) T
  -- Match none
  | w_match_none {Γ t_none T} :
      wellTyped Γ (.tmatch .tvnone t_none .tvnone) (.funT T .unitT)
  -- ErrorOnEmpty
  | w_eoe {Γ t T} :
      wellTyped Γ t (.funT T .unitT) →
      wellTyped Γ (.terrorOnEmpty t) (.funT T .unitT)
  -- DefaultPure
  | w_dpure {Γ t T} :
      wellTyped Γ t T →
      wellTyped Γ (.tdefaultPure t) (.funT T .unitT)

end CatalaLean
