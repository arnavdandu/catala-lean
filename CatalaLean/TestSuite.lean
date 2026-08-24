import CatalaLean.Syntax
import CatalaLean.SmallStep
import Mathlib.Tactic

namespace CatalaLean

/-! # Test Suite for CatalaLean -/

/- ============================================================
  Section 1: Bruijn index tests
  ============================================================ -/

section BruijnTests

open Bruijn

theorem test_ofNat_zero : ofNat 0 = .zero := by simp [ofNat]
theorem test_ofNat_succ : ofNat 3 = .succ (.succ (.succ .zero)) := by simp [ofNat]
theorem test_toNat_zero : toNat .zero = 0 := by simp [toNat]
theorem test_toNat_succ : toNat (.succ (.succ .zero)) = 2 := by simp [toNat]
theorem test_roundtrip_nat : toNat (ofNat 42) = 42 := by simp [toNat_ofNat]
theorem test_roundtrip_bruijn : ofNat (toNat (.succ (.succ .zero))) = .succ (.succ .zero) := by simp [ofNat_toNat]

end BruijnTests

/- ============================================================
  Section 2: getOp tests
  ============================================================ -/

section GetOpTests

theorem test_getOp_add : getOp .add (.tint 1) (.tint 2) = some (.tint 3) := by
  simp [getOp]

theorem test_getOp_mul : getOp .mul (.tint 3) (.tint 4) = some (.tint 12) := by
  simp [getOp]

theorem test_getOp_ge : getOp .ge (.tint 5) (.tint 3) = some (.tbool true) := by
  simp [getOp]

theorem test_getOp_ge_false : getOp .ge (.tint 2) (.tint 3) = some (.tbool false) := by
  simp [getOp]

theorem test_getOp_and : getOp .and (.tbool true) (.tbool false) = some (.tbool false) := by
  simp [getOp]

theorem test_getOp_or : getOp .or (.tbool true) (.tbool false) = some (.tbool true) := by
  simp [getOp]

theorem test_getOp_type_mismatch : getOp .add (.tint 1) (.tbool true) = none := by
  simp [getOp]

end GetOpTests

/- ============================================================
  Section 3: termOf tests
  ============================================================ -/

section TermOfTests

open Bruijn

theorem test_termOf_unit : termOf Val.unit = .tunit := by simp [termOf]
theorem test_termOf_bool : termOf (Val.bool true) = .tbool true := by simp [termOf]
theorem test_termOf_int : termOf (Val.int (42 : Int)) = .tint 42 := by simp [termOf]
theorem test_termOf_vnone : termOf Val.vnone = .tvnone := by simp [termOf]
theorem test_termOf_vpure : termOf (Val.vpure Val.unit) = .tvpure .tunit := by simp [termOf]

end TermOfTests

/- ============================================================
  Section 4: SmallStep reduction tests
  ============================================================ -/

section SmallStepTests

open Bruijn

/-- If true -/
theorem test_if_true :
  red (.tif (.tbool true) (.tint 1) (.tint 2)) (.tint 1) := by
  apply red.if_true

/-- If false -/
theorem test_if_false :
  red (.tif (.tbool false) (.tint 1) (.tint 2)) (.tint 2) := by
  apply red.if_false

/-- Match none -/
theorem test_match_none :
  red (.tmatch .tvnone (.tint 0) (.tvar .zero)) (.tint 0) := by
  apply red.match_none

/-- Match some with explicit value -/
theorem test_match_some :
  let v : Val := Val.unit
  red (.tmatch (.tvsome (termOf v)) (.tint 0) (.tvar .zero))
      (substValTerm v (.tvar .zero) .zero) := by
  apply red.match_some

/-- Empty → vnone -/
theorem test_empty_none :
  red .tempty .tvnone := by
  apply red.empty_none

/-- ErrorOnEmpty: none → conflict -/
theorem test_eoe_none :
  red (.terrorOnEmpty .tvnone) .tconflict := by
  apply red.eoe_none

/-- Conflict doesn't reduce -/
theorem test_conflict_irreducible : ¬ red .tconflict (.tint 0) := red_not_conflict

/-- Binop: 1 + 2 → 3 (via getOp) -/
theorem test_binop_getOp :
  getOp .add (.tint 1) (.tint 2) = some (.tint 3) := by simp [getOp]

/-- Star reflexivity -/
theorem test_star_refl : redStar (.tint 1) (.tint 1) := redStar_refl

/-- Star transitivity -/
theorem test_star_trans :
  redStar (.tint 1) (.tint 1) → redStar (.tint 1) (.tint 1) → redStar (.tint 1) (.tint 1) := by
  intro h1 h2; exact redStar_trans h1 h2

/-- Step implies star -/
theorem test_step_star : red .tempty .tvnone → redStar .tempty .tvnone := redStar_step

/-- App left reduction -/
theorem test_app_l :
  red (.tif (.tbool true) (.tint 1) (.tint 2)) (.tint 1) →
  red (.tapp (.tif (.tbool true) (.tint 1) (.tint 2)) (.tint 0))
      (.tapp (.tint 1) (.tint 0)) := by
  intro h; apply red.app_l h

end SmallStepTests

end CatalaLean