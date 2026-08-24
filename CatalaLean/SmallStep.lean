import CatalaLean.Syntax
import Mathlib.Logic.Relation

namespace CatalaLean

/-!
# Small-step operational semantics for Cata

Values are a separate inductive type to keep pattern matching clean.
The `termOf` / `valOf` functions bridge `Val` ↔ `CataTerm`.
-/

/- ============================================================
   Values
   ============================================================ -/

/-- Cata values -/
inductive Val : Type where
  | unit : Val
  | bool : Bool → Val
  | int : Int → Val
  | pair : Val → Val → Val
  | closure : Bruijn → CataTerm → Val
  | vsome : Val → Val
  | vnone : Val
  | vpure : Val → Val
  deriving Repr, BEq, Inhabited, Nonempty

/-- Convert a value to a CataTerm. -/
def termOf (v : Val) : CataTerm :=
  match v with
  | .unit => .tunit
  | .bool b => .tbool b
  | .int i => .tint i
  | .pair v1 v2 => .tpair (termOf v1) (termOf v2)
  | .closure k body => .tclosure k body
  | .vsome v' => .tvsome (termOf v')
  | .vnone => .tvnone
  | .vpure v' => .tvpure (termOf v')

/-- Try to parse a CataTerm as a value. -/
partial def valOf (t : CataTerm) : Option Val :=
  match t with
  | .tunit => some .unit
  | .tbool b => some (.bool b)
  | .tint i => some (.int i)
  | .tpair t1 t2 =>
    match valOf t1, valOf t2 with
    | some v1, some v2 => some (.pair v1 v2)
    | _, _ => none
  | .tclosure k body => some (.closure k body)
  | .tvsome t' =>
    match valOf t' with
    | some v' => some (.vsome v')
    | none => none
  | .tvnone => some .vnone
  | .tvpure t' =>
    match valOf t' with
    | some v' => some (.vpure v')
    | none => none
  | _ => none

/- ============================================================
   Substitution for beta reduction
   ============================================================ -/

/-- Substitute value `v` for de Bruijn index `k` in `body`. -/
partial def substValTerm (v : Val) (body : CataTerm) (k : Bruijn) : CataTerm :=
  match body with
  | .tvar x =>
    if x = k then termOf v else .tvar x
  | .tunit => .tunit
  | .tbool b => .tbool b
  | .tint i => .tint i
  | .tpair t1 t2 => .tpair (substValTerm v t1 (Bruijn.succ k)) (substValTerm v t2 (Bruijn.succ k))
  | .tlam ty body' => .tlam ty (substValTerm v body' (Bruijn.succ k))
  | .tapp t1 t2 => .tapp (substValTerm v t1 k) (substValTerm v t2 k)
  | .tproj i t' => .tproj i (substValTerm v t' k)
  | .tconflict => .tconflict
  | .tclosure kk body' => .tclosure kk (substValTerm v body' (Bruijn.succ k))
  | .tvsome t' => .tvsome (substValTerm v t' k)
  | .tvnone => .tvnone
  | .tvpure t' => .tvpure (substValTerm v t' k)
  | .tbinop op t1 t2 => .tbinop op (substValTerm v t1 k) (substValTerm v t2 k)
  | .tmatch scrut t1 t2 =>
    .tmatch (substValTerm v scrut k) (substValTerm v t1 k) (substValTerm v t2 (Bruijn.succ k))
  | .tif cond ta tb =>
    .tif (substValTerm v cond k) (substValTerm v ta k) (substValTerm v tb k)
  | .tfold f ts acc =>
    .tfold (substValTerm v f k)
           (ts.map (fun t => substValTerm v t k))
           (substValTerm v acc k)
  | .terrorOnEmpty t' => .terrorOnEmpty (substValTerm v t' k)
  | .tdefaultPure t' => .tdefaultPure (substValTerm v t' k)
  | .tdefault ts tj tc =>
    .tdefault (ts.map (fun t => substValTerm v t k))
              (substValTerm v tj k)
              (substValTerm v tc k)
  | .tempty => .tempty

/- ============================================================
   Small-step reduction
   ============================================================ -/

/-- Cata small-step reduction relation -/
inductive red : CataTerm → CataTerm → Prop where
  -- E-App1
  | app_l {t t' t2} (ht : red t t') : red (.tapp t t2) (.tapp t' t2)

  -- E-App2
  | app_r {v1 t t2} (ht : red t t2) : red (.tapp (termOf v1) t) (.tapp (termOf v1) t2)

  -- E-App (beta)
  | beta {k body v} : red (.tapp (.tclosure k body) (termOf v)) (substValTerm v body k)

  -- E-Binop1
  | binop_l {op t t' t2} (ht : red t t') : red (.tbinop op t t2) (.tbinop op t' t2)

  -- E-Binop2
  | binop_r {op v1 t t'} (ht : red t t') : red (.tbinop op (termOf v1) t) (.tbinop op (termOf v1) t')

  -- E-Binop (eval)
  | binop_eval {op v1 v2 v} (h : getOp op (termOf v1) (termOf v2) = some (termOf v)) :
    red (.tbinop op (termOf v1) (termOf v2)) (termOf v)

  -- E-Match1
  | match_l {u u' t1 t2} (hu : red u u') : red (.tmatch u t1 t2) (.tmatch u' t1 t2)

  -- E-MatchNone
  | match_none {t1 t2} : red (.tmatch .tvnone t1 t2) t1

  -- E-MatchSome
  | match_some {v t1 t2} : red (.tmatch (.tvsome (termOf v)) t1 t2) (substValTerm v t2 Bruijn.zero)

  -- E-If1
  | if_l {b b' ta tb} (hb : red b b') : red (.tif b ta tb) (.tif b' ta tb)

  -- E-IfTrue
  | if_true {ta tb} : red (.tif (.tbool true) ta tb) ta

  -- E-IfFalse
  | if_false {ta tb} : red (.tif (.tbool false) ta tb) tb

  -- E-Default
  | default {t ts tj tc} :
    red (.tdefault (t :: ts) tj tc)
        (.tdefault ts tj
           (.tmatch t (.tif tj tc .tempty) (.tvsome (.tvar Bruijn.zero))))

  -- E-DefaultBase
  | default_base {tc} : red (.tdefault [] (.tbool true) tc) tc

  -- E-DefaultEmpty
  | default_empty {ts tj tc} :
    red (.tdefault (.tempty :: ts) tj tc) (.tdefault ts tj tc)

  -- E-Fold1
  | fold_l {f ts acc acc'} (ha : red acc acc') : red (.tfold f ts acc) (.tfold f ts acc')

  -- E-FoldNil
  | fold_nil {f acc} : red (.tfold f [] acc) acc

  -- E-ErrorOnEmpty1
  | eoe_l {t t'} (ht : red t t') : red (.terrorOnEmpty t) (.terrorOnEmpty t')

  -- E-ErrorOnEmptyNone
  | eoe_none : red (.terrorOnEmpty .tvnone) .tconflict

  -- E-ErrorOnEmptySome
  | eoe_some {v} : red (.terrorOnEmpty (.tvsome (termOf v))) (termOf v)

  -- E-DefaultPure1
  | dpure_l {t t'} (ht : red t t') : red (.tdefaultPure t) (.tdefaultPure t')

  -- E-DefaultPureValue
  | dpure_val {v} : red (.tdefaultPure (termOf v)) (.tvpure (termOf v))

  -- E-EmptyNone
  | empty_none : red .tempty .tvnone

-- ============================================================
-- Star / Plus closures
-- ============================================================

open Relation

/-- Reflexive-transitive closure of red -/
abbrev redStar := ReflTransGen red

/-- Transitive closure of red -/
abbrev redPlus := TransGen red

/-- Reflexivity of star -/
lemma redStar_refl {t : CataTerm} : redStar t t := by
  apply ReflTransGen.refl

/-- Transitivity of star -/
lemma redStar_trans {t1 t2 t3 : CataTerm}
  (h12 : redStar t1 t2) (h23 : redStar t2 t3) : redStar t1 t3 := by
  apply ReflTransGen.trans h12 h23

/-- A single step is also a star step -/
lemma redStar_step {t t' : CataTerm} : red t t' → redStar t t' := by
  intro h; apply ReflTransGen.single h

/-- Conflict doesn't reduce -/
theorem red_not_conflict {t' : CataTerm} : ¬ red .tconflict t' := by
  intro h
  -- .tconflict matches no red constructor LHS, so h is impossible
  cases h

end CatalaLean
