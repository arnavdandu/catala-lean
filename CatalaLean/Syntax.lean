import Mathlib.Data.List.Basic
import Mathlib.Data.Option.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Data.Bool.Basic

namespace CatalaLean

set_option linter.unusedVariables false

/-- De Bruijn indices for bound variables -/
inductive Bruijn where
  | zero : Bruijn
  | succ : Bruijn → Bruijn
  deriving Repr, BEq, DecidableEq

namespace Bruijn

def ofNat (n : Nat) : Bruijn :=
  match n with
  | 0 => .zero
  | Nat.succ m => .succ (ofNat m)

def toNat (x : Bruijn) : Nat :=
  match x with
  | .zero => 0
  | .succ m => (toNat m) + 1

theorem toNat_ofNat (n : Nat) : toNat (ofNat n) = n := by
  induction n with
  | zero => simp [ofNat, toNat]
  | succ k ih => simp [ofNat, toNat, ih]

theorem ofNat_toNat (x : Bruijn) : ofNat (toNat x) = x := by
  induction x with
  | zero => simp [ofNat, toNat]
  | succ x ih => simp [ofNat, toNat, ih]

end Bruijn

/-- Type expressions (Σ-encoding of Cata typing) -/
inductive CataType where
  | unitT | boolT | intT
  | funT : CataType → CataType → CataType
  | prodT : CataType → CataType → CataType
  | arrowT : CataType → CataType → CataType
  | arrowProdT : CataType → CataType → CataType
  | arrowListT : CataType → CataType → CataType
  | conflict
  deriving Repr, BEq, DecidableEq

/-- Binary operators for Cata -/
inductive CataOp where
  | add : CataOp  -- integer addition
  | mul : CataOp  -- integer multiplication
  | ge : CataOp   -- integer greater-or-equal
  | and : CataOp  -- logical and
  | or : CataOp   -- logical or
  deriving Repr, BEq, DecidableEq

-- ============================================================
-- CataTerm: single inductive for terms and values
-- ============================================================

/-- Unified Σ-type for terms and values in Cata. -/
inductive CataTerm where
  | tvar : Bruijn → CataTerm
  | tunit : CataTerm
  | tbool : Bool → CataTerm
  | tint : Int → CataTerm
  | tpair : CataTerm → CataTerm → CataTerm
  | tlam : CataType → CataTerm → CataTerm
  | tapp : CataTerm → CataTerm → CataTerm
  | tproj : Nat → CataTerm → CataTerm
  | tconflict
  | tclosure : Bruijn → CataTerm → CataTerm
  | tvsome : CataTerm → CataTerm
  | tvnone : CataTerm
  | tvpure : CataTerm → CataTerm
  -- Extended constructors (Default calculus)
  | tbinop : CataOp → CataTerm → CataTerm → CataTerm
  | tmatch : CataTerm → CataTerm → CataTerm → CataTerm  -- scrutinee, none_case, some_body
  | tif : CataTerm → CataTerm → CataTerm → CataTerm     -- condition, then, else
  | tfold : CataTerm → List CataTerm → CataTerm → CataTerm  -- func, args, acc
  | terrorOnEmpty : CataTerm → CataTerm
  | tdefaultPure : CataTerm → CataTerm
  | tdefault : List CataTerm → CataTerm → CataTerm → CataTerm  -- ts, tj, tc
  | tempty : CataTerm
  deriving Repr, BEq

/-- Values are represented as CataTerm -/
abbrev CataVal := CataTerm

/-- Value constructor aliases -/
def unitVal : CataVal := .tunit
def boolVal (b : Bool) : CataVal := .tbool b
def intVal (i : Int) : CataVal := .tint i
def pairVal (v1 v2 : CataVal) : CataVal := .tpair v1 v2
def closureVal (k : Bruijn) (body : CataTerm) : CataVal := .tclosure k body
def vsome (v : CataVal) : CataVal := .tvsome v
def vnone : CataVal := .tvnone
def vpure (v : CataVal) : CataVal := .tvpure v

/-- Semantics of binary operators on values -/
def getOp (op : CataOp) (v1 v2 : CataVal) : Option CataVal :=
  match op, v1, v2 with
  | .add, .tint i1, .tint i2 => some (.tint (i1 + i2))
  | .mul, .tint i1, .tint i2 => some (.tint (i1 * i2))
  | .ge, .tint i1, .tint i2 => some (.tbool (i1 >= i2))
  | .and, .tbool b1, .tbool b2 => some (.tbool (b1 && b2))
  | .or, .tbool b1, .tbool b2 => some (.tbool (b1 || b2))
  | _, _, _ => none

-- ============================================================
-- Environment types
-- ============================================================

abbrev CataEnv := List (String × CataType)
abbrev CataSEnv := List (Bruijn × CataTerm)
abbrev CataCEnv := List CataTerm

inductive CataState where
  | emptyState
  | consState : Bruijn × CataTerm → CataState → CataState
  deriving Repr

inductive CataCont where
  | ctret
  | ctclos : Bruijn → CataTerm → CataTerm → CataCont → CataCont
  | ctseq : CataTerm → CataTerm → CataCont → CataCont
  deriving Repr, BEq

inductive CataClosure where
  | cclos : Bruijn → CataTerm → CataClosure
  | ccfail
  deriving Repr, BEq

abbrev CataClosureEnv := List CataClosure
abbrev CataStore := List (CataClosure × CataVal)

inductive CataEnvExt where
  | envEmpty
  | envCons : Bruijn → CataTerm → CataEnvExt → CataEnvExt
  deriving Repr, BEq

abbrev CataEnvList := List CataEnvExt

-- ============================================================
-- Free variable helper
-- ============================================================

def filterFV (fv : List Bruijn) : List Bruijn :=
  fv.filter (fun x => Bruijn.toNat x > 0) |>.map (fun x => Bruijn.ofNat (Bruijn.toNat x - 1))

-- ============================================================
-- Substitution and lifting
-- ============================================================

/-- Lift a term past n binders -/
-- Equation compiler style: generates simp lemmas (liftTerm_zero, liftTerm_succ_tvar, etc.)
-- that enable automated proofs in property tests.
def liftTerm : Nat → Nat → CataTerm → CataTerm
  | 0, d, t => t
  | Nat.succ m, d, .tvar x => if Bruijn.toNat x < d then .tvar (Bruijn.ofNat (Bruijn.toNat x + Nat.succ m)) else .tvar x
  | Nat.succ m, d, .tunit => .tunit
  | Nat.succ m, d, .tbool b => .tbool b
  | Nat.succ m, d, .tint i => .tint i
  | Nat.succ m, d, .tpair t1 t2 => .tpair (liftTerm (Nat.succ m) d t1) (liftTerm (Nat.succ m) d t2)
  | Nat.succ m, d, .tlam ty body => .tlam ty (liftTerm (Nat.succ m) d body)
  | Nat.succ m, d, .tapp t1 t2 => .tapp (liftTerm (Nat.succ m) d t1) (liftTerm (Nat.succ m) d t2)
  | Nat.succ m, d, .tproj i t' => .tproj i (liftTerm (Nat.succ m) d t')
  | Nat.succ m, d, .tconflict => .tconflict
  | Nat.succ m, d, .tclosure k body => .tclosure k (liftTerm (Nat.succ m) d body)
  | Nat.succ m, d, .tvsome t' => .tvsome (liftTerm (Nat.succ m) d t')
  | Nat.succ m, d, .tvnone => .tvnone
  | Nat.succ m, d, .tvpure t' => .tvpure (liftTerm (Nat.succ m) d t')
  | Nat.succ m, d, .tbinop op t1 t2 => .tbinop op (liftTerm (Nat.succ m) d t1) (liftTerm (Nat.succ m) d t2)
  | Nat.succ m, d, .tmatch scrut t1 t2 => .tmatch (liftTerm (Nat.succ m) d scrut) (liftTerm (Nat.succ m) d t1) (liftTerm (Nat.succ m) (d + 1) t2)
  | Nat.succ m, d, .tif cond ta tb => .tif (liftTerm (Nat.succ m) d cond) (liftTerm (Nat.succ m) d ta) (liftTerm (Nat.succ m) d tb)
  | Nat.succ m, d, .tfold f ts acc => .tfold (liftTerm (Nat.succ m) d f) (ts.map (fun t => liftTerm (Nat.succ m) d t)) (liftTerm (Nat.succ m) d acc)
  | Nat.succ m, d, .terrorOnEmpty t' => .terrorOnEmpty (liftTerm (Nat.succ m) d t')
  | Nat.succ m, d, .tdefaultPure t' => .tdefaultPure (liftTerm (Nat.succ m) d t')
  | Nat.succ m, d, .tdefault ts tj tc => .tdefault (ts.map (fun t => liftTerm (Nat.succ m) d t)) (liftTerm (Nat.succ m) d tj) (liftTerm (Nat.succ m) d tc)
  | Nat.succ m, d, .tempty => .tempty

/-- Lift a value past n binders -/
def liftVal (n d : Nat) (v : CataVal) : CataVal :=
  match v with
  | .tunit => .tunit
  | .tbool b => .tbool b
  | .tint i => .tint i
  | .tpair v1 v2 => .tpair (liftVal n d v1) (liftVal n d v2)
  | .tclosure k body => .tclosure k (liftTerm n d body)
  | .tvsome v' => .tvsome (liftVal n d v')
  | .tvnone => .tvnone
  | .tvpure v' => .tvpure (liftVal n d v')
  | _ => v

/-- Substitution at variable -/
def substVar (s : CataTerm) (x : Bruijn) (n : Nat) : CataTerm :=
  match x, n with
  | Bruijn.zero, 0 => s
  | Bruijn.zero, _ => .tvar Bruijn.zero
  | Bruijn.succ _, 0 => .tvar x
  | Bruijn.succ x', Nat.succ m => .tvar (Bruijn.succ x')

/-- Substitution at de Bruijn index n -/
-- NOTE: kept `partial` — calls `liftTerm 1 0 s` (non-structural argument) in .tlam/.tmatch
partial def substTerm (s t : CataTerm) (n : Nat) : CataTerm :=
  match t with
  | .tvar x => substVar s x n
  | .tunit => .tunit
  | .tbool b => .tbool b
  | .tint i => .tint i
  | .tpair t1 t2 => .tpair (substTerm s t1 n) (substTerm s t2 n)
  | .tlam ty body => .tlam ty (substTerm (liftTerm 1 0 s) body (n + 1))
  | .tapp t1 t2 => .tapp (substTerm s t1 n) (substTerm s t2 n)
  | .tproj i t' => .tproj i (substTerm s t' n)
  | .tconflict => .tconflict
  | .tclosure k body => .tclosure k (substTerm s body n)
  | .tvsome t' => .tvsome (substTerm s t' n)
  | .tvnone => .tvnone
  | .tvpure t' => .tvpure (substTerm s t' n)
  | .tbinop op t1 t2 => .tbinop op (substTerm s t1 n) (substTerm s t2 n)
  | .tmatch scrut t1 t2 => .tmatch (substTerm s scrut n) (substTerm s t1 n) (substTerm (liftTerm 1 0 s) t2 (n + 1))
  | .tif cond ta tb => .tif (substTerm s cond n) (substTerm s ta n) (substTerm s tb n)
  | .tfold f ts acc => .tfold (substTerm s f n) (ts.map (fun t => substTerm s t n)) (substTerm s acc n)
  | .terrorOnEmpty t' => .terrorOnEmpty (substTerm s t' n)
  | .tdefaultPure t' => .tdefaultPure (substTerm s t' n)
  | .tdefault ts tj tc => .tdefault (ts.map (fun t => substTerm s t n)) (substTerm s tj n) (substTerm s tc n)
  | .tempty => .tempty

/-- Substitution at value -/
-- NOTE: kept `partial` — calls substTerm (which is partial)
partial def substVal (s : CataTerm) (v : CataVal) (n : Nat) : CataVal :=
  match v with
  | .tunit => .tunit
  | .tbool b => .tbool b
  | .tint i => .tint i
  | .tpair v1 v2 => .tpair (substVal s v1 n) (substVal s v2 n)
  | .tclosure k body => .tclosure k (substTerm s body n)
  | .tvsome v' => .tvsome (substVal s v' n)
  | .tvnone => .tvnone
  | .tvpure v' => .tvpure (substVal s v' n)
  | _ => v

def substTerm0 (s t : CataTerm) : CataTerm := substTerm s t 0
def substVal0 (s : CataTerm) (v : CataVal) : CataVal := substVal s v 0

-- ============================================================
-- Environment operations
-- ============================================================

def envLookup (e : CataEnv) (n : Nat) : Option CataType :=
  if n = 0 then
    match e with
    | (name, ty) :: _ => some ty
    | [] => none
  else
    match e with
    | _ :: rest => envLookup rest (n - 1)
    | [] => none

def envCons (name : String) (t : CataType) (e : CataEnv) : CataEnv :=
  (name, t) :: e

def scons (x : Bruijn) (t : CataTerm) (env : CataSEnv) : CataSEnv :=
  (x, t) :: env

def slookup (x : Bruijn) (env : CataSEnv) : Option CataTerm :=
  match List.find? (fun p => p.1 = x) env with
  | some p => some p.2
  | none => none

def snil (env : CataSEnv) : CataSEnv := env

def sconsEnv (x : Bruijn) (t : CataTerm) (env : CataSEnv) : CataSEnv :=
  (x, t) :: env

def sconsEnvN (x : Bruijn) (w : Bruijn) (env : CataSEnv) : CataSEnv :=
  match env with
  | [] => [(Bruijn.succ w, .tvar Bruijn.zero)]
  | h :: t =>
    if w = Bruijn.zero then
      (x, .tvar Bruijn.zero) :: env
    else
      (h.1, .tvar (Bruijn.succ (Bruijn.ofNat (Bruijn.toNat h.1 + 1)))) :: sconsEnvN x (Bruijn.succ w) t

def sidentity : CataSEnv := []

-- ============================================================
-- Well-formedness and typing invariants
-- ============================================================

def typeValid (t : CataType) : Bool :=
  match t with
  | .conflict => false
  | .unitT | .boolT | .intT => true
  | .funT t1 t2 | .prodT t1 t2 | .arrowT t1 t2 | .arrowProdT t1 t2 | .arrowListT t1 t2 =>
    typeValid t1 && typeValid t2

/-- Check if a term is well-formed -/
-- NOTE: kept `partial` — list elements in .tfold/.tdefault aren't structural subterms
partial def termValid (t : CataTerm) : Bool :=
  match t with
  | .tvar _ | .tconflict => true
  | .tunit | .tbool _ | .tint _ => true
  | .tpair t1 t2 => termValid t1 && termValid t2
  | .tlam _ body => termValid body
  | .tapp t1 t2 => termValid t1 && termValid t2
  | .tproj _ t' => termValid t'
  | .tclosure _ body => termValid body
  | .tvsome t' => termValid t'
  | .tvnone => true
  | .tvpure t' => termValid t'
  | .tbinop _ t1 t2 => termValid t1 && termValid t2
  | .tmatch scrut t1 t2 => termValid scrut && termValid t1 && termValid t2
  | .tif cond ta tb => termValid cond && termValid ta && termValid tb
  | .tfold f ts acc => termValid f && ts.all termValid && termValid acc
  | .terrorOnEmpty t' => termValid t'
  | .tdefaultPure t' => termValid t'
  | .tdefault ts tj tc => ts.all termValid && termValid tj && termValid tc
  | .tempty => true

/-- Check if a value is well-formed -/
def valueValid (v : CataVal) : Bool :=
  match v with
  | .tunit | .tbool _ | .tint _ | .tvnone => true
  | .tpair v1 v2 => valueValid v1 && valueValid v2
  | .tclosure _ body => termValid body
  | .tvsome v' => valueValid v'
  | .tvpure v' => valueValid v'
  | _ => false

/-- Compute free variables in a term -/
def freeVarsTerm (t : CataTerm) : List Bruijn :=
  match t with
  | .tvar x => [x]
  | .tunit | .tbool _ | .tint _ | .tconflict | .tvnone | .tempty => []
  | .tpair t1 t2 => freeVarsTerm t1 ++ freeVarsTerm t2
  | .tlam _ body => filterFV (freeVarsTerm body)
  | .tapp t1 t2 => freeVarsTerm t1 ++ freeVarsTerm t2
  | .tproj _ t' => freeVarsTerm t'
  | .tclosure _ body => filterFV (freeVarsTerm body)
  | .tvsome t' | .tvpure t' => freeVarsTerm t'
  | .tbinop _ t1 t2 => freeVarsTerm t1 ++ freeVarsTerm t2
  | .tmatch scrut t1 t2 => freeVarsTerm scrut ++ freeVarsTerm t1 ++ filterFV (freeVarsTerm t2)
  | .tif cond ta tb => freeVarsTerm cond ++ freeVarsTerm ta ++ freeVarsTerm tb
  | .tfold f ts acc => freeVarsTerm f ++ List.flatMap freeVarsTerm ts ++ freeVarsTerm acc
  | .terrorOnEmpty t' => freeVarsTerm t'
  | .tdefaultPure t' => freeVarsTerm t'
  | .tdefault ts tj tc => List.flatMap freeVarsTerm ts ++ freeVarsTerm tj ++ freeVarsTerm tc

end CatalaLean
