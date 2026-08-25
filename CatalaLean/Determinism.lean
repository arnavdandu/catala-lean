import CatalaLean.SmallStep
import CatalaLean.Typing

namespace CatalaLean

/-! # Determinism of small-step reduction

Hybrid strategy: families whose rules overlap on value-headed subterms get
explicit inversion lemmas (so dependent elimination never unifies through
opaque `termOf`); all other cases use plain `cases`. -/

/-- No reduction exists out of a term headed by `termOf`. -/
theorem not_red_termOf {v : Val} {t : CataTerm} (h : red (termOf v) t) : False :=
  val_irred v t h

/-- No reduction exists out of `.tvsome (termOf v)`. -/
theorem tvsome_term_irred {v : Val} {t : CataTerm} :
    ¬ red (CataTerm.tvsome (termOf v)) t := fun hc => by cases hc

/-! ## Inversion lemmas -/

theorem red_tapp_inv {a b c : CataTerm} (h : red (.tapp a b) c) :
    (∃ a', red a a' ∧ c = .tapp a' b) ∨
    (∃ v1 b', a = termOf v1 ∧ red b b' ∧ c = .tapp (termOf v1) b') ∨
    (∃ k body w, a = .tclosure k body ∧ b = termOf w ∧
      c = substValTerm w body k) := by
  cases h with
  | app_l ha => exact Or.inl ⟨_, ha, rfl⟩
  | app_r hb => exact Or.inr (Or.inl ⟨_, _, rfl, hb, rfl⟩)
  | beta => exact Or.inr (Or.inr ⟨_, _, _, rfl, rfl, rfl⟩)

theorem red_tbinop_inv {op : CataOp} {a b c : CataTerm} (h : red (.tbinop op a b) c) :
    (∃ a', red a a' ∧ c = .tbinop op a' b) ∨
    (∃ v1 b', a = termOf v1 ∧ red b b' ∧ c = .tbinop op (termOf v1) b') ∨
    (∃ v1 v2 w, a = termOf v1 ∧ b = termOf v2 ∧
      getOp op (termOf v1) (termOf v2) = some (termOf w) ∧ c = termOf w) := by
  cases h with
  | binop_l ha => exact Or.inl ⟨_, ha, rfl⟩
  | binop_r hb => exact Or.inr (Or.inl ⟨_, _, rfl, hb, rfl⟩)
  | binop_eval hh => exact Or.inr (Or.inr ⟨_, _, _, rfl, rfl, hh, rfl⟩)

theorem red_tmatch_inv {s x y c : CataTerm} (h : red (.tmatch s x y) c) :
    (∃ s', red s s' ∧ c = .tmatch s' x y) ∨
    (s = .tvnone ∧ c = x) ∨
    (∃ w, s = CataTerm.tvsome (termOf w) ∧ c = substValTerm w y Bruijn.zero) := by
  cases h with
  | match_l ha => exact Or.inl ⟨_, ha, rfl⟩
  | match_none => exact Or.inr (Or.inl ⟨rfl, rfl⟩)
  | @match_some w => exact Or.inr (Or.inr ⟨w, rfl, rfl⟩)

theorem red_teoe_inv {a c : CataTerm} (h : red (.terrorOnEmpty a) c) :
    (∃ a', red a a' ∧ c = .terrorOnEmpty a') ∨
    (a = .tvnone ∧ c = .tconflict) ∨
    (∃ w, a = CataTerm.tvsome (termOf w) ∧ c = termOf w) := by
  cases h with
  | eoe_l ha => exact Or.inl ⟨_, ha, rfl⟩
  | eoe_none => exact Or.inr (Or.inl ⟨rfl, rfl⟩)
  | @eoe_some w => exact Or.inr (Or.inr ⟨w, rfl, rfl⟩)

theorem red_tdpure_inv {a c : CataTerm} (h : red (.tdefaultPure a) c) :
    (∃ a', red a a' ∧ c = .tdefaultPure a') ∨
    (∃ w, a = termOf w ∧ c = .tvpure (termOf w)) := by
  cases h with
  | dpure_l ha => exact Or.inl ⟨_, ha, rfl⟩
  | @dpure_val w => exact Or.inr ⟨w, rfl, rfl⟩

/-! ## Main theorem -/

theorem red_det : ∀ {t t1 t2 : CataTerm}, red t t1 → red t t2 → t1 = t2 := by
  intro t t1 t2 h1
  induction h1 generalizing t2 with
  | app_l a ih =>
    rename_i x x' b
    intro h2
    rcases red_tapp_inv h2 with ⟨y, hy, he⟩ | ⟨v1, z, he1, hz, he⟩ |
      ⟨k, body, w, he1, he2, he⟩
    · rw [he]; exact congrArg (CataTerm.tapp · b) (ih hy)
    · rw [he1] at a; exact absurd a not_red_termOf
    · rw [he1] at a; exact absurd a (val_irred (.closure k body) _)
  | app_r a ih =>
    rename_i v1 u u'
    intro h2
    rcases red_tapp_inv h2 with ⟨y, hy, he⟩ | ⟨v1', z, he1, hz, he⟩ |
      ⟨k, body, w, he1, he2, he⟩
    · exact absurd hy not_red_termOf
    · have hv : v1 = v1' := termOf_inj _ _ he1
      subst hv
      rw [he]; exact congrArg (CataTerm.tapp (termOf v1) ·) (ih hz)
    · rw [he2] at a; exact absurd a not_red_termOf
  | beta =>
    rename_i k body w
    intro h2
    rcases red_tapp_inv (a:=.tclosure k body) (b:=termOf w) h2 with
      ⟨y, hy, he⟩ | ⟨v1, z, he1, hz, he⟩ | ⟨k', body', w', he1, he2, he⟩
    · cases hy
    · exact absurd hz not_red_termOf
    · injection he1 with hk hb
      have hv : w' = w := termOf_inj _ _ he2.symm
      subst hk; subst hb; subst hv
      rw [he]
  | binop_l a ih =>
    rename_i op x y z
    intro h2
    rcases red_tbinop_inv h2 with ⟨y', hy, he⟩ | ⟨v1, w', he1, hw, he⟩ |
      ⟨v1, v2, w, he1, he2, hh, he⟩
    · rw [he]; exact congrArg (CataTerm.tbinop op · z) (ih hy)
    · rw [he1] at a; exact absurd a not_red_termOf
    · rw [he1] at a; exact absurd a not_red_termOf
  | binop_r a ih =>
    rename_i op v1 y z
    intro h2
    rcases red_tbinop_inv h2 with ⟨y', hy, he⟩ | ⟨v1', w', he1, hw, he⟩ |
      ⟨v1'', v2, w, he1, he2, hh, he⟩
    · exact absurd hy not_red_termOf
    · have hv : v1 = v1' := termOf_inj _ _ he1
      subst hv
      rw [he]; exact congrArg (CataTerm.tbinop op (termOf v1) ·) (ih hw)
    · have hv : v1 = v1'' := termOf_inj _ _ he1
      subst hv
      rw [he2] at a
      exact absurd a not_red_termOf
  | binop_eval hget =>
    rename_i op v1 v2 w
    intro h2
    rcases red_tbinop_inv h2 with ⟨y, hy, he⟩ | ⟨v1', z, he1, hz, he⟩ |
      ⟨v1'', v2', w', he1, he2, hh2, he⟩
    · exact absurd hy not_red_termOf
    · exact absurd hz not_red_termOf
    · rw [he]
      have g1 : v1 = v1'' := termOf_inj _ _ he1
      have g2 : v2 = v2' := termOf_inj _ _ he2
      subst g1; subst g2
      rw [hget] at hh2
      injection hh2 with hh2
  | match_l a ih =>
    rename_i u u' x y
    intro h2
    rcases red_tmatch_inv h2 with ⟨s', hs, he⟩ | ⟨he1, he2⟩ | ⟨w, he1, he2⟩
    · rw [he]; exact congrArg (CataTerm.tmatch · x y) (ih hs)
    · rw [he1] at a; cases a
    · rw [he1] at a; exact absurd a tvsome_term_irred
  | match_none =>
    rename_i x y
    intro h2
    rcases red_tmatch_inv h2 with ⟨s', hs, he⟩ | ⟨he1, he2⟩ | ⟨w, he1, he2⟩
    · cases hs
    · rw [he2]
    · exact CataTerm.noConfusion he1
  | match_some =>
    rename_i w x y
    intro h2
    rcases red_tmatch_inv h2 with hA | hB | hC
    · obtain ⟨s', hs', he⟩ := hA
      subst he
      exact absurd hs' tvsome_term_irred
    · obtain ⟨heq1, heq2⟩ := hB
      exact CataTerm.noConfusion heq1
    · obtain ⟨w', he1, he2⟩ := hC
      rw [he2]
      injection he1 with hcon
      have hv : w' = w := termOf_inj _ _ hcon.symm
      subst hv
      rfl
  | if_l a ih =>
    rename_i c c' ta tb
    intro h2
    cases h2 with
    | if_l hb => exact congrArg (CataTerm.tif · ta tb) (ih hb)
    | if_true => exfalso; cases a
    | if_false => exfalso; cases a
  | if_true =>
    rename_i ta tb
    intro h2
    cases h2 with
    | if_l hb => cases hb
    | if_true => rfl
  | if_false =>
    rename_i ta tb
    intro h2
    cases h2 with
    | if_l hb => cases hb
    | if_false => rfl
  | default hne =>
    rename_i t s tj tc
    intro h2
    cases h2 with
    | default _ => rfl
    | default_empty => exact absurd rfl hne
  | default_base =>
    rename_i tc
    intro h2
    cases h2 with
    | default_base => rfl
  | default_empty =>
    rename_i ts tj tc
    intro h2
    cases h2 with
    | default hne2 => exact absurd rfl hne2
    | default_empty => rfl
  | fold_l ha hne ih =>
    rename_i f ts acc acc'
    intro h2
    cases h2 with
    | fold_l hb _ => exact congrArg (CataTerm.tfold f ts · ) (ih hb)
    | fold_nil => exact absurd rfl hne
  | fold_nil =>
    rename_i f acc
    intro h2
    cases h2 with
    | fold_l _ hne2 => exact absurd rfl hne2
    | fold_nil => rfl
  | eoe_l a ih =>
    rename_i u u'
    intro h2
    rcases red_teoe_inv h2 with ⟨x, hx, he⟩ | ⟨he1, he2⟩ | ⟨w, he1, he2⟩
    · rw [he]; exact congrArg CataTerm.terrorOnEmpty (ih hx)
    · rw [he1] at a; cases a
    · rw [he1] at a; exact absurd a tvsome_term_irred
  | eoe_none =>
    intro h2
    rcases red_teoe_inv h2 with ⟨x, hx, he⟩ | ⟨he1, he2⟩ | ⟨w, he1, he2⟩
    · cases hx
    · rw [he2]
    · exact CataTerm.noConfusion he1
  | eoe_some =>
    rename_i w
    intro h2
    rcases red_teoe_inv h2 with hA | hB | hC
    · obtain ⟨x, hx, he⟩ := hA
      rw [he]; cases hx
    · obtain ⟨heq1, heq2⟩ := hB
      exact CataTerm.noConfusion heq1
    · obtain ⟨w', he1, he2⟩ := hC
      rw [he2]
      injection he1
  | dpure_l a ih =>
    rename_i u u'
    intro h2
    rcases red_tdpure_inv h2 with ⟨x, hx, he⟩ | ⟨w, he1, he2⟩
    · rw [he]; exact congrArg CataTerm.tdefaultPure (ih hx)
    · rw [he1] at a; exact absurd a not_red_termOf
  | dpure_val =>
    rename_i w
    intro h2
    rcases red_tdpure_inv h2 with ⟨x, hx, he⟩ | ⟨w', he1, he2⟩
    · exact absurd hx not_red_termOf
    · rw [he2]
      have hv : w' = w := termOf_inj _ _ he1.symm
      subst hv
      rfl
  | empty_none =>
    intro h2
    cases h2 with
    | empty_none => rfl

end CatalaLean
