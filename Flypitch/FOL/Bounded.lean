import Flypitch.FOL.Theory

universe u

namespace Flypitch
namespace fol

/-!
`Flypitch.FOL.Bounded` packages terms and formulas together with proofs that their free
variables stay below a prescribed bound. These bounded wrappers are used to represent
closed syntax and to build Henkin witnesses later in the development.
-/

set_option linter.missingDocs false

local notation "[]" => dvector.nil
local infixr:67 " :: " => dvector.cons

/-- Terms with free variables bounded by `n`. -/
def bounded_preterm (L : Language.{u}) (n : Nat) (l : Nat) : Type u :=
  { t : preterm L l // bounded_term_at t n }

/-- Closed terms with free variables bounded by `n`. -/
abbrev bounded_term (L : Language.{u}) (n : Nat) : Type u :=
  bounded_preterm L n 0

/-- Closed partially applied terms. -/
abbrev closed_preterm (L : Language.{u}) (l : Nat) : Type u :=
  bounded_preterm L 0 l

/-- Closed terms, i.e. terms with no free variables. -/
abbrev closed_term (L : Language.{u}) : Type u :=
  bounded_term L 0

namespace bounded_preterm

variable {L : Language.{u}} {n m l : Nat}

instance : CoeOut (bounded_preterm L n l) (preterm L l) where
  coe := Subtype.val

@[simp] def fst (t : bounded_preterm L n l) : preterm L l :=
  t.1

/-- Eta-expansion for bounded terms as subtypes. -/
theorem eta (t : bounded_preterm L n l) : Subtype.mk t.1 t.2 = t := by
  cases t
  rfl

/-- Reinterpret a bounded term at a larger variable bound. -/
def cast (h : n ≤ m) (t : bounded_preterm L n l) : bounded_preterm L m l :=
  ⟨t.1, bounded_term_at_mono t.1 t.2 h⟩

/-- A bounded term remains bounded when the bound is increased by one. -/
def cast1 (t : bounded_preterm L n l) : bounded_preterm L (n + 1) l :=
  cast (Nat.le_succ n) t

theorem cast_fst (h : n ≤ m) (t : bounded_preterm L n l) :
    (t.cast h).fst = t.fst :=
  rfl

theorem cast1_fst (t : bounded_preterm L n l) :
    (t.cast1).fst = t.fst :=
  rfl

end bounded_preterm

variable {L : Language.{u}}

/-- Lifting a bounded term preserves boundedness after increasing the free-variable bound. -/
theorem bounded_term_at_lift_at : {l : Nat} → (t : preterm L l) → {n k m : Nat} →
    bounded_term_at t n → bounded_term_at (lift_term_at t k m) (n + k)
  | _, .var i, _, k, m, hi => by
      by_cases hmi : m ≤ i
      · simp [lift_term_at, hmi, Nat.add_lt_add_right hi k]
      · simp [lift_term_at, hmi, lt_of_lt_of_le hi (Nat.le_add_right _ _)]
  | _, .func _, _, _, _, _ => trivial
  | _, .app t₁ t₂, _, _, _, h => by
      exact ⟨bounded_term_at_lift_at t₁ h.1, bounded_term_at_lift_at t₂ h.2⟩

/-- Lifting a bounded formula preserves boundedness after increasing the free-variable bound. -/
theorem bounded_formula_at_lift_at : {l : Nat} → (f : preformula L l) → {n k m : Nat} →
    bounded_formula_at f n → bounded_formula_at (lift_formula_at f k m) (n + k)
  | _, .falsum, _, _, _, _ => trivial
  | _, .equal t₁ t₂, _, _, _, h => by
      exact ⟨bounded_term_at_lift_at t₁ h.1, bounded_term_at_lift_at t₂ h.2⟩
  | _, .rel _, _, _, _, _ => trivial
  | _, .apprel f t, _, _, _, h => by
      exact ⟨bounded_formula_at_lift_at f h.1, bounded_term_at_lift_at t h.2⟩
  | _, .imp f₁ f₂, _, _, _, h => by
      exact ⟨bounded_formula_at_lift_at f₁ h.1, bounded_formula_at_lift_at f₂ h.2⟩
  | _, .all f, n, k, m, h => by
      simpa [lift_formula_at, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        (bounded_formula_at_lift_at f (n := n + 1) (k := k) (m := m + 1) h)

namespace bounded_preterm

variable {L : Language.{u}} {n l : Nat}

/-- Lift free variables in a bounded term, increasing the bound accordingly. -/
def liftAt (t : bounded_preterm L n l) (k m : Nat) : bounded_preterm L (n + k) l :=
  ⟨lift_term_at t.fst k m, bounded_term_at_lift_at t.fst t.2⟩

/-- Lift all free variables in a bounded term by one. -/
def lift1 (t : bounded_preterm L n l) : bounded_preterm L (n + 1) l :=
  t.liftAt 1 0

@[simp] theorem liftAt_fst (t : bounded_preterm L n l) (k m : Nat) :
    (t.liftAt k m).fst = lift_term_at t.fst k m :=
  rfl

@[simp] theorem lift1_fst (t : bounded_preterm L n l) :
    t.lift1.fst = lift_term_at t.fst 1 0 :=
  rfl

end bounded_preterm

/-- The bounded variable corresponding to an element of `Fin n`. -/
def bd_var {n : Nat} (k : Fin n) : bounded_term L n :=
  ⟨&k.1, k.2⟩

/-- A function symbol viewed as a bounded partially applied term. -/
def bd_func {n l : Nat} (f : L.functions l) : bounded_preterm L n l :=
  ⟨preterm.func f, trivial⟩

/-- Application of bounded terms preserves boundedness. -/
def bd_app {n l : Nat} (t : bounded_preterm L n (l + 1)) (s : bounded_term L n) :
    bounded_preterm L n l :=
  ⟨preterm.app t.1 s.1, ⟨t.2, s.2⟩⟩

/-- Constants are exactly bounded nullary function symbols. -/
def bd_const {n : Nat} (c : L.constants) : bounded_term L n :=
  bd_func c

/-- Fully apply a bounded partially applied term to bounded arguments. -/
@[simp] def bd_apps : {n l : Nat} → bounded_preterm L n l →
    dvector (bounded_term L n) l → bounded_term L n
  | _, 0, t, [] => t
  | _, _ + 1, t, s :: ts => bd_apps (bd_app t s) ts

/-- Formulas with free variables bounded by `n`. -/
def bounded_preformula (L : Language.{u}) (n : Nat) (l : Nat) : Type u :=
  { f : preformula L l // bounded_formula_at f n }

/-- Closed formulas with free variables bounded by `n`. -/
abbrev bounded_formula (L : Language.{u}) (n : Nat) : Type u :=
  bounded_preformula L n 0

/-- Closed partially applied formulas. -/
abbrev presentence (L : Language.{u}) (l : Nat) : Type u :=
  bounded_preformula L 0 l

namespace bounded_preformula

variable {L : Language.{u}} {n m l : Nat}

instance : CoeOut (bounded_preformula L n l) (preformula L l) where
  coe := Subtype.val

@[simp] def fst (f : bounded_preformula L n l) : preformula L l :=
  f.1

/-- Eta-expansion for bounded formulas as subtypes. -/
theorem eta (f : bounded_preformula L n l) : Subtype.mk f.1 f.2 = f := by
  cases f
  rfl

/-- Reinterpret a bounded formula at a larger free-variable bound. -/
def cast (h : n ≤ m) (f : bounded_preformula L n l) : bounded_preformula L m l :=
  ⟨f.1, bounded_formula_at_mono f.1 f.2 h⟩

/-- A bounded formula remains bounded when the bound is increased by one. -/
def cast1 (f : bounded_preformula L n l) : bounded_preformula L (n + 1) l :=
  cast (Nat.le_succ n) f

theorem cast_fst (h : n ≤ m) (f : bounded_preformula L n l) :
    (f.cast h).fst = f.fst :=
  rfl

theorem cast1_fst (f : bounded_preformula L n l) :
    (f.cast1).fst = f.fst :=
  rfl

end bounded_preformula

variable {L : Language.{u}}

namespace bounded_preformula

variable {L : Language.{u}} {n l : Nat}

/-- Lift free variables in a bounded formula, increasing the bound accordingly. -/
def liftAt (f : bounded_preformula L n l) (k m : Nat) : bounded_preformula L (n + k) l :=
  ⟨lift_formula_at f.fst k m, bounded_formula_at_lift_at f.fst f.2⟩

/-- Lift all free variables in a bounded formula by one. -/
def lift1 (f : bounded_preformula L n l) : bounded_preformula L (n + 1) l :=
  f.liftAt 1 0

@[simp] theorem liftAt_fst (f : bounded_preformula L n l) (k m : Nat) :
    (f.liftAt k m).fst = lift_formula_at f.fst k m :=
  rfl

@[simp] theorem lift1_fst (f : bounded_preformula L n l) :
    f.lift1.fst = lift_formula_at f.fst 1 0 :=
  rfl

end bounded_preformula

/-- The bounded version of falsum. -/
def bd_falsum {n : Nat} : bounded_formula L n :=
  ⟨⊥, trivial⟩

/-- Equality of bounded terms as a bounded formula. -/
def bd_equal {n : Nat} (t₁ t₂ : bounded_term L n) : bounded_formula L n :=
  ⟨t₁.1 ≃ t₂.1, ⟨t₁.2, t₂.2⟩⟩

/-- A relation symbol viewed as a bounded partially applied formula. -/
def bd_rel {n l : Nat} (R : L.relations l) : bounded_preformula L n l :=
  ⟨preformula.rel R, trivial⟩

/-- Apply a bounded partially applied formula to a bounded term. -/
def bd_apprel {n l : Nat} (f : bounded_preformula L n (l + 1)) (t : bounded_term L n) :
    bounded_preformula L n l :=
  ⟨preformula.apprel f.1 t.1, ⟨f.2, t.2⟩⟩

/-- Implication preserves boundedness. -/
def bd_imp {n : Nat} (f₁ f₂ : bounded_formula L n) : bounded_formula L n :=
  ⟨f₁.1 ⟹ f₂.1, ⟨f₁.2, f₂.2⟩⟩

/-- Universal quantification lowers the free-variable bound by one. -/
def bd_all {n : Nat} (f : bounded_formula L (n + 1)) : bounded_formula L n :=
  ⟨∀' f.1, f.2⟩

instance {n : Nat} : Bot (bounded_formula L n) where
  bot := bd_falsum

/-- Negation on bounded formulas. -/
def bd_not {n : Nat} (f : bounded_formula L n) : bounded_formula L n :=
  bd_imp f bd_falsum

/-- Conjunction on bounded formulas. -/
def bd_and {n : Nat} (f₁ f₂ : bounded_formula L n) : bounded_formula L n :=
  bd_not (bd_imp f₁ (bd_not f₂))

/-- Disjunction on bounded formulas. -/
def bd_or {n : Nat} (f₁ f₂ : bounded_formula L n) : bounded_formula L n :=
  bd_imp (bd_not f₁) f₂

/-- Biconditional on bounded formulas. -/
def bd_biimp {n : Nat} (f₁ f₂ : bounded_formula L n) : bounded_formula L n :=
  bd_and (bd_imp f₁ f₂) (bd_imp f₂ f₁)

/-- Existential quantification on bounded formulas. -/
def bd_ex {n : Nat} (f : bounded_formula L (n + 1)) : bounded_formula L n :=
  bd_not (bd_all (bd_not f))

/-- Fully apply a bounded relation formula to bounded arguments. -/
@[simp] def bd_apps_rel : {n l : Nat} → bounded_preformula L n l →
    dvector (bounded_term L n) l → bounded_formula L n
  | _, 0, f, [] => f
  | _, _ + 1, f, t :: ts => bd_apps_rel (bd_apprel f t) ts

theorem bd_var_fst {n : Nat} (k : Fin n) :
    (bd_var (L := L) k).fst = (&k.1 : term L) :=
  rfl

theorem bd_func_fst {n l : Nat} (f : L.functions l) :
    (bd_func (L := L) (n := n) f).fst = preterm.func f :=
  rfl

theorem bd_app_fst {n l : Nat} (t : bounded_preterm L n (l + 1)) (s : bounded_term L n) :
    (bd_app t s).fst = preterm.app t.fst s.fst :=
  rfl

theorem bd_equal_fst {n : Nat} (t₁ t₂ : bounded_term L n) :
    (bd_equal t₁ t₂).fst = (t₁.fst ≃ t₂.fst) :=
  rfl

theorem bd_rel_fst {n l : Nat} (R : L.relations l) :
    (bd_rel (L := L) (n := n) R).fst = preformula.rel R :=
  rfl

theorem bd_apprel_fst {n l : Nat} (f : bounded_preformula L n (l + 1))
    (t : bounded_term L n) :
    (bd_apprel f t).fst = preformula.apprel f.fst t.fst :=
  rfl

theorem bd_imp_fst {n : Nat} (f₁ f₂ : bounded_formula L n) :
    (bd_imp f₁ f₂).fst = (f₁.fst ⟹ f₂.fst) :=
  rfl

theorem bd_all_fst {n : Nat} (f : bounded_formula L (n + 1)) :
    (bd_all f).fst = ∀' f.fst :=
  rfl

theorem bd_not_fst {n : Nat} (f : bounded_formula L n) :
    (bd_not f).fst = ∼f.fst :=
  rfl

theorem bd_and_fst {n : Nat} (f₁ f₂ : bounded_formula L n) :
    (bd_and f₁ f₂).fst = and f₁.fst f₂.fst :=
  rfl

theorem bd_or_fst {n : Nat} (f₁ f₂ : bounded_formula L n) :
    (bd_or f₁ f₂).fst = or f₁.fst f₂.fst :=
  rfl

theorem bd_biimp_fst {n : Nat} (f₁ f₂ : bounded_formula L n) :
    (bd_biimp f₁ f₂).fst = biimp f₁.fst f₂.fst :=
  rfl

theorem bd_ex_fst {n : Nat} (f : bounded_formula L (n + 1)) :
    (bd_ex f).fst = ex f.fst :=
  rfl

/-- Evaluate a bounded term using only the bounded part of a valuation. -/
def realize_bounded_term {M : Structure L} {n : Nat} (v : dvector M.carrier n) :
    {l : Nat} → bounded_preterm L n l → dvector M.carrier l → M.carrier
  | _, ⟨preterm.var k, hk⟩, _ => v.nth k hk
  | _, ⟨preterm.func f, _⟩, xs => M.fun_map f xs
  | _, ⟨preterm.app t₁ t₂, h⟩, xs =>
      realize_bounded_term v ⟨t₁, h.1⟩
        (dvector.cons (realize_bounded_term v ⟨t₂, h.2⟩ dvector.nil) xs)
termination_by l t xs => sizeOf t.1
decreasing_by
  all_goals
    try simp_wf
    try omega

/-- Evaluate a closed term. -/
@[reducible] def realize_closed_term (M : Structure L) (t : closed_term L) : M.carrier :=
  realize_bounded_term (dvector.nil : dvector M.carrier 0) t dvector.nil

/-- A bounded valuation agrees with any total valuation that matches it on the bounded range. -/
theorem realize_bounded_term_eq {M : Structure L} {n : Nat}
    {v₁ : dvector M.carrier n} {v₂ : Nat → M.carrier}
    (hv : ∀ k (hk : k < n), v₁.nth k hk = v₂ k) :
    {l : Nat} → (t : bounded_preterm L n l) → (xs : dvector M.carrier l) →
      realize_bounded_term v₁ t xs = realize_term v₂ t.fst xs
  | _, ⟨preterm.var k, hk⟩, _ => by simp [realize_bounded_term, realize_term, hv k hk]
  | _, ⟨preterm.func f, _⟩, _ => by simp [realize_bounded_term, realize_term]
  | _, ⟨preterm.app t₁ t₂, h⟩, xs => by
      have ht₂ :
          realize_bounded_term v₁ ⟨t₂, h.2⟩ dvector.nil = realize_term v₂ t₂ dvector.nil :=
        realize_bounded_term_eq hv ⟨t₂, h.2⟩ dvector.nil
      simpa [realize_bounded_term, realize_term, ht₂] using
        (realize_bounded_term_eq hv ⟨t₁, h.1⟩
          (dvector.cons (realize_term v₂ t₂ dvector.nil) xs))
termination_by l t xs => sizeOf t.1
decreasing_by
  all_goals
    try simp_wf
    try omega

/-- Evaluate a bounded formula using only the bounded part of a valuation. -/
def realize_bounded_formula {M : Structure L} :
    {n l : Nat} → dvector M.carrier n → bounded_preformula L n l → dvector M.carrier l → Prop
  | _, _, _, ⟨preformula.falsum, _⟩, _ => False
  | _, _, v, ⟨preformula.equal t₁ t₂, h⟩, xs =>
      realize_bounded_term v ⟨t₁, h.1⟩ xs = realize_bounded_term v ⟨t₂, h.2⟩ xs
  | _, _, _, ⟨preformula.rel R, _⟩, xs => M.rel_map R xs
  | _, _, v, ⟨preformula.apprel f t, h⟩, xs =>
      realize_bounded_formula v ⟨f, h.1⟩
        (dvector.cons (realize_bounded_term v ⟨t, h.2⟩ dvector.nil) xs)
  | _, _, v, ⟨preformula.imp f₁ f₂, h⟩, xs =>
      realize_bounded_formula v ⟨f₁, h.1⟩ xs → realize_bounded_formula v ⟨f₂, h.2⟩ xs
  | _, _, v, ⟨preformula.all f, h⟩, xs =>
      ∀ x : M.carrier, realize_bounded_formula (dvector.cons x v) ⟨f, h⟩ xs
termination_by n l v f xs => sizeOf f.1
decreasing_by
  all_goals
    try simp_wf
    try omega

/-- Bounded formula realization agrees with ordinary realization under matching valuations. -/
  theorem realize_bounded_formula_iff {M : Structure L} {n : Nat}
    {v₁ : dvector M.carrier n} {v₂ : Nat → M.carrier}
    (hv : ∀ k (hk : k < n), v₁.nth k hk = v₂ k) :
    {l : Nat} → (f : bounded_preformula L n l) → (xs : dvector M.carrier l) →
      realize_bounded_formula v₁ f xs ↔ realize_formula v₂ f.fst xs
  | _, ⟨preformula.falsum, _⟩, _ => by simp [realize_bounded_formula, realize_formula]
  | _, ⟨preformula.equal t₁ t₂, h⟩, xs => by
      simp [realize_bounded_formula, realize_formula,
        realize_bounded_term_eq (v₁ := v₁) (v₂ := v₂) (hv := hv)
          (t := ⟨t₁, h.1⟩) (xs := xs),
        realize_bounded_term_eq (v₁ := v₁) (v₂ := v₂) (hv := hv)
          (t := ⟨t₂, h.2⟩) (xs := xs)]
  | _, ⟨preformula.rel R, _⟩, _ => by simp [realize_bounded_formula, realize_formula]
  | _, ⟨preformula.apprel f t, h⟩, xs => by
      have ht :
          realize_bounded_term v₁ ⟨t, h.2⟩ dvector.nil = realize_term v₂ t dvector.nil :=
        realize_bounded_term_eq (v₁ := v₁) (v₂ := v₂) (hv := hv)
          (t := ⟨t, h.2⟩) (xs := dvector.nil)
      simpa [realize_bounded_formula, realize_formula, ht] using
        (realize_bounded_formula_iff (v₁ := v₁) (v₂ := v₂) (hv := hv)
          (f := ⟨f, h.1⟩) (xs := dvector.cons (realize_term v₂ t dvector.nil) xs))
  | _, ⟨preformula.imp f₁ f₂, h⟩, xs => by
      simpa [realize_bounded_formula, realize_formula] using
        (show
          (realize_bounded_formula v₁ ⟨f₁, h.1⟩ xs → realize_bounded_formula v₁ ⟨f₂, h.2⟩ xs) ↔
            (realize_formula v₂ f₁ xs → realize_formula v₂ f₂ xs) from
          Iff.intro
            (fun hf h₁ =>
              (realize_bounded_formula_iff (v₁ := v₁) (v₂ := v₂) (hv := hv)
                (f := ⟨f₂, h.2⟩) (xs := xs)).mp
                (hf ((realize_bounded_formula_iff (v₁ := v₁) (v₂ := v₂) (hv := hv)
                  (f := ⟨f₁, h.1⟩) (xs := xs)).mpr h₁)))
            (fun hf h₁ =>
              (realize_bounded_formula_iff (v₁ := v₁) (v₂ := v₂) (hv := hv)
                (f := ⟨f₂, h.2⟩) (xs := xs)).mpr
                (hf ((realize_bounded_formula_iff (v₁ := v₁) (v₂ := v₂) (hv := hv)
                  (f := ⟨f₁, h.1⟩) (xs := xs)).mp h₁))))
  | _, ⟨preformula.all f, h⟩, xs => by
      simpa [realize_bounded_formula, realize_formula] using
        (show
          (∀ x : M.carrier, realize_bounded_formula (dvector.cons x v₁) ⟨f, h⟩ xs) ↔
            (∀ x : M.carrier, realize_formula (v₂[x // 0]) f xs) from
          Iff.intro
            (fun hf x =>
              (realize_bounded_formula_iff
                (v₁ := dvector.cons x v₁) (v₂ := v₂[x // 0])
                (hv := by
                  intro k hk
                  cases k with
                  | zero => rfl
                  | succ k =>
                      simpa using hv k (Nat.lt_of_succ_lt_succ hk))
                (f := ⟨f, h⟩) (xs := xs)).mp (hf x))
            (fun hf x =>
              (realize_bounded_formula_iff
                (v₁ := dvector.cons x v₁) (v₂ := v₂[x // 0])
                (hv := by
                  intro k hk
                  cases k with
                  | zero => rfl
                  | succ k =>
                      simpa using hv k (Nat.lt_of_succ_lt_succ hk))
                (f := ⟨f, h⟩) (xs := xs)).mpr (hf x)))
termination_by l f xs => sizeOf f.1
decreasing_by
  all_goals
    try simp_wf
    try omega

/-- Transport a semantic equivalence on underlying formulas back to bounded formulas. -/
theorem realize_bounded_formula_iff_of_fst {M : Structure L} {n : Nat}
    {v₁ w₁ : dvector M.carrier n} {v₂ w₂ : Nat → M.carrier}
    (hv₁ : ∀ k (hk : k < n), v₁.nth k hk = v₂ k)
    (hw₁ : ∀ k (hk : k < n), w₁.nth k hk = w₂ k) :
    {l₁ l₂ : Nat} → (f₁ : bounded_preformula L n l₁) → (f₂ : bounded_preformula L n l₂) →
      (xs₁ : dvector M.carrier l₁) → (xs₂ : dvector M.carrier l₂) →
      (realize_formula v₂ f₁.fst xs₁ ↔ realize_formula w₂ f₂.fst xs₂) →
        (realize_bounded_formula v₁ f₁ xs₁ ↔ realize_bounded_formula w₁ f₂ xs₂)
  | _, _, f₁, f₂, xs₁, xs₂, h => by
      simpa [realize_bounded_formula_iff (v₁ := v₁) (v₂ := v₂) (hv := hv₁) (f := f₁) (xs := xs₁),
        realize_bounded_formula_iff (v₁ := w₁) (v₂ := w₂) (hv := hw₁) (f := f₂) (xs := xs₂)] using h

/-- Substitution of a closed term at the top bounded variable. -/
@[simp] def substmax_bounded_term {n l : Nat} (t : bounded_preterm L (n + 1) l)
    (s : closed_term L) : bounded_preterm L n l :=
  ⟨subst_term t.fst s.fst n,
    bounded_term_at_subst_closed (t := t.fst) (n := n) (s := s.fst) t.2 s.2⟩

@[simp] theorem substmax_bounded_term_fst {n l : Nat} (t : bounded_preterm L (n + 1) l)
    (s : closed_term L) : (substmax_bounded_term t s).fst = subst_term t.fst s.fst n :=
  rfl

/-- Substitution of a closed term at the top bounded variable in formulas. -/
@[simp] def substmax_bounded_formula {n l : Nat} (f : bounded_preformula L (n + 1) l)
    (s : closed_term L) : bounded_preformula L n l :=
  ⟨subst_formula f.fst s.fst n,
    bounded_formula_at_subst_closed (f := f.fst) (n := n) (s := s.fst) f.2 s.2⟩

@[simp] theorem substmax_bounded_formula_fst {n l : Nat} (f : bounded_preformula L (n + 1) l)
    (s : closed_term L) :
    (substmax_bounded_formula f s).fst = subst_formula f.fst s.fst n :=
  rfl

/-- Specialization to the unique free variable of a `1`-bounded formula. -/
theorem substmax_eq_subst0_formula {l : Nat} (f : bounded_preformula L 1 l) (t : closed_term L) :
    (substmax_bounded_formula f t).fst = subst_formula f.fst t.fst 0 := by
  rfl

/-- Substituting an open term at de Bruijn index `m` lowers the ambient bound by one.

The substituted term is bounded by the variables below the substitution depth; when it is inserted
under `m` binders, `subst_term` lifts it by `m`, so the resulting term is bounded by `n + m`. -/
theorem bounded_term_at_subst_open_at : {l : Nat} → (t : preterm L l) → {n m : Nat} →
    {s : term L} → bounded_term_at t (n + m + 1) → bounded_term_at s n →
      bounded_term_at (subst_term t s m) (n + m)
  | _, .var k, n, m, s, hk, hs => by
      by_cases hlt : k < m
      · have hklt : k < n + m := lt_of_lt_of_le hlt (Nat.le_add_left m n)
        simpa [subst_term, subst_realize, hlt] using hklt
      · by_cases hgt : m < k
        · have hkpos : 0 < k := lt_of_le_of_lt (Nat.zero_le m) hgt
          have hsucc : k - 1 + 1 = k := Nat.succ_pred_eq_of_pos hkpos
          have hklt : k - 1 < n + m := by
            apply Nat.lt_of_succ_lt_succ
            simpa [hsucc, Nat.add_assoc] using hk
          simpa [subst_term, subst_realize, hlt, hgt] using hklt
        · have hEq : k = m := Nat.le_antisymm (Nat.le_of_not_gt hgt) (Nat.le_of_not_gt hlt)
          subst k
          simpa [subst_term, subst_realize, hlt, hgt, Nat.add_comm, Nat.add_left_comm,
            Nat.add_assoc] using
              (bounded_term_at_lift_at (t := s) (n := n) (k := m) (m := 0) hs)
  | _, .func _, _, _, _, _, _ => trivial
  | _, .app t₁ t₂, _, _, s, ht, hs => by
      exact ⟨bounded_term_at_subst_open_at t₁ ht.1 hs,
        bounded_term_at_subst_open_at t₂ ht.2 hs⟩

/-- Substituting an open term at de Bruijn index `m` in formulas lowers the ambient bound by one. -/
theorem bounded_formula_at_subst_open_at : {l : Nat} → (f : preformula L l) → {n m : Nat} →
    {s : term L} → bounded_formula_at f (n + m + 1) → bounded_term_at s n →
      bounded_formula_at (subst_formula f s m) (n + m)
  | _, .falsum, _, _, _, _, _ => trivial
  | _, .equal t₁ t₂, _, _, s, hf, hs => by
      exact ⟨bounded_term_at_subst_open_at t₁ hf.1 hs,
        bounded_term_at_subst_open_at t₂ hf.2 hs⟩
  | _, .rel _, _, _, _, _, _ => trivial
  | _, .apprel f t, _, _, s, hf, hs => by
      exact ⟨bounded_formula_at_subst_open_at f hf.1 hs,
        bounded_term_at_subst_open_at t hf.2 hs⟩
  | _, .imp f₁ f₂, _, _, s, hf, hs => by
      exact ⟨bounded_formula_at_subst_open_at f₁ hf.1 hs,
        bounded_formula_at_subst_open_at f₂ hf.2 hs⟩
  | _, .all f, n, m, s, hf, hs => by
      simpa [subst_formula, Nat.add_assoc] using
        (bounded_formula_at_subst_open_at (f := f) (n := n) (m := m + 1)
          (s := s) hf hs)

/-- Substitution of an open bounded term at a de Bruijn index. -/
@[simp] def subst_bounded_formula_open_at {n m l : Nat}
    (f : bounded_preformula L (n + m + 1) l) (s : bounded_term L n) :
    bounded_preformula L (n + m) l :=
  ⟨subst_formula f.fst s.fst m,
    bounded_formula_at_subst_open_at (f := f.fst) (n := n) (m := m) f.2 s.2⟩

@[simp] theorem subst_bounded_formula_open_at_fst {n m l : Nat}
    (f : bounded_preformula L (n + m + 1) l) (s : bounded_term L n) :
    (subst_bounded_formula_open_at (m := m) f s).fst = subst_formula f.fst s.fst m :=
  rfl

/-- Substitution of an open bounded term at the newest free variable. -/
@[simp] def subst_bounded_formula_open {n l : Nat}
    (f : bounded_preformula L (n + 1) l) (s : bounded_term L n) :
    bounded_preformula L n l :=
  subst_bounded_formula_open_at (m := 0) f s

@[simp] theorem subst_bounded_formula_open_fst {n l : Nat}
    (f : bounded_preformula L (n + 1) l) (s : bounded_term L n) :
    (subst_bounded_formula_open f s).fst = subst_formula f.fst s.fst 0 :=
  rfl

/-- Substituting a closed term at any free-variable index lowers the free-variable bound. -/
theorem bounded_term_at_subst_closed_at : {l : Nat} → (t : preterm L l) → {n m : Nat} →
    m < n + 1 → {s : term L} → bounded_term_at t (n + 1) → bounded_term_at s 0 →
      bounded_term_at (subst_term t s m) n
  | _, .var k, n, m, hm, s, hk, hs => by
      by_cases hlt : k < m
      · have hklt : k < n := by omega
        simpa [subst_term, subst_realize, hlt] using hklt
      · by_cases hgt : m < k
        · have hkpos : 0 < k := lt_of_le_of_lt (Nat.zero_le m) hgt
          have hsucc : k - 1 + 1 = k := Nat.succ_pred_eq_of_pos hkpos
          have hklt : k - 1 < n := by
            apply Nat.lt_of_succ_lt_succ
            simpa [hsucc] using hk
          simpa [subst_term, subst_realize, hlt, hgt] using hklt
        · have hEq : k = m := Nat.le_antisymm (Nat.le_of_not_gt hgt) (Nat.le_of_not_gt hlt)
          subst k
          have hs' : bounded_term_at (lift_term_at s m 0) n := by
            have hlift : lift_term_at s m 0 = s := by
              simpa [lift_term] using bounded_term_at_lift_irrel (t := s) m 0 hs
            rw [hlift]
            exact bounded_term_at_mono (t := s) hs (Nat.zero_le n)
          simpa [subst_term, subst_realize, hlt, hgt] using hs'
  | _, .func _, _, _, _, _, _, _ => trivial
  | _, .app t₁ t₂, _, _, hm, s, ht, hs => by
      exact ⟨bounded_term_at_subst_closed_at t₁ hm ht.1 hs,
        bounded_term_at_subst_closed_at t₂ hm ht.2 hs⟩

/-- Substituting a closed term at any free-variable index in formulas lowers the bound. -/
theorem bounded_formula_at_subst_closed_at : {l : Nat} → (f : preformula L l) → {n m : Nat} →
    m < n + 1 → {s : term L} → bounded_formula_at f (n + 1) → bounded_term_at s 0 →
      bounded_formula_at (subst_formula f s m) n
  | _, .falsum, _, _, _, _, _, _ => trivial
  | _, .equal t₁ t₂, _, _, hm, s, hf, hs => by
      exact ⟨bounded_term_at_subst_closed_at t₁ hm hf.1 hs,
        bounded_term_at_subst_closed_at t₂ hm hf.2 hs⟩
  | _, .rel _, _, _, _, _, _, _ => trivial
  | _, .apprel f t, _, _, hm, s, hf, hs => by
      exact ⟨bounded_formula_at_subst_closed_at f hm hf.1 hs,
        bounded_term_at_subst_closed_at t hm hf.2 hs⟩
  | _, .imp f₁ f₂, _, _, hm, s, hf, hs => by
      exact ⟨bounded_formula_at_subst_closed_at f₁ hm hf.1 hs,
        bounded_formula_at_subst_closed_at f₂ hm hf.2 hs⟩
  | _, .all f, n, m, hm, s, hf, hs => by
      simpa [subst_formula] using
        (bounded_formula_at_subst_closed_at (f := f) (n := n + 1) (m := m + 1)
          (by omega) (s := s) hf hs)

/-- Substitution of a closed term at an arbitrary free-variable index. -/
@[simp] def subst_bounded_formula_at {n l : Nat} (f : bounded_preformula L (n + 1) l)
    (s : closed_term L) (m : Nat) (hm : m < n + 1) : bounded_preformula L n l :=
  ⟨subst_formula f.fst s.fst m,
    bounded_formula_at_subst_closed_at (f := f.fst) (n := n) (m := m) hm f.2 s.2⟩

@[simp] theorem subst_bounded_formula_at_fst {n l : Nat}
    (f : bounded_preformula L (n + 1) l) (s : closed_term L) (m : Nat) (hm : m < n + 1) :
    (subst_bounded_formula_at f s m hm).fst = subst_formula f.fst s.fst m :=
  rfl

end fol
end Flypitch

attribute [nolint docBlame]
  Flypitch.fol.bounded_preterm.fst Flypitch.fol.bounded_preformula.fst
