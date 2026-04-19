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

end fol
end Flypitch

attribute [nolint docBlame]
  Flypitch.fol.bounded_preterm.fst Flypitch.fol.bounded_preformula.fst
