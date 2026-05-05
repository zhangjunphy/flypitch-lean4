import Flypitch.RegularOpenAlgebra
import Flypitch.SetTheory

universe u v w

namespace Flypitch

open TopologicalSpace

set_option linter.missingDocs false
set_option linter.style.longLine false

/-!
Port of the opening of upstream `src/cantor_space.lean`.
-/

/-- The discrete topology on `Prop`, used as the two-point coordinate topology. -/
instance Prop_space : TopologicalSpace Prop := ⊥

instance discrete_Prop : DiscreteTopology Prop := ⟨rfl⟩

/-- The product topology on Cantor spaces represented as predicates/sets. -/
instance product_topology {α : Type u} : TopologicalSpace (Set α) := Pi.topologicalSpace

theorem eq_true_of_provable {p : Prop} (h : p) : p = True := propext ⟨fun _ => trivial, fun _ => h⟩

theorem eq_false_of_provable_neg {p : Prop} (h : ¬ p) : p = False :=
  propext ⟨fun hp => False.elim (h hp), fun hp => False.elim hp⟩

namespace cantor_space

variable {α : Type u}

/-- The set of subsets containing `x`. -/
def principal_open (x : α) : Set (Set α) := {S | x ∈ S}

/-- The set of subsets not containing `x`. -/
def co_principal_open (x : α) : Set (Set α) := {S | x ∉ S}

@[simp] theorem neg_principal_open {x : α} : co_principal_open x = (principal_open x)ᶜ := by
  rfl

@[simp] theorem neg_co_principal_open {x : α} : (co_principal_open x)ᶜ = principal_open x := by
  ext S
  simp [principal_open, co_principal_open]

/-- The four opens determined by one coordinate. -/
def opens_over (x : α) : Set (Set (Set α)) :=
  {principal_open x, co_principal_open x, Set.univ, ∅}

@[simp] theorem principal_open_mem_opens_over {x : α} : principal_open x ∈ opens_over x := by
  simp [opens_over]

@[simp] theorem co_principal_open_mem_opens_over {x : α} : co_principal_open x ∈ opens_over x := by
  simp [opens_over]

@[simp] theorem univ_mem_opens_over {x : α} : (Set.univ : Set (Set α)) ∈ opens_over x := by
  simp [opens_over]

@[simp] theorem empty_mem_opens_over {x : α} : (∅ : Set (Set α)) ∈ opens_over x := by
  simp [opens_over]

theorem isOpen_principal_open {a : α} : IsOpen (principal_open a) := by
  change IsOpen ((fun S : Set α => (a ∈ S : Prop)) ⁻¹' {p | p})
  exact Continuous.isOpen_preimage (continuous_apply a) _ (isOpen_discrete _)

theorem isClosed_principal_open {a : α} : IsClosed (principal_open a) := by
  change IsClosed ((fun S : Set α => (a ∈ S : Prop)) ⁻¹' {p | p})
  exact IsClosed.preimage (continuous_apply a) (isClosed_discrete _)

theorem isOpen_co_principal_open {a : α} : IsOpen (co_principal_open a) := by
  change IsOpen ((fun S : Set α => (a ∈ S : Prop)) ⁻¹' {p | ¬ p})
  exact Continuous.isOpen_preimage (continuous_apply a) _ (isOpen_discrete _)

theorem isClosed_co_principal_open {a : α} : IsClosed (co_principal_open a) := by
  change IsClosed ((fun S : Set α => (a ∈ S : Prop)) ⁻¹' {p | ¬ p})
  exact IsClosed.preimage (continuous_apply a) (isClosed_discrete _)

theorem isClopen_principal_open {a : α} : IsClopen (principal_open a) :=
  ⟨isClosed_principal_open, isOpen_principal_open⟩

theorem isClopen_co_principal_open {a : α} : IsClopen (co_principal_open a) :=
  ⟨isClosed_co_principal_open, isOpen_co_principal_open⟩

/-- Finite intersection of clopen sets. -/
theorem is_clopen_finite_inter' {β : Type v} [TopologicalSpace β] {γ : Type w}
    {X : Finset γ} {f : γ → Set β}
    (H_f : ∀ x ∈ X, IsClopen (f x)) : IsClopen (Finset.inf X f) := by
  classical
  induction X using Finset.induction_on with
  | empty => simpa using (isClopen_univ : IsClopen (Set.univ : Set β))
  | insert a A ha ih =>
      rw [Finset.inf_insert]
      exact (H_f a (by simp)).inter (ih fun x hx => H_f x (by simp [hx]))

/-- Subsets containing a finite set. -/
def principal_open_finset (F : Finset α) : Set (Set α) := {S | (↑F : Set α) ⊆ S}

theorem mem_principal_open_finset_iff {F : Finset α} {S : Set α} :
    S ∈ principal_open_finset F ↔ (↑F : Set α) ⊆ S := by
  rfl

@[simp] theorem principal_open_finset_insert [DecidableEq α] {F : Finset α} {a : α} :
    principal_open_finset (insert a F) = principal_open_finset {a} ∩ principal_open_finset F := by
  ext S
  simp [principal_open_finset, Set.insert_subset_iff]

@[simp] theorem principal_open_finset_singleton {a : α} :
    principal_open_finset {a} = principal_open a := by
  ext S
  simp [principal_open_finset, principal_open]

/-- Subsets avoiding a finite set. -/
def co_principal_open_finset (F : Finset α) : Set (Set α) := {S | (↑F : Set α) ⊆ Sᶜ}

@[simp] theorem co_principal_open_finset_insert [DecidableEq α] {F : Finset α} {a : α} :
    co_principal_open_finset (insert a F) = co_principal_open_finset {a} ∩
      co_principal_open_finset F := by
  ext S
  simp [co_principal_open_finset, Set.insert_subset_iff]

@[simp] theorem co_principal_open_finset_singleton {a : α} :
    co_principal_open_finset {a} = co_principal_open a := by
  ext S
  simp [co_principal_open_finset, co_principal_open]

theorem isClopen_principal_open_finset (F : Finset α) : IsClopen (principal_open_finset F) := by
  classical
  induction F using Finset.induction_on with
  | empty => simpa [principal_open_finset] using
      (isClopen_univ : IsClopen (Set.univ : Set (Set α)))
  | insert a A ha ih =>
      rw [principal_open_finset_insert]
      rw [principal_open_finset_singleton]
      exact (isClopen_principal_open (a := a)).inter ih

theorem isClopen_co_principal_open_finset (F : Finset α) : IsClopen (co_principal_open_finset F) := by
  classical
  induction F using Finset.induction_on with
  | empty => simpa [co_principal_open_finset] using
      (isClopen_univ : IsClopen (Set.univ : Set (Set α)))
  | insert a A ha ih =>
      rw [co_principal_open_finset_insert]
      rw [co_principal_open_finset_singleton]
      exact (isClopen_co_principal_open (a := a)).inter ih

theorem principal_open_finset_eq_inter (F : Finset α) :
    principal_open_finset F = Finset.inf F principal_open := by
  classical
  induction F using Finset.induction_on with
  | empty => simp [principal_open_finset]
  | insert a A ha ih =>
      rw [principal_open_finset_insert, Finset.inf_insert, ih, principal_open_finset_singleton]
      rfl

theorem co_principal_open_finset_eq_inter (F : Finset α) :
    co_principal_open_finset F = Finset.inf F co_principal_open := by
  classical
  induction F using Finset.induction_on with
  | empty => simp [co_principal_open_finset]
  | insert a A ha ih =>
      rw [co_principal_open_finset_insert, Finset.inf_insert, ih]
      rw [co_principal_open_finset_singleton]
      rfl

theorem intersection_standard_basis_nonempty' {p_ins p_out : Finset α}
    (h : Disjoint p_ins p_out) :
    ∃ S : Set α, S ∈ principal_open_finset p_ins ∩ co_principal_open_finset p_out := by
  refine ⟨(↑p_ins : Set α), ?_⟩
  constructor
  · intro x hx
    exact hx
  · intro x hx hx_in
    exact (Finset.disjoint_left.mp h hx_in) hx

theorem nonempty_of_standard_basic_cylinder {T : Set (Set α)} {p_ins p_out : Finset α}
    (h_eq : T = principal_open_finset p_ins ∩ co_principal_open_finset p_out)
    (h : Disjoint p_ins p_out) : T.Nonempty := by
  rcases intersection_standard_basis_nonempty' h with ⟨S, hS⟩
  exact ⟨S, by simpa [h_eq] using hS⟩

theorem standard_basis_reindex (p_ins p_out : Finset α) :
    (⋂₀ ((Finset.image principal_open p_ins ∪ Finset.image co_principal_open p_out :
      Finset (Set (Set α))) : Set (Set (Set α)))) =
      principal_open_finset p_ins ∩ co_principal_open_finset p_out := by
  classical
  ext S
  constructor
  · intro h
    rw [Set.mem_sInter] at h
    constructor
    · intro x hx
      exact h (principal_open x) (by
        rw [Finset.mem_coe, Finset.mem_union]
        exact Or.inl (Finset.mem_image.mpr ⟨x, hx, rfl⟩))
    · intro x hx hxS
      exact h (co_principal_open x) (by
        rw [Finset.mem_coe, Finset.mem_union]
        exact Or.inr (Finset.mem_image.mpr ⟨x, hx, rfl⟩)) hxS
  · intro h
    rw [Set.mem_sInter]
    intro T hT
    rw [Finset.mem_coe, Finset.mem_union] at hT
    rcases hT with hT | hT
    · rcases Finset.mem_image.mp hT with ⟨x, hx, rfl⟩
      exact h.1 hx
    · rcases Finset.mem_image.mp hT with ⟨x, hx, rfl⟩
      exact h.2 hx

theorem intersection_standard_basis_nonempty {p_ins p_out : Finset α}
    (h : Disjoint p_ins p_out) :
    (⋂₀ ((Finset.image principal_open p_ins ∪ Finset.image co_principal_open p_out :
      Finset (Set (Set α))) : Set (Set (Set α)))).Nonempty := by
  rw [standard_basis_reindex]
  exact Set.nonempty_def.mpr (intersection_standard_basis_nonempty' h)

theorem ins₁_out₂_disjoint {S : Set α} {p_ins₁ p_out₁ p_ins₂ p_out₂ : Finset α}
    (h_mem₁ : S ∈ principal_open_finset p_ins₁ ∩ co_principal_open_finset p_out₁)
    (h_mem₂ : S ∈ principal_open_finset p_ins₂ ∩ co_principal_open_finset p_out₂)
    {a : α} (ha_left : a ∈ p_ins₁) (ha_right : a ∈ p_out₂) : False := by
  exact h_mem₂.2 ha_right (h_mem₁.1 ha_left)

theorem out₁_ins₂_disjoint {S : Set α} {p_ins₁ p_out₁ p_ins₂ p_out₂ : Finset α}
    (h_mem₁ : S ∈ principal_open_finset p_ins₁ ∩ co_principal_open_finset p_out₁)
    (h_mem₂ : S ∈ principal_open_finset p_ins₂ ∩ co_principal_open_finset p_out₂)
    {a : α} (ha_left : a ∈ p_out₁) (ha_right : a ∈ p_ins₂) : False := by
  exact h_mem₁.2 ha_left (h_mem₂.1 ha_right)

theorem disjoint_union_of_inter_nonempty [DecidableEq α] {p_ins₁ p_out₁ p_ins₂ p_out₂ : Finset α}
    (h_disjoint₁ : Disjoint p_ins₁ p_out₁) (h_disjoint₂ : Disjoint p_ins₂ p_out₂)
    (h_nonempty : (principal_open_finset p_ins₁ ∩ co_principal_open_finset p_out₁ ∩
      (principal_open_finset p_ins₂ ∩ co_principal_open_finset p_out₂)).Nonempty) :
    Disjoint (p_ins₁ ∪ p_ins₂) (p_out₁ ∪ p_out₂) := by
  classical
  rcases h_nonempty with ⟨S, hS⟩
  rw [Finset.disjoint_left]
  intro a ha hcontra
  rw [Finset.mem_union] at ha hcontra
  rcases ha with ha | ha <;> rcases hcontra with hb | hb
  · exact (Finset.disjoint_left.mp h_disjoint₁ ha) hb
  · exact ins₁_out₂_disjoint hS.1 hS.2 ha hb
  · exact out₁_ins₂_disjoint hS.1 hS.2 hb ha
  · exact (Finset.disjoint_left.mp h_disjoint₂ ha) hb

/-- Standard finite cylinder basis for Cantor space. -/
def standard_basis : Set (Set (Set α)) :=
  {T | ∃ p_ins p_out : Finset α,
    T = principal_open_finset p_ins ∩ co_principal_open_finset p_out ∧ Disjoint p_ins p_out} ∪ {∅}

@[simp] theorem principal_open_mem_standard_basis {a : α} :
    principal_open a ∈ (standard_basis : Set (Set (Set α))) := by
  classical
  rw [standard_basis]
  left
  refine ⟨{a}, ∅, ?_, by simp⟩
  ext S
  simp [principal_open, principal_open_finset, co_principal_open_finset]

@[simp] theorem co_principal_open_mem_standard_basis {a : α} :
    co_principal_open a ∈ (standard_basis : Set (Set (Set α))) := by
  classical
  rw [standard_basis]
  left
  refine ⟨∅, {a}, ?_, by simp⟩
  ext S
  simp [co_principal_open, principal_open_finset, co_principal_open_finset]

theorem univ_mem_standard_basis : (Set.univ : Set (Set α)) ∈ standard_basis := by
  classical
  rw [standard_basis]
  left
  refine ⟨∅, ∅, ?_, by simp⟩
  simp [principal_open_finset, co_principal_open_finset]

theorem empty_mem_standard_basis : (∅ : Set (Set α)) ∈ standard_basis := by
  rw [standard_basis]
  right
  rfl

end cantor_space

end Flypitch
