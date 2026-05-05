import Mathlib

universe u

namespace Flypitch

open Set TopologicalSpace

set_option linter.missingDocs false
set_option linter.style.longLine false

/-!
Port of upstream `src/regular_open_algebra.lean`.
-/

variable {α : Type u} [TopologicalSpace α]

/-- Pseudocomplement: complement of the closure. -/
def perp (S : Set α) : Set α := (closure S)ᶜ

/-- A regular open set equals the interior of its closure. -/
def is_regular (S : Set α) : Prop := S = interior (closure S)

postfix:80 "ᵖ" => perp

theorem perp_unfold (S : Set α) : Sᵖ = (closure S)ᶜ := rfl

theorem perp_eq_int_neg {S : Set α} : Sᵖ = interior (Sᶜ) := by simp [perp]

theorem mem_perp_iff {S : Set α} {x : α} : x ∈ Sᵖ ↔ ∃ T, T ∩ S = ∅ ∧ IsOpen T ∧ x ∈ T := by
  rw [perp_eq_int_neg, mem_interior]
  simp [Set.subset_compl_iff_disjoint_right, Set.disjoint_iff_inter_eq_empty]

@[simp] theorem isOpen_perp {S : Set α} : IsOpen (Sᵖ) := by
  rw [perp_eq_int_neg]; exact isOpen_interior

@[simp] theorem perp_univ : (univ : Set α)ᵖ = (∅ : Set α) := by simp [perp]

@[simp] theorem perp_empty : (∅ : Set α)ᵖ = (univ : Set α) := by simp [perp]

@[simp] theorem isOpen_of_is_regular {S : Set α} (H : is_regular S) : IsOpen S := by
  rw [H]; exact isOpen_interior

theorem is_regular_of_clopen {S : Set α} (H : IsClopen S) : is_regular S := by
  dsimp [is_regular]; rw [H.isClosed.closure_eq, H.isOpen.interior_eq]

theorem regular_iff_p_p {S : Set α} : is_regular S ↔ (Sᵖᵖ) = S := by
  dsimp [is_regular, perp]
  constructor
  · intro h; calc
      (closure ((closure S)ᶜ))ᶜ = interior (closure S) := by simp
      _ = S := h.symm
  · intro h; calc
      S = (closure ((closure S)ᶜ))ᶜ := by symm; exact h
      _ = interior (closure S) := by simp

theorem p_p_eq_int_cl {S : Set α} : Sᵖᵖ = interior (closure S) := by simp [perp]

theorem int_cl_eq_p_p {S : Set α} : interior (closure S) = Sᵖᵖ := (p_p_eq_int_cl).symm

@[simp] theorem is_regular_empty : is_regular (∅ : Set α) := by simp [is_regular]

@[simp] theorem is_regular_univ : is_regular (univ : Set α) := by simp [is_regular]

theorem p_anti {P Q : Set α} (H : P ⊆ Q) : Qᵖ ⊆ Pᵖ := by
  dsimp [perp]
  exact Set.compl_subset_compl.mpr (closure_mono H)

theorem p_p_mono {P Q : Set α} (H : P ⊆ Q) : Pᵖᵖ ⊆ Qᵖᵖ := p_anti (p_anti H)

theorem in_p_p_of_open {S : Set α} (H : IsOpen S) : S ⊆ Sᵖᵖ := by
  rw [p_p_eq_int_cl]
  calc
    S = interior S := by rw [H.interior_eq]
    _ ⊆ interior (closure S) := interior_mono subset_closure

theorem p_eq_p_p_p {S : Set α} (H : IsOpen S) : Sᵖ = Sᵖᵖᵖ := by
  apply le_antisymm
  · apply in_p_p_of_open; exact isOpen_perp
  · exact p_anti (in_p_p_of_open H)

@[simp] theorem p_p_p_p_eq_p_p {S : Set α} : Sᵖᵖᵖᵖ = Sᵖᵖ := by
  rw [← p_eq_p_p_p (isOpen_perp (S := S))]

theorem is_regular_stable_subset {S₁ S₂ : Set α} (H : is_regular S₂) (H₂ : S₁ ⊆ S₂) :
    S₁ᵖᵖ ⊆ S₂ := by
  have h_sub : S₁ᵖᵖ ⊆ S₂ᵖᵖ := p_p_mono H₂
  rw [regular_iff_p_p.mp H] at h_sub
  exact h_sub

@[simp] theorem is_regular_eq_p_p {S : Set α} (H : is_regular S) : Sᵖᵖ = S := by
  apply le_antisymm
  · apply is_regular_stable_subset H; exact fun _ h ↦ h
  · exact in_p_p_of_open (isOpen_of_is_regular H)

theorem subset_p_p_of_open {S : Set α} (H : IsOpen S) : S ⊆ Sᵖᵖ := in_p_p_of_open H

theorem subset_int_cl_of_open {S : Set α} (H : IsOpen S) : S ⊆ interior (closure S) := by
  rw [← p_p_eq_int_cl]; exact subset_p_p_of_open H

theorem is_regular_sup {S₁ S₂ : Set α} : is_regular ((S₁ ∪ S₂)ᵖᵖ) := by
  rw [regular_iff_p_p]; simp

@[simp] theorem isOpen_of_p_p' {S : Set α} : IsOpen (Sᵖᵖ) := by simp

@[simp] theorem is_regular_p_p {S : Set α} : is_regular (Sᵖᵖ) := by
  rw [regular_iff_p_p]; simp

/-- For open S₁: S₁ ∩ closure S₂ ⊆ closure (S₁ ∩ S₂). -/
theorem inter_closure_subset_closure_inter {S₁ S₂ : Set α} (h₁ : IsOpen S₁) :
    S₁ ∩ closure S₂ ⊆ closure (S₁ ∩ S₂) := by
  calc
    S₁ ∩ closure S₂ = closure S₂ ∩ S₁ := Set.inter_comm _ _
    _ ⊆ closure (S₂ ∩ S₁) := h₁.closure_inter (s := S₂)
    _ = closure (S₁ ∩ S₂) := by rw [Set.inter_comm]

/-- For open S₁, S₂: S₁ ∩ (S₂ᵖᵖ) ⊆ (S₁ ∩ S₂)ᵖᵖ. -/
theorem inter_aux {S₁ S₂ : Set α} (h₁ : IsOpen S₁) (_ : IsOpen S₂) :
    S₁ ∩ (S₂ᵖᵖ) ⊆ (S₁ ∩ S₂)ᵖᵖ := by
  rw [p_p_eq_int_cl, p_p_eq_int_cl]
  calc
    S₁ ∩ interior (closure S₂) ⊆ interior S₁ ∩ interior (closure S₂) :=
      Set.inter_subset_inter (by rw [h₁.interior_eq]) le_rfl
    _ = interior (S₁ ∩ closure S₂) := by rw [interior_inter]
    _ ⊆ interior (closure (S₁ ∩ S₂)) := interior_mono (inter_closure_subset_closure_inter h₁)

/-- For open S₁, S₂: (S₁ ∩ S₂)ᵖᵖ = S₁ᵖᵖ ∩ S₂ᵖᵖ. -/
theorem p_p_inter_eq_inter_p_p {S₁ S₂ : Set α} (h₁ : IsOpen S₁) (h₂ : IsOpen S₂) :
    (S₁ ∩ S₂)ᵖᵖ = S₁ᵖᵖ ∩ S₂ᵖᵖ := by
  apply le_antisymm
  · intro x hx
    exact ⟨p_p_mono inter_subset_left hx, p_p_mono inter_subset_right hx⟩
  · intro x ⟨hx₁, hx₂⟩
    have h_open₁ : IsOpen (S₁ᵖᵖ) := isOpen_of_p_p'
    -- Step 1: S₁ᵖᵖ ∩ S₂ᵖᵖ ⊆ (S₁ᵖᵖ ∩ S₂)ᵖᵖ
    have hstep₁ : S₁ᵖᵖ ∩ S₂ᵖᵖ ⊆ (S₁ᵖᵖ ∩ S₂)ᵖᵖ := by
      intro y ⟨hy₁, hy₂⟩
      exact inter_aux h_open₁ h₂ ⟨hy₁, hy₂⟩
    -- Step 2: S₂ ∩ S₁ᵖᵖ ⊆ (S₂ ∩ S₁)ᵖᵖ
    have h_eq1 : (S₂ ∩ S₁)ᵖᵖ = (S₁ ∩ S₂)ᵖᵖ := by rw [Set.inter_comm S₂ S₁]
    have htemp : S₂ ∩ S₁ᵖᵖ ⊆ (S₂ ∩ S₁)ᵖᵖ := inter_aux h₂ h₁
    -- Step 3: Apply p_p_mono to htemp, then rewrite using commutativity
    have htemp_pp : (S₂ ∩ S₁ᵖᵖ)ᵖᵖ ⊆ ((S₂ ∩ S₁)ᵖᵖ)ᵖᵖ := p_p_mono htemp
    -- Simplify: ((S₂ ∩ S₁)ᵖᵖ)ᵖᵖ = (S₂ ∩ S₁)ᵖᵖ (by p_p_p_p_eq_p_p) = (S₁ ∩ S₂)ᵖᵖ (by commute)
    -- And (S₂ ∩ S₁ᵖᵖ)ᵖᵖ = (S₁ᵖᵖ ∩ S₂)ᵖᵖ (by commute)
    have hstep₂ : (S₁ᵖᵖ ∩ S₂)ᵖᵖ ⊆ (S₁ ∩ S₂)ᵖᵖ := by
      have : (S₁ᵖᵖ ∩ S₂)ᵖᵖ = (S₂ ∩ S₁ᵖᵖ)ᵖᵖ := by rw [Set.inter_comm (S₁ᵖᵖ) S₂]
      rw [this]
      calc
        (S₂ ∩ S₁ᵖᵖ)ᵖᵖ ⊆ ((S₂ ∩ S₁)ᵖᵖ)ᵖᵖ := htemp_pp
        _ = (S₂ ∩ S₁)ᵖᵖ := p_p_p_p_eq_p_p
        _ = (S₁ ∩ S₂)ᵖᵖ := by rw [Set.inter_comm S₂ S₁]
    exact hstep₂ (hstep₁ ⟨hx₁, hx₂⟩)

@[simp] theorem is_regular_inter {S₁ S₂ : Set α} (H₁ : is_regular S₁) (H₂ : is_regular S₂) :
    is_regular (S₁ ∩ S₂) := by
  have h_reg₁ := H₁
  have h_reg₂ := H₂
  rw [regular_iff_p_p] at H₁ H₂ ⊢
  rw [p_p_inter_eq_inter_p_p (isOpen_of_is_regular h_reg₁) (isOpen_of_is_regular h_reg₂)]
  rw [H₁, H₂]

/-- Type of regular open subsets of `α`. -/
def regular_opens (α : Type u) [TopologicalSpace α] : Type u := {S : Set α // is_regular S}

end Flypitch
