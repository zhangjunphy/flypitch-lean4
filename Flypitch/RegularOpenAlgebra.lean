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

/-- Postfix notation for the pseudocomplement operation. -/
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

theorem p_p_p_p_eq_p_p {S : Set α} : Sᵖᵖᵖᵖ = Sᵖᵖ := by
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
  rw [regular_iff_p_p]
  exact p_p_p_p_eq_p_p

theorem isOpen_of_p_p' {S : Set α} : IsOpen (Sᵖᵖ) := by
  rw [p_p_eq_int_cl]
  exact isOpen_interior

@[simp] theorem is_regular_p_p {S : Set α} : is_regular (Sᵖᵖ) := by
  rw [regular_iff_p_p]
  exact p_p_p_p_eq_p_p

/-- For open S₁: S₁ ∩ closure S₂ ⊆ closure (S₁ ∩ S₂). -/
theorem inter_closure_subset_closure_inter {S₁ S₂ : Set α} (h₁ : IsOpen S₁) :
    S₁ ∩ closure S₂ ⊆ closure (S₁ ∩ S₂) := by
  calc
    S₁ ∩ closure S₂ = closure S₂ ∩ S₁ := Set.inter_comm _ _
    _ ⊆ closure (S₂ ∩ S₁) := h₁.closure_inter (s := S₂)
    _ = closure (S₁ ∩ S₂) := by rw [Set.inter_comm]

/-- For open `S₁`: `S₁ ∩ (S₂ᵖᵖ) ⊆ (S₁ ∩ S₂)ᵖᵖ`. -/
theorem inter_aux {S₁ S₂ : Set α} (h₁ : IsOpen S₁) :
    S₁ ∩ (S₂ᵖᵖ) ⊆ (S₁ ∩ S₂)ᵖᵖ := by
  rw [p_p_eq_int_cl, p_p_eq_int_cl]
  calc
    S₁ ∩ interior (closure S₂) ⊆ interior S₁ ∩ interior (closure S₂) :=
      Set.inter_subset_inter (by rw [h₁.interior_eq]) le_rfl
    _ = interior (S₁ ∩ closure S₂) := by rw [interior_inter]
    _ ⊆ interior (closure (S₁ ∩ S₂)) := interior_mono (inter_closure_subset_closure_inter h₁)

/-- If `S₂` is open, `(S₁ ∩ S₂)ᵖᵖ = S₁ᵖᵖ ∩ S₂ᵖᵖ`. -/
theorem p_p_inter_eq_inter_p_p {S₁ S₂ : Set α} (h₂ : IsOpen S₂) :
    (S₁ ∩ S₂)ᵖᵖ = S₁ᵖᵖ ∩ S₂ᵖᵖ := by
  apply le_antisymm
  · intro x hx
    exact ⟨p_p_mono inter_subset_left hx, p_p_mono inter_subset_right hx⟩
  · intro x ⟨hx₁, hx₂⟩
    have h_open₁ : IsOpen (S₁ᵖᵖ) := isOpen_of_p_p'
    -- Step 1: S₁ᵖᵖ ∩ S₂ᵖᵖ ⊆ (S₁ᵖᵖ ∩ S₂)ᵖᵖ
    have hstep₁ : S₁ᵖᵖ ∩ S₂ᵖᵖ ⊆ (S₁ᵖᵖ ∩ S₂)ᵖᵖ := by
      intro y ⟨hy₁, hy₂⟩
      exact inter_aux h_open₁ ⟨hy₁, hy₂⟩
    -- Step 2: S₂ ∩ S₁ᵖᵖ ⊆ (S₂ ∩ S₁)ᵖᵖ
    have h_eq1 : (S₂ ∩ S₁)ᵖᵖ = (S₁ ∩ S₂)ᵖᵖ := by rw [Set.inter_comm S₂ S₁]
    have htemp : S₂ ∩ S₁ᵖᵖ ⊆ (S₂ ∩ S₁)ᵖᵖ := inter_aux h₂
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
  rw [p_p_inter_eq_inter_p_p (isOpen_of_is_regular h_reg₂)]
  rw [H₁, H₂]

/-- Type of regular open subsets of `α`. -/
def regular_opens (α : Type u) [TopologicalSpace α] : Type u := {S : Set α // is_regular S}

/-- Coerce a regular open to its underlying set. -/
instance regularOpenCoe : Coe (regular_opens α) (Set α) where
  coe S := S.1

/-- The regular opens are ordered by inclusion of their underlying sets. -/
instance regularOpenPartialOrder : PartialOrder (regular_opens α) where
  le S T := (S : Set α) ⊆ (T : Set α)
  le_refl S := subset_rfl
  le_trans S T U hST hTU := Set.Subset.trans hST hTU
  le_antisymm S T hST hTS := Subtype.ext (Set.Subset.antisymm hST hTS)

theorem regularOpen_le_iff_subset {S T : regular_opens α} :
    S ≤ T ↔ (S : Set α) ⊆ (T : Set α) := by
  rfl

/-- Regular opens form a lattice under regularized union and intersection. -/
instance regularOpenLattice : Lattice (regular_opens α) where
  sup S T := ⟨((S : Set α) ∪ (T : Set α))ᵖᵖ, is_regular_sup⟩
  le_sup_left S T := by
    change (S : Set α) ⊆ ((S : Set α) ∪ (T : Set α))ᵖᵖ
    exact subset_trans (fun _ hx => Or.inl hx)
      (subset_p_p_of_open ((isOpen_of_is_regular S.2).union (isOpen_of_is_regular T.2)))
  le_sup_right S T := by
    change (T : Set α) ⊆ ((S : Set α) ∪ (T : Set α))ᵖᵖ
    exact subset_trans (fun _ hx => Or.inr hx)
      (subset_p_p_of_open ((isOpen_of_is_regular S.2).union (isOpen_of_is_regular T.2)))
  sup_le S T U hSU hTU := by
    change ((S : Set α) ∪ (T : Set α))ᵖᵖ ⊆ (U : Set α)
    apply is_regular_stable_subset U.2
    intro x hx
    exact hx.elim (fun hxS => hSU hxS) (fun hxT => hTU hxT)
  inf S T := ⟨(S : Set α) ∩ (T : Set α), is_regular_inter S.2 T.2⟩
  inf_le_left S T := by
    intro x hx
    exact hx.1
  inf_le_right S T := by
    intro x hx
    exact hx.2
  le_inf S T U hST hSU := by
    intro x hx
    exact ⟨hST hx, hSU hx⟩

/-- Regular opens have bottom `∅` and top `univ`. -/
instance regularOpenBoundedOrder : BoundedOrder (regular_opens α) where
  top := ⟨Set.univ, is_regular_univ⟩
  le_top S := by
    intro x hx
    trivial
  bot := ⟨∅, is_regular_empty⟩
  bot_le S := by
    intro x hx
    exact False.elim hx

theorem regularOpen_coe_bot : ((⊥ : regular_opens α) : Set α) = ∅ := rfl

theorem regularOpen_inf_unfold {S T : regular_opens α} :
    S ⊓ T = ⟨(S : Set α) ∩ (T : Set α), is_regular_inter S.2 T.2⟩ := rfl

theorem regularOpen_sup_unfold {S T : regular_opens α} :
    S ⊔ T = ⟨((S : Set α) ∪ (T : Set α))ᵖᵖ, is_regular_sup⟩ := rfl

theorem is_regular_perp_of_open {S : Set α} (hS : IsOpen S) : is_regular (Sᵖ) := by
  rw [regular_iff_p_p]
  exact (p_eq_p_p_p hS).symm

theorem is_regular_perp_of_regular {S : Set α} (hS : is_regular S) : is_regular (Sᵖ) :=
  is_regular_perp_of_open (isOpen_of_is_regular hS)

/-- The Boolean complement of a regular open is its pseudocomplement. -/
instance regularOpenCompl : Compl (regular_opens α) where
  compl S := ⟨(S : Set α)ᵖ, is_regular_perp_of_regular S.2⟩

theorem regularOpen_compl_unfold {S : regular_opens α} :
    Sᶜ = ⟨(S : Set α)ᵖ, is_regular_perp_of_regular S.2⟩ := rfl

theorem regularOpen_compl_compl (S : regular_opens α) : Sᶜᶜ = S := by
  apply Subtype.ext
  exact regular_iff_p_p.mp S.2

theorem regularOpen_inf_compl_eq_bot (S : regular_opens α) : S ⊓ Sᶜ = ⊥ := by
  apply Subtype.ext
  ext x
  constructor
  · intro hx
    rw [regularOpen_inf_unfold] at hx
    exact hx.2 (subset_closure hx.1)
  · intro hx
    exact False.elim hx

theorem regularOpen_sup_compl_eq_top (S : regular_opens α) : S ⊔ Sᶜ = ⊤ := by
  apply Subtype.ext
  rw [regularOpen_sup_unfold]
  change (((S : Set α) ∪ (S : Set α)ᵖ)ᵖᵖ) = Set.univ
  rw [p_p_eq_int_cl]
  have h_closure : closure ((S : Set α) ∪ (S : Set α)ᵖ) = Set.univ := by
    apply eq_univ_of_forall
    intro x
    by_cases hx : x ∈ closure (S : Set α)
    · exact closure_mono (by intro y hy; exact Or.inl hy) hx
    · apply subset_closure
      exact Or.inr hx
  rw [h_closure, interior_univ]

theorem regularOpen_inf_sup_left (S T U : regular_opens α) :
    S ⊓ (T ⊔ U) = (S ⊓ T) ⊔ (S ⊓ U) := by
  apply Subtype.ext
  change (S : Set α) ∩ (((T : Set α) ∪ (U : Set α))ᵖᵖ) =
    ((((S : Set α) ∩ (T : Set α)) ∪ ((S : Set α) ∩ (U : Set α)))ᵖᵖ)
  have h_union :
      ((S : Set α) ∩ (T : Set α)) ∪ ((S : Set α) ∩ (U : Set α)) =
        ((T : Set α) ∪ (U : Set α)) ∩ (S : Set α) := by
    ext x
    constructor
    · intro hx
      rcases hx with ⟨hxS, hxT⟩ | ⟨hxS, hxU⟩
      · exact ⟨Or.inl hxT, hxS⟩
      · exact ⟨Or.inr hxU, hxS⟩
    · intro hx
      rcases hx.1 with hxT | hxU
      · exact Or.inl ⟨hx.2, hxT⟩
      · exact Or.inr ⟨hx.2, hxU⟩
  rw [h_union]
  rw [p_p_inter_eq_inter_p_p (S₁ := (T : Set α) ∪ (U : Set α))
    (S₂ := (S : Set α)) (isOpen_of_is_regular S.2)]
  rw [is_regular_eq_p_p S.2, Set.inter_comm]

/-- Regular opens form a distributive lattice. -/
instance regularOpenDistribLattice : DistribLattice (regular_opens α) :=
  DistribLattice.ofInfSupLe fun S T U => by
    rw [regularOpen_inf_sup_left]

/-- Regular opens form a Boolean algebra under pseudocomplement. -/
instance regularOpenBooleanAlgebra : BooleanAlgebra (regular_opens α) where
  __ := regularOpenDistribLattice
  __ := regularOpenCompl
  top := ⊤
  bot := ⊥
  inf_compl_le_bot S := by
    rw [regularOpen_inf_compl_eq_bot]
  top_le_sup_compl S := by
    rw [regularOpen_sup_compl_eq_top]
  le_top S := by
    intro x hx
    trivial
  bot_le S := by
    intro x hx
    exact False.elim hx

/-- The supremum of a family of regular opens is the regularization of their union. -/
instance regularOpenSupSet : SupSet (regular_opens α) where
  sSup S := ⟨(⋃₀ ((fun T : regular_opens α => (T : Set α)) '' S))ᵖᵖ, is_regular_p_p⟩

theorem regularOpen_sSup_unfold {S : Set (regular_opens α)} :
    sSup S = ⟨(⋃₀ ((fun T : regular_opens α => (T : Set α)) '' S))ᵖᵖ, is_regular_p_p⟩ :=
  rfl

theorem regularOpen_isLUB_sSup (S : Set (regular_opens α)) : IsLUB S (sSup S) := by
  constructor
  · intro T hT
    change (T : Set α) ⊆ (⋃₀ ((fun U : regular_opens α => (U : Set α)) '' S))ᵖᵖ
    have h_open : IsOpen (⋃₀ ((fun U : regular_opens α => (U : Set α)) '' S)) := by
      apply isOpen_sUnion
      intro U hU
      rcases hU with ⟨V, _, rfl⟩
      exact isOpen_of_is_regular V.2
    apply subset_trans ?_ (subset_p_p_of_open h_open)
    intro x hx
    exact Set.mem_sUnion.mpr ⟨(T : Set α), ⟨T, hT, rfl⟩, hx⟩
  · intro B hB
    change (⋃₀ ((fun U : regular_opens α => (U : Set α)) '' S))ᵖᵖ ⊆ (B : Set α)
    apply is_regular_stable_subset B.2
    intro x hx
    rcases Set.mem_sUnion.mp hx with ⟨U, hU, hxU⟩
    rcases hU with ⟨T, hT, rfl⟩
    exact hB hT hxU

/-- Regular opens form a complete lattice under arbitrary regularized unions. -/
instance regularOpenCompleteLattice : CompleteLattice (regular_opens α) where
  top := ⟨Set.univ, is_regular_univ⟩
  le_top S := by
    intro x hx
    trivial
  bot := ⟨∅, is_regular_empty⟩
  bot_le S := by
    intro x hx
    exact False.elim hx
  sup S T := ⟨((S : Set α) ∪ (T : Set α))ᵖᵖ, is_regular_sup⟩
  le_sup_left S T := by
    change (S : Set α) ⊆ ((S : Set α) ∪ (T : Set α))ᵖᵖ
    exact subset_trans (fun _ hx => Or.inl hx)
      (subset_p_p_of_open ((isOpen_of_is_regular S.2).union (isOpen_of_is_regular T.2)))
  le_sup_right S T := by
    change (T : Set α) ⊆ ((S : Set α) ∪ (T : Set α))ᵖᵖ
    exact subset_trans (fun _ hx => Or.inr hx)
      (subset_p_p_of_open ((isOpen_of_is_regular S.2).union (isOpen_of_is_regular T.2)))
  sup_le S T U hSU hTU := by
    change ((S : Set α) ∪ (T : Set α))ᵖᵖ ⊆ (U : Set α)
    apply is_regular_stable_subset U.2
    intro x hx
    exact hx.elim (fun hxS => hSU hxS) (fun hxT => hTU hxT)
  inf S T := ⟨(S : Set α) ∩ (T : Set α), is_regular_inter S.2 T.2⟩
  inf_le_left S T := by
    intro x hx
    exact hx.1
  inf_le_right S T := by
    intro x hx
    exact hx.2
  le_inf S T U hST hSU := by
    intro x hx
    exact ⟨hST hx, hSU hx⟩
  __ := completeLatticeOfSup (regular_opens α) regularOpen_isLUB_sSup

/-- Regular opens form a complete Boolean algebra. -/
instance regularOpenCompleteBooleanAlgebra : CompleteBooleanAlgebra (regular_opens α) where
  __ := regularOpenCompleteLattice
  __ := regularOpenBooleanAlgebra

theorem regularOpen_bot_lt {S : regular_opens α} : ⊥ < S ↔ (S : Set α).Nonempty := by
  constructor
  · intro h
    by_contra h_empty
    apply h.2
    intro x hx
    exact h_empty ⟨x, hx⟩
  · intro h_nonempty
    constructor
    · exact bot_le
    · intro hle
      rcases h_nonempty with ⟨x, hx⟩
      exact hle hx

instance regularOpenNontrivial [Nonempty α] : Nontrivial (regular_opens α) where
  exists_pair_ne := by
    refine ⟨⊥, ⊤, ne_of_lt ?_⟩
    apply (regularOpen_bot_lt (S := (⊤ : regular_opens α))).mpr
    rcases ‹Nonempty α› with ⟨x⟩
    exact ⟨x, trivial⟩

end Flypitch
