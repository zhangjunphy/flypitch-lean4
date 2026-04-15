import Mathlib

universe u v w w'

namespace Flypitch
namespace delta_system

open Cardinal Function Set

/-- A family of sets is a delta-system when all pairwise intersections agree on a common root. -/
def is_delta_system {ι : Type w} {α : Type u} (A : ι → Set α) : Prop :=
  ∃ root : Set α, ∀ ⦃x y : ι⦄, x ≠ y → A x ∩ A y = root

/-- In a delta-system indexed by at least two points, the common root sits inside each member. -/
theorem root_subset {ι : Type w} {α : Type u} {A : ι → Set α} (hι : (2 : Cardinal) ≤ Cardinal.mk ι)
    {root : Set α} (x : ι) (h : ∀ ⦃x y : ι⦄, x ≠ y → A x ∩ A y = root) : root ⊆ A x := by
  rcases (Cardinal.two_le_iff' x).mp hι with ⟨y, hy⟩
  rw [← h hy]
  exact inter_subset_right

/-- If each member of a delta-system is finite, then the common root is finite as well. -/
theorem finite_root {ι : Type w} {α : Type u} {A : ι → Set α} (hι : (2 : Cardinal) ≤ Cardinal.mk ι)
    {root : Set α} (h2A : ∀ x : ι, (A x).Finite)
    (h : ∀ ⦃x y : ι⦄, x ≠ y → A x ∩ A y = root) : root.Finite := by
  rcases (Cardinal.two_le_iff.mp hι) with ⟨t, u, htu⟩
  rw [← h htu]
  exact (h2A t).subset inter_subset_left

/-- Taking preimages preserves the delta-system property. -/
theorem is_delta_system_preimage {ι : Type w} {α : Type u} {β : Type v} {A : ι → Set α}
    (f : β → α) (h : is_delta_system A) : is_delta_system (fun i => f ⁻¹' A i) := by
  rcases h with ⟨root, hroot⟩
  refine ⟨f ⁻¹' root, ?_⟩
  intro x y hxy
  rw [← preimage_inter]
  exact congrArg (preimage f) (hroot hxy)

/-- Injective images preserve and reflect the delta-system property. -/
theorem is_delta_system_image {ι : Type w} {α : Type u} {β : Type v} {A : ι → Set α} {f : α → β}
    (hf : Injective f) : is_delta_system (fun i => f '' A i) ↔ is_delta_system A := by
  constructor
  · intro h
    have h' := is_delta_system_preimage f h
    simpa [preimage_image_eq _ hf] using h'
  · rintro ⟨root, hroot⟩
    refine ⟨f '' root, ?_⟩
    intro x y hxy
    rw [← Set.image_inter hf, hroot hxy]

/-- When each set lies in the range of an injective map, preimages characterize delta-systems. -/
theorem is_delta_system_preimage_iff {ι : Type w} {α : Type u} {β : Type v} {A : ι → Set α}
    {f : β → α} (hf : Injective f) (hfA : ∀ i, A i ⊆ range f) :
    is_delta_system (fun i => f ⁻¹' A i) ↔ is_delta_system A := by
  constructor
  · rintro ⟨root, hroot⟩
    refine ⟨f '' root, ?_⟩
    intro i j hij
    calc
      A i ∩ A j = (f '' (f ⁻¹' A i)) ∩ (f '' (f ⁻¹' A j)) := by
        rw [Set.image_preimage_eq_of_subset (hfA i), Set.image_preimage_eq_of_subset (hfA j)]
      _ = f '' (f ⁻¹' A i ∩ f ⁻¹' A j) := by rw [← Set.image_inter hf]
      _ = f '' root := by rw [hroot hij]
  · exact is_delta_system_preimage f

/-- Precomposing a delta-system family by an injective map preserves the property. -/
theorem is_delta_system_precompose {ι : Type w} {ι' : Type w'} {α : Type u} {A : ι → Set α}
    (f : ι' → ι) (hf : Injective f) (h : is_delta_system A) : is_delta_system (A ∘ f) := by
  rcases h with ⟨root, hroot⟩
  refine ⟨root, ?_⟩
  intro x y hxy
  exact hroot (fun hEq => hxy (hf hEq))

/-- Reindexing by an equivalence preserves delta-systems in both directions. -/
theorem is_delta_system_precompose_iff {ι : Type w} {ι' : Type w'} {α : Type u} {A : ι → Set α}
    (f : ι' ≃ ι) : is_delta_system A ↔ is_delta_system (A ∘ f) := by
  constructor
  · exact is_delta_system_precompose f f.injective
  · intro h
    simpa [Function.comp_def] using is_delta_system_precompose f.symm f.symm.injective h

end delta_system
end Flypitch
