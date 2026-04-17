import Mathlib

universe u v w w'

namespace Flypitch
namespace delta_system

open Cardinal Function Set

set_option linter.missingDocs false
set_option linter.style.longLine false

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

namespace Set

open Cardinal Subtype

/-- A finite image of an injective-on-set map comes from a finite source set. -/
theorem finite_of_finite_image_of_inj_on {α : Type u} {β : Type v} (f : α → β) (s : Set α)
    (hf : Set.InjOn f s) (h : (f '' s).Finite) : s.Finite := by
  let e : s ↪ (f '' s) :=
    ⟨fun x => ⟨f x, ⟨x, x.2, rfl⟩⟩, fun x y hxy => by
      apply Subtype.ext
      exact hf x.2 y.2 (Subtype.ext_iff.mp hxy)⟩
  haveI : Finite (f '' s) := h.to_subtype
  haveI : Finite s := Finite.of_injective e e.injective
  exact s.toFinite

/-- An embedding into a countable set has countable domain. -/
theorem countable_of_embedding {α : Type u} {β : Type v} {s : Set α} {t : Set β} (f : s ↪ t)
    (h : t.Countable) : s.Countable := by
  letI : Countable t := h.to_subtype
  have hs : Countable s := f.injective.countable
  simpa [Set.countable_coe_iff] using hs

/-- Dependent pointwise equality over a subset. -/
def eqOn' {α : Type u} {β : α → Type v} (f g : ∀ x, β x) (s : Set α) : Prop :=
  ∀ ⦃x⦄, x ∈ s → f x = g x

theorem eqOn'_iff {α : Type u} {β : α → Type v} (f g : ∀ x, β x) (s : Set α) :
    eqOn' f g s ↔ Set.restrict s f = Set.restrict s g := by
  constructor
  · intro h
    funext x
    exact h x.2
  · intro h x hx
    exact congrArg (fun k => k ⟨x, hx⟩) h

end Set

open Set TopologicalSpace Cardinal Subtype

section CCC

variable (α : Type u) [TopologicalSpace α]

/-- Every pairwise-disjoint family of open sets is countable. -/
def countable_chain_condition : Prop :=
  ∀ s : Set (Set α), (∀ ⦃o⦄, o ∈ s → IsOpen o) → s.PairwiseDisjoint id → s.Countable

variable {α}

theorem countable_chain_condition_of_nonempty
    [TopologicalSpace α]
    (h : ∀ s : Set (Set α), (∀ ⦃o⦄, o ∈ s → o ≠ ∅) → (∀ ⦃o⦄, o ∈ s → IsOpen o) →
      s.PairwiseDisjoint id → s.Countable) :
    countable_chain_condition α := by
  intro s hopen hdisj
  let s' : Set (Set α) := s \ {∅}
  have hs' : ∀ ⦃o : Set α⦄, o ∈ s' → o ≠ ∅ := by
    intro o ho hEmpty
    exact ho.2 (by simpa [hEmpty])
  have hopen' : ∀ ⦃o : Set α⦄, o ∈ s' → IsOpen o := by
    intro o ho
    exact hopen ho.1
  have hdisj' : s'.PairwiseDisjoint id := by
    intro a ha b hb hab
    exact hdisj ha.1 hb.1 hab
  have hcount' : s'.Countable := h _ hs' hopen' hdisj'
  have hcount : (insert ∅ s').Countable := hcount'.insert ∅
  refine hcount.mono ?_
  intro o ho
  by_cases hEmpty : o = ∅
  · simpa [hEmpty] using mem_insert ∅ s'
  · exact Or.inr ⟨ho, hEmpty⟩

theorem countable_chain_condition_of_countable
    [TopologicalSpace α] (h : Cardinal.mk α ≤ Cardinal.aleph0) :
    countable_chain_condition α := by
  have hcountable : Countable α := Cardinal.mk_le_aleph0_iff.mp <| by simpa using h
  letI : Countable α := hcountable
  apply countable_chain_condition_of_nonempty
  intro s hsnonempty _ hsdisj
  let point (x : s) : α :=
    (Classical.choice ((Set.nonempty_iff_ne_empty.mpr (hsnonempty x.2)).to_subtype) : x.1).1
  let f : s ↪ α :=
    ⟨point,
      fun x y hxy => by
        apply Subtype.ext
        by_contra hne
        have hdis := hsdisj x.2 y.2 hne
        let px : α := point x
        let py : α := point y
        have hxy' : px = py := hxy
        have hxmem : px ∈ x.1 := by
          dsimp [px, point]
          exact (Classical.choice ((Set.nonempty_iff_ne_empty.mpr (hsnonempty x.2)).to_subtype) : x.1).2
        have hymem : py ∈ y.1 := by
          dsimp [py, point]
          exact (Classical.choice ((Set.nonempty_iff_ne_empty.mpr (hsnonempty y.2)).to_subtype) : y.1).2
        have hymem' : px ∈ y.1 := hxy' ▸ hymem
        exact hdis.le_bot ⟨hxmem, hymem'⟩⟩
  have hsCount : Countable s := f.injective.countable
  simpa [Set.countable_coe_iff] using hsCount

end CCC

end Flypitch

attribute [nolint unusedArguments]
  Flypitch.countable_chain_condition_of_nonempty Flypitch.countable_chain_condition_of_countable
