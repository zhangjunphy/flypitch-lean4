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

/-- The order type of a linear well-founded order as an ordinal. -/
abbrev orderType (α : Type u) [LinearOrder α] [WellFoundedLT α] : Ordinal :=
  Ordinal.type (α := α) (· < ·)

/-- For a linear order, relation-style unboundedness for `<` is the same as `IsCofinal`. -/
theorem unbounded_lt_iff_isCofinal {α : Type u} [LinearOrder α] (s : Set α) :
    Set.Unbounded (· < ·) s ↔ IsCofinal s := by
  constructor
  · intro h a
    rcases h a with ⟨b, hb, hba⟩
    exact ⟨b, hb, not_lt.mp hba⟩
  · intro h a
    rcases h a with ⟨b, hb, hle⟩
    exact ⟨b, hb, not_lt.mpr hle⟩

/-- In a well-founded linear order of regular cardinality, the order cofinality is that cardinal. -/
theorem cof_eq_mk_of_isRegular {α : Type u} [LinearOrder α] [WellFoundedLT α]
    (h : Cardinal.IsRegular (Cardinal.mk α))
    (htype : Cardinal.ord (Cardinal.mk α) = orderType α) : Order.cof α = Cardinal.mk α := by
  calc
    Order.cof α = (orderType α).cof := by simpa [orderType] using (Ordinal.cof_type α).symm
    _ = (Cardinal.ord (Cardinal.mk α)).cof := by rw [htype]
    _ = Cardinal.mk α := h.cof_ord

/-- A small-index union of bounded sets is bounded. Contrapositive of the Mathlib cofinality API. -/
theorem exists_unbounded_of_unbounded_iUnion {α ι : Type u} [LinearOrder α]
    {s : ι → Set α} (hU : Set.Unbounded (· < ·) (⋃ i, s i))
    (hsmall : Cardinal.mk ι < Order.cof α) : ∃ i, Set.Unbounded (· < ·) (s i) := by
  have hC : IsCofinal (⋃ i, s i) := (unbounded_lt_iff_isCofinal _).1 hU
  rcases isCofinal_of_isCofinal_iUnion hC hsmall with ⟨i, hi⟩
  exact ⟨i, (unbounded_lt_iff_isCofinal _).2 hi⟩

/-- The first selection step in the Δ-system lemma proof: from an unbounded union of
order-isomorphic fibers, choose a `<`-minimal parameter whose realized range is unbounded. -/
theorem exists_minimal_unbounded_parameter {κ : Cardinal}
    {θ : Type u} [LinearOrder θ] [WellFoundedLT θ]
    (hκθ : κ < Cardinal.mk θ) (hθ : Cardinal.IsRegular (Cardinal.mk θ))
    (htype : Cardinal.ord (Cardinal.mk θ) = orderType θ)
    {ρ : Type u} [LinearOrder ρ] [WellFoundedLT ρ]
    (hρ : Cardinal.mk ρ < κ)
    {ι : Type u} {A : ι → Set θ}
    (h2A : ∀ i, RelIso (· < · : ρ → ρ → Prop) (Subrel (· < · : θ → θ → Prop) (A i)))
    (hU : Set.Unbounded (· < ·) (⋃ i, A i)) :
    ∃ ξ : ρ,
      Set.Unbounded (· < ·) (Set.range fun i : ι => ((h2A i) ξ).val) ∧
        ∀ η : ρ, η < ξ → ¬ Set.Unbounded (· < ·) (Set.range fun i : ι => ((h2A i) η).val) := by
  classical
  let nr : ι → ρ → θ := fun i ξ => ((h2A i) ξ).val
  have hmem (i : ι) (ξ : ρ) : nr i ξ ∈ A i := ((h2A i) ξ).2
  have hU_eq : (⋃ i, A i) = (⋃ ξ : ρ, Set.range fun i : ι => nr i ξ) := by
    apply Set.Subset.antisymm
    · intro x hx
      rcases Set.mem_iUnion.1 hx with ⟨i, hi⟩
      refine Set.mem_iUnion.mpr ⟨(h2A i).symm ⟨x, hi⟩, ?_⟩
      exact Set.mem_range.mpr ⟨i, by
        simpa [nr] using congrArg Subtype.val ((h2A i).apply_symm_apply ⟨x, hi⟩)⟩
    · intro x hx
      rcases Set.mem_iUnion.1 hx with ⟨ξ, hξ⟩
      rcases Set.mem_range.1 hξ with ⟨i, rfl⟩
      exact Set.mem_iUnion.mpr ⟨i, hmem i ξ⟩
  have hcof : Cardinal.mk ρ < Order.cof θ := by
    rw [cof_eq_mk_of_isRegular hθ htype]
    exact lt_trans hρ hκθ
  have hU' : Set.Unbounded (· < ·) (⋃ ξ : ρ, Set.range fun i : ι => nr i ξ) := by
    simpa [hU_eq] using hU
  rcases exists_unbounded_of_unbounded_iUnion hU' hcof with ⟨ξ₀, hξ₀⟩
  let good : Set ρ := {ξ | Set.Unbounded (· < ·) (Set.range fun i : ι => nr i ξ)}
  have hξ₀_good : ξ₀ ∈ good := hξ₀
  have hwf : WellFounded ((· < ·) : ρ → ρ → Prop) := IsWellFounded.wf
  let ξ : ρ := hwf.min good ⟨ξ₀, hξ₀_good⟩
  have hξ : ξ ∈ good := hwf.min_mem good ⟨ξ₀, hξ₀_good⟩
  refine ⟨ξ, hξ, ?_⟩
  intro η hη hηU
  exact hwf.not_lt_min good hηU hη

/-- Initial segments in a well-founded linear order have strictly smaller cardinality than the
ambient regular ordinal representation. -/
theorem mk_Iio_lt_of_ord_eq {α : Type u} [LinearOrder α] [WellFoundedLT α]
    (x : α) (h : Cardinal.ord (Cardinal.mk α) = orderType α) :
    Cardinal.mk (Set.Iio x) < Cardinal.mk α := by
  simpa [orderType] using Cardinal.mk_Iio_lt x h

/-- A bounded subset of a well-founded linear order has cardinality strictly below the ambient
regular cardinal. -/
theorem mk_lt_of_bounded {α : Type u} [LinearOrder α] [WellFoundedLT α]
    (s : Set α) (hord : Cardinal.ord (Cardinal.mk α) = orderType α)
    (hbdd : Set.Bounded (· < ·) s) : Cardinal.mk s < Cardinal.mk α := by
  rcases hbdd with ⟨x, hx⟩
  have hs : s ⊆ Set.Iio x := by
    intro y hy
    exact hx y hy
  exact lt_of_le_of_lt (Cardinal.mk_le_mk_of_subset hs) (mk_Iio_lt_of_ord_eq x hord)

/-- A typein-initial segment determined by an ordinal below the order type has small cardinality. -/
theorem mk_typein_initial_segment_lt {α : Type u} [LinearOrder α] [WellFoundedLT α]
    [IsWellOrder α (· < ·)] (hord : Cardinal.ord (Cardinal.mk α) = orderType α)
    {o : Ordinal} (ho : o < orderType α) :
    Cardinal.mk {x : α | Ordinal.typein (· < ·) x < o} < Cardinal.mk α := by
  rcases Ordinal.typein_surj (· < ·) ho with ⟨a, ha⟩
  have hsub : {x : α | Ordinal.typein (· < ·) x < o} ⊆ Set.Iio a := by
    intro x hx
    rw [← ha] at hx
    exact (Ordinal.typein_lt_typein (· < ·)).1 hx
  exact lt_of_le_of_lt (Cardinal.mk_le_mk_of_subset hsub) (mk_Iio_lt_of_ord_eq a hord)

/-- The order type of a regular cardinality well-order is a successor-limit ordinal. -/
theorem isSuccLimit_orderType_of_isRegular {α : Type u} [LinearOrder α] [WellFoundedLT α]
    (h : Cardinal.IsRegular (Cardinal.mk α))
    (htype : Cardinal.ord (Cardinal.mk α) = orderType α) : Order.IsSuccLimit (orderType α) := by
  rw [← htype]
  exact Cardinal.isSuccLimit_ord h.aleph0_le

/-- A small supremum of ordinals below a regular order type is still below it. -/
theorem iSup_lt_orderType_of_isRegular {α : Type u} {ι : Type u}
    [LinearOrder α] [WellFoundedLT α]
    (h : Cardinal.IsRegular (Cardinal.mk α))
    (htype : Cardinal.ord (Cardinal.mk α) = orderType α)
    (hι : Cardinal.mk ι < Cardinal.mk α)
    {f : ι → Ordinal} (hf : ∀ i, f i < orderType α) :
    iSup f < orderType α := by
  rw [← htype]
  exact Cardinal.iSup_lt_ord_of_isRegular h hι (fun i => by simpa [htype] using hf i)

/-- A small supremum of successors of ordinals below a regular order type is still below it. -/
theorem iSup_succ_lt_orderType_of_isRegular {α : Type u} {ι : Type u}
    [LinearOrder α] [WellFoundedLT α]
    (h : Cardinal.IsRegular (Cardinal.mk α))
    (htype : Cardinal.ord (Cardinal.mk α) = orderType α)
    (hι : Cardinal.mk ι < Cardinal.mk α)
    {f : ι → Ordinal} (hf : ∀ i, f i < orderType α) :
    iSup (fun i => Order.succ (f i)) < orderType α := by
  have hlim := isSuccLimit_orderType_of_isRegular h htype
  exact iSup_lt_orderType_of_isRegular h htype hι (fun i => hlim.succ_lt (hf i))

/-- Initial segments of a well-founded linear order are small relative to any strictly larger
cardinal. -/
theorem mk_Iio_lt_of_lt_card {ρ : Type u} [LinearOrder ρ]
    {c : Cardinal} (hρc : Cardinal.mk ρ < c) (ξ : ρ) : Cardinal.mk (Set.Iio ξ) < c :=
  lt_of_le_of_lt (Cardinal.mk_set_le (Set.Iio ξ)) hρc

/-- Subtype form of `mk_Iio_lt_of_lt_card`, convenient for indexing `α₀` by `{x // x < ξ}`. -/
theorem mk_subtype_lt_of_lt_card {ρ : Type u} [LinearOrder ρ]
    {c : Cardinal} (hρc : Cardinal.mk ρ < c) (ξ : ρ) : Cardinal.mk {x : ρ // x < ξ} < c :=
  calc
    Cardinal.mk {x : ρ // x < ξ} = Cardinal.mk (Set.Iio ξ) := by
      apply Cardinal.mk_congr
      exact
      { toFun := fun x => ⟨x.1, x.2⟩
        invFun := fun x => ⟨x.1, x.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    _ < c := mk_Iio_lt_of_lt_card hρc ξ

/-- Outer-supremum bound for the `α₀` construction in the Δ-system lemma. -/
theorem iSup_Iio_lt_orderType_of_isRegular
    {θ ρ : Type u} [LinearOrder θ] [WellFoundedLT θ] [LinearOrder ρ]
    (hθ : Cardinal.IsRegular (Cardinal.mk θ))
    (hθtype : Cardinal.ord (Cardinal.mk θ) = orderType θ)
    (hρθ : Cardinal.mk ρ < Cardinal.mk θ) (ξ : ρ)
    {f : {x : ρ // x < ξ} → Ordinal} (hf : ∀ x, f x < orderType θ) :
    iSup f < orderType θ := by
  exact iSup_lt_orderType_of_isRegular hθ hθtype
    (mk_subtype_lt_of_lt_card hρθ ξ) hf

/-- If the range of a map into a well-founded linear order is bounded, then the supremum of
successor type-indices of its values is below the full order type. This is the inner-bound step in
the `α₀` construction. -/
theorem iSup_succ_typein_range_lt_of_bounded {α ι : Type u} [LinearOrder α] [WellFoundedLT α]
    [IsWellOrder α (· < ·)]
    (f : ι → α) (hbdd : Set.Bounded (· < ·) (Set.range f)) :
    iSup (fun i : ι => Order.succ (Ordinal.typein (· < ·) (f i))) < orderType α := by
  rcases hbdd with ⟨μ, hμ⟩
  have hle : (iSup fun i : ι => Order.succ (Ordinal.typein (· < ·) (f i))) ≤
      Ordinal.typein (· < ·) μ := by
    refine Ordinal.iSup_le fun i => ?_
    rw [Order.succ_le_iff]
    exact (Ordinal.typein_lt_typein (· < ·)).2 (hμ (f i) ⟨i, rfl⟩)
  exact lt_of_le_of_lt hle (by simpa [orderType] using Ordinal.typein_lt_type (· < ·) μ)

/-- Inner-bound step specialized to a minimal unbounded parameter: every parameter below it has a
bounded realized range, hence a bounded successor-type-index supremum. -/
theorem inner_iSup_lt_of_minimal_unbounded_parameter
    {θ ρ ι : Type u} [LinearOrder θ] [WellFoundedLT θ] [IsWellOrder θ (· < ·)] [LinearOrder ρ]
    (nr : ι → ρ → θ) {ξ : ρ}
    (hmin : ∀ η : ρ, η < ξ → ¬ Set.Unbounded (· < ·) (Set.range fun i : ι => nr i η))
    (η : {x : ρ // x < ξ}) :
    iSup (fun i : ι => Order.succ (Ordinal.typein (· < ·) (nr i η.1))) < orderType θ := by
  have hbdd : Set.Bounded (· < ·) (Set.range fun i : ι => nr i η.1) := by
    exact (Set.not_unbounded_iff (s := Set.range fun i : ι => nr i η.1)).1 (hmin η.1 η.2)
  exact iSup_succ_typein_range_lt_of_bounded (fun i : ι => nr i η.1) hbdd

/-- The full `α₀` bound from the Δ-system lemma proof, assembled from the inner and outer helper
tranches. -/
theorem alpha0_lt_orderType_of_minimal_unbounded_parameter
    {θ ρ ι : Type u} [LinearOrder θ] [WellFoundedLT θ] [IsWellOrder θ (· < ·)]
    [LinearOrder ρ]
    (hθ : Cardinal.IsRegular (Cardinal.mk θ))
    (hθtype : Cardinal.ord (Cardinal.mk θ) = orderType θ)
    (hρθ : Cardinal.mk ρ < Cardinal.mk θ)
    (nr : ι → ρ → θ) {ξ : ρ}
    (hmin : ∀ η : ρ, η < ξ → ¬ Set.Unbounded (· < ·) (Set.range fun i : ι => nr i η)) :
    (iSup fun η : {x : ρ // x < ξ} =>
      iSup fun i : ι => Order.succ (Ordinal.typein (· < ·) (nr i η.1))) < orderType θ := by
  apply iSup_Iio_lt_orderType_of_isRegular hθ hθtype hρθ ξ
  intro η
  exact inner_iSup_lt_of_minimal_unbounded_parameter nr hmin η

/-- Packaged opening of `delta_system_lemma_2`: choose the minimal unbounded parameter and prove the
associated `α₀` double supremum is below the ambient order type. -/
theorem exists_minimal_parameter_with_alpha0_bound {κ : Cardinal}
    {θ : Type u} [LinearOrder θ] [WellFoundedLT θ] [IsWellOrder θ (· < ·)]
    (hκθ : κ < Cardinal.mk θ) (hθ : Cardinal.IsRegular (Cardinal.mk θ))
    (hθtype : Cardinal.ord (Cardinal.mk θ) = orderType θ)
    {ρ : Type u} [LinearOrder ρ] [WellFoundedLT ρ]
    (hρθ : Cardinal.mk ρ < Cardinal.mk θ)
    (hρ : Cardinal.mk ρ < κ)
    {ι : Type u} {A : ι → Set θ}
    (h2A : ∀ i, RelIso (· < · : ρ → ρ → Prop) (Subrel (· < · : θ → θ → Prop) (A i)))
    (hU : Set.Unbounded (· < ·) (⋃ i, A i)) :
    ∃ ξ : ρ,
      Set.Unbounded (· < ·) (Set.range fun i : ι => ((h2A i) ξ).val) ∧
      (∀ η : ρ, η < ξ →
        ¬ Set.Unbounded (· < ·) (Set.range fun i : ι => ((h2A i) η).val)) ∧
      (iSup fun η : {x : ρ // x < ξ} =>
        iSup fun i : ι => Order.succ (Ordinal.typein (· < ·) ((h2A i) η.1).val)) <
          orderType θ := by
  rcases exists_minimal_unbounded_parameter hκθ hθ hθtype hρ h2A hU with ⟨ξ, hξU, hξmin⟩
  refine ⟨ξ, hξU, hξmin, ?_⟩
  exact alpha0_lt_orderType_of_minimal_unbounded_parameter hθ hθtype hρθ
    (fun i ξ => ((h2A i) ξ).val) hξmin

/-- Packaged opening of `delta_system_lemma_2` through the smallness of the typein-initial
segment determined by the constructed `α₀`. -/
theorem exists_minimal_parameter_with_small_alpha0_segment {κ : Cardinal}
    {θ : Type u} [LinearOrder θ] [WellFoundedLT θ] [IsWellOrder θ (· < ·)]
    (hκθ : κ < Cardinal.mk θ) (hθ : Cardinal.IsRegular (Cardinal.mk θ))
    (hθtype : Cardinal.ord (Cardinal.mk θ) = orderType θ)
    {ρ : Type u} [LinearOrder ρ] [WellFoundedLT ρ]
    (hρθ : Cardinal.mk ρ < Cardinal.mk θ)
    (hρ : Cardinal.mk ρ < κ)
    {ι : Type u} {A : ι → Set θ}
    (h2A : ∀ i, RelIso (· < · : ρ → ρ → Prop) (Subrel (· < · : θ → θ → Prop) (A i)))
    (hU : Set.Unbounded (· < ·) (⋃ i, A i)) :
    ∃ ξ : ρ,
      Set.Unbounded (· < ·) (Set.range fun i : ι => ((h2A i) ξ).val) ∧
      (∀ η : ρ, η < ξ →
        ¬ Set.Unbounded (· < ·) (Set.range fun i : ι => ((h2A i) η).val)) ∧
      Cardinal.mk
        {x : θ |
          Ordinal.typein (· < ·) x <
            iSup fun η : {x : ρ // x < ξ} =>
              iSup fun i : ι => Order.succ (Ordinal.typein (· < ·) ((h2A i) η.1).val)} <
        Cardinal.mk θ := by
  rcases exists_minimal_parameter_with_alpha0_bound hκθ hθ hθtype hρθ hρ h2A hU with
    ⟨ξ, hξU, hξmin, hα⟩
  exact ⟨ξ, hξU, hξmin, mk_typein_initial_segment_lt hθtype hα⟩

/-- A successor-limit order type gives arbitrarily large elements in the underlying well-order. -/
theorem exists_gt_of_isSuccLimit_orderType {α : Type u} [LinearOrder α] [WellFoundedLT α]
    [IsWellOrder α (· < ·)] (hlim : Order.IsSuccLimit (orderType α)) (x : α) :
    ∃ y : α, x < y := by
  have hx : Ordinal.typein (· < ·) x < orderType α := by
    simpa [orderType] using Ordinal.typein_lt_type (· < ·) x
  have hsx : Order.succ (Ordinal.typein (· < ·) x) < orderType α := hlim.succ_lt hx
  rcases Ordinal.typein_surj (· < ·) hsx with ⟨y, hy⟩
  refine ⟨y, ?_⟩
  rw [← Ordinal.typein_lt_typein (· < ·)]
  rw [hy]
  exact Order.lt_succ _

/-- An unbounded range in a successor-limit well-order strictly dominates every point. -/
theorem exists_range_gt_of_unbounded {α ι : Type u} [LinearOrder α] [WellFoundedLT α]
    [IsWellOrder α (· < ·)] (hlim : Order.IsSuccLimit (orderType α)) (f : ι → α)
    (hU : Set.Unbounded (· < ·) (Set.range f)) (x : α) : ∃ i : ι, x < f i := by
  rcases exists_gt_of_isSuccLimit_orderType hlim x with ⟨y, hxy⟩
  rcases hU y with ⟨z, hz, hzy⟩
  rcases hz with ⟨i, rfl⟩
  have hyz : y ≤ f i := not_lt.mp hzy
  exact ⟨i, lt_of_lt_of_le hxy hyz⟩

/-- Rephrase unboundedness of a range as the ability to dominate any ordinal bound below the full
order type. This is the selection step used in the recursive `pick` construction. -/
theorem exists_index_above_ordinal_of_unbounded
    {α ι : Type u} [LinearOrder α] [WellFoundedLT α] [IsWellOrder α (· < ·)]
    (hlim : Order.IsSuccLimit (orderType α)) (f : ι → α)
    (hU : Set.Unbounded (· < ·) (Set.range f)) {o : Ordinal} (ho : o < orderType α) :
    ∃ i : ι, Ordinal.enum (· < ·) ⟨o, ho⟩ < f i := by
  let x : α := Ordinal.enum (· < ·) ⟨o, ho⟩
  rcases exists_range_gt_of_unbounded hlim f hU x with ⟨i, hi⟩
  exact ⟨i, hi⟩

/-- A choice function version of `exists_index_above_ordinal_of_unbounded`. -/
noncomputable def choose_index_above_ordinal_of_unbounded
    {α ι : Type u} [LinearOrder α] [WellFoundedLT α] [IsWellOrder α (· < ·)]
    (hlim : Order.IsSuccLimit (orderType α)) (f : ι → α)
    (hU : Set.Unbounded (· < ·) (Set.range f)) {o : Ordinal} (ho : o < orderType α) : ι :=
  Classical.choose (exists_index_above_ordinal_of_unbounded hlim f hU ho)

theorem choose_index_above_ordinal_of_unbounded_spec
    {α ι : Type u} [LinearOrder α] [WellFoundedLT α] [IsWellOrder α (· < ·)]
    (hlim : Order.IsSuccLimit (orderType α)) (f : ι → α)
    (hU : Set.Unbounded (· < ·) (Set.range f)) {o : Ordinal} (ho : o < orderType α) :
    Ordinal.enum (· < ·) ⟨o, ho⟩ <
      f (choose_index_above_ordinal_of_unbounded hlim f hU ho) :=
  Classical.choose_spec (exists_index_above_ordinal_of_unbounded hlim f hU ho)

/-- Recursive choice of indices whose realized values stay above the ordinal bound determined by
all previously chosen values, under the regularity hypotheses used in the Δ-system proof. -/
noncomputable def pickAboveOrdinalRec
    {α ι : Type u} [LinearOrder α] [WellFoundedLT α] [IsWellOrder α (· < ·)]
    (hreg : Cardinal.IsRegular (Cardinal.mk α))
    (hord : Cardinal.ord (Cardinal.mk α) = orderType α)
    (hlim : Order.IsSuccLimit (orderType α)) (f : ι → α)
    (hU : Set.Unbounded (· < ·) (Set.range f)) : α → ι :=
  WellFounded.fix (r := (· < ·)) IsWellFounded.wf fun x rec =>
    let o : Ordinal :=
      iSup (fun y : {y : α // y < x} => Ordinal.typein (· < ·) (f (rec y.1 y.2)))
    let ho : o < orderType α := by
      apply iSup_lt_orderType_of_isRegular hreg hord (mk_Iio_lt_of_ord_eq x hord)
      intro y
      simpa [orderType] using Ordinal.typein_lt_type (· < ·) (f (rec y.1 y.2))
    choose_index_above_ordinal_of_unbounded hlim f hU ho

theorem pickAboveOrdinalRec_eq
    {α ι : Type u} [LinearOrder α] [WellFoundedLT α] [IsWellOrder α (· < ·)]
    (hreg : Cardinal.IsRegular (Cardinal.mk α))
    (hord : Cardinal.ord (Cardinal.mk α) = orderType α)
    (hlim : Order.IsSuccLimit (orderType α)) (f : ι → α)
    (hU : Set.Unbounded (· < ·) (Set.range f)) (x : α) :
    pickAboveOrdinalRec hreg hord hlim f hU x =
      let o : Ordinal :=
        iSup (fun y : {y : α // y < x} =>
          Ordinal.typein (· < ·) (f (pickAboveOrdinalRec hreg hord hlim f hU y.1)))
      let ho : o < orderType α := by
        apply iSup_lt_orderType_of_isRegular hreg hord (mk_Iio_lt_of_ord_eq x hord)
        intro y
        simpa [orderType] using Ordinal.typein_lt_type (· < ·)
          (f (pickAboveOrdinalRec hreg hord hlim f hU y.1))
      choose_index_above_ordinal_of_unbounded hlim f hU ho := by
  rw [pickAboveOrdinalRec, WellFounded.fix_eq]

theorem typein_lt_pickAboveOrdinalRec
    {α ι : Type u} [LinearOrder α] [WellFoundedLT α] [IsWellOrder α (· < ·)]
    (hreg : Cardinal.IsRegular (Cardinal.mk α))
    (hord : Cardinal.ord (Cardinal.mk α) = orderType α)
    (hlim : Order.IsSuccLimit (orderType α)) (f : ι → α)
    (hU : Set.Unbounded (· < ·) (Set.range f)) {x y : α} (hyx : y < x) :
    Ordinal.typein (· < ·) (f (pickAboveOrdinalRec hreg hord hlim f hU y)) <
      Ordinal.typein (· < ·) (f (pickAboveOrdinalRec hreg hord hlim f hU x)) := by
  rw [pickAboveOrdinalRec_eq hreg hord hlim f hU x]
  let o := iSup (fun z : {z : α // z < x} =>
    Ordinal.typein (· < ·) (f (pickAboveOrdinalRec hreg hord hlim f hU z.1)))
  have ho : o < orderType α := by
    apply iSup_lt_orderType_of_isRegular hreg hord (mk_Iio_lt_of_ord_eq x hord)
    intro z
    simpa [orderType] using Ordinal.typein_lt_type (· < ·)
      (f (pickAboveOrdinalRec hreg hord hlim f hU z.1))
  have hchosen : Ordinal.enum (· < ·) ⟨o, ho⟩ <
      f (choose_index_above_ordinal_of_unbounded hlim f hU ho) :=
    choose_index_above_ordinal_of_unbounded_spec hlim f hU ho
  have hchosen' : o < Ordinal.typein (· < ·)
      (f (choose_index_above_ordinal_of_unbounded hlim f hU ho)) := by
    simpa [Ordinal.typein_enum] using
      (Ordinal.typein_lt_typein (· < ·)).2 hchosen
  have hle : Ordinal.typein (· < ·) (f (pickAboveOrdinalRec hreg hord hlim f hU y)) ≤ o := by
    dsimp [o]
    exact Ordinal.le_iSup (fun z : {z : α // z < x} =>
      Ordinal.typein (· < ·) (f (pickAboveOrdinalRec hreg hord hlim f hU z.1))) ⟨y, hyx⟩
  simpa using lt_of_le_of_lt hle hchosen'

theorem strictMono_pickAboveOrdinalRec_values
    {α ι : Type u} [LinearOrder α] [WellFoundedLT α] [IsWellOrder α (· < ·)]
    (hreg : Cardinal.IsRegular (Cardinal.mk α))
    (hord : Cardinal.ord (Cardinal.mk α) = orderType α)
    (hlim : Order.IsSuccLimit (orderType α)) (f : ι → α)
    (hU : Set.Unbounded (· < ·) (Set.range f)) :
    StrictMono fun x : α => f (pickAboveOrdinalRec hreg hord hlim f hU x) := by
  intro x y hxy
  exact (Ordinal.typein_lt_typein (· < ·)).1 <|
    typein_lt_pickAboveOrdinalRec hreg hord hlim f hU hxy

/-- The recursive picked values have full cardinality. -/
theorem mk_range_pickAboveOrdinalRec_eq
    {α ι : Type u} [LinearOrder α] [WellFoundedLT α] [IsWellOrder α (· < ·)]
    (hreg : Cardinal.IsRegular (Cardinal.mk α))
    (hord : Cardinal.ord (Cardinal.mk α) = orderType α)
    (hlim : Order.IsSuccLimit (orderType α)) (f : ι → α)
    (hU : Set.Unbounded (· < ·) (Set.range f)) :
    Cardinal.mk (Set.range fun x : α => f (pickAboveOrdinalRec hreg hord hlim f hU x)) =
      Cardinal.mk α := by
  apply Cardinal.mk_range_eq
  exact (strictMono_pickAboveOrdinalRec_values hreg hord hlim f hU).injective

/-- The range of recursively picked indices has full cardinality. -/
theorem mk_range_picked_indices_eq
    {α ι : Type u} [LinearOrder α] [WellFoundedLT α] [IsWellOrder α (· < ·)]
    (hreg : Cardinal.IsRegular (Cardinal.mk α))
    (hord : Cardinal.ord (Cardinal.mk α) = orderType α)
    (hlim : Order.IsSuccLimit (orderType α)) (f : ι → α)
    (hU : Set.Unbounded (· < ·) (Set.range f)) :
    Cardinal.mk (Set.range fun x : α => pickAboveOrdinalRec hreg hord hlim f hU x) =
      Cardinal.mk α := by
  apply Cardinal.mk_range_eq
  intro x y hxy
  apply (strictMono_pickAboveOrdinalRec_values hreg hord hlim f hU).injective
  exact congrArg f hxy

/-- Recursive choice of indices for the actual Δ-system proof: at stage `x`, choose an index whose
distinguished coordinate `ξ₀` lies above both the fixed base bound and every previously chosen
coordinate value. -/
noncomputable def pickParamAboveOrdinalRec
    {α σ ι : Type u} [LinearOrder α] [WellFoundedLT α] [IsWellOrder α (· < ·)]
    (hreg : Cardinal.IsRegular (Cardinal.mk α))
    (hord : Cardinal.ord (Cardinal.mk α) = orderType α)
    (hlim : Order.IsSuccLimit (orderType α)) (hσ : Cardinal.mk σ < Cardinal.mk α)
    (g : ι → σ → α) (ξ₀ : σ)
    (hU : Set.Unbounded (· < ·) (Set.range fun i : ι => g i ξ₀))
    {base : Ordinal} (hbase : base < orderType α) : α → ι :=
  WellFounded.fix (r := (· < ·)) IsWellFounded.wf fun x rec =>
    let o : Ordinal :=
      max base <| iSup fun p : σ × {y : α // y < x} =>
        Ordinal.typein (· < ·) (g (rec p.2.1 p.2.2) p.1)
    let ho : o < orderType α := by
      apply max_lt hbase
      apply iSup_lt_orderType_of_isRegular hreg hord
      · simpa [Cardinal.mk_prod] using
          Cardinal.mul_lt_of_lt hreg.aleph0_le hσ (mk_Iio_lt_of_ord_eq x hord)
      · intro p
        simpa [orderType] using Ordinal.typein_lt_type (· < ·) (g (rec p.2.1 p.2.2) p.1)
    choose_index_above_ordinal_of_unbounded hlim (fun i : ι => g i ξ₀) hU ho

theorem pickParamAboveOrdinalRec_eq
    {α σ ι : Type u} [LinearOrder α] [WellFoundedLT α] [IsWellOrder α (· < ·)]
    (hreg : Cardinal.IsRegular (Cardinal.mk α))
    (hord : Cardinal.ord (Cardinal.mk α) = orderType α)
    (hlim : Order.IsSuccLimit (orderType α)) (hσ : Cardinal.mk σ < Cardinal.mk α)
    (g : ι → σ → α) (ξ₀ : σ)
    (hU : Set.Unbounded (· < ·) (Set.range fun i : ι => g i ξ₀))
    {base : Ordinal} (hbase : base < orderType α) (x : α) :
    pickParamAboveOrdinalRec hreg hord hlim hσ g ξ₀ hU hbase x =
      let o : Ordinal :=
        max base <| iSup fun p : σ × {y : α // y < x} =>
          Ordinal.typein (· < ·)
            (g (pickParamAboveOrdinalRec hreg hord hlim hσ g ξ₀ hU hbase p.2.1) p.1)
      let ho : o < orderType α := by
        apply max_lt hbase
        apply iSup_lt_orderType_of_isRegular hreg hord
        · simpa [Cardinal.mk_prod] using
            Cardinal.mul_lt_of_lt hreg.aleph0_le hσ (mk_Iio_lt_of_ord_eq x hord)
        · intro p
          simpa [orderType] using Ordinal.typein_lt_type (· < ·)
            (g (pickParamAboveOrdinalRec hreg hord hlim hσ g ξ₀ hU hbase p.2.1) p.1)
      choose_index_above_ordinal_of_unbounded hlim (fun i : ι => g i ξ₀) hU ho := by
  rw [pickParamAboveOrdinalRec, WellFounded.fix_eq]

theorem base_lt_pickParamAboveOrdinalRec
    {α σ ι : Type u} [LinearOrder α] [WellFoundedLT α] [IsWellOrder α (· < ·)]
    (hreg : Cardinal.IsRegular (Cardinal.mk α))
    (hord : Cardinal.ord (Cardinal.mk α) = orderType α)
    (hlim : Order.IsSuccLimit (orderType α)) (hσ : Cardinal.mk σ < Cardinal.mk α)
    (g : ι → σ → α) (ξ₀ : σ)
    (hU : Set.Unbounded (· < ·) (Set.range fun i : ι => g i ξ₀))
    {base : Ordinal} (hbase : base < orderType α) (x : α) :
    base < Ordinal.typein (· < ·)
      (g (pickParamAboveOrdinalRec hreg hord hlim hσ g ξ₀ hU hbase x) ξ₀) := by
  rw [pickParamAboveOrdinalRec_eq hreg hord hlim hσ g ξ₀ hU hbase x]
  let o : Ordinal := max base <| iSup fun p : σ × {y : α // y < x} =>
    Ordinal.typein (· < ·)
      (g (pickParamAboveOrdinalRec hreg hord hlim hσ g ξ₀ hU hbase p.2.1) p.1)
  have ho : o < orderType α := by
    dsimp [o]
    apply max_lt hbase
    apply iSup_lt_orderType_of_isRegular hreg hord
    · simpa [Cardinal.mk_prod] using
        Cardinal.mul_lt_of_lt hreg.aleph0_le hσ (mk_Iio_lt_of_ord_eq x hord)
    · intro p
      simpa [orderType] using Ordinal.typein_lt_type (· < ·)
        (g (pickParamAboveOrdinalRec hreg hord hlim hσ g ξ₀ hU hbase p.2.1) p.1)
  have hchosen : Ordinal.enum (· < ·) ⟨o, ho⟩ <
      g (choose_index_above_ordinal_of_unbounded hlim (fun i : ι => g i ξ₀) hU ho) ξ₀ :=
    choose_index_above_ordinal_of_unbounded_spec hlim (fun i : ι => g i ξ₀) hU ho
  have hchosen' : o < Ordinal.typein (· < ·)
      (g (choose_index_above_ordinal_of_unbounded hlim (fun i : ι => g i ξ₀) hU ho) ξ₀) := by
    simpa [Ordinal.typein_enum] using (Ordinal.typein_lt_typein (· < ·)).2 hchosen
  exact lt_of_le_of_lt (le_max_left _ _) hchosen'

theorem typein_param_lt_pickParamAboveOrdinalRec
    {α σ ι : Type u} [LinearOrder α] [WellFoundedLT α] [IsWellOrder α (· < ·)]
    (hreg : Cardinal.IsRegular (Cardinal.mk α))
    (hord : Cardinal.ord (Cardinal.mk α) = orderType α)
    (hlim : Order.IsSuccLimit (orderType α)) (hσ : Cardinal.mk σ < Cardinal.mk α)
    (g : ι → σ → α) (ξ₀ : σ)
    (hU : Set.Unbounded (· < ·) (Set.range fun i : ι => g i ξ₀))
    {base : Ordinal} (hbase : base < orderType α) {x y : α} (hyx : y < x) (η : σ) :
    Ordinal.typein (· < ·)
        (g (pickParamAboveOrdinalRec hreg hord hlim hσ g ξ₀ hU hbase y) η) <
      Ordinal.typein (· < ·)
        (g (pickParamAboveOrdinalRec hreg hord hlim hσ g ξ₀ hU hbase x) ξ₀) := by
  rw [pickParamAboveOrdinalRec_eq hreg hord hlim hσ g ξ₀ hU hbase x]
  let o : Ordinal := max base <| iSup fun p : σ × {y : α // y < x} =>
    Ordinal.typein (· < ·)
      (g (pickParamAboveOrdinalRec hreg hord hlim hσ g ξ₀ hU hbase p.2.1) p.1)
  have ho : o < orderType α := by
    dsimp [o]
    apply max_lt hbase
    apply iSup_lt_orderType_of_isRegular hreg hord
    · simpa [Cardinal.mk_prod] using
        Cardinal.mul_lt_of_lt hreg.aleph0_le hσ (mk_Iio_lt_of_ord_eq x hord)
    · intro p
      simpa [orderType] using Ordinal.typein_lt_type (· < ·)
        (g (pickParamAboveOrdinalRec hreg hord hlim hσ g ξ₀ hU hbase p.2.1) p.1)
  have hchosen : Ordinal.enum (· < ·) ⟨o, ho⟩ <
      g (choose_index_above_ordinal_of_unbounded hlim (fun i : ι => g i ξ₀) hU ho) ξ₀ :=
    choose_index_above_ordinal_of_unbounded_spec hlim (fun i : ι => g i ξ₀) hU ho
  have hchosen' : o < Ordinal.typein (· < ·)
      (g (choose_index_above_ordinal_of_unbounded hlim (fun i : ι => g i ξ₀) hU ho) ξ₀) := by
    simpa [Ordinal.typein_enum] using (Ordinal.typein_lt_typein (· < ·)).2 hchosen
  have hle : Ordinal.typein (· < ·)
      (g (pickParamAboveOrdinalRec hreg hord hlim hσ g ξ₀ hU hbase y) η) ≤ o := by
    dsimp [o]
    refine le_trans ?_ (le_max_right _ _)
    exact Ordinal.le_iSup (fun p : σ × {y : α // y < x} =>
      Ordinal.typein (· < ·)
        (g (pickParamAboveOrdinalRec hreg hord hlim hσ g ξ₀ hU hbase p.2.1) p.1))
      (η, ⟨y, hyx⟩)
  simpa using lt_of_le_of_lt hle hchosen'

/-- The `pickParamAboveOrdinalRec` function is globally injective. -/
theorem pickParamAboveOrdinalRec_injective
    {α σ ι : Type u} [LinearOrder α] [WellFoundedLT α] [IsWellOrder α (· < ·)]
    (hreg : Cardinal.IsRegular (Cardinal.mk α))
    (hord : Cardinal.ord (Cardinal.mk α) = orderType α)
    (hlim : Order.IsSuccLimit (orderType α)) (hσ : Cardinal.mk σ < Cardinal.mk α)
    (g : ι → σ → α) (ξ₀ : σ)
    (hU : Set.Unbounded (· < ·) (Set.range fun i : ι => g i ξ₀))
    {base : Ordinal} (hbase : base < orderType α) :
    Function.Injective (pickParamAboveOrdinalRec hreg hord hlim hσ g ξ₀ hU hbase) := by
  intro x y h
  by_contra hne
  rcases lt_trichotomy x y with (hlt | heq | hgt)
  · have h_lt := typein_param_lt_pickParamAboveOrdinalRec hreg hord hlim hσ g ξ₀ hU hbase hlt ξ₀
    rw [h] at h_lt
    exact lt_irrefl _ h_lt
  · exact hne heq
  · have h_lt := typein_param_lt_pickParamAboveOrdinalRec hreg hord hlim hσ g ξ₀ hU hbase hgt ξ₀
    rw [h] at h_lt
    exact lt_irrefl _ h_lt

/-- Membership in the `η < ξ₀` part of the `α₀` supremum gives a strict type-index bound. -/
theorem typein_lt_alpha0_of_param_lt
    {α σ ι : Type u} [LinearOrder α] [IsWellOrder α (· < ·)]
    [LinearOrder σ] (g : ι → σ → α) {ξ₀ η : σ} (hη : η < ξ₀) (i : ι) :
    Ordinal.typein (· < ·) (g i η) <
      iSup (fun η' : {x : σ // x < ξ₀} =>
        iSup fun j : ι => Order.succ (Ordinal.typein (· < ·) (g j η'.1))) := by
  refine lt_of_lt_of_le (Order.lt_succ _) ?_
  refine le_trans ?_ (Ordinal.le_iSup (fun η' : {x : σ // x < ξ₀} =>
    iSup fun j : ι => Order.succ (Ordinal.typein (· < ·) (g j η'.1))) ⟨η, hη⟩)
  exact Ordinal.le_iSup (fun j : ι => Order.succ (Ordinal.typein (· < ·) (g j η))) i

/-- If a value is in a member `A i`, then the inverse image of that value under the rel-isomorphism
has type-index at least `ξ₀` exactly when it is not below `ξ₀`. -/
theorem not_lt_of_typein_ge_typein
    {σ : Type u} [LinearOrder σ] [IsWellOrder σ (· < ·)]
    {η ξ₀ : σ} (hη : ¬ Ordinal.typein (· < ·) η < Ordinal.typein (· < ·) ξ₀) :
    ¬ η < ξ₀ := by
  intro hlt
  exact hη ((Ordinal.typein_lt_typein (· < ·)).2 hlt)

/-- A rel-isomorphism to a picked set turns the parameterized pick inequality into a strict
comparison in the parameter order. This is the contradiction branch in the intersection proof. -/
theorem param_lt_of_mem_and_pick_bound
    {α σ ι : Type u} [LinearOrder α] [LinearOrder σ]
    {A : ι → Set α}
    (hA : ∀ i, RelIso (· < · : σ → σ → Prop) (Subrel (· < · : α → α → Prop) (A i)))
    {j : ι} {z : α} (hzj : z ∈ A j) {ξ₀ : σ}
    (hbound : z < ((hA j) ξ₀).val) : (hA j).symm ⟨z, hzj⟩ < ξ₀ := by
  have hrel : Subrel (· < · : α → α → Prop) (A j) ⟨z, hzj⟩ ((hA j) ξ₀) := by
    simpa [Subrel] using hbound
  simpa using ((hA j).symm_apply_rel).2 hrel

/-- Pairwise intersections of the parameterized picked family lie in the `α₀` initial segment. -/
theorem picked_inter_subset_alpha0
    {α σ ι : Type u} [LinearOrder α] [WellFoundedLT α] [IsWellOrder α (· < ·)]
    [LinearOrder σ]
    (hreg : Cardinal.IsRegular (Cardinal.mk α))
    (hord : Cardinal.ord (Cardinal.mk α) = orderType α)
    (hlim : Order.IsSuccLimit (orderType α)) (hσ : Cardinal.mk σ < Cardinal.mk α)
    {A : ι → Set α}
    (hA : ∀ i, RelIso (· < · : σ → σ → Prop) (Subrel (· < · : α → α → Prop) (A i)))
    (ξ₀ : σ)
    (hU : Set.Unbounded (· < ·) (Set.range fun i : ι => ((hA i) ξ₀).val))
    {base : Ordinal}
    (hbase_eq : base =
      iSup (fun η : {x : σ // x < ξ₀} =>
        iSup fun i : ι => Order.succ (Ordinal.typein (· < ·) ((hA i) η.1).val)))
    (hbase : base < orderType α) {x y : α} (hxy : x < y) :
    A (pickParamAboveOrdinalRec hreg hord hlim hσ (fun i η => ((hA i) η).val) ξ₀ hU hbase x) ∩
        A (pickParamAboveOrdinalRec hreg hord hlim hσ (fun i η => ((hA i) η).val) ξ₀ hU hbase y) ⊆
      {z : α | Ordinal.typein (· < ·) z < base} := by
  intro z hz
  let pick := pickParamAboveOrdinalRec hreg hord hlim hσ (fun i η => ((hA i) η).val) ξ₀ hU hbase
  let ηy : σ := (hA (pick y)).symm ⟨z, hz.2⟩
  have hz_eq_y : z = ((hA (pick y)) ηy).val := by
    dsimp [ηy]
    exact congrArg Subtype.val ((hA (pick y)).apply_symm_apply ⟨z, hz.2⟩).symm
  by_cases hη : ηy < ξ₀
  · rw [hbase_eq, hz_eq_y]
    exact typein_lt_alpha0_of_param_lt (fun i η => ((hA i) η).val) hη (pick y)
  · have hlt_typein : Ordinal.typein (· < ·) z <
        Ordinal.typein (· < ·) (((hA (pick y)) ξ₀).val) := by
      let ηx : σ := (hA (pick x)).symm ⟨z, hz.1⟩
      have hx_eq : z = ((hA (pick x)) ηx).val := by
        dsimp [ηx]
        exact congrArg Subtype.val ((hA (pick x)).apply_symm_apply ⟨z, hz.1⟩).symm
      have hpick := typein_param_lt_pickParamAboveOrdinalRec hreg hord hlim hσ
        (fun i η => ((hA i) η).val) ξ₀ hU hbase hxy ηx
      rw [hx_eq]
      simpa [pick] using hpick
    have hlt : z < ((hA (pick y)) ξ₀).val :=
      (Ordinal.typein_lt_typein (· < ·)).1 hlt_typein
    have hηlt : ηy < ξ₀ := param_lt_of_mem_and_pick_bound hA hz.2 hlt
    exact False.elim (hη hηlt)

/-- Each picked member has only `#σ` many points below the `α₀` initial segment. This is the
bounded-codomain estimate used before applying infinite pigeonhole. -/
theorem picked_alpha0_inter_mk_le
    {α σ ι : Type u} [LinearOrder α] [WellFoundedLT α] [IsWellOrder α (· < ·)]
    [LinearOrder σ]
    (hreg : Cardinal.IsRegular (Cardinal.mk α))
    (hord : Cardinal.ord (Cardinal.mk α) = orderType α)
    (hlim : Order.IsSuccLimit (orderType α)) (hσ : Cardinal.mk σ < Cardinal.mk α)
    {A : ι → Set α}
    (hA : ∀ i, RelIso (· < · : σ → σ → Prop) (Subrel (· < · : α → α → Prop) (A i)))
    (ξ₀ : σ)
    (hU : Set.Unbounded (· < ·) (Set.range fun i : ι => ((hA i) ξ₀).val))
    {base : Ordinal} (hbase : base < orderType α) (x : α) :
    Cardinal.mk
        ((A (pickParamAboveOrdinalRec hreg hord hlim hσ (fun i η => ((hA i) η).val) ξ₀ hU hbase x) ∩
          {z : α | Ordinal.typein (· < ·) z < base}) : Set α) ≤
      Cardinal.mk σ := by
  let pick := pickParamAboveOrdinalRec hreg hord hlim hσ (fun i η => ((hA i) η).val) ξ₀ hU hbase
  let s : Set α := A (pick x) ∩ {z : α | Ordinal.typein (· < ·) z < base}
  have hbase_lt := base_lt_pickParamAboveOrdinalRec hreg hord hlim hσ
    (fun i η => ((hA i) η).val) ξ₀ hU hbase x
  let e : s ↪ {η : σ // η < ξ₀} :=
    { toFun := fun z =>
        let η : σ := (hA (pick x)).symm ⟨z.1, z.2.1⟩
        ⟨η, by
          have hzt : Ordinal.typein (· < ·) z.1 <
              Ordinal.typein (· < ·) (((hA (pick x)) ξ₀).val) :=
            lt_trans z.2.2 hbase_lt
          have hzlt : z.1 < ((hA (pick x)) ξ₀).val :=
            (Ordinal.typein_lt_typein (· < ·)).1 hzt
          exact param_lt_of_mem_and_pick_bound hA z.2.1 hzlt⟩
      inj' := by
        intro z w hzw
        apply Subtype.ext
        have hη : (hA (pick x)).symm ⟨z.1, z.2.1⟩ = (hA (pick x)).symm ⟨w.1, w.2.1⟩ :=
          Subtype.ext_iff.mp hzw
        have happ := congrArg (fun η => ((hA (pick x)) η).val) hη
        simpa [pick] using happ }
  calc
    Cardinal.mk ((A (pickParamAboveOrdinalRec hreg hord hlim hσ
        (fun i η => ((hA i) η).val) ξ₀ hU hbase x) ∩
          {z : α | Ordinal.typein (· < ·) z < base}) : Set α) = Cardinal.mk s := by rfl
    _ ≤ Cardinal.mk {η : σ // η < ξ₀} := ⟨e⟩
    _ ≤ Cardinal.mk σ := Cardinal.mk_subtype_le _

/-- Infinite pigeonhole applied to the colors `x ↦ A (pick x) ∩ sub_α₀`. This produces a
full-cardinality set of stages on which the intersection with the small initial segment is constant. -/
theorem exists_large_constant_picked_alpha0_inter
    {α σ ι : Type u} [LinearOrder α] [WellFoundedLT α] [IsWellOrder α (· < ·)]
    [LinearOrder σ]
    (hreg : Cardinal.IsRegular (Cardinal.mk α))
    (hord : Cardinal.ord (Cardinal.mk α) = orderType α)
    (hlim : Order.IsSuccLimit (orderType α)) (hσ : Cardinal.mk σ < Cardinal.mk α)
    {A : ι → Set α}
    (hA : ∀ i, RelIso (· < · : σ → σ → Prop) (Subrel (· < · : α → α → Prop) (A i)))
    (ξ₀ : σ)
    (hU : Set.Unbounded (· < ·) (Set.range fun i : ι => ((hA i) ξ₀).val))
    {base : Ordinal} (hbase : base < orderType α)
    (hcod : Cardinal.mk {s : Set α //
        s ⊆ {z : α | Ordinal.typein (· < ·) z < base} ∧ Cardinal.mk s ≤ Cardinal.mk σ} <
      (Cardinal.mk α).ord.cof) :
    ∃ r : Set α, ∃ t : Set α,
      r ⊆ {z : α | Ordinal.typein (· < ·) z < base} ∧
      Cardinal.mk t = Cardinal.mk α ∧
      ∀ ⦃x⦄, x ∈ t →
        A (pickParamAboveOrdinalRec hreg hord hlim hσ (fun i η => ((hA i) η).val) ξ₀ hU hbase x) ∩
            {z : α | Ordinal.typein (· < ·) z < base} = r := by
  let subα : Set α := {z : α | Ordinal.typein (· < ·) z < base}
  let pick := pickParamAboveOrdinalRec hreg hord hlim hσ (fun i η => ((hA i) η).val) ξ₀ hU hbase
  let codomain := {s : Set α // s ⊆ subα ∧ Cardinal.mk s ≤ Cardinal.mk σ}
  let color : α → codomain := fun x =>
    ⟨A (pick x) ∩ subα, inter_subset_right, by
      dsimp [subα, pick]
      exact picked_alpha0_inter_mk_le hreg hord hlim hσ hA ξ₀ hU hbase x⟩
  have hfiber := Cardinal.infinite_pigeonhole_card color (Cardinal.mk α) le_rfl hreg.aleph0_le (by
    simpa [codomain, subα] using hcod)
  rcases hfiber with ⟨r', hr'⟩
  refine ⟨r'.1, color ⁻¹' {r'}, r'.2.1, ?_, ?_⟩
  · apply le_antisymm
    · exact Cardinal.mk_set_le _
    · exact hr'
  · intro x hx
    have hx' : color x = r' := by simpa using hx
    exact congrArg Subtype.val hx'

/-- Assemble a delta-system on stages from the constant-color pigeonhole output. -/
theorem is_delta_system_of_constant_picked_alpha0_inter
    {α σ ι : Type u} [LinearOrder α] [WellFoundedLT α] [IsWellOrder α (· < ·)]
    [LinearOrder σ]
    (hreg : Cardinal.IsRegular (Cardinal.mk α))
    (hord : Cardinal.ord (Cardinal.mk α) = orderType α)
    (hlim : Order.IsSuccLimit (orderType α)) (hσ : Cardinal.mk σ < Cardinal.mk α)
    {A : ι → Set α}
    (hA : ∀ i, RelIso (· < · : σ → σ → Prop) (Subrel (· < · : α → α → Prop) (A i)))
    (ξ₀ : σ)
    (hU : Set.Unbounded (· < ·) (Set.range fun i : ι => ((hA i) ξ₀).val))
    {base : Ordinal}
    (hbase_eq : base =
      iSup (fun η : {x : σ // x < ξ₀} =>
        iSup fun i : ι => Order.succ (Ordinal.typein (· < ·) ((hA i) η.1).val)))
    (hbase : base < orderType α)
    {r t : Set α}
    (hconst : ∀ ⦃x⦄, x ∈ t →
      A (pickParamAboveOrdinalRec hreg hord hlim hσ (fun i η => ((hA i) η).val) ξ₀ hU hbase x) ∩
          {z : α | Ordinal.typein (· < ·) z < base} = r) :
    is_delta_system
      (fun x : t =>
        A (pickParamAboveOrdinalRec hreg hord hlim hσ (fun i η => ((hA i) η).val) ξ₀ hU hbase x.1)) := by
  refine ⟨r, ?_⟩
  intro x y hxy
  apply Set.Subset.antisymm
  · intro z hz
    rcases lt_trichotomy x.1 y.1 with hlt | heq | hgt
    · have hsub := picked_inter_subset_alpha0 hreg hord hlim hσ hA ξ₀ hU hbase_eq hbase hlt
      have hzsub : z ∈ {z : α | Ordinal.typein (· < ·) z < base} := hsub hz
      have hzroot : z ∈
          A (pickParamAboveOrdinalRec hreg hord hlim hσ (fun i η => ((hA i) η).val) ξ₀ hU hbase x.1) ∩
            {z : α | Ordinal.typein (· < ·) z < base} := ⟨hz.1, hzsub⟩
      simpa [hconst x.2] using hzroot
    · exact False.elim (hxy (Subtype.ext heq))
    · have hsub := picked_inter_subset_alpha0 hreg hord hlim hσ hA ξ₀ hU hbase_eq hbase hgt
      have hzswap : z ∈
          A (pickParamAboveOrdinalRec hreg hord hlim hσ (fun i η => ((hA i) η).val) ξ₀ hU hbase y.1) ∩
            A (pickParamAboveOrdinalRec hreg hord hlim hσ (fun i η => ((hA i) η).val) ξ₀ hU hbase x.1) :=
        ⟨hz.2, hz.1⟩
      have hzsub : z ∈ {z : α | Ordinal.typein (· < ·) z < base} := hsub hzswap
      have hzroot : z ∈
          A (pickParamAboveOrdinalRec hreg hord hlim hσ (fun i η => ((hA i) η).val) ξ₀ hU hbase x.1) ∩
            {z : α | Ordinal.typein (· < ·) z < base} := ⟨hz.1, hzsub⟩
      simpa [hconst x.2] using hzroot
  · intro z hz
    have hxz : z ∈
        A (pickParamAboveOrdinalRec hreg hord hlim hσ (fun i η => ((hA i) η).val) ξ₀ hU hbase x.1) ∩
          {z : α | Ordinal.typein (· < ·) z < base} := by
      simpa [hconst x.2] using hz
    have hyz : z ∈
        A (pickParamAboveOrdinalRec hreg hord hlim hσ (fun i η => ((hA i) η).val) ξ₀ hU hbase y.1) ∩
          {z : α | Ordinal.typein (· < ·) z < base} := by
      simpa [hconst y.2] using hz
    exact ⟨hxz.1, hyz.1⟩

/-- Assembled unbounded-case Δ-system theorem, with the final bounded-codomain estimate supplied as
an explicit hypothesis. This is the fully wired version of the helper stack for
`delta_system_lemma_2`; the remaining wrapper only has to prove `hcod` from the original cardinal
arithmetic hypothesis. -/
theorem delta_system_lemma_2_of_bounded_codomain {κ : Cardinal}
    {θ : Type u} [LinearOrder θ] [WellFoundedLT θ] [IsWellOrder θ (· < ·)]
    (hκθ : κ < Cardinal.mk θ)
    (hθ : Cardinal.IsRegular (Cardinal.mk θ))
    (hθtype : Cardinal.ord (Cardinal.mk θ) = orderType θ)
    {ρ : Type u} [LinearOrder ρ] [WellFoundedLT ρ]
    (hρ : Cardinal.mk ρ < κ)
    {ι : Type u} {A : ι → Set θ}
    (h2A : ∀ i, RelIso (· < · : ρ → ρ → Prop) (Subrel (· < · : θ → θ → Prop) (A i)))
    (hU : Set.Unbounded (· < ·) (⋃ i, A i))
    (hcod : ∀ {base : Ordinal}, base < orderType θ →
      Cardinal.mk {s : Set θ //
          s ⊆ {z : θ | Ordinal.typein (· < ·) z < base} ∧ Cardinal.mk s ≤ Cardinal.mk ρ} <
        (Cardinal.mk θ).ord.cof) :
    ∃ t : Set θ, Cardinal.mk t = Cardinal.mk θ ∧
      ∃ pick : θ → ι, is_delta_system (fun x : t => A (pick x.1)) := by
  classical
  let hlim := isSuccLimit_orderType_of_isRegular hθ hθtype
  rcases exists_minimal_parameter_with_alpha0_bound hκθ hθ hθtype (lt_trans hρ hκθ) hρ h2A hU with
    ⟨ξ₀, hξU, _hξmin, hbase_lt⟩
  let base : Ordinal :=
    iSup (fun η : {x : ρ // x < ξ₀} =>
      iSup fun i : ι => Order.succ (Ordinal.typein (· < ·) ((h2A i) η.1).val))
  have hbase_eq : base =
      iSup (fun η : {x : ρ // x < ξ₀} =>
        iSup fun i : ι => Order.succ (Ordinal.typein (· < ·) ((h2A i) η.1).val)) := rfl
  have hbase : base < orderType θ := by simpa [base] using hbase_lt
  let pick := pickParamAboveOrdinalRec hθ hθtype hlim (lt_trans hρ hκθ)
    (fun i η => ((h2A i) η).val) ξ₀ hξU hbase
  rcases exists_large_constant_picked_alpha0_inter hθ hθtype hlim (lt_trans hρ hκθ)
      h2A ξ₀ hξU hbase (hcod hbase) with
    ⟨r, stages, _hrsub, hstages, hconst⟩
  refine ⟨stages, hstages, pick, ?_⟩
  exact is_delta_system_of_constant_picked_alpha0_inter hθ hθtype hlim
    (lt_trans hρ hκθ) h2A ξ₀ hξU hbase_eq hbase hconst


/-- Bounded codomain estimate derived from the cardinal arithmetic hypothesis. -/
theorem mk_bounded_subsets_lt_cof {κ : Cardinal} (hκ : ℵ₀ ≤ κ)
    {θ : Type u} [LinearOrder θ] [WellFoundedLT θ] [IsWellOrder θ (· < ·)]
    (hκθ : κ < Cardinal.mk θ) (hθ : Cardinal.IsRegular (Cardinal.mk θ))
    (hθtype : Cardinal.ord (Cardinal.mk θ) = orderType θ)
    (hθ_le : ∀ β < Cardinal.mk θ, β ^< κ < Cardinal.mk θ)
    {ρ : Type u}
    (hρ : Cardinal.mk ρ < κ)
    {base : Ordinal} (hbase : base < orderType θ) :
    Cardinal.mk {s : Set θ //
      s ⊆ {z : θ | Ordinal.typein (· < ·) z < base} ∧ Cardinal.mk s ≤ Cardinal.mk ρ} <
    (Cardinal.mk θ).ord.cof := by
  let T : Set θ := {z : θ | Ordinal.typein (· < ·) z < base}
  have hT_lt : Cardinal.mk T < Cardinal.mk θ := mk_typein_initial_segment_lt hθtype hbase
  have h_aleph0_lt : ℵ₀ < Cardinal.mk θ := lt_of_le_of_lt hκ hκθ
  have hmax_lt : max (Cardinal.mk T) ℵ₀ < Cardinal.mk θ :=
    max_lt hT_lt h_aleph0_lt
  have hpow_lt : max (Cardinal.mk T) ℵ₀ ^ (Cardinal.mk ρ) < Cardinal.mk θ :=
    calc
      max (Cardinal.mk T) ℵ₀ ^ (Cardinal.mk ρ) ≤
        max (Cardinal.mk T) ℵ₀ ^< κ := Cardinal.le_powerlt (max (Cardinal.mk T) ℵ₀) hρ
      _ < Cardinal.mk θ := hθ_le _ hmax_lt
  calc
    Cardinal.mk {s : Set θ // s ⊆ T ∧ Cardinal.mk s ≤ Cardinal.mk ρ} ≤
      max (Cardinal.mk T) ℵ₀ ^ (Cardinal.mk ρ) :=
      Cardinal.mk_bounded_subset_le T (Cardinal.mk ρ)
    _ < Cardinal.mk θ := hpow_lt
    _ = (Cardinal.mk θ).ord.cof := hθ.cof_ord.symm

/-- Full Δ-system lemma for the unbounded-index case, without the `hcod` hypothesis. -/
theorem delta_system_lemma_2 {κ : Cardinal} (hκ : ℵ₀ ≤ κ)
    {θ : Type u} [LinearOrder θ] [WellFoundedLT θ] [IsWellOrder θ (· < ·)]
    (hκθ : κ < Cardinal.mk θ) (hθ : Cardinal.IsRegular (Cardinal.mk θ))
    (hθtype : Cardinal.ord (Cardinal.mk θ) = orderType θ)
    (hθ_le : ∀ β < Cardinal.mk θ, β ^< κ < Cardinal.mk θ)
    {ρ : Type u} [LinearOrder ρ] [WellFoundedLT ρ]
    (hρθ : Cardinal.mk ρ < Cardinal.mk θ) (hρ : Cardinal.mk ρ < κ)
    {ι : Type u} {A : ι → Set θ}
    (h2A : ∀ i, RelIso (· < · : ρ → ρ → Prop) (Subrel (· < · : θ → θ → Prop) (A i)))
    (hU : Set.Unbounded (· < ·) (⋃ i, A i)) :
    ∃ t : Set θ, Cardinal.mk t = Cardinal.mk θ ∧ ∃ pick : θ → ι,
      is_delta_system (fun x : t => A (pick x.1)) := by
  classical
  let hlim := isSuccLimit_orderType_of_isRegular hθ hθtype
  rcases exists_minimal_parameter_with_alpha0_bound hκθ hθ hθtype hρθ hρ h2A hU with
    ⟨ξ₀, hξU, _hξmin, hbase_lt⟩
  let base : Ordinal :=
    iSup (fun η : {x : ρ // x < ξ₀} =>
      iSup fun i : ι => Order.succ (Ordinal.typein (· < ·) ((h2A i) η.1).val))
  have hbase_eq : base =
      iSup (fun η : {x : ρ // x < ξ₀} =>
        iSup fun i : ι => Order.succ (Ordinal.typein (· < ·) ((h2A i) η.1).val)) := rfl
  have hbase : base < orderType θ := by simpa [base] using hbase_lt
  let pick := pickParamAboveOrdinalRec hθ hθtype hlim hρθ
    (fun i η => ((h2A i) η).val) ξ₀ hξU hbase
  rcases exists_large_constant_picked_alpha0_inter hθ hθtype hlim hρθ
      h2A ξ₀ hξU hbase (mk_bounded_subsets_lt_cof hκ hκθ hθ hθtype hθ_le hρ hbase) with
    ⟨r, stages, _hrsub, hstages, hconst⟩
  refine ⟨stages, hstages, pick, ?_⟩
  exact is_delta_system_of_constant_picked_alpha0_inter hθ hθtype hlim
    hρθ h2A ξ₀ hξU hbase_eq hbase hconst

/-- Δ-system lemma, step 1: transfer from θ to ι, handling both unbounded and bounded cases. -/
theorem delta_system_lemma_1 {κ : Cardinal} (hκ : ℵ₀ ≤ κ)
    {θ : Type u} [LinearOrder θ] [WellFoundedLT θ] [IsWellOrder θ (· < ·)]
    (hκθ : κ < Cardinal.mk θ) (hθ : Cardinal.IsRegular (Cardinal.mk θ))
    (hθtype : Cardinal.ord (Cardinal.mk θ) = orderType θ)
    (hθ_le : ∀ β < Cardinal.mk θ, β ^< κ < Cardinal.mk θ)
    {ρ : Type u} [LinearOrder ρ] [WellFoundedLT ρ]
    (hρθ : Cardinal.mk ρ < Cardinal.mk θ) (hρ : Cardinal.mk ρ < κ)
    {ι : Type u} (hι : Cardinal.mk θ = Cardinal.mk ι) {A : ι → Set θ}
    (h2A : ∀ i, RelIso (· < · : ρ → ρ → Prop) (Subrel (· < · : θ → θ → Prop) (A i))) :
    ∃ t : Set ι, Cardinal.mk t = Cardinal.mk θ ∧
      is_delta_system (fun i : t => A i.1) := by
  by_cases hU : Set.Unbounded (· < ·) (⋃ i, A i)
  · -- Unbounded case
    classical
    let hlim := isSuccLimit_orderType_of_isRegular hθ hθtype
    rcases exists_minimal_parameter_with_alpha0_bound hκθ hθ hθtype hρθ hρ h2A hU with
      ⟨ξ₀, hξU, _hξmin, hbase_lt⟩
    let base : Ordinal :=
      iSup (fun η : {x : ρ // x < ξ₀} =>
        iSup fun i : ι => Order.succ (Ordinal.typein (· < ·) ((h2A i) η.1).val))
    have hbase_eq : base =
        iSup (fun η : {x : ρ // x < ξ₀} =>
          iSup fun i : ι => Order.succ (Ordinal.typein (· < ·) ((h2A i) η.1).val)) := rfl
    have hbase : base < orderType θ := by simpa [base] using hbase_lt
    let pick := pickParamAboveOrdinalRec hθ hθtype hlim hρθ
      (fun i η => ((h2A i) η).val) ξ₀ hξU hbase
    have hinj : Function.Injective pick :=
      pickParamAboveOrdinalRec_injective hθ hθtype hlim hρθ
        (fun i η => ((h2A i) η).val) ξ₀ hξU hbase
    rcases exists_large_constant_picked_alpha0_inter hθ hθtype hlim hρθ
        h2A ξ₀ hξU hbase (mk_bounded_subsets_lt_cof hκ hκθ hθ hθtype hθ_le hρ hbase) with
      ⟨r, stages, _hrsub, hstages, hconst⟩
    let pickOnStages : stages → ι := fun x => pick x.1
    have hinjOnSet : Function.Injective pickOnStages := by
      intro x y h
      apply Subtype.ext
      exact hinj (by simpa [pickOnStages] using h)
    have hds : is_delta_system (fun (x : stages) => A (pickOnStages x)) := by
      simpa [pickOnStages] using
        is_delta_system_of_constant_picked_alpha0_inter hθ hθtype hlim
          hρθ h2A ξ₀ hξU hbase_eq hbase hconst
    let t_img : Set ι := Set.range pickOnStages
    have h_mk_img : Cardinal.mk t_img = Cardinal.mk θ := by
      rw [Cardinal.mk_range_eq pickOnStages hinjOnSet, hstages]
    have hds_img : is_delta_system (fun (x : t_img) => A x.1) := by
      let e : stages ≃ t_img := Equiv.ofInjective pickOnStages hinjOnSet
      have h_eq : (fun (x : stages) => A (pickOnStages x)) ∘ e.symm =
          fun (x : t_img) => A x.1 := by
        ext x
        dsimp
        have hval : pickOnStages (e.symm x) = x.1 :=
          calc
            pickOnStages (e.symm x) = (e (e.symm x)).1 := rfl
            _ = x.1 := by rw [Equiv.apply_symm_apply e x]
        rw [hval]
      have hds_trans := (is_delta_system_precompose_iff
        (A := fun (x : stages) => A (pickOnStages x)) e.symm).mp hds
      simpa [h_eq] using hds_trans
    exact ⟨t_img, h_mk_img, hds_img⟩
  · -- Bounded case
    rcases ((Set.not_unbounded_iff (s := ⋃ i, A i)).mp hU) with ⟨a, ha⟩
    let U : Set θ := Set.Iio a
    have hU_sub : (Set.iUnion A) ⊆ U := fun x hx => ha x hx
    have hU_lt : Cardinal.mk U < Cardinal.mk θ := mk_Iio_lt_of_ord_eq a hθtype
    have hAi_sub (i : ι) : A i ⊆ U := fun x hx =>
      hU_sub (Set.mem_iUnion.mpr ⟨i, hx⟩)
    have hAi_card (i : ι) : Cardinal.mk (A i) = Cardinal.mk ρ := by
      have eqv : ρ ≃ A i := (h2A i).toEquiv
      exact (Cardinal.mk_congr eqv).symm
    let codomain := {s : Set θ // s ⊆ U ∧ Cardinal.mk s ≤ Cardinal.mk ρ}
    let color : ι → codomain := fun i =>
      ⟨A i, hAi_sub i, le_of_eq (hAi_card i)⟩
    have h_aleph0_lt : ℵ₀ < Cardinal.mk θ := lt_of_le_of_lt hκ hκθ
    have hmax_lt : max (Cardinal.mk U) ℵ₀ < Cardinal.mk θ :=
      max_lt hU_lt h_aleph0_lt
    have hcod_lt : Cardinal.mk codomain < (Cardinal.mk θ).ord.cof := by
      calc
        Cardinal.mk codomain ≤ max (Cardinal.mk U) ℵ₀ ^ (Cardinal.mk ρ) :=
          Cardinal.mk_bounded_subset_le U (Cardinal.mk ρ)
        _ ≤ max (Cardinal.mk U) ℵ₀ ^< κ := Cardinal.le_powerlt (max (Cardinal.mk U) ℵ₀) hρ
        _ < Cardinal.mk θ := hθ_le _ hmax_lt
        _ = (Cardinal.mk θ).ord.cof := hθ.cof_ord.symm
    have hθ_inf : ℵ₀ ≤ Cardinal.mk θ := hκ.trans (le_of_lt hκθ)
    have hdomain_le : Cardinal.mk θ ≤ Cardinal.mk ι := by
      rw [hι]
    rcases Cardinal.infinite_pigeonhole_card color (Cardinal.mk θ) hdomain_le hθ_inf hcod_lt with
      ⟨root, hroot⟩
    let t : Set ι := color ⁻¹' {root}
    have ht_mk : Cardinal.mk t = Cardinal.mk θ := by
      apply le_antisymm
      · calc
          Cardinal.mk t ≤ Cardinal.mk ι := Cardinal.mk_set_le t
          _ = Cardinal.mk θ := hι.symm
      · exact hroot
    refine ⟨t, ht_mk, ?_⟩
    refine ⟨root.1, ?_⟩
    intro x y hxy
    have hx : color x.1 = root := by
      have hx' := x.2
      rw [Set.mem_preimage] at hx'
      simpa using hx'
    have hy : color y.1 = root := by
      have hy' := y.2
      rw [Set.mem_preimage] at hy'
      simpa using hy'
    have hAx : A x.1 = root.1 := by
      dsimp [color] at hx
      simpa using congrArg Subtype.val hx
    have hAy : A y.1 = root.1 := by
      dsimp [color] at hy
      simpa using congrArg Subtype.val hy
    simp [hAx, hAy]

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

theorem countable_chain_condition_of_topological_basis
    [TopologicalSpace α] (B : Set (Set α)) (hB : IsTopologicalBasis B)
    (h : ∀ s : Set (Set α), s ⊆ B → s.PairwiseDisjoint id → s.Countable) :
    countable_chain_condition α := by
  apply countable_chain_condition_of_nonempty
  intro s hsnonempty hsopen hsdisj
  let f : ∀ x : s, { y : Set α // y ∈ B ∧ y.Nonempty ∧ y ⊆ x.1 } := by
    intro x
    let hx : x.1.Nonempty := by
      rw [Set.nonempty_iff_ne_empty]
      exact hsnonempty x.2
    let y : α := Classical.choose hx
    have hy : y ∈ x.1 := Classical.choose_spec hx
    let u : Set α := Classical.choose (hB.exists_subset_of_mem_open hy (hsopen x.2))
    have huB : u ∈ B := (Classical.choose_spec (hB.exists_subset_of_mem_open hy (hsopen x.2))).1
    have hyu : y ∈ u := (Classical.choose_spec (hB.exists_subset_of_mem_open hy (hsopen x.2))).2.1
    have huSub : u ⊆ x.1 :=
      (Classical.choose_spec (hB.exists_subset_of_mem_open hy (hsopen x.2))).2.2
    exact ⟨u, huB, ⟨y, hyu⟩, huSub⟩
  let s' : Set (Set α) := Set.range fun x : s => (f x).1
  have hs' : s' ⊆ B := by
    intro o ho
    rcases ho with ⟨x, rfl⟩
    exact (f x).2.1
  have hdisj' : s'.PairwiseDisjoint id := by
    intro a ha b hb hab
    rcases ha with ⟨x, rfl⟩
    rcases hb with ⟨x', rfl⟩
    have hxx' : (x : Set α) ≠ (x' : Set α) := by
      intro h
      have hSub : x = x' := Subtype.ext h
      subst hSub
      exact hab rfl
    exact (hsdisj x.2 x'.2 hxx').mono (f x).2.2.2 (f x').2.2.2
  have hs'Count : s'.Countable := h s' hs' hdisj'
  let emb : s ↪ s' :=
    ⟨fun x => ⟨(f x).1, ⟨x, rfl⟩⟩, fun x x' hxx' => by
      apply Subtype.ext
      have hEq : (f x).1 = (f x').1 := Subtype.ext_iff.mp hxx'
      rcases (f x).2.2.1 with ⟨y, hy⟩
      have hy' : y ∈ (f x').1 := by simpa [hEq] using hy
      exact hsdisj.elim_set x.2 x'.2 y ((f x).2.2.2 hy) ((f x').2.2.2 hy')⟩
  simpa [Set.countable_coe_iff] using Set.countable_of_embedding emb hs'Count

theorem countable_chain_condition_of_separable_space
    [TopologicalSpace α] [SeparableSpace α] : countable_chain_condition α := by
  apply countable_chain_condition_of_nonempty
  intro s hsnonempty hsopen hsdisj
  exact hsdisj.countable_of_isOpen hsopen fun o ho => by
    rw [Set.nonempty_iff_ne_empty]
    exact hsnonempty ho

end CCC

section Pi

variable {α : Type u} {β : α → Type v} [∀ x, TopologicalSpace (β x)]

/-- A subbasic open in the product topology, constraining a single coordinate. -/
def standard_open {i : α} (o : Opens (β i)) : Set (∀ x, β x) :=
  {f | f i ∈ o}

variable (β)

/-- The standard subbasis for the product topology. -/
def pi_subbasis : Set (Set (∀ x, β x)) :=
  Set.range fun x : Σ i : α, Opens (β i) => standard_open x.2

theorem mem_pi_subbasis_iff {s : Set (∀ x, β x)} :
    s ∈ pi_subbasis β ↔ ∃ i : α, ∃ o : Opens (β i), s = standard_open o := by
  constructor
  · rintro ⟨⟨i, o⟩, rfl⟩
    exact ⟨i, o, rfl⟩
  · rintro ⟨i, o, rfl⟩
    exact ⟨⟨i, o⟩, rfl⟩

theorem isOpen_standard_open {i : α} (o : Opens (β i)) :
    IsOpen (standard_open o : Set (∀ x, β x)) := by
  simpa [standard_open] using o.isOpen.preimage (continuous_apply i)

theorem isOpen_of_mem_pi_subbasis {s : Set (∀ x, β x)} (hs : s ∈ pi_subbasis β) : IsOpen s := by
  rcases (mem_pi_subbasis_iff (β := β)).1 hs with ⟨_, o, rfl⟩
  exact isOpen_standard_open (β := β) o

/-- A basis candidate for the product topology given by nonempty finite intersections of subbasic
opens. -/
def pi_basis : Set (Set (∀ x, β x)) :=
  (fun f : Set (Set (∀ x, β x)) => ⋂₀ f) ''
    {f | f.Finite ∧ f ⊆ pi_subbasis β ∧ (⋂₀ f) ≠ ∅}

theorem nonempty_of_mem_pi_basis {o : Set (∀ x, β x)} (h : o ∈ pi_basis β) : o.Nonempty := by
  rcases h with ⟨s, hs, rfl⟩
  exact Set.nonempty_iff_ne_empty.mpr hs.2.2

theorem mem_pi_basis_of_pi {s : ∀ x, Set (β x)} {i : Finset α}
    (hs : ∀ x ∈ i, IsOpen (s x)) (hne : Set.pi (i : Set α) s ≠ ∅) :
    Set.pi (i : Set α) s ∈ pi_basis β := by
  let O : ↥(i : Set α) → Set (∀ x, β x) := fun x =>
    standard_open ⟨s x.1, hs x.1 x.2⟩
  have hInter : ⋂₀ Set.range O = Set.pi (i : Set α) s := by
    ext f
    constructor
    · intro hf
      rw [Set.mem_sInter] at hf
      rw [Set.mem_pi]
      intro x hx
      exact hf (O ⟨x, hx⟩) ⟨⟨x, hx⟩, rfl⟩
    · intro hf
      rw [Set.mem_sInter]
      intro t ht
      rcases ht with ⟨x, rfl⟩
      exact hf x.1 x.2
  refine ⟨Set.range O, ?_, hInter⟩
  refine ⟨Set.finite_range O, ?_, ?_⟩
  · intro t ht
    rcases ht with ⟨x, rfl⟩
    exact (mem_pi_subbasis_iff (β := β)).2 ⟨x.1, ⟨s x.1, hs x.1 x.2⟩, rfl⟩
  · simpa [hInter] using hne

theorem sInter_eq_pi_of_finite_subbasis {f : Set (Set (∀ x, β x))} (hfin : f.Finite)
    (hsub : f ⊆ pi_subbasis β) :
    ∃ i : Finset α, ∃ s : ∀ x, Set (β x),
      (∀ x ∈ i, IsOpen (s x)) ∧ (∀ x ∉ i, s x = Set.univ) ∧ ⋂₀ f = Set.pi (i : Set α) s := by
  classical
  induction f, hfin using Set.Finite.induction_on with
  | empty =>
      refine ⟨∅, fun _ => Set.univ, ?_, ?_, ?_⟩
      · intro x hx
        exact False.elim (Finset.notMem_empty x hx)
      · intro x hx
        rfl
      · simp
  | @insert t f htNotMem hfin ih =>
      have htSub : t ∈ pi_subbasis β := hsub (by simp)
      rcases (mem_pi_subbasis_iff (β := β)).1 htSub with ⟨coord, U, hU⟩
      rcases ih (fun u hu => hsub (by simp [hu])) with ⟨i, s, hsOpen, hsUniv, hsInter⟩
      let s' : ∀ a, Set (β a) := fun a =>
        if h : a = coord then h ▸ (s coord ∩ ((U : Opens (β coord)) : Set (β coord))) else s a
      refine ⟨insert coord i, s', ?_, ?_, ?_⟩
      · intro a ha
        by_cases hEq : a = coord
        · subst hEq
          have hscoord : IsOpen (s a) := by
            by_cases hcoord : a ∈ i
            · exact hsOpen a hcoord
            · simpa [hsUniv a hcoord] using isOpen_univ
          simpa [s'] using hscoord.inter U.isOpen
        · simpa [s', hEq] using hsOpen a ((Finset.mem_insert.mp ha).resolve_left hEq)
      · intro a ha
        have hEq : a ≠ coord := fun h => ha (by simpa [h] using Finset.mem_insert_self coord i)
        have hai : a ∉ i := fun hai => ha (by simp [hai])
        simpa [s', hEq, hsUniv a hai]
      · calc
          ⋂₀ insert t f = t ∩ ⋂₀ f := by simp
          _ = standard_open U ∩ ⋂₀ f := by rw [hU]
          _ = standard_open U ∩ Set.pi (i : Set α) s := by rw [hsInter]
          _ = Set.pi ((insert coord i : Finset α) : Set α) s' := by
            ext g
            rw [Set.mem_inter_iff, Set.mem_pi, Set.mem_pi]
            constructor
            · rintro ⟨hgU, hgpi⟩ a ha
              rcases Finset.mem_insert.mp ha with rfl | haI
              · have hgs : g a ∈ s a := by
                  by_cases hcoord : a ∈ i
                  · exact hgpi a hcoord
                  · simpa [hsUniv a hcoord]
                simpa [s'] using And.intro hgs hgU
              · have hgs : g a ∈ s a := hgpi a haI
                by_cases hEq : a = coord
                · subst hEq
                  simpa [s'] using And.intro (hgpi a haI) hgU
                · simpa [s', hEq] using hgs
            · intro hgpi
              refine ⟨?_, ?_⟩
              · have hgcoord : g coord ∈ s' coord := hgpi coord (by simp)
                have hgpair : g coord ∈ s coord ∩ ((U : Opens (β coord)) : Set (β coord)) := by
                  simpa [s'] using hgcoord
                exact hgpair.2
              · intro a haI
                have hga : g a ∈ s' a := hgpi a (by simp [haI])
                by_cases hEq : a = coord
                · subst hEq
                  have hgpair : g a ∈ s a ∩ ((U : Opens (β a)) : Set (β a)) := by
                    simpa [s'] using hga
                  exact hgpair.1
                · simpa [s', hEq] using hga

theorem mem_pi_basis_iff {o : Set (∀ x, β x)} :
    o ∈ pi_basis β ↔ ∃ i : Finset α, ∃ s : ∀ x, Set (β x),
      (∀ x ∈ i, IsOpen (s x)) ∧ Set.pi (i : Set α) s ≠ ∅ ∧ o = Set.pi (i : Set α) s := by
  constructor
  · intro ho
    rcases ho with ⟨f, hf, rfl⟩
    rcases sInter_eq_pi_of_finite_subbasis (β := β) hf.1 hf.2.1 with ⟨i, s, hsOpen, _, hsEq⟩
    refine ⟨i, s, hsOpen, ?_, hsEq⟩
    simpa [hsEq] using hf.2.2
  · rintro ⟨i, s, hsOpen, hsNe, rfl⟩
    exact mem_pi_basis_of_pi (β := β) hsOpen hsNe

theorem pi_basis_eq :
    pi_basis β =
      ({g | ∃ s : ∀ x, Set (β x), ∃ i : Finset α, (∀ x ∈ i, IsOpen (s x)) ∧
        g = Set.pi (i : Set α) s} \ {∅}) := by
  ext g
  constructor
  · intro hg
    rcases (mem_pi_basis_iff (β := β)).1 hg with ⟨i, s, hsOpen, hsNe, rfl⟩
    refine ⟨⟨s, i, hsOpen, rfl⟩, ?_⟩
    exact hsNe
  · rintro ⟨⟨s, i, hsOpen, rfl⟩, hsNe⟩
    exact mem_pi_basis_of_pi (β := β) hsOpen hsNe

/-- The coordinates that matter for deciding membership in a set of dependent functions. -/
def support (o : Set (∀ x, β x)) : Set α :=
  ⋂₀ {s : Set α | ∀ ⦃f g : ∀ x, β x⦄, Set.eqOn' f g s → f ∈ o → g ∈ o}

omit [∀ x, TopologicalSpace (β x)] in
theorem support_pi {i : Set α} {s : ∀ x, Set (β x)}
    (h : (Set.pi i s).Nonempty) :
    support (β := β) (Set.pi i s) = {x | x ∈ i ∧ s x ≠ Set.univ} := by
  classical
  apply Set.Subset.antisymm
  · apply Set.sInter_subset_of_mem
    intro f g hfg hf x hxi
    by_cases hsx : s x = Set.univ
    · simpa [hsx]
    · have hx' : x ∈ {x | x ∈ i ∧ s x ≠ Set.univ} := ⟨hxi, hsx⟩
      simpa [hfg hx'] using hf x hxi
  · intro x hx
    apply Set.mem_sInter.2
    intro t ht
    by_contra hxt
    rcases h with ⟨f, hf⟩
    have hNotUniv : s x ≠ Set.univ := hx.2
    have hExists : ∃ z₂, z₂ ∉ s x := by
      by_contra hNo
      apply hNotUniv
      ext z
      constructor
      · intro hz
        trivial
      · intro _
        by_contra hzNot
        exact hNo ⟨z, hzNot⟩
    rcases hExists with ⟨z₂, hz₂⟩
    let g : ∀ x, β x := Function.update f x z₂
    have hEqOn : Set.eqOn' f g t := by
      intro y hy
      by_cases hyx : y = x
      · exact False.elim (hxt (hyx ▸ hy))
      · simp [g, Function.update_of_ne hyx]
    have hg : g ∈ Set.pi i s := ht hEqOn hf
    have : z₂ ∈ s x := by
      simpa [g, Function.update_self] using hg x hx.1
    exact hz₂ this

theorem support_elim {o : Set (∀ x, β x)} {f g : ∀ x, β x} (ho : o ∈ pi_basis β)
    (hEq : Set.eqOn' f g (support (β := β) o)) (hf : f ∈ o) : g ∈ o := by
  rcases (mem_pi_basis_iff (β := β)).1 ho with ⟨i, s, _, hsNe, rfl⟩
  have hsupp : support (β := β) (Set.pi (i : Set α) s) = {x | x ∈ (i : Set α) ∧ s x ≠ Set.univ} :=
    support_pi (β := β) (i := (i : Set α)) (s := s) (Set.nonempty_iff_ne_empty.mpr hsNe)
  rw [hsupp] at hEq
  intro x hx
  by_cases hsx : s x = Set.univ
  · simpa [hsx]
  · have hxSupp : x ∈ {x | x ∈ (i : Set α) ∧ s x ≠ Set.univ} := ⟨hx, hsx⟩
    simpa [hEq hxSupp] using hf x hx

theorem finite_support_of_pi_subbasis {o : Set (∀ x, β x)} (h : o ∈ pi_subbasis β) :
    (support (β := β) o).Finite := by
  rcases (mem_pi_subbasis_iff (β := β)).1 h with ⟨i, o, rfl⟩
  apply Set.Finite.subset (Set.finite_singleton i)
  apply Set.sInter_subset_of_mem
  intro f g hfg hf
  have hgi : f i = g i := by simpa [Set.eqOn'] using hfg (by simp : i ∈ ({i} : Set α))
  simpa [standard_open, hgi] using hf

theorem finite_support_of_pi_basis {o : Set (∀ x, β x)} (h : o ∈ pi_basis β) :
    (support (β := β) o).Finite := by
  rcases (mem_pi_basis_iff (β := β)).1 h with ⟨i, s, _, hsNe, rfl⟩
  rw [support_pi (β := β) (i := (i : Set α)) (s := s) (Set.nonempty_iff_ne_empty.mpr hsNe)]
  exact Set.Finite.subset i.finite_toSet (by intro x hx; exact hx.1)

/-- Splice two dependent functions, using the first on `s` and the second off `s`. -/
noncomputable def extend (g₁ g₂ : ∀ x, β x) (s : Set α) (x : α) : β x := by
  classical
  exact if h : x ∈ s then g₁ x else g₂ x

theorem isOpenMap_apply (i : α) : IsOpenMap (fun f : ∀ x, β x => f i) := by
  simpa using isOpenMap_eval (i := i)

theorem is_open_map_apply (i : α) : IsOpenMap (fun f : ∀ x, β x => f i) :=
  isOpenMap_apply (β := β) i

omit [∀ x, TopologicalSpace (β x)] in
theorem restrict_image_pi (t s : Set α) (s' : ∀ i, Set (β i))
    (h : (Set.pi t s').Nonempty) :
    (Set.restrict s) '' Set.pi t s' = Set.pi (Subtype.val ⁻¹' t) (fun i => s' i.1) := by
  classical
  apply Set.Subset.antisymm
  · rintro _ ⟨f, hf, rfl⟩ i hi
    exact hf _ hi
  · rcases h with ⟨f', hf'⟩
    intro f hf
    refine ⟨fun i => if hmem : i ∈ s then f ⟨i, hmem⟩ else f' i, ?_, ?_⟩
    · intro i hi
      by_cases his : i ∈ s
      · simpa [Set.restrict, his] using hf ⟨i, his⟩ hi
      · simpa [extend, his] using hf' i hi
    · funext i
      simp [Set.restrict, i.2]

/-- The coordinate support of a cylinder family: the coordinates where the fiber is not `univ`. -/
def pi_set_support (s : ∀ x, Set (β x)) : Set α :=
  {x | s x ≠ Set.univ}

omit [∀ x, TopologicalSpace (β x)] in
theorem pi_set_support_subset_of_eq_univ_outside
    {s : ∀ x, Set (β x)} {i : Finset α}
    (hsUniv : ∀ x ∉ i, s x = Set.univ) : pi_set_support (β := β) s ⊆ (i : Set α) := by
  intro x hx
  by_contra hxNotMem
  exact hx (hsUniv x hxNotMem)

omit [∀ x, TopologicalSpace (β x)] in
theorem finite_pi_set_support_of_eq_univ_outside {s : ∀ x, Set (β x)} {i : Finset α}
    (hsUniv : ∀ x ∉ i, s x = Set.univ) : (pi_set_support (β := β) s).Finite := by
  exact Set.Finite.subset i.finite_toSet
    (pi_set_support_subset_of_eq_univ_outside (β := β) hsUniv)

theorem exists_eq_pi_with_finite_support_of_mem_pi_basis {o : Set (∀ x, β x)} (ho : o ∈ pi_basis β) :
    ∃ i : Finset α, ∃ s : ∀ x, Set (β x),
      (∀ x ∈ i, IsOpen (s x)) ∧ (∀ x ∉ i, s x = Set.univ) ∧ o = Set.pi (i : Set α) s := by
  rcases ho with ⟨f, hf, rfl⟩
  exact sInter_eq_pi_of_finite_subbasis (β := β) hf.1 hf.2.1

theorem exists_finite_pi_set_support_of_mem_pi_basis {o : Set (∀ x, β x)} (ho : o ∈ pi_basis β) :
    ∃ s : ∀ x, Set (β x),
      (pi_set_support (β := β) s).Finite ∧ o = Set.pi (pi_set_support (β := β) s) s := by
  classical
  rcases exists_eq_pi_with_finite_support_of_mem_pi_basis (β := β) ho with
    ⟨i, s, _, hsUniv, rfl⟩
  refine ⟨s, finite_pi_set_support_of_eq_univ_outside (β := β) hsUniv, ?_⟩
  ext g
  rw [Set.mem_pi, Set.mem_pi]
  constructor
  · intro hg x hx
    exact hg x (pi_set_support_subset_of_eq_univ_outside (β := β) hsUniv hx)
  · intro hg x hx
    by_cases hxs : x ∈ pi_set_support (β := β) s
    · exact hg x hxs
    · have hsx : s x = Set.univ := by
        simpa [pi_set_support] using hxs
      simpa [hsx]

omit [∀ x, TopologicalSpace (β x)] in
theorem mem_pi_pi_set_support_iff {s : ∀ x, Set (β x)} {f : ∀ x, β x} :
    f ∈ Set.pi (pi_set_support (β := β) s) s ↔
      ∀ x ∈ pi_set_support (β := β) s, f x ∈ s x := by
  rw [Set.mem_pi]

omit [∀ x, TopologicalSpace (β x)] in
theorem mem_pi_pi_set_support_congr {s : ∀ x, Set (β x)} {f g : ∀ x, β x}
    (hEq : Set.eqOn' f g (pi_set_support (β := β) s)) :
    f ∈ Set.pi (pi_set_support (β := β) s) s ↔ g ∈ Set.pi (pi_set_support (β := β) s) s := by
  rw [mem_pi_pi_set_support_iff (β := β), mem_pi_pi_set_support_iff (β := β)]
  constructor
  · intro hf x hx
    simpa [hEq hx] using hf x hx
  · intro hg x hx
    simpa [hEq hx] using hg x hx

theorem mem_pi_basis_congr {o : Set (∀ x, β x)} (ho : o ∈ pi_basis β) {f g : ∀ x, β x}
    (hEq : ∃ s : ∀ x, Set (β x),
      o = Set.pi (pi_set_support (β := β) s) s ∧ Set.eqOn' f g (pi_set_support (β := β) s)) :
    f ∈ o ↔ g ∈ o := by
  rcases hEq with ⟨s, rfl, hEq⟩
  exact mem_pi_pi_set_support_congr (β := β) hEq

/-- Cylinders over a fixed finite coordinate set, with fibers drawn from prescribed families. -/
def pi_basis_from_finset (T : ∀ x, Set (Set (β x))) (i : Finset α) : Set (Set (∀ x, β x)) :=
  {o | ∃ s : ∀ x, Set (β x),
    (∀ x ∈ i, s x ∈ T x) ∧ (∀ x ∉ i, s x = Set.univ) ∧ o = Set.pi (i : Set α) s}

/-- Cylinders with finite support, with supported fibers drawn from prescribed families. -/
def pi_basis_from (T : ∀ x, Set (Set (β x))) : Set (Set (∀ x, β x)) :=
  {o | ∃ i : Finset α, o ∈ pi_basis_from_finset (β := β) T i}

omit [∀ x, TopologicalSpace (β x)] in
theorem mem_pi_basis_from_iff
    {T : ∀ x, Set (Set (β x))} {o : Set (∀ x, β x)} :
    o ∈ pi_basis_from (β := β) T ↔
      ∃ i : Finset α, ∃ s : ∀ x, Set (β x),
        (∀ x ∈ i, s x ∈ T x) ∧ (∀ x ∉ i, s x = Set.univ) ∧ o = Set.pi (i : Set α) s := by
  constructor
  · rintro ⟨i, s, hsT, hsUniv, rfl⟩
    exact ⟨i, s, hsT, hsUniv, rfl⟩
  · rintro ⟨i, s, hsT, hsUniv, rfl⟩
    exact ⟨i, s, hsT, hsUniv, rfl⟩

omit [∀ x, TopologicalSpace (β x)] in
theorem countable_pi_basis_from_finset
    (T : ∀ x, Set (Set (β x))) (i : Finset α)
    (hT : ∀ x, (T x).Countable) : (pi_basis_from_finset (β := β) T i).Countable := by
  classical
  let F : ((x : (i : Set α)) → Set (β x.1)) → Set (∀ x, β x) := fun u =>
    {f | ∀ x : (i : Set α), f x.1 ∈ u x}
  have hCountFuncs : (Set.pi Set.univ (fun x : (i : Set α) => T x.1)).Countable := by
    exact Set.countable_univ_pi fun x => hT x.1
  letI : Countable ↥(Set.pi Set.univ (fun x : (i : Set α) => T x.1)) := hCountFuncs.to_subtype
  let G : ↥(Set.pi Set.univ (fun x : (i : Set α) => T x.1)) → Set (∀ x, β x) := fun u => F u
  have hRange : (Set.range G).Countable := Set.countable_range G
  refine hRange.mono ?_
  intro o ho
  rcases ho with ⟨u, hu, hsUniv, rfl⟩
  refine ⟨⟨fun x : (i : Set α) => u x.1, ?_⟩, ?_⟩
  · rw [Set.mem_pi]
    intro x hx
    exact hu x.1 x.2
  · ext f
    change (∀ x : (i : Set α), f x.1 ∈ u x.1) ↔ ∀ x ∈ i, f x ∈ u x
    constructor
    · intro hf x hx
      exact hf ⟨x, hx⟩
    · intro hf x
      exact hf x.1 x.2

omit [∀ x, TopologicalSpace (β x)] in
theorem countable_pi_basis_from [Countable α] (T : ∀ x, Set (Set (β x)))
    (hT : ∀ x, (T x).Countable) : (pi_basis_from (β := β) T).Countable := by
  rw [show pi_basis_from (β := β) T = ⋃ i : Finset α, pi_basis_from_finset (β := β) T i by
    ext o
    constructor
    · rintro ⟨i, ho⟩
      exact Set.mem_iUnion.2 ⟨i, ho⟩
    · intro ho
      rcases Set.mem_iUnion.1 ho with ⟨i, hi⟩
      exact ⟨i, hi⟩]
  exact Set.countable_iUnion fun i => countable_pi_basis_from_finset (β := β) T i hT

theorem mem_pi_basis_of_mem_pi_basis_from_finset {T : ∀ x, Set (Set (β x))} {i : Finset α}
    (hOpen : ∀ x, T x ⊆ {s : Set (β x) | IsOpen s})
    {o : Set (∀ x, β x)} (ho : o ∈ pi_basis_from_finset (β := β) T i) (hne : o ≠ ∅) :
    o ∈ pi_basis β := by
  rcases ho with ⟨s, hsT, hsUniv, rfl⟩
  apply mem_pi_basis_of_pi (β := β)
  · intro x hx
    exact hOpen x (hsT x hx)
  · exact hne

theorem mem_pi_basis_of_mem_pi_basis_from {T : ∀ x, Set (Set (β x))}
    (hOpen : ∀ x, T x ⊆ {s : Set (β x) | IsOpen s})
    {o : Set (∀ x, β x)} (ho : o ∈ pi_basis_from (β := β) T) (hne : o ≠ ∅) :
    o ∈ pi_basis β := by
  rcases ho with ⟨i, hi⟩
  exact mem_pi_basis_of_mem_pi_basis_from_finset (β := β) hOpen hi hne

theorem isOpen_of_mem_pi_basis_from {T : ∀ x, Set (Set (β x))}
    (hOpen : ∀ x, T x ⊆ {s : Set (β x) | IsOpen s})
    {o : Set (∀ x, β x)} (ho : o ∈ pi_basis_from (β := β) T) : IsOpen o := by
  rcases (mem_pi_basis_from_iff (β := β)).1 ho with ⟨i, s, hsT, _, rfl⟩
  exact isOpen_set_pi i.finite_toSet fun x hx => hOpen x (hsT x hx)

theorem isTopologicalBasis_pi_basis_from {T : ∀ x, Set (Set (β x))}
    (hBasis : ∀ x, IsTopologicalBasis (T x)) : IsTopologicalBasis (pi_basis_from (β := β) T) := by
  classical
  apply isTopologicalBasis_of_isOpen_of_nhds
  · intro o ho
    exact isOpen_of_mem_pi_basis_from (β := β) (fun x s hs => (hBasis x).isOpen hs) ho
  · intro f o hfo ho
    rcases isOpen_pi_iff.1 ho f hfo with ⟨i, s, hs, hsub⟩
    choose t htT hft htsub using
      fun x hx => (hBasis x).isOpen_iff.1 ((hs x hx).1) (f x) ((hs x hx).2)
    let u : ∀ x, Set (β x) := fun x =>
      if hx : x ∈ i then t x hx else Set.univ
    have huT : ∀ x ∈ i, u x ∈ T x := by
      intro x hx
      simpa [u, hx] using htT x hx
    have huUniv : ∀ x ∉ i, u x = Set.univ := by
      intro x hx
      simp [u, hx]
    have hfU : f ∈ Set.pi (i : Set α) u := by
      intro x hx
      dsimp [u]
      split_ifs with h
      · simpa using hft x hx
      · contradiction
    have huSub : Set.pi (i : Set α) u ⊆ o := by
      intro g hg
      exact hsub fun x hx => (htsub x hx) (by
        have hgx := hg x hx
        dsimp [u] at hgx
        split_ifs at hgx with h
        · simpa using hgx
        · contradiction)
    refine ⟨Set.pi (i : Set α) u, ?_, hfU, huSub⟩
    exact (mem_pi_basis_from_iff (β := β)).2 ⟨i, u, huT, huUniv, rfl⟩

theorem countable_pi_basis_from_countableBasis [Countable α]
    [∀ x, SecondCountableTopology (β x)] :
    (pi_basis_from (β := β) fun x => countableBasis (β x)).Countable := by
  exact countable_pi_basis_from (β := β) (fun x => countableBasis (β x))
    (fun x => countable_countableBasis (β x))

theorem isTopologicalBasis_pi_basis_from_countableBasis
    [∀ x, SecondCountableTopology (β x)] :
    IsTopologicalBasis (pi_basis_from (β := β) fun x => countableBasis (β x)) := by
  exact isTopologicalBasis_pi_basis_from (β := β)
    (fun x => isBasis_countableBasis (β x))

theorem secondCountableTopology_pi_of_countable [Countable α]
    [∀ x, SecondCountableTopology (β x)] :
    SecondCountableTopology (∀ x, β x) :=
  (isTopologicalBasis_pi_basis_from_countableBasis (β := β)).secondCountableTopology
    (countable_pi_basis_from_countableBasis (β := β))

theorem countable_chain_condition_pi_of_countable [Countable α]
    [∀ x, SecondCountableTopology (β x)] :
    countable_chain_condition (∀ x, β x) := by
  letI : SecondCountableTopology (∀ x, β x) := secondCountableTopology_pi_of_countable (β := β)
  exact countable_chain_condition_of_separable_space

theorem isOpen_of_mem_pi_basis {o : Set (∀ x, β x)} (ho : o ∈ pi_basis β) : IsOpen o := by
  rcases ho with ⟨s, hs, rfl⟩
  refine hs.1.isOpen_sInter ?_
  intro t ht
  exact isOpen_of_mem_pi_subbasis (β := β) (hs.2.1 ht)

theorem isTopologicalBasis_pi_basis : IsTopologicalBasis (pi_basis β) := by
  apply isTopologicalBasis_of_isOpen_of_nhds
  · intro o ho
    exact isOpen_of_mem_pi_basis (β := β) ho
  · intro f o hfo ho
    rcases isOpen_pi_iff.1 ho f hfo with ⟨i, s, hs, hsub⟩
    refine ⟨Set.pi (i : Set α) s, mem_pi_basis_of_pi (β := β) (fun x hx => (hs x hx).1) ?_, ?_,
      hsub⟩
    · exact Set.nonempty_iff_ne_empty.mp ⟨f, fun x hx => (hs x hx).2⟩
    · exact fun x hx => (hs x hx).2

theorem is_topological_basis_pi : IsTopologicalBasis (pi_basis β) :=
  isTopologicalBasis_pi_basis (β := β)

theorem isOpenMap_restrict (s : Set α) : IsOpenMap (fun f : ∀ x, β x => Set.restrict s f) := by
  refine (isTopologicalBasis_pi_basis (β := β)).isOpenMap_iff.2 ?_
  intro o ho
  rcases (mem_pi_basis_iff (β := β)).1 ho with ⟨i, s', hsOpen, hsNe, rfl⟩
  have hne : (Set.pi (i : Set α) s').Nonempty := Set.nonempty_iff_ne_empty.mpr hsNe
  rw [restrict_image_pi (β := β) (t := (i : Set α)) (s := s) (s' := s') hne]
  have hpre : ((Subtype.val : s → α) ⁻¹' (i : Set α)).Finite := by
    exact i.finite_toSet.preimage Subtype.val_injective.injOn
  exact isOpen_set_pi hpre (fun x hx => hsOpen x.1 hx)

theorem is_open_map_restrict (s : Set α) : IsOpenMap (fun f : ∀ x, β x => Set.restrict s f) :=
  isOpenMap_restrict (β := β) s

/-- If two product-basis opens have support intersection contained in `R`, then their images under
restriction to `R` remain disjoint. This isolates the splicing argument used in the uncountable
product CCC proof. -/
theorem disjoint_restrict_image_of_support_inter_subset
    {C : Set (Set (∀ x, β x))} {s t : Set (∀ x, β x)} {R : Set α}
    (hC : ∀ ⦃o⦄, o ∈ C → o ∈ pi_basis β)
    (hdisj : C.PairwiseDisjoint id) (hsC : s ∈ C) (htC : t ∈ C) (hst : s ≠ t)
    (hroot : support (β := β) s ∩ support (β := β) t ⊆ R) :
    Disjoint ((fun f : ∀ x, β x => Set.restrict R f) '' s)
      ((fun f : ∀ x, β x => Set.restrict R f) '' t) := by
  rw [Set.disjoint_iff_inter_eq_empty]
  ext f
  constructor
  · intro hf
    rcases hf with ⟨⟨g₁, hg₁s, hg₁⟩, ⟨g₂, hg₂t, hg₂⟩⟩
    have hEqR : Set.eqOn' g₁ g₂ R := by
      rw [Set.eqOn'_iff]
      exact hg₁.trans hg₂.symm
    have hstDisj := hdisj hsC htC hst
    have hg₁in : extend (β := β) g₁ g₂ (support (β := β) s) ∈ s := by
      apply support_elim (β := β) (hC hsC) (f := g₁)
      · intro x hx
        simp [extend, hx]
      · exact hg₁s
    have hg₂in : extend (β := β) g₁ g₂ (support (β := β) s) ∈ t := by
      apply support_elim (β := β) (hC htC) (f := g₂)
      · intro x hx
        by_cases hxs : x ∈ support (β := β) s
        · have hxR : x ∈ R := hroot ⟨hxs, hx⟩
          simpa [extend, hxs] using (hEqR hxR).symm
        · simp [extend, hxs]
      · exact hg₂t
    exact hstDisj.le_bot ⟨hg₁in, hg₂in⟩
  · intro hf
    exact False.elim hf

/-- A Δ-system root for supports gives pairwise disjoint restricted images. This is the indexed
form of `disjoint_restrict_image_of_support_inter_subset` used in the product CCC proof. -/
theorem pairwise_disjoint_restrict_image_of_delta_supports
    {ι : Type u} {C : Set (Set (∀ x, β x))} {A : ι → Set (∀ x, β x)} {R : Set α}
    (hC : ∀ ⦃o⦄, o ∈ C → o ∈ pi_basis β)
    (hdisj : C.PairwiseDisjoint id) (hA : ∀ i, A i ∈ C)
    (hAne : Pairwise fun i j => A i ≠ A j)
    (hroot : ∀ ⦃i j : ι⦄, i ≠ j → support (β := β) (A i) ∩ support (β := β) (A j) = R) :
    Pairwise fun i j =>
      Disjoint ((fun f : ∀ x, β x => Set.restrict R f) '' A i)
        ((fun f : ∀ x, β x => Set.restrict R f) '' A j) := by
  intro i j hij
  apply disjoint_restrict_image_of_support_inter_subset (β := β) hC hdisj (hA i) (hA j)
    (hAne hij)
  intro x hx
  rw [hroot hij] at hx
  exact hx

/-- The restricted-image family coming from a Δ-system of supports is pairwise disjoint as a set of
opens. -/
theorem pairwiseDisjoint_restrict_image_range_of_delta_supports
    {ι : Type u} {C : Set (Set (∀ x, β x))} {A : ι → Set (∀ x, β x)} {R : Set α}
    (hC : ∀ ⦃o⦄, o ∈ C → o ∈ pi_basis β)
    (hdisj : C.PairwiseDisjoint id) (hA : ∀ i, A i ∈ C)
    (hAne : Pairwise fun i j => A i ≠ A j)
    (hroot : ∀ ⦃i j : ι⦄, i ≠ j → support (β := β) (A i) ∩ support (β := β) (A j) = R) :
    (Set.range fun i => (fun f : ∀ x, β x => Set.restrict R f) '' A i).PairwiseDisjoint id := by
  intro s hs t ht hst
  rcases hs with ⟨i, rfl⟩
  rcases ht with ⟨j, rfl⟩
  by_cases hij : i = j
  · subst hij
    exact (hst rfl).elim
  · exact pairwise_disjoint_restrict_image_of_delta_supports (β := β) hC hdisj hA hAne hroot hij

/-- The restricted-image family used in the product CCC proof consists of open sets in the finite
root subproduct. -/
theorem isOpen_of_mem_restrict_image_range
    {ι : Type u} {C : Set (Set (∀ x, β x))} {A : ι → Set (∀ x, β x)} {R : Set α}
    (hC : ∀ ⦃o⦄, o ∈ C → o ∈ pi_basis β) (hA : ∀ i, A i ∈ C)
    {o : Set (∀ x : R, β x)}
    (ho : o ∈ Set.range fun i => (fun f : ∀ x, β x => Set.restrict R f) '' A i) :
    IsOpen o := by
  rcases ho with ⟨i, rfl⟩
  exact (isOpenMap_restrict (β := β) R) (A i) (isOpen_of_mem_pi_basis (β := β) (hC (hA i)))

/-- The restricted image of every selected product-basis open is nonempty. -/
theorem nonempty_restrict_image_of_delta_member
    {ι : Type u} {C : Set (Set (∀ x, β x))} {A : ι → Set (∀ x, β x)} {R : Set α}
    (hC : ∀ ⦃o⦄, o ∈ C → o ∈ pi_basis β) (hA : ∀ i, A i ∈ C) (i : ι) :
    ((fun f : ∀ x, β x => Set.restrict R f) '' A i).Nonempty := by
  rcases nonempty_of_mem_pi_basis (β := β) (hC (hA i)) with ⟨f, hf⟩
  exact ⟨Set.restrict R f, f, hf, rfl⟩

/-- Every member of the restricted-image range is nonempty. -/
theorem nonempty_of_mem_restrict_image_range
    {ι : Type u} {C : Set (Set (∀ x, β x))} {A : ι → Set (∀ x, β x)} {R : Set α}
    (hC : ∀ ⦃o⦄, o ∈ C → o ∈ pi_basis β) (hA : ∀ i, A i ∈ C)
    {o : Set (∀ x : R, β x)}
    (ho : o ∈ Set.range fun i => (fun f : ∀ x, β x => Set.restrict R f) '' A i) :
    o.Nonempty := by
  rcases ho with ⟨i, rfl⟩
  exact nonempty_restrict_image_of_delta_member (β := β) hC hA i

/-- The restricted-image range is a family of open sets. -/
theorem restrict_image_range_subset_open
    {ι : Type u} {C : Set (Set (∀ x, β x))} {A : ι → Set (∀ x, β x)} {R : Set α}
    (hC : ∀ ⦃o⦄, o ∈ C → o ∈ pi_basis β) (hA : ∀ i, A i ∈ C) :
    Set.range (fun i => (fun f : ∀ x, β x => Set.restrict R f) '' A i) ⊆
      {o : Set (∀ x : R, β x) | IsOpen o} := by
  intro o ho
  exact isOpen_of_mem_restrict_image_range (β := β) hC hA ho

/-- The restricted-image range is a family of nonempty sets. -/
theorem restrict_image_range_subset_nonempty
    {ι : Type u} {C : Set (Set (∀ x, β x))} {A : ι → Set (∀ x, β x)} {R : Set α}
    (hC : ∀ ⦃o⦄, o ∈ C → o ∈ pi_basis β) (hA : ∀ i, A i ∈ C) :
    Set.range (fun i => (fun f : ∀ x, β x => Set.restrict R f) '' A i) ⊆
      {o : Set (∀ x : R, β x) | o.Nonempty} := by
  intro o ho
  exact nonempty_of_mem_restrict_image_range (β := β) hC hA ho

/-- The support of every selected product-basis open is finite. -/
theorem finite_support_of_delta_member
    {ι : Type u} {C : Set (Set (∀ x, β x))} {A : ι → Set (∀ x, β x)}
    (hC : ∀ ⦃o⦄, o ∈ C → o ∈ pi_basis β) (hA : ∀ i, A i ∈ C) (i : ι) :
    (support (β := β) (A i)).Finite :=
  finite_support_of_pi_basis (β := β) (hC (hA i))

/-- The supports of a selected product-basis family are pointwise finite. -/
theorem finite_supports_of_delta_family
    {ι : Type u} {C : Set (Set (∀ x, β x))} {A : ι → Set (∀ x, β x)}
    (hC : ∀ ⦃o⦄, o ∈ C → o ∈ pi_basis β) (hA : ∀ i, A i ∈ C) :
    ∀ i, (support (β := β) (A i)).Finite :=
  finite_support_of_delta_member (β := β) hC hA

/-- A Δ-system root of product-basis supports is finite once the index has at least two points. -/
theorem finite_root_of_delta_supports
    {ι : Type u} {C : Set (Set (∀ x, β x))} {A : ι → Set (∀ x, β x)} {R : Set α}
    (hC : ∀ ⦃o⦄, o ∈ C → o ∈ pi_basis β) (hA : ∀ i, A i ∈ C)
    (hι : (2 : Cardinal) ≤ Cardinal.mk ι)
    (hroot : ∀ ⦃i j : ι⦄, i ≠ j → support (β := β) (A i) ∩ support (β := β) (A j) = R) :
    R.Finite := by
  exact delta_system.finite_root hι (finite_supports_of_delta_family (β := β) hC hA) hroot

/-- A finite root subproduct is CCC when every coordinate is second-countable. -/
theorem countable_chain_condition_root_subproduct_of_finite
    [∀ x, SecondCountableTopology (β x)] {R : Set α} (hR : R.Finite) :
    countable_chain_condition (∀ x : R, β x) := by
  letI : Finite R := hR.to_subtype
  letI : Countable R := Finite.to_countable
  exact countable_chain_condition_pi_of_countable (β := fun x : R => β x)

/-- A Δ-system root subproduct is CCC under second-countability. -/
theorem countable_chain_condition_root_subproduct_of_delta_supports
    [∀ x, SecondCountableTopology (β x)]
    {ι : Type u} {C : Set (Set (∀ x, β x))} {A : ι → Set (∀ x, β x)} {R : Set α}
    (hC : ∀ ⦃o⦄, o ∈ C → o ∈ pi_basis β) (hA : ∀ i, A i ∈ C)
    (hι : (2 : Cardinal) ≤ Cardinal.mk ι)
    (hroot : ∀ ⦃i j : ι⦄, i ≠ j → support (β := β) (A i) ∩ support (β := β) (A j) = R) :
    countable_chain_condition (∀ x : R, β x) := by
  exact countable_chain_condition_root_subproduct_of_finite (β := β)
    (finite_root_of_delta_supports (β := β) hC hA hι hroot)

/-- Under the same Δ-system support hypotheses, restriction to the root is injective on the indexed
family of opens. This supplies the cardinal lower bound used in the final product CCC argument. -/
theorem mk_restrict_image_range_eq_of_delta_supports
    {ι : Type u} {C : Set (Set (∀ x, β x))} {A : ι → Set (∀ x, β x)} {R : Set α}
    (hC : ∀ ⦃o⦄, o ∈ C → o ∈ pi_basis β)
    (hdisj : C.PairwiseDisjoint id) (hA : ∀ i, A i ∈ C)
    (hAne : Pairwise fun i j => A i ≠ A j)
    (hroot : ∀ ⦃i j : ι⦄, i ≠ j → support (β := β) (A i) ∩ support (β := β) (A j) = R) :
    Cardinal.lift.{u} (Cardinal.mk (Set.range fun i =>
      (fun f : ∀ x, β x => Set.restrict R f) '' A i)) =
      Cardinal.lift.{max u v} (Cardinal.mk ι) := by
  apply Cardinal.mk_range_eq_of_injective
  intro i j hij
  by_contra hne
  have hDisj := pairwise_disjoint_restrict_image_of_delta_supports (β := β) hC hdisj hA hAne hroot hne
  rcases nonempty_of_mem_pi_basis (β := β) (hC (hA i)) with ⟨f, hf⟩
  have hfLeft : Set.restrict R f ∈ (fun f : ∀ x, β x => Set.restrict R f) '' A i :=
    ⟨f, hf, rfl⟩
  have hfRight : Set.restrict R f ∈ (fun f : ∀ x, β x => Set.restrict R f) '' A j := by
    simpa [hij] using hfLeft
  exact hDisj.le_bot ⟨hfLeft, hfRight⟩

theorem aleph0_lt_mk_restrict_image_range_of_delta_supports
    {ι : Type u} {C : Set (Set (∀ x, β x))} {A : ι → Set (∀ x, β x)} {R : Set α}
    (hC : ∀ ⦃o⦄, o ∈ C → o ∈ pi_basis β)
    (hdisj : C.PairwiseDisjoint id) (hA : ∀ i, A i ∈ C)
    (hAne : Pairwise fun i j => A i ≠ A j)
    (hroot : ∀ ⦃i j : ι⦄, i ≠ j → support (β := β) (A i) ∩ support (β := β) (A j) = R)
    (hι : ℵ₀ < Cardinal.mk ι) :
    Cardinal.lift.{u} ℵ₀ < Cardinal.lift.{u} (Cardinal.mk (Set.range fun i =>
      (fun f : ∀ x, β x => Set.restrict R f) '' A i)) := by
  rw [mk_restrict_image_range_eq_of_delta_supports (β := β) hC hdisj hA hAne hroot]
  simpa [Cardinal.lift_aleph0] using (Cardinal.lift_strictMono.{u, v} hι)

/-- A set with lifted cardinality strictly above `ℵ₀` is not countable. -/
theorem not_countable_of_lift_aleph0_lt_mk {γ : Type w} {s : Set γ}
    (h : Cardinal.lift.{u} ℵ₀ < Cardinal.lift.{u} (Cardinal.mk s)) : ¬ s.Countable := by
  intro hs
  have hle : Cardinal.lift.{u} (Cardinal.mk s) ≤ Cardinal.lift.{u} ℵ₀ := by
    rw [Cardinal.lift_le]
    letI : Countable s := hs.to_subtype
    exact Cardinal.mk_le_aleph0
  exact not_lt_of_ge hle h

/-- The restricted-image family produced from an uncountable Δ-system is not countable. -/
theorem not_countable_restrict_image_range_of_delta_supports
    {ι : Type u} {C : Set (Set (∀ x, β x))} {A : ι → Set (∀ x, β x)} {R : Set α}
    (hC : ∀ ⦃o⦄, o ∈ C → o ∈ pi_basis β)
    (hdisj : C.PairwiseDisjoint id) (hA : ∀ i, A i ∈ C)
    (hAne : Pairwise fun i j => A i ≠ A j)
    (hroot : ∀ ⦃i j : ι⦄, i ≠ j → support (β := β) (A i) ∩ support (β := β) (A j) = R)
    (hι : ℵ₀ < Cardinal.mk ι) :
    ¬ (Set.range fun i => (fun f : ∀ x, β x => Set.restrict R f) '' A i).Countable := by
  intro hcount
  have hlt := aleph0_lt_mk_restrict_image_range_of_delta_supports (β := β) hC hdisj hA
    hAne hroot hι
  have hle : Cardinal.lift.{u} (Cardinal.mk (Set.range fun i =>
      (fun f : ∀ x, β x => Set.restrict R f) '' A i)) ≤ Cardinal.lift.{u} ℵ₀ := by
    letI : Countable ↥(Set.range fun i => (fun f : ∀ x, β x => Set.restrict R f) '' A i) :=
      hcount.to_subtype
    simpa [Cardinal.lift_id] using
      (Cardinal.lift_le.{u, max u v}.2 (Cardinal.mk_le_aleph0 (α :=
        ↥(Set.range fun i => (fun f : ∀ x, β x => Set.restrict R f) '' A i))))
  exact not_lt_of_ge hle hlt

/-- CCC on the root subproduct makes the restricted-image family countable. -/
theorem countable_restrict_image_range_of_root_ccc
    {ι : Type u} {C : Set (Set (∀ x, β x))} {A : ι → Set (∀ x, β x)} {R : Set α}
    (hC : ∀ ⦃o⦄, o ∈ C → o ∈ pi_basis β)
    (hdisj : C.PairwiseDisjoint id) (hA : ∀ i, A i ∈ C)
    (hAne : Pairwise fun i j => A i ≠ A j)
    (hroot : ∀ ⦃i j : ι⦄, i ≠ j → support (β := β) (A i) ∩ support (β := β) (A j) = R)
    (hccc : countable_chain_condition (∀ x : R, β x)) :
    (Set.range fun i => (fun f : ∀ x, β x => Set.restrict R f) '' A i).Countable := by
  exact hccc _ (fun ho hmem => isOpen_of_mem_restrict_image_range (β := β) hC hA hmem)
    (pairwiseDisjoint_restrict_image_range_of_delta_supports (β := β) hC hdisj hA hAne hroot)

/-- Under second-countability and a finite support root, the restricted-image family is countable. -/
theorem countable_restrict_image_range_of_delta_supports
    [∀ x, SecondCountableTopology (β x)]
    {ι : Type u} {C : Set (Set (∀ x, β x))} {A : ι → Set (∀ x, β x)} {R : Set α}
    (hC : ∀ ⦃o⦄, o ∈ C → o ∈ pi_basis β)
    (hdisj : C.PairwiseDisjoint id) (hA : ∀ i, A i ∈ C)
    (hAne : Pairwise fun i j => A i ≠ A j)
    (hι : (2 : Cardinal) ≤ Cardinal.mk ι)
    (hroot : ∀ ⦃i j : ι⦄, i ≠ j → support (β := β) (A i) ∩ support (β := β) (A j) = R) :
    (Set.range fun i => (fun f : ∀ x, β x => Set.restrict R f) '' A i).Countable := by
  exact countable_restrict_image_range_of_root_ccc (β := β) hC hdisj hA hAne hroot
    (countable_chain_condition_root_subproduct_of_delta_supports (β := β) hC hA hι hroot)

/-- The restricted-image range contradicts any CCC proof on the root subproduct. -/
theorem not_countable_of_restrict_image_range_ccc_contradiction
    {ι : Type u} {C : Set (Set (∀ x, β x))} {A : ι → Set (∀ x, β x)} {R : Set α}
    (hC : ∀ ⦃o⦄, o ∈ C → o ∈ pi_basis β)
    (hdisj : C.PairwiseDisjoint id) (hA : ∀ i, A i ∈ C)
    (hAne : Pairwise fun i j => A i ≠ A j)
    (hroot : ∀ ⦃i j : ι⦄, i ≠ j → support (β := β) (A i) ∩ support (β := β) (A j) = R)
    (hι : ℵ₀ < Cardinal.mk ι)
    (hccc : countable_chain_condition (∀ x : R, β x)) : False := by
  exact not_countable_restrict_image_range_of_delta_supports (β := β) hC hdisj hA hAne hroot hι
    (countable_restrict_image_range_of_root_ccc (β := β) hC hdisj hA hAne hroot hccc)

/-- The finite-root CCC countability conclusion contradicts an uncountable Δ-system. -/
theorem false_of_uncountable_delta_supports_and_finite_root_ccc
    [∀ x, SecondCountableTopology (β x)]
    {ι : Type u} {C : Set (Set (∀ x, β x))} {A : ι → Set (∀ x, β x)} {R : Set α}
    (hC : ∀ ⦃o⦄, o ∈ C → o ∈ pi_basis β)
    (hdisj : C.PairwiseDisjoint id) (hA : ∀ i, A i ∈ C)
    (hAne : Pairwise fun i j => A i ≠ A j)
    (hTwo : (2 : Cardinal) ≤ Cardinal.mk ι) (hUncountable : ℵ₀ < Cardinal.mk ι)
    (hroot : ∀ ⦃i j : ι⦄, i ≠ j → support (β := β) (A i) ∩ support (β := β) (A j) = R) :
    False := by
  exact not_countable_restrict_image_range_of_delta_supports (β := β) hC hdisj hA hAne hroot
    hUncountable
    (countable_restrict_image_range_of_delta_supports (β := β) hC hdisj hA hAne hTwo hroot)

end Pi

end Flypitch

attribute [nolint unusedArguments]
  Flypitch.countable_chain_condition_of_nonempty Flypitch.countable_chain_condition_of_countable
  Flypitch.countable_chain_condition_of_topological_basis
  Flypitch.countable_chain_condition_of_separable_space
