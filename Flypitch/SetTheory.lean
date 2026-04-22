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

end Pi

end Flypitch

attribute [nolint unusedArguments]
  Flypitch.countable_chain_condition_of_nonempty Flypitch.countable_chain_condition_of_countable
  Flypitch.countable_chain_condition_of_topological_basis
  Flypitch.countable_chain_condition_of_separable_space
