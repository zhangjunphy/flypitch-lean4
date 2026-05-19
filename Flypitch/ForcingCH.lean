import Flypitch.Collapse
import Flypitch.AlephOne

universe u v

namespace Flypitch

open Cardinal PFun

set_option linter.missingDocs false
set_option linter.style.longLine false

private theorem regularOpen_iSup_eq_top_of_iUnion_eq_univ {α : Type u} [TopologicalSpace α]
    {ι : Sort u} (F : ι → regular_opens α)
    (hUnion : (⋃ i : ι, (F i : Set α)) = Set.univ) :
    (⨆ i : ι, F i) = ⊤ := by
  apply le_antisymm le_top
  change (Set.univ : Set α) ⊆
    (⋃₀ ((fun T : regular_opens α => (T : Set α)) '' Set.range F))ᵖᵖ
  have hSUnion :
      (⋃₀ ((fun T : regular_opens α => (T : Set α)) '' Set.range F)) = Set.univ := by
    ext x
    constructor
    · intro _; trivial
    · intro _
      have hx : x ∈ ⋃ i : ι, (F i : Set α) := by
        simpa [hUnion]
      rcases Set.mem_iUnion.mp hx with ⟨i, hi⟩
      exact Set.mem_sUnion.mpr ⟨(F i : Set α), ⟨F i, ⟨i, rfl⟩, rfl⟩, hi⟩
  rw [hSUnion]
  simp

private theorem iSup_eq_top_of_dense_below {α : Type u} [CompleteBooleanAlgebra α]
    {ι : Sort v} {D : Set α} (hD : dense_subset D) (F : ι → α)
    (hBelow : ∀ d ∈ D, ∃ e ∈ D, e ≤ d ∧ ∃ i, e ≤ F i) :
    (⨆ i : ι, F i) = ⊤ := by
  apply le_antisymm le_top
  by_contra hNot
  have hComplNonzero : ⊥ < (⨆ i : ι, F i)ᶜ := by
    rw [bot_lt_iff_ne_bot]
    intro hComplBot
    apply hNot
    rw [compl_eq_bot.mp hComplBot]
  rcases hD.2 ((⨆ i : ι, F i)ᶜ) hComplNonzero with ⟨d, hdD, hdCompl⟩
  rcases hBelow d hdD with ⟨e, heD, hed, i, heF⟩
  have heNonzero : ⊥ < e := by
    rw [bot_lt_iff_ne_bot]
    intro heBot
    exact hD.1 (heBot ▸ heD)
  have heSup : e ≤ ⨆ i : ι, F i :=
    heF.trans (le_iSup (fun i : ι => F i) i)
  have heCompl : e ≤ (⨆ i : ι, F i)ᶜ :=
    hed.trans hdCompl
  have heBot : e ≤ ⊥ := by
    exact (le_inf heSup heCompl).trans (by rw [inf_compl_eq_bot])
  exact not_le_of_gt heNonzero heBot

private theorem exists_dense_below_iSup {α : Type u} [CompleteBooleanAlgebra α]
    {ι : Sort v} {D : Set α} (hD : dense_subset D) {Γ : α}
    (hNonzero : ⊥ < Γ) (F : ι → α) (hLe : Γ ≤ ⨆ i : ι, F i) :
    ∃ i d, ⊥ < d ∧ d ≤ F i ⊓ Γ ∧ d ∈ D := by
  classical
  have hSome : ∃ i, ⊥ < Γ ⊓ F i := by
    by_contra hNone
    push Not at hNone
    have hAllBot : ∀ i, Γ ⊓ F i ≤ ⊥ := by
      intro i
      rw [le_bot_iff]
      by_contra hne
      exact hNone i (bot_lt_iff_ne_bot.mpr hne)
    have hΓBot : Γ ≤ ⊥ := by
      calc
        Γ = Γ ⊓ (⨆ i : ι, F i) := by
          exact (inf_eq_left.mpr hLe).symm
        _ = ⨆ i : ι, Γ ⊓ F i := by
          rw [inf_iSup_eq]
        _ ≤ ⊥ := iSup_le hAllBot
    exact (not_le_of_gt hNonzero) hΓBot
  rcases hSome with ⟨i, hi⟩
  rcases hD.2 (Γ ⊓ F i) hi with ⟨d, hdD, hdLe⟩
  have hdNonzero : ⊥ < d := by
    rw [bot_lt_iff_ne_bot]
    intro hd
    exact hD.1 (hd ▸ hdD)
  refine ⟨i, d, hdNonzero, ?_, hdD⟩
  exact hdLe.trans (by rw [inf_comm])

/-!
Port of the opening layer of upstream `src/forcing_CH.lean`.

This module names the collapse Boolean algebra, exposes the Boolean-valued `aleph_one`
wrapper expected by the CH forcing branch, and packages the collapse relation through
functionality and surjectivity.  The forcing-specific endpoint `collapse_algebra.CH₂_true`
is still to be ported.
-/

namespace bSet

section aleph_one

variable {𝔹 : Type u} [CompleteBooleanAlgebra 𝔹]

noncomputable def aleph_one : bSet 𝔹 :=
  a1

lemma aleph_one_satisfies_spec {Γ : 𝔹} :
    Γ ≤ aleph_one_Ord_spec (aleph_one : bSet 𝔹) :=
  a1_spec

lemma aleph_one_check_sub_aleph_one {Γ : 𝔹} :
    Γ ≤ (check (pSet.card_ex (Cardinal.aleph 1)) : bSet 𝔹) ⊆ᴮ aleph_one :=
  aleph_one_check_sub_aleph_one_aux a1_Ord a1_spec

lemma aleph_one_le_of_omega_lt {Γ : 𝔹} :
    Γ ≤ le_of_omega_lt (aleph_one : bSet 𝔹) :=
  a1_le_of_omega_lt

end aleph_one

section lemmas

variable {𝔹 : Type u} [CompleteBooleanAlgebra 𝔹]

lemma aleph_one_check_is_aleph_one_of_omega_lt {Γ : 𝔹}
    (hOmegaLt : Γ ≤ (larger_than omega (check pSet.aleph_one : bSet 𝔹))ᶜ) :
    Γ ≤ (check pSet.aleph_one : bSet 𝔹) =ᴮ aleph_one := by
  apply subset_ext
  · exact aleph_one_check_sub_aleph_one
  · have hSpec : Γ ≤ aleph_one_Ord_spec (aleph_one : bSet 𝔹) :=
      aleph_one_satisfies_spec
    unfold aleph_one_Ord_spec at hSpec
    have hMinimal : Γ ≤ (⨅ y : bSet 𝔹, lattice.imp (Ord y)
        (lattice.imp ((injects_into y omega)ᶜ) ((aleph_one : bSet 𝔹) ⊆ᴮ y))) := by
      exact hSpec.trans (inf_le_right.trans inf_le_right)
    have hOrdImp : Γ ≤ lattice.imp (Ord (check pSet.aleph_one : bSet 𝔹))
        (lattice.imp ((injects_into (check pSet.aleph_one : bSet 𝔹) omega)ᶜ)
          ((aleph_one : bSet 𝔹) ⊆ᴮ (check pSet.aleph_one : bSet 𝔹))) :=
      hMinimal.trans (iInf_le _ (check pSet.aleph_one : bSet 𝔹))
    have hAfterOrd : Γ ≤ lattice.imp ((injects_into (check pSet.aleph_one : bSet 𝔹) omega)ᶜ)
        ((aleph_one : bSet 𝔹) ⊆ᴮ (check pSet.aleph_one : bSet 𝔹)) :=
      lattice.bv_context_apply hOrdImp (check_Ord pSet.aleph_one_Ord)
    have hNotInjects : Γ ≤ (injects_into (check pSet.aleph_one : bSet 𝔹) omega)ᶜ := by
      have hBot : Γ ⊓ injects_into (check pSet.aleph_one : bSet 𝔹) omega ≤ ⊥ := by
        let Δ : 𝔹 := Γ ⊓ injects_into (check pSet.aleph_one : bSet 𝔹) omega
        have hSurj : Δ ≤ surjects_onto omega (check pSet.aleph_one : bSet 𝔹) :=
          surjects_onto_of_injects_into inf_le_right aleph_one_check_exists_mem
        have hLarge : Δ ≤ larger_than omega (check pSet.aleph_one : bSet 𝔹) :=
          larger_than_of_surjects_onto hSurj
        have hNotLarge : Δ ≤ (larger_than omega (check pSet.aleph_one : bSet 𝔹))ᶜ :=
          inf_le_left.trans hOmegaLt
        exact (le_inf hLarge hNotLarge).trans (by rw [inf_compl_eq_bot])
      rw [le_compl_iff_disjoint_right]
      exact disjoint_iff.mpr (eq_bot_iff.mpr hBot)
    exact lattice.bv_context_apply hAfterOrd hNotInjects

lemma aleph_one_check_le_of_omega_lt {Γ : 𝔹}
    (hOmegaLt : Γ ≤ (larger_than omega (check pSet.aleph_one : bSet 𝔹))ᶜ) :
    Γ ≤ le_of_omega_lt (check pSet.aleph_one : bSet 𝔹) := by
  have hEq : Γ ≤ (check pSet.aleph_one : bSet 𝔹) =ᴮ aleph_one :=
    aleph_one_check_is_aleph_one_of_omega_lt hOmegaLt
  exact (le_inf (bv_symm hEq) aleph_one_le_of_omega_lt).trans
    (B_ext_le_of_omega_lt (aleph_one : bSet 𝔹) (check pSet.aleph_one : bSet 𝔹))

/-- If every checked member of a pre-set satisfies a Boolean-valued predicate, then the bounded
infimum over that checked pre-set does too. -/
lemma check_forall (x : pSet.{u}) (φ : bSet 𝔹 → 𝔹) {Γ : 𝔹}
    (h : ∀ y : x.Type, Γ ≤ φ (check (x.Func y))) :
    Γ ≤ ⨅ y : x.Type, φ (check (x.Func y)) :=
  le_iInf h

/-- Relation over `x × y` coded by a Boolean-valued array on the concrete indices. -/
def rel_of_array (x y : bSet 𝔹) (af : x.type → y.type → 𝔹) : bSet 𝔹 :=
  set_of_indicator (x := prod x y) (fun pr => af pr.1 pr.2)

lemma mem_left_of_mem_rel_of_array {x y w₁ w₂ : bSet 𝔹} {af : x.type → y.type → 𝔹}
    {Γ : 𝔹} (hMem : Γ ≤ pair w₁ w₂ ∈ᴮ rel_of_array x y af)
    (hBVal₁ : ∀ i, x.bval i = ⊤) :
    Γ ≤ w₁ ∈ᴮ x := by
  unfold rel_of_array at hMem
  rw [mem_set_of_indicator_iff] at hMem
  apply (le_inf le_rfl hMem).trans
  apply lattice.bv_cases_right
  intro p
  let Δ : 𝔹 := Γ ⊓ ((af p.1 p.2 ⊓ (prod x y).bval p) ⊓
    pair w₁ w₂ =ᴮ (prod x y).func p)
  change Δ ≤ w₁ ∈ᴮ x
  have hPairEq : Δ ≤ pair w₁ w₂ =ᴮ (prod x y).func p := by
    dsimp [Δ]
    exact inf_le_right.trans inf_le_right
  have hw₁Eq : Δ ≤ w₁ =ᴮ x.func p.1 := by
    simpa [Prod.fst] using eq_of_eq_pair_left' hPairEq
  have hxMem : Δ ≤ x.func p.1 ∈ᴮ x := by
    rw [mem_unfold]
    apply le_iSup_of_le p.1
    apply le_inf
    · simpa [hBVal₁ p.1] using (le_top : Δ ≤ x.bval p.1)
    · exact bv_refl
  exact subst_congr_mem_left' (bv_symm hw₁Eq) hxMem

lemma mem_right_of_mem_rel_of_array {x y w₁ w₂ : bSet 𝔹} {af : x.type → y.type → 𝔹}
    {Γ : 𝔹} (hMem : Γ ≤ pair w₁ w₂ ∈ᴮ rel_of_array x y af)
    (hBVal₂ : ∀ i, y.bval i = ⊤) :
    Γ ≤ w₂ ∈ᴮ y := by
  unfold rel_of_array at hMem
  rw [mem_set_of_indicator_iff] at hMem
  apply (le_inf le_rfl hMem).trans
  apply lattice.bv_cases_right
  intro p
  let Δ : 𝔹 := Γ ⊓ ((af p.1 p.2 ⊓ (prod x y).bval p) ⊓
    pair w₁ w₂ =ᴮ (prod x y).func p)
  change Δ ≤ w₂ ∈ᴮ y
  have hPairEq : Δ ≤ pair w₁ w₂ =ᴮ (prod x y).func p := by
    dsimp [Δ]
    exact inf_le_right.trans inf_le_right
  have hw₂Eq : Δ ≤ w₂ =ᴮ y.func p.2 := by
    simpa [Prod.snd] using eq_of_eq_pair_right' hPairEq
  have hyMem : Δ ≤ y.func p.2 ∈ᴮ y := by
    rw [mem_unfold]
    apply le_iSup_of_le p.2
    apply le_inf
    · simpa [hBVal₂ p.2] using (le_top : Δ ≤ y.bval p.2)
    · exact bv_refl
  exact subst_congr_mem_left' (bv_symm hw₂Eq) hyMem

lemma rel_of_array_surj (x y : bSet 𝔹) (af : x.type → y.type → 𝔹)
    (hBVal₁ : ∀ i, x.bval i = ⊤)
    (hBVal₂ : ∀ i, y.bval i = ⊤)
    (hWide : ∀ j, (⨆ i : x.type, af i j) = ⊤) {Γ : 𝔹} :
    Γ ≤ is_surj x y (rel_of_array x y af) := by
  unfold is_surj
  apply le_iInf
  intro z
  apply lattice.bv_imp_intro
  let Δ : 𝔹 := Γ ⊓ z ∈ᴮ y
  change Δ ≤ ⨆ w : bSet 𝔹, w ∈ᴮ x ⊓ pair w z ∈ᴮ rel_of_array x y af
  have hzCases : Δ ≤ ⨆ j : y.type, y.bval j ⊓ z =ᴮ y.func j := by
    have hzMem : Δ ≤ z ∈ᴮ y := inf_le_right
    rw [mem_unfold] at hzMem
    exact hzMem
  apply (le_inf le_rfl hzCases).trans
  apply lattice.bv_cases_right
  intro j
  let Θ : 𝔹 := Δ ⊓ (y.bval j ⊓ z =ᴮ y.func j)
  change Θ ≤ ⨆ w : bSet 𝔹, w ∈ᴮ x ⊓ pair w z ∈ᴮ rel_of_array x y af
  have hWideΘ : Θ ≤ ⨆ i : x.type, af i j := by
    rw [hWide j]
    exact le_top
  apply (le_inf le_rfl hWideΘ).trans
  apply lattice.bv_cases_right
  intro i
  let Ω : 𝔹 := Θ ⊓ af i j
  change Ω ≤ ⨆ w : bSet 𝔹, w ∈ᴮ x ⊓ pair w z ∈ᴮ rel_of_array x y af
  apply lattice.bv_use (x.func i)
  apply le_inf
  · rw [mem_unfold]
    apply le_iSup_of_le i
    apply le_inf
    · simpa [hBVal₁ i] using (le_top : Ω ≤ x.bval i)
    · exact bv_refl
  · unfold rel_of_array
    rw [mem_set_of_indicator_iff]
    apply le_iSup_of_le (i, j)
    apply le_inf
    · apply le_inf
      · dsimp [Ω]
        exact inf_le_right
      · dsimp [prod]
        exact le_inf
          (by simpa [hBVal₁ i] using (le_top : Ω ≤ x.bval i))
          (by simpa [hBVal₂ j] using (le_top : Ω ≤ y.bval j))
    · have hzEq : Ω ≤ z =ᴮ y.func j := by
        dsimp [Ω, Θ]
        exact inf_le_left.trans (inf_le_right.trans inf_le_right)
      have hPairEq : Ω ≤ pair (x.func i) z =ᴮ (prod x y).func (i, j) := by
        simpa [prod] using subst_congr_pair_right hzEq
      exact hPairEq

lemma rel_of_array_is_func (x y : bSet 𝔹) (af : x.type → y.type → 𝔹)
    (hExt : ∀ i₁ i₂ j₁ j₂,
      af i₁ j₁ ⊓ af i₂ j₂ ⊓ (x.func i₁ =ᴮ x.func i₂) ≤ y.func j₁ =ᴮ y.func j₂)
    {Γ : 𝔹} :
    Γ ≤ is_func (rel_of_array x y af) := by
  unfold is_func
  apply le_iInf
  intro w₁
  apply le_iInf
  intro w₂
  apply le_iInf
  intro v₁
  apply le_iInf
  intro v₂
  apply lattice.bv_imp_intro
  apply lattice.bv_imp_intro
  let Δ : 𝔹 :=
    Γ ⊓ (pair w₁ v₁ ∈ᴮ rel_of_array x y af ⊓
      pair w₂ v₂ ∈ᴮ rel_of_array x y af) ⊓ (w₁ =ᴮ w₂)
  change Δ ≤ v₁ =ᴮ v₂
  have hMem₁ : Δ ≤ pair w₁ v₁ ∈ᴮ rel_of_array x y af := by
    dsimp [Δ]
    exact inf_le_left.trans (inf_le_right.trans inf_le_left)
  have hMem₂ : Δ ≤ pair w₂ v₂ ∈ᴮ rel_of_array x y af := by
    dsimp [Δ]
    exact inf_le_left.trans (inf_le_right.trans inf_le_right)
  have hInput : Δ ≤ w₁ =ᴮ w₂ := by
    dsimp [Δ]
    exact inf_le_right
  unfold rel_of_array at hMem₁ hMem₂
  rw [mem_set_of_indicator_iff] at hMem₁ hMem₂
  apply (le_inf le_rfl hMem₁).trans
  apply lattice.bv_cases_right
  intro pr₁
  let Θ : 𝔹 := Δ ⊓ ((af pr₁.1 pr₁.2 ⊓ (prod x y).bval pr₁) ⊓
    pair w₁ v₁ =ᴮ (prod x y).func pr₁)
  change Θ ≤ v₁ =ᴮ v₂
  have hMem₂Θ : Θ ≤ pair w₂ v₂ ∈ᴮ set_of_indicator
      (x := prod x y) (fun pr => af pr.1 pr.2) :=
    inf_le_left.trans hMem₂
  rw [mem_set_of_indicator_iff] at hMem₂Θ
  apply (le_inf le_rfl hMem₂Θ).trans
  apply lattice.bv_cases_right
  intro pr₂
  let Ω : 𝔹 := Θ ⊓ ((af pr₂.1 pr₂.2 ⊓ (prod x y).bval pr₂) ⊓
    pair w₂ v₂ =ᴮ (prod x y).func pr₂)
  change Ω ≤ v₁ =ᴮ v₂
  have hAf₁ : Ω ≤ af pr₁.1 pr₁.2 := by
    dsimp [Ω, Θ]
    exact inf_le_left.trans (inf_le_right.trans (inf_le_left.trans inf_le_left))
  have hAf₂ : Ω ≤ af pr₂.1 pr₂.2 := by
    dsimp [Ω]
    exact inf_le_right.trans (inf_le_left.trans inf_le_left)
  have hPair₁ : Ω ≤ pair w₁ v₁ =ᴮ (prod x y).func pr₁ := by
    dsimp [Ω, Θ]
    exact inf_le_left.trans (inf_le_right.trans inf_le_right)
  have hPair₂ : Ω ≤ pair w₂ v₂ =ᴮ (prod x y).func pr₂ := by
    dsimp [Ω]
    exact inf_le_right.trans inf_le_right
  have hw₁ : Ω ≤ w₁ =ᴮ x.func pr₁.1 := by
    simpa [prod] using eq_of_eq_pair_left' hPair₁
  have hv₁ : Ω ≤ v₁ =ᴮ y.func pr₁.2 := by
    simpa [prod] using eq_of_eq_pair_right' hPair₁
  have hw₂ : Ω ≤ w₂ =ᴮ x.func pr₂.1 := by
    simpa [prod] using eq_of_eq_pair_left' hPair₂
  have hv₂ : Ω ≤ v₂ =ᴮ y.func pr₂.2 := by
    simpa [prod] using eq_of_eq_pair_right' hPair₂
  have hInputΩ : Ω ≤ w₁ =ᴮ w₂ := inf_le_left.trans (inf_le_left.trans hInput)
  have hxEq : Ω ≤ x.func pr₁.1 =ᴮ x.func pr₂.1 :=
    bv_trans (bv_symm hw₁) (bv_trans hInputΩ hw₂)
  have hyEq : Ω ≤ y.func pr₁.2 =ᴮ y.func pr₂.2 := by
    exact (le_inf (le_inf hAf₁ hAf₂) hxEq).trans (hExt pr₁.1 pr₂.1 pr₁.2 pr₂.2)
  exact bv_trans hv₁ (bv_trans hyEq (bv_symm hv₂))

lemma rel_of_array_total (x y : bSet 𝔹) (af : x.type → y.type → 𝔹)
    (hBVal₁ : ∀ i, x.bval i = ⊤)
    (hBVal₂ : ∀ i, y.bval i = ⊤)
    (hTall : ∀ i, (⨆ j : y.type, af i j) = ⊤) {Γ : 𝔹} :
    Γ ≤ is_total x y (rel_of_array x y af) := by
  unfold is_total
  apply le_iInf
  intro z
  apply lattice.bv_imp_intro
  let Δ : 𝔹 := Γ ⊓ z ∈ᴮ x
  change Δ ≤ ⨆ w : bSet 𝔹, w ∈ᴮ y ⊓ pair z w ∈ᴮ rel_of_array x y af
  have hzCases : Δ ≤ ⨆ i : x.type, x.bval i ⊓ z =ᴮ x.func i := by
    have hzMem : Δ ≤ z ∈ᴮ x := inf_le_right
    rw [mem_unfold] at hzMem
    exact hzMem
  apply (le_inf le_rfl hzCases).trans
  apply lattice.bv_cases_right
  intro i
  let Θ : 𝔹 := Δ ⊓ (x.bval i ⊓ z =ᴮ x.func i)
  change Θ ≤ ⨆ w : bSet 𝔹, w ∈ᴮ y ⊓ pair z w ∈ᴮ rel_of_array x y af
  have hTallΘ : Θ ≤ ⨆ j : y.type, af i j := by
    rw [hTall i]
    exact le_top
  apply (le_inf le_rfl hTallΘ).trans
  apply lattice.bv_cases_right
  intro j
  let Ω : 𝔹 := Θ ⊓ af i j
  change Ω ≤ ⨆ w : bSet 𝔹, w ∈ᴮ y ⊓ pair z w ∈ᴮ rel_of_array x y af
  apply lattice.bv_use (y.func j)
  apply le_inf
  · rw [mem_unfold]
    apply le_iSup_of_le j
    apply le_inf
    · simpa [hBVal₂ j] using (le_top : Ω ≤ y.bval j)
    · exact bv_refl
  · unfold rel_of_array
    rw [mem_set_of_indicator_iff]
    apply le_iSup_of_le (i, j)
    apply le_inf
    · apply le_inf
      · dsimp [Ω]
        exact inf_le_right
      · dsimp [prod]
        exact le_inf
          (by simpa [hBVal₁ i] using (le_top : Ω ≤ x.bval i))
          (by simpa [hBVal₂ j] using (le_top : Ω ≤ y.bval j))
    · have hzEq : Ω ≤ z =ᴮ x.func i := by
        dsimp [Ω, Θ]
        exact inf_le_left.trans (inf_le_right.trans inf_le_right)
      have hPairEq : Ω ≤ pair z (y.func j) =ᴮ (prod x y).func (i, j) := by
        simpa [prod] using subst_congr_pair_left hzEq
      exact hPairEq

lemma rel_of_array_is_func' (x y : bSet 𝔹) (af : x.type → y.type → 𝔹)
    (hBVal₁ : ∀ i, x.bval i = ⊤)
    (hBVal₂ : ∀ i, y.bval i = ⊤)
    (hTall : ∀ i, (⨆ j : y.type, af i j) = ⊤)
    (hExt : ∀ i₁ i₂ j₁ j₂,
      af i₁ j₁ ⊓ af i₂ j₂ ⊓ (x.func i₁ =ᴮ x.func i₂) ≤ y.func j₁ =ᴮ y.func j₂)
    {Γ : 𝔹} :
    Γ ≤ is_func' x y (rel_of_array x y af) :=
  le_inf (rel_of_array_is_func x y af hExt)
    (rel_of_array_total x y af hBVal₁ hBVal₂ hTall)

end lemmas

end bSet

namespace collapse_algebra

open bSet
open collapse_poset

/-- Upstream-compatible name for the collapse Boolean algebra used by the CH forcing branch. -/
abbrev 𝔹_collapse : Type u :=
  collapse_poset.collapse_boolean_algebra.{u}

instance collapseBooleanAlgebraAsCompleteBooleanAlgebra :
    CompleteBooleanAlgebra (𝔹_collapse.{u}) :=
  inferInstance

instance collapseBooleanAlgebraAsNontrivial :
    Nontrivial (𝔹_collapse.{u}) :=
  inferInstance

local notation "β" => 𝔹_collapse

private abbrev X₁ : Type u :=
  (pSet.card_ex (Cardinal.aleph 1) : pSet.{u}).Type

private abbrev Yω : Type u :=
  (PSet.powerset PSet.omega : pSet.{u}).Type

local notation "ℵ₁̌" => (check (pSet.card_ex (Cardinal.aleph 1)) : bSet β)
local notation "𝒫ω̌" => (check (PSet.powerset PSet.omega) : bSet β)

private lemma ordinal_mk_func_inj {o : ordinal.{u}} {i j : (ordinal.mk o).Type}
    (h : PSet.Equiv ((ordinal.mk o).Func i) ((ordinal.mk o).Func j)) : i = j := by
  change PSet.Equiv ((Ordinal.toPSet o).Func i) ((Ordinal.toPSet o).Func j) at h
  revert i j
  let M : PSet.{u} → Prop := fun x =>
    ∀ {i j : x.Type}, PSet.Equiv (x.Func i) (x.Func j) → i = j
  change M (Ordinal.toPSet o)
  rw [Ordinal.toPSet.eq_1 o]
  intro i j h
  apply Ordinal.ToType.mk.symm.injective
  apply Subtype.ext
  exact ordinal.mk_inj h

private lemma card_ex_aleph_one_func_inj {i j : X₁}
    (h : PSet.Equiv ((pSet.card_ex (Cardinal.aleph 1) : pSet.{u}).Func i)
      ((pSet.card_ex (Cardinal.aleph 1) : pSet.{u}).Func j)) : i = j := by
  simpa [pSet.card_ex] using ordinal_mk_func_inj (o := Cardinal.ord (Cardinal.aleph 1)) h

lemma exists_aleph_one_index_not_mem_dom
    (p : collapse_poset (pSet.card_ex (Cardinal.aleph 1) : pSet.{u}).Type
        (PSet.powerset PSet.omega : pSet.{u}).Type (Order.succ Cardinal.aleph0)) :
    ∃ η : (pSet.card_ex (Cardinal.aleph 1) : pSet.{u}).Type, η ∉ PFun.Dom p.f := by
  classical
  by_contra h
  push_neg at h
  have hSurj : Function.Surjective
      (fun η : PFun.Dom p.f => (η : (pSet.card_ex (Cardinal.aleph 1) : pSet.{u}).Type)) := by
    intro η
    exact ⟨⟨η, h η⟩, rfl⟩
  have hLe : (Cardinal.aleph 1 : Cardinal.{u}) ≤ Cardinal.mk (PFun.Dom p.f) := by
    have hMk : Cardinal.mk (pSet.card_ex (Cardinal.aleph 1) : pSet.{u}).Type ≤
        Cardinal.mk (PFun.Dom p.f) :=
      Cardinal.mk_le_of_surjective hSurj
    simpa [pSet.card_ex_type] using hMk
  have hLt : (Cardinal.aleph 1 : Cardinal.{u}) < Cardinal.aleph 1 := by
    have hLt' : (Cardinal.aleph 1 : Cardinal.{u}) < Order.succ Cardinal.aleph0 :=
      lt_of_le_of_lt hLe p.Hc
    simpa [← pSet.aleph_one_eq_succ_aleph_zero] using hLt'
  exact (lt_irrefl (Cardinal.aleph 1 : Cardinal.{u}) hLt).elim

/-- The regular-open value of the collapse relation array at a ground-model index pair. -/
noncomputable def π_af (η : ℵ₁̌.type) (S : 𝒫ω̌.type) : β :=
  let η' : (pSet.card_ex (Cardinal.aleph 1) : pSet.{u}).Type := check_cast (𝔹 := β) η
  let S' : (PSet.powerset PSet.omega : pSet.{u}).Type := check_cast (𝔹 := β) S
  ⟨{g : (pSet.card_ex (Cardinal.aleph 1) : pSet.{u}).Type →
        (PSet.powerset PSet.omega : pSet.{u}).Type | g η' = S'},
    is_regular_singleton_regular_open' (x := η') (y := S')⟩

/-- Collapse relation from `aleph_one` onto the ground-model powerset of `omega`. -/
noncomputable def π : bSet.{u} β :=
  rel_of_array ℵ₁̌ 𝒫ω̌ π_af

private lemma inclusion_union_le_left {X Y : Type u} [Nonempty Y]
    {p q : collapse_poset X Y (Order.succ Cardinal.aleph0)}
    (hcomp : compatible p q) :
    inclusion (union p q) ≤ inclusion p := by
  change principal_open (union p q) ⊆ principal_open p
  intro g hg
  have hg' : g ∈ principal_open p ∩ principal_open q := by
    simpa [inter_principal_open hcomp] using hg
  exact hg'.1

private lemma inclusion_le_pi_af_of_forces
    (p : collapse_poset X₁ Yω (Order.succ Cardinal.aleph0))
    (η : ℵ₁̌.type) (S : 𝒫ω̌.type)
    (h : ∀ g ∈ principal_open p, g (check_cast (𝔹 := β) η) = check_cast (𝔹 := β) S) :
    inclusion p ≤ π_af η S := by
  change principal_open p ⊆
    ({g : X₁ → Yω | g (check_cast (𝔹 := β) η) = check_cast (𝔹 := β) S} : Set (X₁ → Yω))
  intro g hg
  exact h g hg

private lemma compatible_singleton_of_not_mem_dom
    (p : collapse_poset X₁ Yω (Order.succ Cardinal.aleph0))
    {η : X₁} (S : Yω) (hη : η ∉ PFun.Dom p.f) :
    compatible p (singleton_collapse_poset η S one_lt_succ_aleph0) := by
  intro a hp hq
  have ha : a = η := by
    simpa [singleton_collapse_poset, pfun_singleton_dom] using hq
  exact False.elim (hη (ha ▸ hp))

private lemma inclusion_union_singleton_le_pi_af
    (p : collapse_poset X₁ Yω (Order.succ Cardinal.aleph0))
    (η : ℵ₁̌.type) (S : 𝒫ω̌.type)
    (hcomp : compatible p
      (singleton_collapse_poset (check_cast (𝔹 := β) η) (check_cast (𝔹 := β) S)
        one_lt_succ_aleph0)) :
    inclusion (union p
      (singleton_collapse_poset (check_cast (𝔹 := β) η) (check_cast (𝔹 := β) S)
        one_lt_succ_aleph0)) ≤ π_af η S := by
  apply inclusion_le_pi_af_of_forces
  intro g hg
  have hg' : g ∈ principal_open p ∩ principal_open
      (singleton_collapse_poset (check_cast (𝔹 := β) η) (check_cast (𝔹 := β) S)
        one_lt_succ_aleph0) := by
    simpa [inter_principal_open hcomp] using hg
  simpa [singleton_collapse_poset_principal_open] using hg'.2

private lemma inclusion_le_pi_af_of_mem_dom
    (p : collapse_poset X₁ Yω (Order.succ Cardinal.aleph0))
    (η : ℵ₁̌.type) (hη : check_cast (𝔹 := β) η ∈ PFun.Dom p.f) :
    inclusion p ≤ π_af η (check_cast.symm (𝔹 := β) (fn p.f (check_cast (𝔹 := β) η) hη)) := by
  apply inclusion_le_pi_af_of_forces
  intro g hg
  exact (mem_principal_open_iff'.mp hg) (check_cast (𝔹 := β) η) hη

lemma π_af_wide (S : 𝒫ω̌.type) :
    (⨆ η : ℵ₁̌.type, π_af η S) = ⊤ := by
  let F : ℵ₁̌.type → β := fun η => π_af η S
  have hBelow : ∀ d ∈ collapse_principal_opens X₁ Yω,
      ∃ e ∈ collapse_principal_opens X₁ Yω, e ≤ d ∧ ∃ η, e ≤ F η := by
    intro d hd
    rcases hd with ⟨p, rfl⟩
    let S' : Yω := check_cast (𝔹 := β) S
    rcases exists_aleph_one_index_not_mem_dom p with ⟨η', hη'⟩
    let η : ℵ₁̌.type := check_cast.symm (𝔹 := β) η'
    let q : collapse_poset X₁ Yω (Order.succ Cardinal.aleph0) :=
      union p (singleton_collapse_poset η' S' one_lt_succ_aleph0)
    have hcomp : compatible p (singleton_collapse_poset η' S' one_lt_succ_aleph0) :=
      compatible_singleton_of_not_mem_dom p S' hη'
    have hcompη : compatible p
        (singleton_collapse_poset (check_cast (𝔹 := β) η) (check_cast (𝔹 := β) S)
          one_lt_succ_aleph0) := by
      simpa [η, S'] using hcomp
    refine ⟨inclusion q, ⟨q, rfl⟩, ?_, η, ?_⟩
    · exact inclusion_union_le_left hcomp
    · dsimp [F, q, η, S']
      simpa [η, S'] using inclusion_union_singleton_le_pi_af p η S hcompη
  exact iSup_eq_top_of_dense_below (α := β) (ι := ℵ₁̌.type)
    (D := collapse_principal_opens X₁ Yω) collapse_principal_opens_dense F hBelow

lemma π_af_tall (η : ℵ₁̌.type) :
    (⨆ S : 𝒫ω̌.type, π_af η S) = ⊤ := by
  let F : 𝒫ω̌.type → β := fun S => π_af η S
  have hBelow : ∀ d ∈ collapse_principal_opens X₁ Yω,
      ∃ e ∈ collapse_principal_opens X₁ Yω, e ≤ d ∧ ∃ S, e ≤ F S := by
    intro d hd
    rcases hd with ⟨p, rfl⟩
    let η' : X₁ := check_cast (𝔹 := β) η
    by_cases hη' : η' ∈ PFun.Dom p.f
    · let S : 𝒫ω̌.type := check_cast.symm (𝔹 := β) (fn p.f η' hη')
      refine ⟨inclusion p, ⟨p, rfl⟩, le_rfl, S, ?_⟩
      dsimp [F, S, η']
      simpa using inclusion_le_pi_af_of_mem_dom p η hη'
    · let S' : Yω := collapse_poset.empty_powerset_omega
      let S : 𝒫ω̌.type := check_cast.symm (𝔹 := β) S'
      let q : collapse_poset X₁ Yω (Order.succ Cardinal.aleph0) :=
        union p (singleton_collapse_poset η' S' one_lt_succ_aleph0)
      have hcomp : compatible p (singleton_collapse_poset η' S' one_lt_succ_aleph0) :=
        compatible_singleton_of_not_mem_dom p S' hη'
      have hcompη : compatible p
          (singleton_collapse_poset (check_cast (𝔹 := β) η) (check_cast (𝔹 := β) S)
            one_lt_succ_aleph0) := by
        simpa [η', S, S'] using hcomp
      refine ⟨inclusion q, ⟨q, rfl⟩, ?_, S, ?_⟩
      · exact inclusion_union_le_left hcomp
      · dsimp [F, q, S, S', η']
        simpa [S, S', η'] using inclusion_union_singleton_le_pi_af p η S hcompη
  exact iSup_eq_top_of_dense_below (α := β) (ι := 𝒫ω̌.type)
    (D := collapse_principal_opens X₁ Yω) collapse_principal_opens_dense F hBelow

private lemma check_aleph_one_bval_top (η : ℵ₁̌.type) : ℵ₁̌.bval η = ⊤ := by
  simp

private lemma check_powerset_omega_bval_top (S : 𝒫ω̌.type) : 𝒫ω̌.bval S = ⊤ := by
  simp

lemma π_is_total {Γ : β} :
    Γ ≤ is_total ℵ₁̌ 𝒫ω̌ π :=
  rel_of_array_total ℵ₁̌ 𝒫ω̌ π_af check_aleph_one_bval_top
    check_powerset_omega_bval_top π_af_tall

lemma π_is_surj {Γ : β} :
    Γ ≤ is_surj ℵ₁̌ 𝒫ω̌ π :=
  rel_of_array_surj ℵ₁̌ 𝒫ω̌ π_af check_aleph_one_bval_top
    check_powerset_omega_bval_top π_af_wide

private lemma π_af_inf_le_bot_of_ne (η : ℵ₁̌.type) {S₁ S₂ : 𝒫ω̌.type}
    (hS : check_cast (𝔹 := β) S₁ ≠ check_cast (𝔹 := β) S₂) :
    π_af η S₁ ⊓ π_af η S₂ ≤ ⊥ := by
  change ({g : X₁ → Yω | g (check_cast (𝔹 := β) η) = check_cast (𝔹 := β) S₁} ∩
      {g : X₁ → Yω | g (check_cast (𝔹 := β) η) = check_cast (𝔹 := β) S₂} :
      Set (X₁ → Yω)) ⊆ ∅
  intro g hg
  exact hS (hg.1.symm.trans hg.2)

lemma π_ext
    (η₁ η₂ : (check (pSet.card_ex (Cardinal.aleph 1) : pSet.{u}) : bSet.{u} β).type)
    (S₁ S₂ : (check (PSet.powerset PSet.omega : pSet.{u}) : bSet.{u} β).type) :
    π_af η₁ S₁ ⊓ π_af η₂ S₂ ⊓ (ℵ₁̌.func η₁ =ᴮ ℵ₁̌.func η₂) ≤
      𝒫ω̌.func S₁ =ᴮ 𝒫ω̌.func S₂ := by
  classical
  by_cases hηEquiv : PSet.Equiv
      ((pSet.card_ex (Cardinal.aleph 1) : pSet.{u}).Func
        (check_cast (𝔹 := β) (x := (pSet.card_ex (Cardinal.aleph 1) : pSet.{u})) η₁))
      ((pSet.card_ex (Cardinal.aleph 1) : pSet.{u}).Func
        (check_cast (𝔹 := β) (x := (pSet.card_ex (Cardinal.aleph 1) : pSet.{u})) η₂))
  · have hη : check_cast (𝔹 := β) η₁ = check_cast (𝔹 := β) η₂ :=
      card_ex_aleph_one_func_inj hηEquiv
    have hηidx : η₁ = η₂ := by
      calc
        η₁ = check_cast.symm (𝔹 := β) (check_cast (𝔹 := β) η₁) := by simp [check_cast, check_cast.symm]
        _ = check_cast.symm (𝔹 := β) (check_cast (𝔹 := β) η₂) := by rw [hη]
        _ = η₂ := by simp [check_cast, check_cast.symm]
    by_cases hS : check_cast (𝔹 := β) S₁ = check_cast (𝔹 := β) S₂
    · have hSidx : S₁ = S₂ := by
        calc
          S₁ = check_cast.symm (𝔹 := β) (check_cast (𝔹 := β) S₁) := by simp [check_cast, check_cast.symm]
          _ = check_cast.symm (𝔹 := β) (check_cast (𝔹 := β) S₂) := by rw [hS]
          _ = S₂ := by simp [check_cast, check_cast.symm]
      subst hηidx
      subst hSidx
      exact bv_refl
    · have hBot : π_af η₁ S₁ ⊓ π_af η₂ S₂ ⊓ (ℵ₁̌.func η₁ =ᴮ ℵ₁̌.func η₂) ≤ ⊥ := by
        subst hηidx
        exact inf_le_left.trans (π_af_inf_le_bot_of_ne η₁ hS)
      exact hBot.trans bot_le
  · have hEqBot : (ℵ₁̌.func η₁ =ᴮ ℵ₁̌.func η₂) = ⊥ := by
      simpa using (check_bv_eq_bot_of_not_equiv
        (𝔹 := β)
        (x := (pSet.card_ex (Cardinal.aleph 1) : pSet.{u}).Func
          (check_cast (𝔹 := β) (x := (pSet.card_ex (Cardinal.aleph 1) : pSet.{u})) η₁))
        (y := (pSet.card_ex (Cardinal.aleph 1) : pSet.{u}).Func
          (check_cast (𝔹 := β) (x := (pSet.card_ex (Cardinal.aleph 1) : pSet.{u})) η₂))
        hηEquiv)
    calc
      π_af η₁ S₁ ⊓ π_af η₂ S₂ ⊓ (ℵ₁̌.func η₁ =ᴮ ℵ₁̌.func η₂) ≤ ⊥ := by
        rw [hEqBot, inf_bot_eq]
      _ ≤ 𝒫ω̌.func S₁ =ᴮ 𝒫ω̌.func S₂ := bot_le

lemma π_is_func' {Γ : β} :
    Γ ≤ is_func' ℵ₁̌ 𝒫ω̌ π :=
  rel_of_array_is_func' ℵ₁̌ 𝒫ω̌ π_af check_aleph_one_bval_top
    check_powerset_omega_bval_top π_af_tall π_ext

lemma π_is_surj_onto_of_is_func' {Γ : β}
    (hFunc : Γ ≤ is_func' ℵ₁̌ 𝒫ω̌ π) :
    Γ ≤ is_surj_onto ℵ₁̌ 𝒫ω̌ π :=
  le_inf hFunc π_is_surj

lemma π_is_surj_onto {Γ : β} :
    Γ ≤ is_surj_onto ℵ₁̌ 𝒫ω̌ π :=
  π_is_surj_onto_of_is_func' π_is_func'

lemma aleph_one_larger_than_powerset_omega_check {Γ : β} :
    Γ ≤ larger_than ℵ₁̌ 𝒫ω̌ := by
  apply larger_than_of_surjects_onto
  unfold surjects_onto
  apply le_iSup_of_le π
  exact π_is_surj_onto

lemma aleph_one_larger_than_powerset_omega {Γ : β} :
    Γ ≤ larger_than (bSet.aleph_one : bSet.{u} β) 𝒫ω̌ := by
  have hSub : Γ ≤ ℵ₁̌ ⊆ᴮ (bSet.aleph_one : bSet.{u} β) :=
    bSet.aleph_one_check_sub_aleph_one
  have hInj : Γ ≤ injects_into ℵ₁̌ (bSet.aleph_one : bSet.{u} β) :=
    injects_into_of_subset hSub
  exact larger_than_of_larger_than_and_domain_injects
    aleph_one_larger_than_powerset_omega_check hInj

lemma aleph_one_injects_into_of_omega_not_larger {x : bSet.{u} β} {Γ : β}
    (hOrd : Γ ≤ Ord x) (hNotOmega : Γ ≤ (larger_than omega x)ᶜ) :
    Γ ≤ injects_into (bSet.aleph_one : bSet.{u} β) x := by
  have hLe : Γ ≤ le_of_omega_lt (bSet.aleph_one : bSet.{u} β) :=
    bSet.aleph_one_le_of_omega_lt
  unfold le_of_omega_lt at hLe
  have hAtX : Γ ≤ lattice.imp (Ord x)
      (lattice.imp ((larger_than omega x)ᶜ)
        (injects_into (bSet.aleph_one : bSet.{u} β) x)) :=
    hLe.trans (iInf_le _ x)
  have hAfterOrd : Γ ≤ lattice.imp ((larger_than omega x)ᶜ)
      (injects_into (bSet.aleph_one : bSet.{u} β) x) :=
    lattice.bv_context_apply hAtX hOrd
  exact lattice.bv_context_apply hAfterOrd hNotOmega

lemma powerset_omega_larger_than_of_omega_not_larger {x : bSet.{u} β} {Γ : β}
    (hOrd : Γ ≤ Ord x) (hNotOmega : Γ ≤ (larger_than omega x)ᶜ) :
    Γ ≤ larger_than x 𝒫ω̌ :=
  larger_than_of_larger_than_and_domain_injects
    aleph_one_larger_than_powerset_omega
    (aleph_one_injects_into_of_omega_not_larger hOrd hNotOmega)

lemma bv_powerset_omega_larger_than_of_omega_not_larger {x : bSet.{u} β} {Γ : β}
    (hContinuum : Γ ≤ injects_into (bv_powerset (omega : bSet.{u} β)) 𝒫ω̌)
    (hOrd : Γ ≤ Ord x) (hNotOmega : Γ ≤ (larger_than omega x)ᶜ) :
    Γ ≤ larger_than x (bv_powerset (omega : bSet.{u} β)) :=
  larger_than_of_larger_than_and_injects
    (powerset_omega_larger_than_of_omega_not_larger hOrd hNotOmega)
    hContinuum

lemma continuum_le_continuum_check_of_check_functions_eq {Γ : β}
    (hFunctions : Γ ≤
      (check (pSet.functions PSet.omega (PSet.ofNat 2)) : bSet.{u} β) =ᴮ
        functions (omega : bSet.{u} β) (2 : bSet.{u} β)) :
    Γ ≤ injects_into (bv_powerset (omega : bSet.{u} β)) 𝒫ω̌ := by
  have hPowersetToFunctions :
      Γ ≤ injects_into (bv_powerset (omega : bSet.{u} β))
        (functions (omega : bSet.{u} β) (2 : bSet.{u} β)) :=
    powerset_injects.powerset_injects_into_functions
  have hCheckedFunctionsToPowerset :
      Γ ≤ injects_into
        (check (pSet.functions PSet.omega (PSet.ofNat 2)) : bSet.{u} β) 𝒫ω̌ := by
    apply injects_into_iff_injection_into.mpr
    rcases pSet.functions_2_injects_into_powerset (PSet.omega : pSet.{u}) with ⟨f, hf⟩
    unfold injection_into
    exact le_iSup_of_le (check f : bSet.{u} β) (check_is_injective_function hf)
  have hFunctionsToPowerset :
      Γ ≤ injects_into (functions (omega : bSet.{u} β) (2 : bSet.{u} β)) 𝒫ω̌ :=
    (le_inf hFunctions hCheckedFunctionsToPowerset).trans
      (B_ext_injects_into_left
        (y := 𝒫ω̌)
        (check (pSet.functions PSet.omega (PSet.ofNat 2)) : bSet.{u} β)
        (functions (omega : bSet.{u} β) (2 : bSet.{u} β)))
  exact injects_into_trans hPowersetToFunctions hFunctionsToPowerset

lemma CH₂_true_of_continuum_le_continuum_check {Γ : β}
    (hContinuum : Γ ≤ injects_into (bv_powerset (omega : bSet.{u} β)) 𝒫ω̌) :
    Γ ≤ CH₂ := by
  dsimp [CH₂]
  rw [le_compl_iff_disjoint_right, disjoint_iff]
  apply le_antisymm ?_ bot_le
  apply lattice.bv_cases_right
  intro x
  let Δ : β := Γ ⊓
    (Ord x ⊓ (larger_than (omega : bSet.{u} β) x)ᶜ ⊓
      (larger_than x (bv_powerset (omega : bSet.{u} β)))ᶜ)
  change Δ ≤ ⊥
  have hΔΓ : Δ ≤ Γ := by
    dsimp [Δ]
    exact inf_le_left
  have hOrd : Δ ≤ Ord x := by
    dsimp [Δ]
    exact inf_le_right.trans (inf_le_left.trans inf_le_left)
  have hNotOmega : Δ ≤ (larger_than (omega : bSet.{u} β) x)ᶜ := by
    dsimp [Δ]
    exact inf_le_right.trans (inf_le_left.trans inf_le_right)
  have hNotLarge : Δ ≤ (larger_than x (bv_powerset (omega : bSet.{u} β)))ᶜ := by
    dsimp [Δ]
    exact inf_le_right.trans inf_le_right
  have hLarge : Δ ≤ larger_than x (bv_powerset (omega : bSet.{u} β)) :=
    bv_powerset_omega_larger_than_of_omega_not_larger (hΔΓ.trans hContinuum) hOrd hNotOmega
  exact (le_inf hLarge hNotLarge).trans (by rw [inf_compl_eq_bot])

lemma CH₂_true_of_check_functions_eq {Γ : β}
    (hFunctions : Γ ≤
      (check (pSet.functions PSet.omega (PSet.ofNat 2)) : bSet.{u} β) =ᴮ
        functions (omega : bSet.{u} β) (2 : bSet.{u} β)) :
    Γ ≤ CH₂ :=
  CH₂_true_of_continuum_le_continuum_check
    (continuum_le_continuum_check_of_check_functions_eq hFunctions)

private lemma AE_of_check_func_check'
    (x y : pSet.{u}) {f : bSet.{u} β} {Γ : β}
    (hFunc : Γ ≤ is_func' (check x : bSet.{u} β) (check y : bSet.{u} β) f)
    (hNonzero : ⊥ < Γ) (i : x.Type) :
    ∃ (j : y.Type) (Γ' : β), ⊥ < Γ' ∧ Γ' ≤ Γ ∧
      Γ' ≤ is_func' (check x : bSet.{u} β) (check y : bSet.{u} β) f ∧
      Γ' ≤ pair (check (x.Func i) : bSet.{u} β) (check (y.Func j) : bSet.{u} β) ∈ᴮ f ∧
      Γ' ∈ collapse_principal_opens X₁ Yω := by
  let xi : bSet.{u} β := check (x.Func i)
  have hTotal : Γ ≤ is_total (check x : bSet.{u} β) (check y : bSet.{u} β) f :=
    is_total_of_is_func' hFunc
  have hXiMem : Γ ≤ xi ∈ᴮ (check x : bSet.{u} β) := by
    dsimp [xi]
    exact check_mem pSet.mem_mk'
  have hImp : Γ ≤ lattice.imp (xi ∈ᴮ (check x : bSet.{u} β))
      (⨆ w : bSet.{u} β, w ∈ᴮ (check y : bSet.{u} β) ⊓ pair xi w ∈ᴮ f) :=
    hTotal.trans (iInf_le _ xi)
  have hCasesW : Γ ≤ ⨆ w : bSet.{u} β, w ∈ᴮ (check y : bSet.{u} β) ⊓ pair xi w ∈ᴮ f :=
    lattice.bv_context_apply hImp hXiMem
  have hCasesJ : Γ ≤ ⨆ j : (check y : bSet.{u} β).type,
      pair xi ((check y : bSet.{u} β).func j) ∈ᴮ f := by
    apply (le_inf le_rfl hCasesW).trans
    apply lattice.bv_cases_right
    intro w
    let Δ : β := Γ ⊓ (w ∈ᴮ (check y : bSet.{u} β) ⊓ pair xi w ∈ᴮ f)
    have hwMem : Δ ≤ w ∈ᴮ (check y : bSet.{u} β) := by
      dsimp [Δ]
      exact inf_le_right.trans inf_le_left
    have hPairW : Δ ≤ pair xi w ∈ᴮ f := by
      dsimp [Δ]
      exact inf_le_right.trans inf_le_right
    rw [mem_unfold] at hwMem
    apply (le_inf le_rfl hwMem).trans
    apply lattice.bv_cases_right
    intro j
    let Θ : β := Δ ⊓ ((check y : bSet.{u} β).bval j ⊓ w =ᴮ (check y : bSet.{u} β).func j)
    change Θ ≤ ⨆ j : (check y : bSet.{u} β).type, pair xi ((check y : bSet.{u} β).func j) ∈ᴮ f
    apply le_iSup_of_le j
    have hwEq : Θ ≤ w =ᴮ (check y : bSet.{u} β).func j := by
      dsimp [Θ]
      exact inf_le_right.trans inf_le_right
    have hPairWΘ : Θ ≤ pair xi w ∈ᴮ f := inf_le_left.trans hPairW
    have hPairEq : Θ ≤ pair xi w =ᴮ pair xi ((check y : bSet.{u} β).func j) :=
      subst_congr_pair_right hwEq
    exact subst_congr_mem_left' hPairEq hPairWΘ
  let F : (check y : bSet.{u} β).type → β :=
    fun j => is_func' (check x : bSet.{u} β) (check y : bSet.{u} β) f ⊓
      pair xi ((check y : bSet.{u} β).func j) ∈ᴮ f
  have hLeF : Γ ≤ ⨆ j : (check y : bSet.{u} β).type, F j := by
    calc
      Γ ≤ Γ ⊓ (⨆ j : (check y : bSet.{u} β).type,
          pair xi ((check y : bSet.{u} β).func j) ∈ᴮ f) := le_inf le_rfl hCasesJ
      _ = ⨆ j : (check y : bSet.{u} β).type,
          Γ ⊓ pair xi ((check y : bSet.{u} β).func j) ∈ᴮ f := by
            rw [inf_iSup_eq]
      _ ≤ ⨆ j : (check y : bSet.{u} β).type, F j := by
        apply iSup_mono
        intro j
        exact le_inf (inf_le_left.trans hFunc) inf_le_right
  rcases exists_dense_below_iSup (α := β) (ι := (check y : bSet.{u} β).type)
      (D := collapse_principal_opens X₁ Yω) collapse_principal_opens_dense
      hNonzero F hLeF with ⟨j, Γ', hΓ'Nonzero, hΓ'Le, hΓ'D⟩
  refine ⟨check_cast (𝔹 := β) j, Γ', hΓ'Nonzero, ?_, ?_, ?_, hΓ'D⟩
  · exact hΓ'Le.trans inf_le_right
  · exact (hΓ'Le.trans inf_le_left).trans inf_le_left
  · have hPair : Γ' ≤ pair xi ((check y : bSet.{u} β).func j) ∈ᴮ f :=
      (hΓ'Le.trans inf_le_left).trans inf_le_right
    dsimp [xi]
    simpa [check_cast] using hPair

private abbrev omegaIdx (n : ℕ) : PSet.omega.Type :=
  ULift.up n

private structure ReflectState (f : bSet.{u} β) (Γ : β) (n : ℕ) where
  context : β
  Γn : β
  j : (PSet.ofNat 2 : pSet.{u}).Type
  nonzero : ⊥ < Γn
  le_context : Γn ≤ context
  le_base : Γn ≤ Γ
  is_func : Γn ≤ is_func' (check PSet.omega : bSet.{u} β) (check (PSet.ofNat 2) : bSet.{u} β) f
  mem_dense : Γn ∈ collapse_principal_opens X₁ Yω
  pair_mem : Γn ≤ pair (check (PSet.omega.Func (omegaIdx n)) : bSet.{u} β)
    (check ((PSet.ofNat 2 : pSet.{u}).Func j) : bSet.{u} β) ∈ᴮ f

private noncomputable def reflectStep (f : bSet.{u} β) {Γ Γ₀ : β} (n : ℕ)
    (hLe : Γ₀ ≤ Γ)
    (hFunc : Γ₀ ≤ is_func' (check PSet.omega : bSet.{u} β) (check (PSet.ofNat 2) : bSet.{u} β) f)
    (hNonzero : ⊥ < Γ₀) : ReflectState f Γ n := by
  let ex₁ := AE_of_check_func_check' (PSet.omega : pSet.{u}) (PSet.ofNat 2 : pSet.{u})
    hFunc hNonzero (omegaIdx n)
  let j : (PSet.ofNat 2 : pSet.{u}).Type := Classical.choose ex₁
  let ex₂ := Classical.choose_spec ex₁
  let Γ' : β := Classical.choose ex₂
  have hSpec : ⊥ < Γ' ∧ Γ' ≤ Γ₀ ∧
      Γ' ≤ is_func' (check PSet.omega : bSet.{u} β) (check (PSet.ofNat 2) : bSet.{u} β) f ∧
      Γ' ≤ pair (check (PSet.omega.Func (omegaIdx n)) : bSet.{u} β)
          (check ((PSet.ofNat 2 : pSet.{u}).Func j) : bSet.{u} β) ∈ᴮ f ∧
      Γ' ∈ collapse_principal_opens X₁ Yω :=
    Classical.choose_spec ex₂
  exact {
    context := Γ₀
    Γn := Γ'
    j := j
    nonzero := hSpec.1
    le_context := hSpec.2.1
    le_base := hSpec.2.1.trans hLe
    is_func := hSpec.2.2.1
    mem_dense := hSpec.2.2.2.2
    pair_mem := hSpec.2.2.2.1
  }

private noncomputable def reflectSequence (f : bSet.{u} β) {Γ : β}
    (hFunc : Γ ≤ is_func' (check PSet.omega : bSet.{u} β) (check (PSet.ofNat 2) : bSet.{u} β) f)
    (hNonzero : ⊥ < Γ) : (n : ℕ) → ReflectState f Γ n
  | 0 => reflectStep f 0 le_rfl hFunc hNonzero
  | n + 1 => by
      let prev := reflectSequence f hFunc hNonzero n
      exact reflectStep f (n + 1) prev.le_base prev.is_func prev.nonzero

private noncomputable def reflectCondition (f : bSet.{u} β) {Γ : β}
    (hFunc : Γ ≤ is_func' (check PSet.omega : bSet.{u} β) (check (PSet.ofNat 2) : bSet.{u} β) f)
    (hNonzero : ⊥ < Γ) (n : ℕ) : β :=
  (reflectSequence f hFunc hNonzero n).Γn

private noncomputable def reflectValueIndex (f : bSet.{u} β) {Γ : β}
    (hFunc : Γ ≤ is_func' (check PSet.omega : bSet.{u} β) (check (PSet.ofNat 2) : bSet.{u} β) f)
    (hNonzero : ⊥ < Γ) (n : ℕ) : (PSet.ofNat 2 : pSet.{u}).Type :=
  (reflectSequence f hFunc hNonzero n).j

private lemma reflectCondition_nonzero (f : bSet.{u} β) {Γ : β}
    (hFunc : Γ ≤ is_func' (check PSet.omega : bSet.{u} β) (check (PSet.ofNat 2) : bSet.{u} β) f)
    (hNonzero : ⊥ < Γ) (n : ℕ) :
    ⊥ < reflectCondition f hFunc hNonzero n :=
  (reflectSequence f hFunc hNonzero n).nonzero

private lemma reflectCondition_le_base (f : bSet.{u} β) {Γ : β}
    (hFunc : Γ ≤ is_func' (check PSet.omega : bSet.{u} β) (check (PSet.ofNat 2) : bSet.{u} β) f)
    (hNonzero : ⊥ < Γ) (n : ℕ) :
    reflectCondition f hFunc hNonzero n ≤ Γ :=
  (reflectSequence f hFunc hNonzero n).le_base

private lemma reflectCondition_is_func (f : bSet.{u} β) {Γ : β}
    (hFunc : Γ ≤ is_func' (check PSet.omega : bSet.{u} β) (check (PSet.ofNat 2) : bSet.{u} β) f)
    (hNonzero : ⊥ < Γ) (n : ℕ) :
    reflectCondition f hFunc hNonzero n ≤
      is_func' (check PSet.omega : bSet.{u} β) (check (PSet.ofNat 2) : bSet.{u} β) f :=
  (reflectSequence f hFunc hNonzero n).is_func

private lemma reflectCondition_mem_dense (f : bSet.{u} β) {Γ : β}
    (hFunc : Γ ≤ is_func' (check PSet.omega : bSet.{u} β) (check (PSet.ofNat 2) : bSet.{u} β) f)
    (hNonzero : ⊥ < Γ) (n : ℕ) :
    reflectCondition f hFunc hNonzero n ∈ collapse_principal_opens X₁ Yω :=
  (reflectSequence f hFunc hNonzero n).mem_dense

private lemma reflectCondition_pair (f : bSet.{u} β) {Γ : β}
    (hFunc : Γ ≤ is_func' (check PSet.omega : bSet.{u} β) (check (PSet.ofNat 2) : bSet.{u} β) f)
    (hNonzero : ⊥ < Γ) (n : ℕ) :
    reflectCondition f hFunc hNonzero n ≤
      pair (check (PSet.omega.Func (omegaIdx n)) : bSet.{u} β)
        (check ((PSet.ofNat 2 : pSet.{u}).Func
          (reflectValueIndex f hFunc hNonzero n)) : bSet.{u} β) ∈ᴮ f :=
  (reflectSequence f hFunc hNonzero n).pair_mem

private lemma reflectCondition_succ_le (f : bSet.{u} β) {Γ : β}
    (hFunc : Γ ≤ is_func' (check PSet.omega : bSet.{u} β) (check (PSet.ofNat 2) : bSet.{u} β) f)
    (hNonzero : ⊥ < Γ) (n : ℕ) :
    reflectCondition f hFunc hNonzero (n + 1) ≤
      reflectCondition f hFunc hNonzero n := by
  dsimp [reflectCondition, reflectSequence]
  exact (reflectStep f (n + 1)
    (reflectSequence f hFunc hNonzero n).le_base
    (reflectSequence f hFunc hNonzero n).is_func
    (reflectSequence f hFunc hNonzero n).nonzero).le_context

private noncomputable def reflectLimit (f : bSet.{u} β) {Γ : β}
    (hFunc : Γ ≤ is_func' (check PSet.omega : bSet.{u} β) (check (PSet.ofNat 2) : bSet.{u} β) f)
    (hNonzero : ⊥ < Γ) : β :=
  ⨅ n : ℕ, reflectCondition f hFunc hNonzero n

private lemma reflectLimit_le_condition (f : bSet.{u} β) {Γ : β}
    (hFunc : Γ ≤ is_func' (check PSet.omega : bSet.{u} β) (check (PSet.ofNat 2) : bSet.{u} β) f)
    (hNonzero : ⊥ < Γ) (n : ℕ) :
    reflectLimit f hFunc hNonzero ≤ reflectCondition f hFunc hNonzero n := by
  dsimp [reflectLimit]
  exact iInf_le _ n

private lemma reflectLimit_le_base (f : bSet.{u} β) {Γ : β}
    (hFunc : Γ ≤ is_func' (check PSet.omega : bSet.{u} β) (check (PSet.ofNat 2) : bSet.{u} β) f)
    (hNonzero : ⊥ < Γ) :
    reflectLimit f hFunc hNonzero ≤ Γ :=
  (reflectLimit_le_condition f hFunc hNonzero 0).trans
    (reflectCondition_le_base f hFunc hNonzero 0)

private lemma reflectLimit_nonzero (f : bSet.{u} β) {Γ : β}
    (hFunc : Γ ≤ is_func' (check PSet.omega : bSet.{u} β) (check (PSet.ofNat 2) : bSet.{u} β) f)
    (hNonzero : ⊥ < Γ) :
    ⊥ < reflectLimit f hFunc hNonzero := by
  dsimp [reflectLimit]
  exact nonzero_infi_of_mem_dense_omega_closed_subset
    collapse_principal_opens_dense_omega_closed
    (reflectCondition_succ_le f hFunc hNonzero)
    (reflectCondition_mem_dense f hFunc hNonzero)

private lemma reflectLimit_pair (f : bSet.{u} β) {Γ : β}
    (hFunc : Γ ≤ is_func' (check PSet.omega : bSet.{u} β) (check (PSet.ofNat 2) : bSet.{u} β) f)
    (hNonzero : ⊥ < Γ) (n : ℕ) :
    reflectLimit f hFunc hNonzero ≤
      pair (check (PSet.omega.Func (omegaIdx n)) : bSet.{u} β)
        (check ((PSet.ofNat 2 : pSet.{u}).Func
          (reflectValueIndex f hFunc hNonzero n)) : bSet.{u} β) ∈ᴮ f :=
  (reflectLimit_le_condition f hFunc hNonzero n).trans
    (reflectCondition_pair f hFunc hNonzero n)

private noncomputable def reflectFunction (f : bSet.{u} β) {Γ : β}
    (hFunc : Γ ≤ is_func' (check PSet.omega : bSet.{u} β) (check (PSet.ofNat 2) : bSet.{u} β) f)
    (hNonzero : ⊥ < Γ) : pSet.{u} :=
  pSet.function.mk (fun i : PSet.omega.Type =>
    (PSet.ofNat 2 : pSet.{u}).Func (reflectValueIndex f hFunc hNonzero i.down))

private lemma reflectFunction_is_func (f : bSet.{u} β) {Γ : β}
    (hFunc : Γ ≤ is_func' (check PSet.omega : bSet.{u} β) (check (PSet.ofNat 2) : bSet.{u} β) f)
    (hNonzero : ⊥ < Γ) :
    pSet.is_func PSet.omega (PSet.ofNat 2 : pSet.{u})
      (reflectFunction f hFunc hNonzero) := by
  unfold reflectFunction
  apply pSet.function.mk_is_func
  · intro i
    exact pSet.mem_mk' (x := (PSet.ofNat 2 : pSet.{u}))
      (i := reflectValueIndex f hFunc hNonzero i.down)
  · intro i j hEq
    have hij : i = j := pSet.omega_inj hEq
    subst hij
    exact PSet.Equiv.rfl

private lemma reflectFunction_pair (f : bSet.{u} β) {Γ : β}
    (hFunc : Γ ≤ is_func' (check PSet.omega : bSet.{u} β) (check (PSet.ofNat 2) : bSet.{u} β) f)
    (hNonzero : ⊥ < Γ) (n : ℕ) :
    reflectLimit f hFunc hNonzero ≤
      pair (check (PSet.omega.Func (omegaIdx n)) : bSet.{u} β)
        (check ((PSet.ofNat 2 : pSet.{u}).Func
          (reflectValueIndex f hFunc hNonzero n)) : bSet.{u} β) ∈ᴮ
        (check (reflectFunction f hFunc hNonzero) : bSet.{u} β) := by
  have hMem : reflectLimit f hFunc hNonzero ≤
      (check (pSet.pair (PSet.omega.Func (omegaIdx n))
        ((PSet.ofNat 2 : pSet.{u}).Func
          (reflectValueIndex f hFunc hNonzero n))) : bSet.{u} β) ∈ᴮ
        (check (reflectFunction f hFunc hNonzero) : bSet.{u} β) :=
    check_mem (pSet.function.mk_mem
      (ψ := fun i : PSet.omega.Type =>
        (PSet.ofNat 2 : pSet.{u}).Func (reflectValueIndex f hFunc hNonzero i.down))
      (i := omegaIdx n))
  exact subst_congr_mem_left' check_pair hMem

private lemma reflectFunction_check_subset_original (f : bSet.{u} β) {Γ : β}
    (hFunc : Γ ≤ is_func' (check PSet.omega : bSet.{u} β) (check (PSet.ofNat 2) : bSet.{u} β) f)
    (hNonzero : ⊥ < Γ) :
    reflectLimit f hFunc hNonzero ≤
      (check (reflectFunction f hFunc hNonzero) : bSet.{u} β) ⊆ᴮ f := by
  apply subset_intro
  intro i
  let i' : (reflectFunction f hFunc hNonzero).Type :=
    cast (check_type (𝔹 := β) (x := reflectFunction f hFunc hNonzero)) i
  change reflectLimit f hFunc hNonzero ⊓
      (check (reflectFunction f hFunc hNonzero) : bSet.{u} β).bval i ≤
    (check (reflectFunction f hFunc hNonzero) : bSet.{u} β).func i ∈ᴮ f
  rw [check_bval, inf_top_eq, check_func]
  change reflectLimit f hFunc hNonzero ≤
    (check ((reflectFunction f hFunc hNonzero).Func i') : bSet.{u} β) ∈ᴮ f
  cases i' with
  | up n =>
      change reflectLimit f hFunc hNonzero ≤
        (check (pSet.pair (PSet.omega.Func (omegaIdx n))
          ((PSet.ofNat 2 : pSet.{u}).Func
            (reflectValueIndex f hFunc hNonzero n))) : bSet.{u} β) ∈ᴮ f
      exact subst_congr_mem_left' (bv_symm check_pair)
        (reflectLimit_pair f hFunc hNonzero n)

private lemma reflectFunction_pair_of_original_pair {f : bSet.{u} β} {Γ Δ : β}
    (hFunc : Γ ≤ is_func' (check PSet.omega : bSet.{u} β) (check (PSet.ofNat 2) : bSet.{u} β) f)
    (hNonzero : ⊥ < Γ) {k : PSet.omega.Type} {j : (PSet.ofNat 2 : pSet.{u}).Type}
    (hΔLimit : Δ ≤ reflectLimit f hFunc hNonzero)
    (hPair : Δ ≤ pair (check (PSet.omega.Func k) : bSet.{u} β)
      (check ((PSet.ofNat 2 : pSet.{u}).Func j) : bSet.{u} β) ∈ᴮ f) :
    Δ ≤ pair (check (PSet.omega.Func k) : bSet.{u} β)
      (check ((PSet.ofNat 2 : pSet.{u}).Func j) : bSet.{u} β) ∈ᴮ
        (check (reflectFunction f hFunc hNonzero) : bSet.{u} β) := by
  cases k with
  | up n =>
      have hChosenF : Δ ≤
          pair (check (PSet.omega.Func (omegaIdx n)) : bSet.{u} β)
            (check ((PSet.ofNat 2 : pSet.{u}).Func
              (reflectValueIndex f hFunc hNonzero n)) : bSet.{u} β) ∈ᴮ f :=
        hΔLimit.trans (reflectLimit_pair f hFunc hNonzero n)
      have hChosenCheck : Δ ≤
          pair (check (PSet.omega.Func (omegaIdx n)) : bSet.{u} β)
            (check ((PSet.ofNat 2 : pSet.{u}).Func
              (reflectValueIndex f hFunc hNonzero n)) : bSet.{u} β) ∈ᴮ
            (check (reflectFunction f hFunc hNonzero) : bSet.{u} β) :=
        hΔLimit.trans (reflectFunction_pair f hFunc hNonzero n)
      have hFuncΔ : Δ ≤ is_func' (check PSet.omega : bSet.{u} β)
          (check (PSet.ofNat 2) : bSet.{u} β) f :=
        hΔLimit.trans (reflectLimit_le_base f hFunc hNonzero) |>.trans hFunc
      have hOutEq : Δ ≤
          (check ((PSet.ofNat 2 : pSet.{u}).Func j) : bSet.{u} β) =ᴮ
            check ((PSet.ofNat 2 : pSet.{u}).Func
              (reflectValueIndex f hFunc hNonzero n)) :=
        eq_of_is_func'_of_eq hFuncΔ bv_refl hPair hChosenF
      have hPairEq : Δ ≤
          pair (check (PSet.omega.Func (omegaIdx n)) : bSet.{u} β)
            (check ((PSet.ofNat 2 : pSet.{u}).Func
              (reflectValueIndex f hFunc hNonzero n)) : bSet.{u} β) =ᴮ
          pair (check (PSet.omega.Func (omegaIdx n)) : bSet.{u} β)
            (check ((PSet.ofNat 2 : pSet.{u}).Func j) : bSet.{u} β) :=
        pair_congr bv_refl (bv_symm hOutEq)
      exact subst_congr_mem_left' hPairEq hChosenCheck

private lemma original_subset_reflectFunction_check {f : bSet.{u} β} {Γ : β}
    (hFunction : Γ ≤ is_function (check PSet.omega : bSet.{u} β)
      (check (PSet.ofNat 2) : bSet.{u} β) f)
    (hNonzero : ⊥ < Γ) :
    let hFunc : Γ ≤ is_func' (check PSet.omega : bSet.{u} β)
        (check (PSet.ofNat 2) : bSet.{u} β) f :=
      is_func'_of_is_function hFunction
    reflectLimit f hFunc hNonzero ≤ f ⊆ᴮ
      (check (reflectFunction f hFunc hNonzero) : bSet.{u} β) := by
  intro hFunc
  apply subset_intro
  intro i
  let Δ : β := reflectLimit f hFunc hNonzero ⊓ f.bval i
  change Δ ≤ f.func i ∈ᴮ
    (check (reflectFunction f hFunc hNonzero) : bSet.{u} β)
  have hΔLimit : Δ ≤ reflectLimit f hFunc hNonzero := by
    dsimp [Δ]
    exact inf_le_left
  have hMemF : Δ ≤ f.func i ∈ᴮ f := by
    dsimp [Δ]
    exact mem.mk'' inf_le_right
  have hFunctionΔ : Δ ≤ is_function (check PSet.omega : bSet.{u} β)
      (check (PSet.ofNat 2) : bSet.{u} β) f :=
    hΔLimit.trans (reflectLimit_le_base f hFunc hNonzero) |>.trans hFunction
  have hProd : Δ ≤ f.func i ∈ᴮ prod (check PSet.omega : bSet.{u} β)
      (check (PSet.ofNat 2) : bSet.{u} β) :=
    mem_of_mem_subset' (subset_prod_of_is_function hFunctionΔ) hMemF
  rw [mem_unfold] at hProd
  apply (le_inf le_rfl hProd).trans
  apply lattice.bv_cases_right
  intro p
  let Θ : β := Δ ⊓ (((prod (check PSet.omega : bSet.{u} β)
    (check (PSet.ofNat 2) : bSet.{u} β)).bval p) ⊓
      f.func i =ᴮ (prod (check PSet.omega : bSet.{u} β)
        (check (PSet.ofNat 2) : bSet.{u} β)).func p)
  change Θ ≤ f.func i ∈ᴮ
    (check (reflectFunction f hFunc hNonzero) : bSet.{u} β)
  have hEq : Θ ≤ f.func i =ᴮ (prod (check PSet.omega : bSet.{u} β)
      (check (PSet.ofNat 2) : bSet.{u} β)).func p := by
    dsimp [Θ]
    exact inf_le_right.trans inf_le_right
  have hMemFΘ : Θ ≤ f.func i ∈ᴮ f := by
    dsimp [Θ]
    exact inf_le_left.trans hMemF
  have hPairMemF : Θ ≤
      pair (check (PSet.omega.Func (check_cast (𝔹 := β) p.1)) : bSet.{u} β)
        (check ((PSet.ofNat 2 : pSet.{u}).Func (check_cast (𝔹 := β) p.2)) :
          bSet.{u} β) ∈ᴮ f := by
    have hProdMem : Θ ≤ (prod (check PSet.omega : bSet.{u} β)
        (check (PSet.ofNat 2) : bSet.{u} β)).func p ∈ᴮ f :=
      subst_congr_mem_left' hEq hMemFΘ
    simpa [bSet.prod, check_cast, check_func] using hProdMem
  have hPairMemCheck : Θ ≤
      pair (check (PSet.omega.Func (check_cast (𝔹 := β) p.1)) : bSet.{u} β)
        (check ((PSet.ofNat 2 : pSet.{u}).Func (check_cast (𝔹 := β) p.2)) :
          bSet.{u} β) ∈ᴮ
        (check (reflectFunction f hFunc hNonzero) : bSet.{u} β) :=
    reflectFunction_pair_of_original_pair hFunc hNonzero
      (inf_le_left.trans hΔLimit) hPairMemF
  have hProdMemCheck : Θ ≤ (prod (check PSet.omega : bSet.{u} β)
      (check (PSet.ofNat 2) : bSet.{u} β)).func p ∈ᴮ
      (check (reflectFunction f hFunc hNonzero) : bSet.{u} β) := by
    simpa [bSet.prod, check_cast, check_func] using hPairMemCheck
  exact subst_congr_mem_left' (bv_symm hEq) hProdMemCheck

private lemma reflectFunction_eq_original_of_is_function {f : bSet.{u} β} {Γ : β}
    (hFunction : Γ ≤ is_function (check PSet.omega : bSet.{u} β)
      (check (PSet.ofNat 2) : bSet.{u} β) f)
    (hNonzero : ⊥ < Γ) :
    let hFunc : Γ ≤ is_func' (check PSet.omega : bSet.{u} β)
        (check (PSet.ofNat 2) : bSet.{u} β) f :=
      is_func'_of_is_function hFunction
    reflectLimit f hFunc hNonzero ≤
      (check (reflectFunction f hFunc hNonzero) : bSet.{u} β) =ᴮ f := by
  intro hFunc
  exact subset_ext
    (reflectFunction_check_subset_original f hFunc hNonzero)
    (original_subset_reflectFunction_check hFunction hNonzero)

private lemma function_reflect_of_omega_closed_two {f : bSet.{u} β} {Γ : β}
    (hNonzero : ⊥ < Γ)
    (hFunction : Γ ≤ is_function (check PSet.omega : bSet.{u} β)
      (check (PSet.ofNat 2) : bSet.{u} β) f) :
    ∃ f' Γ', ⊥ < Γ' ∧ Γ' ≤ Γ ∧
      Γ' ≤ (check f' : bSet.{u} β) =ᴮ f ∧
      pSet.is_func PSet.omega (PSet.ofNat 2 : pSet.{u}) f' := by
  let hFunc : Γ ≤ is_func' (check PSet.omega : bSet.{u} β)
      (check (PSet.ofNat 2) : bSet.{u} β) f :=
    is_func'_of_is_function hFunction
  refine ⟨reflectFunction f hFunc hNonzero, reflectLimit f hFunc hNonzero,
    reflectLimit_nonzero f hFunc hNonzero, reflectLimit_le_base f hFunc hNonzero, ?_, ?_⟩
  · exact reflectFunction_eq_original_of_is_function hFunction hNonzero
  · exact reflectFunction_is_func f hFunc hNonzero

private lemma functions_subset_check_functions {Γ : β} :
    Γ ≤ functions (check PSet.omega : bSet.{u} β) (check (PSet.ofNat 2) : bSet.{u} β) ⊆ᴮ
      (check (pSet.functions PSet.omega (PSet.ofNat 2)) : bSet.{u} β) := by
  apply subset_intro
  intro i
  let f : bSet.{u} β :=
    (functions (check PSet.omega : bSet.{u} β) (check (PSet.ofNat 2) : bSet.{u} β)).func i
  let Δ : β := Γ ⊓
    (functions (check PSet.omega : bSet.{u} β) (check (PSet.ofNat 2) : bSet.{u} β)).bval i
  change Δ ≤ f ∈ᴮ (check (pSet.functions PSet.omega (PSet.ofNat 2)) : bSet.{u} β)
  let M : β := f ∈ᴮ (check (pSet.functions PSet.omega (PSet.ofNat 2)) : bSet.{u} β)
  by_contra hNot
  have hNonzero : ⊥ < Δ ⊓ Mᶜ := by
    rw [bot_lt_iff_ne_bot]
    intro hbot
    apply hNot
    have hLe : Δ ≤ M := by
      rw [← compl_compl M, le_compl_iff_disjoint_right, disjoint_iff]
      exact hbot
    exact hLe
  have hFunction : Δ ⊓ Mᶜ ≤ is_function (check PSet.omega : bSet.{u} β)
      (check (PSet.ofNat 2) : bSet.{u} β) f := by
    dsimp [Δ, f]
    simpa [functions_bval] using inf_le_left.trans inf_le_right
  rcases function_reflect_of_omega_closed_two hNonzero hFunction with
    ⟨f', Γ', hΓ'Nonzero, hΓ'Le, hEq, hPFunc⟩
  have hCheckedMem : Γ' ≤
      (check f' : bSet.{u} β) ∈ᴮ
        (check (pSet.functions PSet.omega (PSet.ofNat 2)) : bSet.{u} β) :=
    check_mem ((pSet.mem_functions_iff).mpr hPFunc)
  have hMem : Γ' ≤ M := by
    dsimp [M]
    exact subst_congr_mem_left' hEq hCheckedMem
  have hNotMem : Γ' ≤ Mᶜ := hΓ'Le.trans inf_le_right
  have hBot : Γ' ≤ ⊥ := (le_inf hMem hNotMem).trans (by rw [inf_compl_eq_bot])
  exact (not_le_of_gt hΓ'Nonzero) hBot

lemma check_functions_eq_functions {Γ : β} :
    Γ ≤ (check (pSet.functions PSet.omega (PSet.ofNat 2)) : bSet.{u} β) =ᴮ
      functions (omega : bSet.{u} β) (2 : bSet.{u} β) :=
  subset_ext
    check_functions_subset_functions
    functions_subset_check_functions

lemma continuum_le_continuum_check {Γ : β} :
    Γ ≤ injects_into (bv_powerset (omega : bSet.{u} β)) 𝒫ω̌ :=
  continuum_le_continuum_check_of_check_functions_eq check_functions_eq_functions

theorem CH₂_true {Γ : β} :
    Γ ≤ CH₂ :=
  CH₂_true_of_check_functions_eq check_functions_eq_functions

theorem CH_true {Γ : β} :
    Γ ≤ CH :=
  (CH_iff_CH₂).2 CH₂_true

end collapse_algebra

end Flypitch
