import Flypitch.BVMExtras
import Flypitch.CantorSpace
import Flypitch.RegularOpenAlgebra
import Flypitch.AlephOne

open Set TopologicalSpace Cardinal

universe u

namespace Flypitch

set_option linter.missingDocs false
set_option linter.style.longLine false

/-!
Port of upstream `src/forcing.lean`.

Cohen forcing: in the Boolean-valued model built from the regular open algebra of
the Cantor space `2^(ℵ₂ × ℕ)`, the continuum hypothesis fails.
-/

open bSet

/-!
## CCC for complete Boolean algebras

We define the countable chain condition for a complete Boolean algebra:
every family of pairwise-disjoint nonzero elements is countable.
-/

section BA_CCC

variable (𝔹 : Type u) [CompleteBooleanAlgebra 𝔹]

/-- A complete Boolean algebra satisfies the countable chain condition if every
family of pairwise-disjoint nonzero elements is countable. -/
def BA_CCC : Prop :=
  ∀ s : Set 𝔹, (∀ a ∈ s, a ≠ ⊥) → (∀ a ∈ s, ∀ b ∈ s, a ≠ b → a ⊓ b = ⊥) → s.Countable

end BA_CCC

/-!
## CCC for regular open algebras

If the underlying topological space has CCC, then its regular open algebra
satisfies `BA_CCC`.
-/

section CCC_regular_opens

variable (α : Type u) [TopologicalSpace α]

theorem CCC_regular_opens (hCCC : countable_chain_condition α) :
    BA_CCC (regular_opens α) := by
  intro s hNonzero hDisj
  let s' : Set (Set α) := Subtype.val '' s
  have hopen' : ∀ ⦃o : Set α⦄, o ∈ s' → IsOpen o := by
    intro o ho
    rcases ho with ⟨U, _hU, rfl⟩
    exact isOpen_of_is_regular U.2
  have hdisj' : s'.PairwiseDisjoint id := by
    intro a ha b hb hne
    rcases ha with ⟨Ua, hUa, rfl⟩
    rcases hb with ⟨Ub, hUb, rfl⟩
    have hUab : Ua ≠ Ub := by
      intro hEq; exact hne (by rw [hEq])
    have hInfBot := hDisj Ua hUa Ub hUb hUab
    have hInterEmpty : (Ua : Set α) ∩ (Ub : Set α) = ∅ := by
      calc
        (Ua : Set α) ∩ (Ub : Set α) = ((Ua ⊓ Ub : regular_opens α) : Set α) := by
          simpa using (congrArg Subtype.val (regularOpen_inf_unfold (S := Ua) (T := Ub))).symm
        _ = ((⊥ : regular_opens α) : Set α) := by simpa [hInfBot]
        _ = ∅ := by simpa using regularOpen_coe_bot (α := α)
    exact (Set.disjoint_iff_inter_eq_empty (s := (Ua : Set α)) (t := (Ub : Set α))).mpr hInterEmpty
  have hcount' : s'.Countable := hCCC s' hopen' hdisj'
  have emb : s ↪ s' := by
    refine ⟨?_, ?_⟩
    · intro U
      exact ⟨(U.val : Set α), U.val, U.2, rfl⟩
    · intro U V h
      have h_eq_val : (U.val : Set α) = (V.val : Set α) := by
        simpa using congrArg (fun (x : ↥s') => (x : Set α)) h
      have h_eq : U.val = V.val := Subtype.ext h_eq_val
      exact Subtype.ext h_eq
  exact Set.countable_of_embedding emb hcount'

end CCC_regular_opens

/-!
## Cohen algebra
-/

/-- The Cohen Boolean algebra: regular opens of the Cantor space `2^(ℵ₂ × ℕ)`. -/
@[reducible] def 𝔹_cohen : Type u := regular_opens (Set (pSet.aleph_two.Type × ℕ))

instance : TopologicalSpace (Set (pSet.aleph_two.Type × ℕ)) := Pi.topologicalSpace

instance : Nonempty (Set (pSet.aleph_two.Type × ℕ)) := ⟨∅⟩

noncomputable instance : CompleteBooleanAlgebra 𝔹_cohen :=
  inferInstanceAs (CompleteBooleanAlgebra (regular_opens _))

local notation "𝔹" => 𝔹_cohen

lemma le_iff_subset' {x y : 𝔹} : x ≤ y ↔ x.1 ⊆ y.1 := ⟨fun h => h, fun h => h⟩

lemma bot_eq_empty : (⊥ : 𝔹) = ⟨∅, is_regular_empty⟩ := rfl

/-- The Cohen algebra has CCC. -/
theorem 𝔹_CCC : BA_CCC (𝔹 : Type u) := by
  apply CCC_regular_opens
  exact cantor_space.countable_chain_condition_set

/-- The principal regular open associated to a point `(ν, n)` in `ℵ₂ × ℕ`. -/
def principal_open (ν : pSet.aleph_two.Type) (n : ℕ) : 𝔹 :=
  ⟨cantor_space.principal_open (ν, n),
   is_regular_of_clopen cantor_space.isClopen_principal_open⟩

lemma isClopen_principal_open {ν : pSet.aleph_two.Type} {n : ℕ} :
    IsClopen (principal_open ν n).val :=
  cantor_space.isClopen_principal_open

/-!
## Finite condition structure `𝒞`

A finite condition is a pair of disjoint finite subsets of `ℵ₂ × ℕ`,
representing a basic clopen set in the Cohen algebra.
-/

structure 𝒞 : Type where
  ins : Finset (pSet.aleph_two.Type × ℕ)
  out : Finset (pSet.aleph_two.Type × ℕ)
  H : ∀ x, x ∈ ins → x ∉ out

/-- Embed a finite condition as a regular open in the Cohen algebra. -/
noncomputable def ι (p : 𝒞) : 𝔹 :=
  ⟨{S : Set (pSet.aleph_two.Type × ℕ) | (p.ins : Set _) ⊆ S ∧ (p.out : Set _) ⊆ Sᶜ},
   is_regular_of_clopen
     (IsClopen.inter
       (cantor_space.isClopen_principal_open_finset p.ins)
       (cantor_space.isClopen_co_principal_open_finset p.out))⟩

lemma 𝒞_anti {p₁ p₂ : 𝒞} (hIns : p₁.ins ⊆ p₂.ins) (hOut : p₁.out ⊆ p₂.out) : ι p₂ ≤ ι p₁ := by
  rw [le_iff_subset']
  intro S hS
  rcases hS with ⟨hInsS, hOutS⟩
  refine ⟨Set.Subset.trans hIns hInsS, Set.Subset.trans hOut hOutS⟩

/-!

### Density lemmas for `𝒞`

Every nonzero element of the Cohen algebra contains a finite condition.
-/

lemma 𝒞_dense_basis : ∀ T ∈ (cantor_space.standard_basis : Set (Set (Set (pSet.aleph_two.Type × ℕ)))),
    T ≠ ∅ → ∃ p : 𝒞, (ι p).val ⊆ T := by
  intro T hT h_nonempty
  classical
  rw [cantor_space.standard_basis] at hT
  rcases hT with (hT | hT)
  · rcases hT with ⟨p_ins, p_out, rfl, h_disjoint⟩
    have hInsOut : ∀ x, x ∈ p_ins → x ∉ p_out := by
      intro x hxIns hxOut
      have hxInter : x ∈ p_ins ∩ p_out := Finset.mem_inter.mpr ⟨hxIns, hxOut⟩
      have hDisjEmpty : p_ins ∩ p_out = ∅ := by
        have := Finset.disjoint_iff_inter_eq_empty.mp h_disjoint
        exact this
      rw [hDisjEmpty] at hxInter
      simp at hxInter
    refine ⟨⟨p_ins, p_out, hInsOut⟩, ?_⟩
    intro S hS
    rcases hS with ⟨hIns, hOut⟩
    refine ⟨?_, ?_⟩
    · rw [cantor_space.mem_principal_open_finset_iff]
      exact hIns
    · simpa [cantor_space.co_principal_open_finset] using hOut
  · exact False.elim (h_nonempty hT)

lemma 𝒞_dense {b : 𝔹} (H : ⊥ < b) : ∃ p : 𝒞, (ι p) ≤ b := by
  have hNonempty : b.val.Nonempty :=
    (regularOpen_bot_lt (S := b)).mp H
  rcases hNonempty with ⟨S_wit, hSwit⟩
  have hOpen : IsOpen b.val := isOpen_of_is_regular b.2
  have hBasis : IsTopologicalBasis (cantor_space.standard_basis :
      Set (Set (Set (pSet.aleph_two.Type × ℕ)))) :=
    cantor_space.is_topological_basis_standard_basis
  rcases hBasis.exists_subset_of_mem_open hSwit hOpen with ⟨v, hvBasis, hvMem, hvSub⟩
  by_cases hvEmpty : v = ∅
  · rw [hvEmpty] at hvMem
    simp at hvMem
  · rcases 𝒞_dense_basis v hvBasis hvEmpty with ⟨p, hp⟩
    exact ⟨p, le_iff_subset'.mpr (Set.Subset.trans hp hvSub)⟩

lemma 𝒞_nonzero (p : 𝒞) : (⊥ : 𝔹) ≠ (ι p) := by
  intro H
  have h_val_eq : (⊥ : 𝔹).val = (ι p).val := congrArg (fun (x : 𝔹) => x.val) H
  have hMemRHS : (p.ins : Set (pSet.aleph_two.Type × ℕ)) ∈
      {S : Set (pSet.aleph_two.Type × ℕ) | (p.ins : Set _) ⊆ S ∧ (p.out : Set _) ⊆ Sᶜ} := by
    refine ⟨Set.Subset.refl _, ?_⟩
    intro a ha hx
    exact p.H a hx ha
  have hEmptyIsEmpty : (⊥ : 𝔹).val = (∅ : Set (Set (pSet.aleph_two.Type × ℕ))) := by
    simpa using regularOpen_coe_bot (α := Set (pSet.aleph_two.Type × ℕ))
  rw [hEmptyIsEmpty] at h_val_eq
  have hNonempty : (∅ : Set (Set (pSet.aleph_two.Type × ℕ))).Nonempty := by
    rw [h_val_eq]
    exact ⟨(p.ins : Set _), hMemRHS⟩
  exact Set.not_nonempty_empty hNonempty

lemma 𝒞_disjoint_row (p : 𝒞) : ∃ n : ℕ, ∀ ξ : pSet.aleph_two.Type, (ξ, n) ∉ p.ins ∧ (ξ, n) ∉ p.out := by
  classical
  let Y : Finset ℕ := (Finset.image Prod.snd p.ins) ∪ (Finset.image Prod.snd p.out)
  have hYfinite : Set.Finite (Y : Set ℕ) := Finset.finite_toSet _
  rcases hYfinite.exists_notMem with ⟨n, hn⟩
  use n
  intro ξ
  constructor
  · intro h; apply hn; apply Finset.mem_union_left; exact Finset.mem_image.mpr ⟨(ξ, n), h, rfl⟩
  · intro h; apply hn; apply Finset.mem_union_right; exact Finset.mem_image.mpr ⟨(ξ, n), h, rfl⟩

/-!
## Cohen reals

For each ordinal `ν < ℵ₂`, define a Boolean-valued subset `cohen_real.mk ν` of `ω`.
-/

namespace cohen_real

/-- The indicator function for the `ν`-th Cohen real. -/
def χ (ν : pSet.aleph_two.Type) : ℕ → 𝔹 :=
  fun n => principal_open ν n

/-- The Boolean-valued subset of `omega` determined by `χ ν`. -/
noncomputable def mk (ν : pSet.aleph_two.Type) : bSet 𝔹 :=
  set_of_indicator (x := omega) (fun n : (omega : bSet 𝔹).type => χ ν n.down)

@[simp] theorem mk_type {ν} : (mk ν).type = (omega : bSet 𝔹).type := rfl

@[simp] theorem mk_func {ν} {n : (mk ν).type} :
    (mk ν).func n = (omega : bSet 𝔹).func n := rfl

@[simp] theorem mk_bval {ν} {n : (mk ν).type} :
    (mk ν).bval n = (χ ν) (n.down) := by
  simp [mk, χ, set_of_indicator]

/-- The Boolean-valued model believes each `mk ν` is a subset of omega. -/
lemma definite {ν : pSet.aleph_two.Type} {Γ : 𝔹} : Γ ≤ mk ν ⊆ᴮ omega := by
  simpa [mk, set_of_indicator] using
    subset.mk_subset (x := omega) (χ := fun n : (omega : bSet 𝔹).type => χ ν n.down)

/-- The Boolean-valued model believes each `mk ν` is in `𝒫(ω)`. -/
lemma definite' {ν : pSet.aleph_two.Type} {Γ : 𝔹} : Γ ≤ mk ν ∈ᴮ bv_powerset omega :=
  bv_powerset_spec.mp definite

/-- Boolean separation for Cohen reals: if n ∈ mk ν₁ but n ∉ mk ν₂, then mk ν₁ ≠ mk ν₂. -/
lemma sep {n : ℕ} {Γ : 𝔹} {ν₁ ν₂ : pSet.aleph_two.Type}
    (H₁ : Γ ≤ (ofNat n) ∈ᴮ (mk ν₁)) (H₂ : Γ ≤ ((ofNat n) ∈ᴮ (mk ν₂))ᶜ) :
    Γ ≤ ((mk ν₁) =ᴮ (mk ν₂))ᶜ := by
  rw [eq_iff_subset_subset, compl_inf]
  refine le_trans ?_ le_sup_left
  rw [subset_unfold, compl_iInf]
  have h_simp : (fun i : (mk ν₁).type => (lattice.imp ((mk ν₁).bval i) (((mk ν₁).func i) ∈ᴮ (mk ν₂)))ᶜ) =
      (fun i => ((mk ν₁).bval i) ⊓ (((mk ν₁).func i) ∈ᴮ (mk ν₂))ᶜ) := by
    ext i; simp [lattice.imp]
  rw [h_simp]
  have hB : B_ext (fun z : bSet 𝔹 => ((z ∈ᴮ (mk ν₂))ᶜ)) :=
    B_ext_compl (B_ext_mem_left (mk ν₂))
  rw [bounded_exists (mk ν₁) (fun z => ((z ∈ᴮ (mk ν₂))ᶜ)) hB]
  apply lattice.bv_use (ofNat n)
  exact le_inf H₁ H₂

/-- If `(ν, n) ∈ p.out`, then the condition forces that `n ∉ mk ν`. -/
lemma principal_open_compl_val_eq {ν : pSet.aleph_two.Type} {n : ℕ} :
    ((principal_open ν n)ᶜ).val = ((principal_open ν n).val)ᶜ := by
  have h_clopen : IsClopen ((principal_open ν n).val) := isClopen_principal_open
  have h_closed : IsClosed ((principal_open ν n).val) := IsClopen.isClosed h_clopen
  show ((principal_open ν n)ᶜ).val = ((principal_open ν n).val)ᶜ
  calc
    ((principal_open ν n)ᶜ).val = ((principal_open ν n) : Set _)ᵖ := rfl
    _ = ((principal_open ν n).val)ᵖ := rfl
    _ = (closure ((principal_open ν n).val))ᶜ := by rw [perp_unfold]
    _ = ((principal_open ν n).val)ᶜ := by rw [IsClosed.closure_eq h_closed]

lemma not_mem_of_not_mem {p : 𝒞} {ν : pSet.aleph_two.Type} {n : ℕ}
    (H : (ν, n) ∈ p.out) : ι p ≤ ((ofNat n) ∈ᴮ (mk ν))ᶜ := by
  rw [mem_unfold, compl_iSup]
  apply le_iInf; intro k
  rw [compl_inf]
  simp [mk_bval, mk_func, χ]
  by_cases hEq : n = k.down
  · rw [hEq]
    simp [bv_eq_refl]
    rw [le_iff_subset', principal_open_compl_val_eq]
    intro S hS
    rcases hS with ⟨hIns, hOut⟩
    have hmem : (ν, k.down) ∈ (p.out : Set (pSet.aleph_two.Type × ℕ)) :=
      by simpa [hEq] using H
    have h_not_mem : (ν, k.down) ∉ S := hOut hmem
    simpa [cantor_space.principal_open, Set.mem_setOf_eq]
  · apply le_trans ?_ le_sup_right
    have h_eq_top : ((ofNat n : bSet 𝔹) =ᴮ (ofNat k.down))ᶜ = ⊤ := by
      simp [ofNat_inj hEq]
    rw [h_eq_top]
    exact le_top

/-- Distinct ordinals yield distinct Cohen reals in the Boolean-valued model. -/
lemma inj {ν₁ ν₂ : pSet.aleph_two.{0}.Type} (H_neq : ν₁ ≠ ν₂) :
    (mk ν₁) =ᴮ (mk ν₂) ≤ (⊥ : 𝔹) := by
  classical
  by_contra hlt
  have h_ne_bot : (mk ν₁) =ᴮ (mk ν₂) ≠ ⊥ := by
    intro h_eq
    apply hlt
    rw [h_eq]
  have hpos : ⊥ < (mk ν₁) =ᴮ (mk ν₂) := Ne.bot_lt h_ne_bot
  rcases 𝒞_dense (b := (mk ν₁) =ᴮ (mk ν₂)) hpos with ⟨p, H_p⟩
  rcases 𝒞_disjoint_row p with ⟨n, H_n⟩
  -- Build p' by adding (ν₁, n) to ins and (ν₂, n) to out
  let p' : 𝒞 :=
    { ins := insert (ν₁, n) p.ins
      out := insert (ν₂, n) p.out
      H := by
        intro x hxIns hxOut
        have hxIns' : x ∈ insert (ν₁, n) p.ins := hxIns
        have hxOut' : x ∈ insert (ν₂, n) p.out := hxOut
        rcases Finset.mem_insert.mp hxIns' with (hxEq | hxInsP)
        · -- x = (ν₁, n)
          rw [hxEq] at hxOut'
          rcases Finset.mem_insert.mp hxOut' with (hxEq' | hxOutP)
          · -- x = (ν₂, n), so ν₁ = ν₂, contradiction
            simp at hxEq'
            exact H_neq hxEq'
          · -- x ∈ p.out, but H_n says (ν₁, n) ∉ p.out
            exact (H_n ν₁).right hxOutP
        · -- x ∈ p.ins
          rcases Finset.mem_insert.mp hxOut' with (hxEq' | hxOutP)
          · -- x = (ν₂, n), but H_n says (ν₂, n) ∉ p.ins
            rw [hxEq'] at hxInsP
            exact (H_n ν₂).left hxInsP
          · -- x ∈ p.ins ∩ p.out, use p.H
            exact p.H x hxInsP hxOutP }
  have h_anti : ι p' ≤ ι p :=
    𝒞_anti (by
      intro x hx; apply Finset.mem_insert_of_mem; exact hx)
      (by
        intro x hx; apply Finset.mem_insert_of_mem; exact hx)
  have h_mem₁ : ι p' ≤ (ofNat n) ∈ᴮ (mk ν₁) := by
    rw [mem_unfold]
    apply lattice.bv_use (ULift.up n)
    refine le_inf ?_ ?_
    · simp [mk_bval, mk_func, χ, le_iff_subset', ι, cantor_space.principal_open]
      intro S hS
      have : (ν₁, n) ∈ insert (ν₁, n) p.ins := Finset.mem_insert.mpr (Or.inl rfl)
      rcases hS with ⟨hIns, hOut⟩
      exact hIns this
    · simpa [mk_func] using (bv_eq_refl (ofNat n : bSet 𝔹))
  have h_mem₂ : ι p' ≤ ((ofNat n) ∈ᴮ (mk ν₂))ᶜ := by
    have : (ν₂, n) ∈ p'.out := by
      dsimp [p']
      exact Finset.mem_insert.mpr (Or.inl rfl)
    exact not_mem_of_not_mem this
  have h_neq : ι p' ≤ ((mk ν₁) =ᴮ (mk ν₂))ᶜ := sep h_mem₁ h_mem₂
  have h_eq : ι p' ≤ (mk ν₁) =ᴮ (mk ν₂) := le_trans h_anti H_p
  have h_contra : ι p' ≤ ⊥ := by
    have : ι p' ≤ (mk ν₁) =ᴮ (mk ν₂) ⊓ ((mk ν₁) =ᴮ (mk ν₂))ᶜ := le_inf h_eq h_neq
    simpa using this
  have h_nonzero : (⊥ : 𝔹) ≠ ι p' := 𝒞_nonzero p'
  exact h_nonzero (le_antisymm h_contra bot_le).symm

end cohen_real

/-!
## Cardinal preservation

The central technical lemmas: if a check-name is Boolean-valued larger than another,
we can extract a concrete function at the meta-level.
-/

section cardinal_preservation

lemma AE_of_check_larger_than_check'' {x y : pSet.{u}} (f : bSet 𝔹) {Γ : 𝔹}
    (H_nonzero : ⊥ < Γ) (H : Γ ≤ is_surj_onto (check x) (check y) f)
    (H_nonempty : ∃ z, z ∈ y) : ∀ i : (check y : bSet 𝔹).type,
    ∃ j : (check x : bSet 𝔹).type,
    ⊥ < (is_func f) ⊓ (pair ((check x : bSet 𝔹).func j) ((check y : bSet 𝔹).func i) ∈ᴮ f) := by
  intro i
  let x' := (check x : bSet 𝔹)
  let y' := (check y : bSet 𝔹)
  have h_func' : Γ ≤ is_func' x' y' f := H.trans inf_le_left
  have h_surj : Γ ≤ is_surj x' y' f := H.trans inf_le_right
  have h_func : Γ ≤ is_func f := is_func_of_is_func' h_func'
  -- y'.func i ∈ y' = ⊤
  have h_func_mem_eq_top : y'.func i ∈ᴮ y' = ⊤ := by
    rw [mem_unfold]
    refine le_antisymm le_top ?_
    calc
      ⊤ = y'.func i =ᴮ y'.func i := (bv_eq_refl _).symm
      _ = ⊤ ⊓ (y'.func i =ᴮ y'.func i) := by simp
      _ = y'.bval i ⊓ y'.func i =ᴮ y'.func i := by dsimp [y']; simp [check_bval]
      _ ≤ ⨆ (j : y'.type), y'.bval j ⊓ y'.func i =ᴮ y'.func j :=
        le_iSup (fun j => y'.bval j ⊓ y'.func i =ᴮ y'.func j) i
  have h_func_mem : Γ ≤ y'.func i ∈ᴮ y' := by
    rw [h_func_mem_eq_top]; exact le_top
  -- Specialize is_surj to y'.func i
  have h_imp_surj : (⨅ v : bSet 𝔹, lattice.imp (v ∈ᴮ y') (⨆ w : bSet 𝔹, w ∈ᴮ x' ⊓ pair w v ∈ᴮ f))
      ≤ lattice.imp (y'.func i ∈ᴮ y') (⨆ w : bSet 𝔹, w ∈ᴮ x' ⊓ pair w (y'.func i) ∈ᴮ f) :=
    iInf_le (fun v : bSet 𝔹 => lattice.imp (v ∈ᴮ y') (⨆ w : bSet 𝔹, w ∈ᴮ x' ⊓ pair w v ∈ᴮ f)) (y'.func i)
  have h_imp : Γ ≤ lattice.imp (y'.func i ∈ᴮ y') (⨆ w : bSet 𝔹, w ∈ᴮ x' ⊓ pair w (y'.func i) ∈ᴮ f) :=
    h_surj.trans h_imp_surj
  have h_sup : Γ ≤ ⨆ w : bSet 𝔹, (w ∈ᴮ x' ⊓ pair w (y'.func i) ∈ᴮ f) := by
    calc
      Γ = Γ ⊓ (y'.func i ∈ᴮ y') := (inf_of_le_left h_func_mem).symm
      _ ≤ ⨆ w : bSet 𝔹, (w ∈ᴮ x' ⊓ pair w (y'.func i) ∈ᴮ f) := lattice.le_imp_iff.mp h_imp
  -- Get witness w via exists_convert
  have h_B_ext : B_ext (fun (w : bSet 𝔹) => w ∈ᴮ x' ⊓ pair w (y'.func i) ∈ᴮ f) :=
    B_ext_inf (B_ext_mem_left x') (B_ext_pair_mem_left (x := y'.func i) (y := f))
  rcases exists_convert h_sup h_B_ext with ⟨w, hw⟩
  have h_w_mem : Γ ≤ w ∈ᴮ x' := hw.trans inf_le_left
  have h_w_pair : Γ ≤ pair w (y'.func i) ∈ᴮ f := hw.trans inf_le_right
  have h_w_total : Γ ≤ is_func f ⊓ pair w (y'.func i) ∈ᴮ f := le_inf h_func h_w_pair
  -- w ∈ check x = ⨆ j, w = (check x).func j
  have h_w_mem_sup : w ∈ᴮ x' = ⨆ (j : x'.type), w =ᴮ x'.func j := by
    rw [mem_unfold]; dsimp [x']; simp [check_bval]
  have h_w_mem_sup_ineq : Γ ≤ ⨆ (j : x'.type), w =ᴮ x'.func j := by
    rw [← h_w_mem_sup]; exact h_w_mem
  -- Classical: assume no j works, derive Γ = ⊥, contradiction with H_nonzero
  by_cases h_exists : ∃ j : x'.type, ⊥ < is_func f ⊓ pair (x'.func j) (y'.func i) ∈ᴮ f
  · exact h_exists
  · push_neg at h_exists
    have h_bot : ∀ j : x'.type, is_func f ⊓ pair (x'.func j) (y'.func i) ∈ᴮ f = ⊥ := by
      intro j
      have h_not_lt : ¬ ⊥ < is_func f ⊓ pair (x'.func j) (y'.func i) ∈ᴮ f := h_exists j
      by_contra h_ne
      apply h_not_lt
      exact Ne.bot_lt h_ne
    have h_zero : ∀ j : x'.type, Γ ⊓ (w =ᴮ x'.func j) = ⊥ := by
      intro j
      have h_B_ext_app : (w =ᴮ x'.func j) ⊓ (pair w (y'.func i) ∈ᴮ f) ≤ pair (x'.func j) (y'.func i) ∈ᴮ f :=
        B_ext_pair_mem_left (x := y'.func i) (y := f) w (x'.func j)
      have h_combined : (w =ᴮ x'.func j) ⊓ (is_func f ⊓ pair w (y'.func i) ∈ᴮ f) ≤ ⊥ := by
        calc
          (w =ᴮ x'.func j) ⊓ (is_func f ⊓ pair w (y'.func i) ∈ᴮ f)
              = is_func f ⊓ ((w =ᴮ x'.func j) ⊓ pair w (y'.func i) ∈ᴮ f) := by ac_rfl
          _ ≤ is_func f ⊓ pair (x'.func j) (y'.func i) ∈ᴮ f :=
            inf_le_inf_left (is_func f) h_B_ext_app
          _ ≤ ⊥ := by rw [h_bot j]
      apply le_antisymm ?_ bot_le
      calc
        Γ ⊓ (w =ᴮ x'.func j) ≤ (is_func f ⊓ pair w (y'.func i) ∈ᴮ f) ⊓ (w =ᴮ x'.func j) :=
          inf_le_inf_right (w =ᴮ x'.func j) h_w_total
        _ = (w =ᴮ x'.func j) ⊓ (is_func f ⊓ pair w (y'.func i) ∈ᴮ f) := by
          simp [inf_comm, inf_left_comm, inf_assoc]
        _ ≤ ⊥ := h_combined
    have h_Gamma_eq_bot : Γ = ⊥ := by
      calc
        Γ = Γ ⊓ (w ∈ᴮ x') := (inf_of_le_left h_w_mem).symm
        _ = Γ ⊓ ⨆ (j : x'.type), (w =ᴮ x'.func j) := by rw [h_w_mem_sup]
        _ = ⨆ (j : x'.type), Γ ⊓ (w =ᴮ x'.func j) := by rw [inf_iSup_eq]
        _ = ⨆ (_j : x'.type), (⊥ : 𝔹) := by simp [h_zero]
        _ = ⊥ := by simp
    exfalso
    exact H_nonzero.ne' h_Gamma_eq_bot

lemma AE_of_check_larger_than_check' {x y : pSet.{u}} {Γ : 𝔹}
    (H_nonzero : ⊥ < Γ) (H : Γ ≤ surjects_onto (check x) (check y))
    (H_mem : ∃ z, z ∈ y) : ∃ f : bSet 𝔹, ∀ i : (check y : bSet 𝔹).type,
    ∃ j : (check x : bSet 𝔹).type,
    ⊥ < (is_func f) ⊓ (pair ((check x : bSet 𝔹).func j) ((check y : bSet 𝔹).func i) ∈ᴮ f) := by
  unfold surjects_onto at H
  have h_congr : B_ext (fun w : bSet 𝔹 => is_surj_onto (check x) (check y) w) :=
    B_ext_inf (B_ext_is_func'_right (check x) (check y))
      (B_ext_is_surj_right (x := check x) (y := check y))
  rcases exists_convert H h_congr with ⟨f, Hf⟩
  exact ⟨f, AE_of_check_larger_than_check'' f H_nonzero Hf H_mem⟩

lemma surjects_onto_of_larger_than_and_exists_mem {x y : bSet 𝔹} {Γ : 𝔹}
    (h_larger : Γ ≤ larger_than x y) (h_exists : Γ ≤ exists_mem y) : Γ ≤ surjects_onto x y := by
  unfold larger_than at h_larger
  unfold surjects_onto
  -- h_larger: Γ ≤ ⨆ S, ⨆ f, S ⊆ᴮ x ⊓ is_func' S y f ⊓ is_surj S y f
  apply (le_inf le_rfl h_larger).trans
  apply lattice.bv_cases_right
  intro S
  apply lattice.bv_cases_right
  intro f
  let Ω : 𝔹 := Γ ⊓ (S ⊆ᴮ x ⊓ is_func' S y f ⊓ is_surj S y f)
  have h_sub : Ω ≤ S ⊆ᴮ x := by
    dsimp [Ω]; exact inf_le_right.trans (inf_le_left.trans inf_le_left)
  have h_func' : Ω ≤ is_func' S y f := by
    dsimp [Ω]; exact inf_le_right.trans (inf_le_left.trans inf_le_right)
  have h_surj : Ω ≤ is_surj S y f := by
    dsimp [Ω]; exact inf_le_right.trans inf_le_right
  have hΩΓ : Ω ≤ Γ := inf_le_left
  have h_exists_Ω : Ω ≤ exists_mem y := hΩΓ.trans h_exists
  unfold exists_mem at h_exists_Ω
  apply (le_inf le_rfl h_exists_Ω).trans
  apply lattice.bv_cases_right
  intro z
  let Θ : 𝔹 := Ω ⊓ (z ∈ᴮ y)
  have hΘ_Ω : Θ ≤ Ω := inf_le_left
  have h_sub_Θ : Θ ≤ S ⊆ᴮ x := hΘ_Ω.trans h_sub
  have h_func'_Θ : Θ ≤ is_func' S y f := hΘ_Ω.trans h_func'
  have h_surj_Θ : Θ ≤ is_surj S y f := hΘ_Ω.trans h_surj
  have hz_mem : Θ ≤ z ∈ᴮ y := inf_le_right
  -- Construct extension g: takes f on S×y, defaults to z on x\S
  let g : bSet 𝔹 := subset.mk (x := prod x y) (fun pr : (prod x y).type =>
    ((x.func pr.1 ∈ᴮ S) ⊓ (pair (x.func pr.1) (y.func pr.2) ∈ᴮ f)) ⊔
    (((x.func pr.1 ∈ᴮ S)ᶜ) ⊓ (y.func pr.2 =ᴮ z)))
  apply lattice.bv_use g
  unfold is_surj_onto
  apply le_inf
  · -- Part 1: Θ ≤ is_func' x y g = is_func g ⊓ is_total x y g
    unfold is_func'
    apply le_inf
    · -- 1a: Θ ≤ is_func g
      unfold is_func
      apply le_iInf; intro w₁; apply le_iInf; intro w₂
      apply le_iInf; intro v₁; apply le_iInf; intro v₂
      apply lattice.bv_imp_intro
      apply lattice.bv_imp_intro
      let Φ : 𝔹 := Θ ⊓ (pair w₁ v₁ ∈ᴮ g ⊓ pair w₂ v₂ ∈ᴮ g) ⊓ (w₁ =ᴮ w₂)
      have hMem₁ : Φ ≤ pair w₁ v₁ ∈ᴮ g := by
        dsimp [Φ]; exact inf_le_left.trans inf_le_right |>.trans inf_le_left
      have hMem₂ : Φ ≤ pair w₂ v₂ ∈ᴮ g := by
        dsimp [Φ]; exact inf_le_left.trans inf_le_right |>.trans inf_le_right
      have hwEq : Φ ≤ w₁ =ᴮ w₂ := by
        dsimp [Φ]; exact inf_le_right
      have hΦ_Θ : Φ ≤ Θ := by dsimp [Φ]; exact inf_le_left.trans inf_le_left
      -- Expand g membership to type-indexed form
      dsimp [g] at hMem₁ hMem₂
      rw [mem_subset.mk_iff₂] at hMem₁ hMem₂
      -- Case split on index for pair 1
      apply (le_inf le_rfl hMem₁).trans
      apply lattice.bv_cases_right
      intro pr₁
      -- Case split on index for pair 2 (weakened)
      have hMem₂_ext : Φ ⊓ ((prod x y).bval pr₁ ⊓
          (pair w₁ v₁ =ᴮ (prod x y).func pr₁ ⊓
            (((x.func pr₁.1 ∈ᴮ S) ⊓ (pair (x.func pr₁.1) (y.func pr₁.2) ∈ᴮ f)) ⊔
             (((x.func pr₁.1 ∈ᴮ S)ᶜ) ⊓ (y.func pr₁.2 =ᴮ z))))) ≤
          ⨆ pr : (prod x y).type,
            (prod x y).bval pr ⊓ (pair w₂ v₂ =ᴮ (prod x y).func pr ⊓
              (((x.func pr.1 ∈ᴮ S) ⊓ (pair (x.func pr.1) (y.func pr.2) ∈ᴮ f)) ⊔
               (((x.func pr.1 ∈ᴮ S)ᶜ) ⊓ (y.func pr.2 =ᴮ z)))) := by
        exact inf_le_left.trans hMem₂
      apply (le_inf le_rfl hMem₂_ext).trans
      apply lattice.bv_cases_right
      intro pr₂
      -- Reassociate: extract base parts and χ parts
      let base₁ : 𝔹 := (prod x y).bval pr₁ ⊓ (pair w₁ v₁ =ᴮ (prod x y).func pr₁)
      let base₂ : 𝔹 := (prod x y).bval pr₂ ⊓ (pair w₂ v₂ =ᴮ (prod x y).func pr₂)
      let C : 𝔹 := Φ ⊓ base₁ ⊓ base₂
      -- Reassociate goal to C ⊓ χ₁ ⊓ χ₂ ≤ v₁ = v₂
      refine
        calc
          (Φ ⊓ ((prod x y).bval pr₁ ⊓
              (pair w₁ v₁ =ᴮ (prod x y).func pr₁ ⊓
                (((x.func pr₁.1 ∈ᴮ S) ⊓ (pair (x.func pr₁.1) (y.func pr₁.2) ∈ᴮ f)) ⊔
                 (((x.func pr₁.1 ∈ᴮ S)ᶜ) ⊓ (y.func pr₁.2 =ᴮ z)))))) ⊓
            ((prod x y).bval pr₂ ⊓
              (pair w₂ v₂ =ᴮ (prod x y).func pr₂ ⊓
                (((x.func pr₂.1 ∈ᴮ S) ⊓ (pair (x.func pr₂.1) (y.func pr₂.2) ∈ᴮ f)) ⊔
                 (((x.func pr₂.1 ∈ᴮ S)ᶜ) ⊓ (y.func pr₂.2 =ᴮ z)))))
              = C ⊓
                (((x.func pr₁.1 ∈ᴮ S) ⊓ (pair (x.func pr₁.1) (y.func pr₁.2) ∈ᴮ f)) ⊔
                 (((x.func pr₁.1 ∈ᴮ S)ᶜ) ⊓ (y.func pr₁.2 =ᴮ z))) ⊓
                (((x.func pr₂.1 ∈ᴮ S) ⊓ (pair (x.func pr₂.1) (y.func pr₂.2) ∈ᴮ f)) ⊔
                 (((x.func pr₂.1 ∈ᴮ S)ᶜ) ⊓ (y.func pr₂.2 =ᴮ z))) := by
            dsimp [C, base₁, base₂]; ac_rfl
          _ ≤ v₁ =ᴮ v₂ := ?_
      -- Extract structural info from C
      have hC_Θ : C ≤ Θ := by
        dsimp [C, Φ]; exact inf_le_left.trans inf_le_left |>.trans inf_le_left |>.trans inf_le_left
      have hC_wEq : C ≤ w₁ =ᴮ w₂ := by
        dsimp [C, Φ]; exact (inf_le_left.trans inf_le_left).trans inf_le_right
      have hC_pairEq₁ : C ≤ pair w₁ v₁ =ᴮ (prod x y).func pr₁ := by
        dsimp [C, base₁]; exact inf_le_left.trans inf_le_right |>.trans inf_le_right
      have hC_pairEq₂ : C ≤ pair w₂ v₂ =ᴮ (prod x y).func pr₂ := by
        dsimp [C, base₂]; exact inf_le_right.trans inf_le_right
      -- Pair equalities expanded via prod_func
      have hC_pairEq₁' : C ≤ pair w₁ v₁ =ᴮ pair (x.func pr₁.1) (y.func pr₁.2) := by
        simpa [prod_func] using hC_pairEq₁
      have hC_pairEq₂' : C ≤ pair w₂ v₂ =ᴮ pair (x.func pr₂.1) (y.func pr₂.2) := by
        simpa [prod_func] using hC_pairEq₂
      have hw₁_eq : C ≤ w₁ =ᴮ x.func pr₁.1 := eq_of_eq_pair_left' hC_pairEq₁'
      have hv₁_eq : C ≤ v₁ =ᴮ y.func pr₁.2 := eq_of_eq_pair_right' hC_pairEq₁'
      have hw₂_eq : C ≤ w₂ =ᴮ x.func pr₂.1 := eq_of_eq_pair_left' hC_pairEq₂'
      have hv₂_eq : C ≤ v₂ =ᴮ y.func pr₂.2 := eq_of_eq_pair_right' hC_pairEq₂'
      have h_x_eq : C ≤ x.func pr₁.1 =ᴮ x.func pr₂.1 :=
        bv_trans (bv_trans (bv_symm hw₁_eq) hC_wEq) hw₂_eq
      -- Get is_func f for later use
      have hC_func_f : C ≤ is_func f :=
        hC_Θ.trans (by
          have : Θ ≤ is_func' S y f := h_func'_Θ
          unfold is_func' at this; exact this.trans inf_le_left)
      -- Reassociate: C ⊓ (A₂ ⊔ B₂) ⊓ (A₁ ⊔ B₁) ≤ v₁ = v₂
      -- Split on A₁ ⊔ B₁ first
      have h_split₁ : C ⊓
          (((x.func pr₁.1 ∈ᴮ S) ⊓ (pair (x.func pr₁.1) (y.func pr₁.2) ∈ᴮ f)) ⊔
           (((x.func pr₁.1 ∈ᴮ S)ᶜ) ⊓ (y.func pr₁.2 =ᴮ z))) ⊓
          (((x.func pr₂.1 ∈ᴮ S) ⊓ (pair (x.func pr₂.1) (y.func pr₂.2) ∈ᴮ f)) ⊔
           (((x.func pr₂.1 ∈ᴮ S)ᶜ) ⊓ (y.func pr₂.2 =ᴮ z)))
          = (C ⊓
            (((x.func pr₂.1 ∈ᴮ S) ⊓ (pair (x.func pr₂.1) (y.func pr₂.2) ∈ᴮ f)) ⊔
             (((x.func pr₂.1 ∈ᴮ S)ᶜ) ⊓ (y.func pr₂.2 =ᴮ z)))) ⊓
            (((x.func pr₁.1 ∈ᴮ S) ⊓ (pair (x.func pr₁.1) (y.func pr₁.2) ∈ᴮ f)) ⊔
             (((x.func pr₁.1 ∈ᴮ S)ᶜ) ⊓ (y.func pr₁.2 =ᴮ z))) := by
        ac_rfl
      rw [h_split₁]
      apply lattice.bv_or_elim_right
      · -- Case A₁: from f, with x.func pr₁.1 ∈ S
        have hA₁_reassoc : ((C : 𝔹) ⊓
            (((x.func pr₂.1 ∈ᴮ S) ⊓ (pair (x.func pr₂.1) (y.func pr₂.2) ∈ᴮ f)) ⊔
             (((x.func pr₂.1 ∈ᴮ S)ᶜ) ⊓ (y.func pr₂.2 =ᴮ z)))) ⊓
            ((x.func pr₁.1 ∈ᴮ S) ⊓ (pair (x.func pr₁.1) (y.func pr₁.2) ∈ᴮ f))
            = ((C : 𝔹) ⊓ (x.func pr₁.1 ∈ᴮ S) ⊓ (pair (x.func pr₁.1) (y.func pr₁.2) ∈ᴮ f)) ⊓
              (((x.func pr₂.1 ∈ᴮ S) ⊓ (pair (x.func pr₂.1) (y.func pr₂.2) ∈ᴮ f)) ⊔
               (((x.func pr₂.1 ∈ᴮ S)ᶜ) ⊓ (y.func pr₂.2 =ᴮ z))) := by
          ac_rfl
        rw [hA₁_reassoc]
        apply lattice.bv_or_elim_right
        · -- Case A₁ + A₂: both from f
          let C' : 𝔹 := (C : 𝔹) ⊓ (x.func pr₁.1 ∈ᴮ S) ⊓ (pair (x.func pr₁.1) (y.func pr₁.2) ∈ᴮ f) ⊓
            ((x.func pr₂.1 ∈ᴮ S) ⊓ (pair (x.func pr₂.1) (y.func pr₂.2) ∈ᴮ f))
          have hC'_C : C' ≤ C := by dsimp [C']; exact inf_le_left.trans inf_le_left |>.trans inf_le_left
          have hC'_hf₁ : C' ≤ pair (x.func pr₁.1) (y.func pr₁.2) ∈ᴮ f := by
            dsimp [C']; exact inf_le_left.trans inf_le_right
          have hC'_hf₂ : C' ≤ pair (x.func pr₂.1) (y.func pr₂.2) ∈ᴮ f := by
            dsimp [C']; exact inf_le_right.trans inf_le_right
          have hC'_x_eq : C' ≤ x.func pr₁.1 =ᴮ x.func pr₂.1 := hC'_C.trans h_x_eq
          -- Use is_func f on the two pairs
          have h_func_spec : C' ≤ lattice.imp
              (pair (x.func pr₁.1) (y.func pr₁.2) ∈ᴮ f ⊓
               pair (x.func pr₂.1) (y.func pr₂.2) ∈ᴮ f)
              (lattice.imp (x.func pr₁.1 =ᴮ x.func pr₂.1)
                (y.func pr₁.2 =ᴮ y.func pr₂.2)) :=
            (hC'_C.trans hC_func_f).trans
              (iInf_le _ (x.func pr₁.1)) |>.trans
              (iInf_le _ (x.func pr₂.1)) |>.trans
              (iInf_le _ (y.func pr₁.2)) |>.trans
              (iInf_le _ (y.func pr₂.2))
          have h_ypair_eq : C' ≤ y.func pr₁.2 =ᴮ y.func pr₂.2 := by
            have h_imp1 : C' ≤ lattice.imp (x.func pr₁.1 =ᴮ x.func pr₂.1)
                (y.func pr₁.2 =ᴮ y.func pr₂.2) :=
              lattice.bv_context_apply h_func_spec (le_inf hC'_hf₁ hC'_hf₂)
            exact lattice.bv_context_apply h_imp1 hC'_x_eq
          have hC'_v₁_eq : C' ≤ v₁ =ᴮ y.func pr₁.2 := hC'_C.trans hv₁_eq
          have hC'_v₂_eq : C' ≤ y.func pr₂.2 =ᴮ v₂ := bv_symm (hC'_C.trans hv₂_eq)
          exact bv_trans (bv_trans hC'_v₁_eq h_ypair_eq) hC'_v₂_eq
        · -- Case A₁ + B₂: from f and default → contradiction via w ∈ S ∧ w ∉ S
          let C' : 𝔹 := C ⊓ (x.func pr₁.1 ∈ᴮ S) ⊓ (pair (x.func pr₁.1) (y.func pr₁.2) ∈ᴮ f) ⊓
            ((x.func pr₂.1 ∈ᴮ S)ᶜ ⊓ y.func pr₂.2 =ᴮ z)
          have hC'_C : C' ≤ C := by dsimp [C']; exact inf_le_left.trans inf_le_left |>.trans inf_le_left
          have hC'_inS : C' ≤ x.func pr₁.1 ∈ᴮ S := by
            dsimp [C']; exact inf_le_left.trans inf_le_left |>.trans inf_le_right
          have hC'_notinS : C' ≤ (x.func pr₂.1 ∈ᴮ S)ᶜ := by
            dsimp [C']; exact inf_le_right.trans inf_le_left
          have hC'_x_eq' : C' ≤ x.func pr₁.1 =ᴮ x.func pr₂.1 := hC'_C.trans h_x_eq
          -- Transfer membership: x.func pr₁.1 ∈ S and x.func pr₁.1 = x.func pr₂.1
          -- implies x.func pr₂.1 ∈ S
          have hC'_inS₂ : C' ≤ x.func pr₂.1 ∈ᴮ S := by
            have h_mem_eq : x.func pr₁.1 ∈ᴮ S ⊓ (x.func pr₁.1 =ᴮ x.func pr₂.1) ≤
                x.func pr₂.1 ∈ᴮ S := by
              simpa [inf_comm] using subst_congr_mem_left (u := x.func pr₁.1)
                (v := x.func pr₂.1) (w := S)
            exact (le_inf hC'_inS hC'_x_eq').trans h_mem_eq
          -- Contradiction: both in S and not in S
          have h_contra : C' ≤ ⊥ :=
            calc
              C' ≤ x.func pr₂.1 ∈ᴮ S ⊓ (x.func pr₂.1 ∈ᴮ S)ᶜ :=
                le_inf hC'_inS₂ hC'_notinS
              _ = ⊥ := by simp
          exact lattice.bv_exfalso h_contra
      · -- Case B₁: default case for pair 1
        have hB₁_reassoc : ((C : 𝔹) ⊓
            (((x.func pr₂.1 ∈ᴮ S) ⊓ (pair (x.func pr₂.1) (y.func pr₂.2) ∈ᴮ f)) ⊔
             (((x.func pr₂.1 ∈ᴮ S)ᶜ) ⊓ (y.func pr₂.2 =ᴮ z)))) ⊓
            (((x.func pr₁.1 ∈ᴮ S)ᶜ) ⊓ (y.func pr₁.2 =ᴮ z))
            = ((C : 𝔹) ⊓ ((x.func pr₁.1 ∈ᴮ S)ᶜ) ⊓ (y.func pr₁.2 =ᴮ z)) ⊓
              (((x.func pr₂.1 ∈ᴮ S) ⊓ (pair (x.func pr₂.1) (y.func pr₂.2) ∈ᴮ f)) ⊔
               (((x.func pr₂.1 ∈ᴮ S)ᶜ) ⊓ (y.func pr₂.2 =ᴮ z))) := by
          ac_rfl
        rw [hB₁_reassoc]
        apply lattice.bv_or_elim_right
        · -- Case B₁ + A₂: default + from f → contradiction
          let C' : 𝔹 := (C : 𝔹) ⊓ ((x.func pr₁.1 ∈ᴮ S)ᶜ) ⊓ (y.func pr₁.2 =ᴮ z) ⊓
            ((x.func pr₂.1 ∈ᴮ S) ⊓ (pair (x.func pr₂.1) (y.func pr₂.2) ∈ᴮ f))
          have hC'_C : C' ≤ C := by
            dsimp [C']
            calc
              ((C ⊓ ((x.func pr₁.1 ∈ᴮ S)ᶜ) ⊓ (y.func pr₁.2 =ᴮ z)) ⊓
                ((x.func pr₂.1 ∈ᴮ S) ⊓ (pair (x.func pr₂.1) (y.func pr₂.2) ∈ᴮ f))) ≤
                  C ⊓ ((x.func pr₁.1 ∈ᴮ S)ᶜ) ⊓ (y.func pr₁.2 =ᴮ z) := inf_le_left
              _ ≤ C ⊓ ((x.func pr₁.1 ∈ᴮ S)ᶜ) := inf_le_left
              _ ≤ C := inf_le_left
          have hC'_notinS : C' ≤ (x.func pr₁.1 ∈ᴮ S)ᶜ := by
            dsimp [C']
            calc
              ((C ⊓ ((x.func pr₁.1 ∈ᴮ S)ᶜ) ⊓ (y.func pr₁.2 =ᴮ z)) ⊓
                ((x.func pr₂.1 ∈ᴮ S) ⊓ (pair (x.func pr₂.1) (y.func pr₂.2) ∈ᴮ f))) ≤
                  C ⊓ ((x.func pr₁.1 ∈ᴮ S)ᶜ) ⊓ (y.func pr₁.2 =ᴮ z) := inf_le_left
              _ ≤ C ⊓ ((x.func pr₁.1 ∈ᴮ S)ᶜ) := inf_le_left
              _ ≤ ((x.func pr₁.1 ∈ᴮ S)ᶜ) := inf_le_right
          have hC'_inS₂ : C' ≤ x.func pr₂.1 ∈ᴮ S := by
            dsimp [C']
            calc
              ((C ⊓ ((x.func pr₁.1 ∈ᴮ S)ᶜ) ⊓ (y.func pr₁.2 =ᴮ z)) ⊓
                ((x.func pr₂.1 ∈ᴮ S) ⊓ (pair (x.func pr₂.1) (y.func pr₂.2) ∈ᴮ f))) ≤
                  ((x.func pr₂.1 ∈ᴮ S) ⊓ (pair (x.func pr₂.1) (y.func pr₂.2) ∈ᴮ f)) := inf_le_right
              _ ≤ x.func pr₂.1 ∈ᴮ S := inf_le_left
          have hC'_x_eq' : C' ≤ x.func pr₁.1 =ᴮ x.func pr₂.1 := hC'_C.trans h_x_eq
          -- Transfer not-in-S to pr₂
          have hC'_notinS₂ : C' ≤ (x.func pr₂.1 ∈ᴮ S)ᶜ := by
            have h_mem_compl : (x.func pr₁.1 ∈ᴮ S)ᶜ ⊓ (x.func pr₁.1 =ᴮ x.func pr₂.1) ≤
                (x.func pr₂.1 ∈ᴮ S)ᶜ := by
              have hB_ext := B_ext_compl (B_ext_mem_left S)
              simpa [inf_comm] using hB_ext (x.func pr₁.1) (x.func pr₂.1)
            exact (le_inf hC'_notinS hC'_x_eq').trans h_mem_compl
          have h_contra : C' ≤ ⊥ :=
            calc
              C' ≤ x.func pr₂.1 ∈ᴮ S ⊓ (x.func pr₂.1 ∈ᴮ S)ᶜ :=
                le_inf hC'_inS₂ hC'_notinS₂
              _ = ⊥ := by simp
          exact lattice.bv_exfalso h_contra
        · -- Case B₁ + B₂: both default → v₁ = z = v₂
          let C' : 𝔹 := (C : 𝔹) ⊓ ((x.func pr₁.1 ∈ᴮ S)ᶜ) ⊓ (y.func pr₁.2 =ᴮ z) ⊓
            (((x.func pr₂.1 ∈ᴮ S)ᶜ) ⊓ (y.func pr₂.2 =ᴮ z))
          have hC'_C : C' ≤ C := by
            dsimp [C']
            calc
              ((C ⊓ ((x.func pr₁.1 ∈ᴮ S)ᶜ) ⊓ (y.func pr₁.2 =ᴮ z)) ⊓
                (((x.func pr₂.1 ∈ᴮ S)ᶜ) ⊓ (y.func pr₂.2 =ᴮ z))) ≤
                  C ⊓ ((x.func pr₁.1 ∈ᴮ S)ᶜ) ⊓ (y.func pr₁.2 =ᴮ z) := inf_le_left
              _ ≤ C ⊓ ((x.func pr₁.1 ∈ᴮ S)ᶜ) := inf_le_left
              _ ≤ C := inf_le_left
          have hC'_v₁z : C' ≤ y.func pr₁.2 =ᴮ z := by
            dsimp [C']
            calc
              ((C ⊓ ((x.func pr₁.1 ∈ᴮ S)ᶜ) ⊓ (y.func pr₁.2 =ᴮ z)) ⊓
                (((x.func pr₂.1 ∈ᴮ S)ᶜ) ⊓ (y.func pr₂.2 =ᴮ z))) ≤
                  C ⊓ ((x.func pr₁.1 ∈ᴮ S)ᶜ) ⊓ (y.func pr₁.2 =ᴮ z) := inf_le_left
              _ ≤ y.func pr₁.2 =ᴮ z := inf_le_right
          have hC'_v₂z : C' ≤ y.func pr₂.2 =ᴮ z := by
            dsimp [C']
            calc
              ((C ⊓ ((x.func pr₁.1 ∈ᴮ S)ᶜ) ⊓ (y.func pr₁.2 =ᴮ z)) ⊓
                (((x.func pr₂.1 ∈ᴮ S)ᶜ) ⊓ (y.func pr₂.2 =ᴮ z))) ≤
                  (((x.func pr₂.1 ∈ᴮ S)ᶜ) ⊓ (y.func pr₂.2 =ᴮ z)) := inf_le_right
              _ ≤ y.func pr₂.2 =ᴮ z := inf_le_right
          have hC'_v₁_eq : C' ≤ v₁ =ᴮ y.func pr₁.2 := hC'_C.trans hv₁_eq
          have hC'_v₂_eq : C' ≤ v₂ =ᴮ y.func pr₂.2 := hC'_C.trans hv₂_eq
          have hC'_v₁_to_z : C' ≤ v₁ =ᴮ z := bv_trans hC'_v₁_eq hC'_v₁z
          have hC'_v₂_to_z : C' ≤ v₂ =ᴮ z := bv_trans hC'_v₂_eq hC'_v₂z
          exact bv_trans hC'_v₁_to_z (bv_symm hC'_v₂_to_z)
    · -- 1b: Θ ≤ is_total x y g
      unfold is_total
      apply le_iInf; intro a
      apply lattice.bv_imp_intro
      let Φ : 𝔹 := Θ ⊓ a ∈ᴮ x
      have h_split : Φ = (Φ ⊓ (a ∈ᴮ S)) ⊔ (Φ ⊓ ((a ∈ᴮ S)ᶜ)) := by
        calc
          Φ = Φ ⊓ ⊤ := by simp
          _ = Φ ⊓ (a ∈ᴮ S ⊔ (a ∈ᴮ S)ᶜ) := by simp
          _ = (Φ ⊓ (a ∈ᴮ S)) ⊔ (Φ ⊓ ((a ∈ᴮ S)ᶜ)) := by rw [inf_sup_left]
      rw [show Θ ⊓ a ∈ᴮ x = Φ by dsimp [Φ], h_split]
      apply sup_le
      · -- a ∈ S: use the original total function from S to y.
        let Φ₁ : 𝔹 := Φ ⊓ (a ∈ᴮ S)
        have h_total_f : Θ ≤ is_total S y f := is_total_of_is_func' h_func'_Θ
        have h_cases : Φ₁ ≤ ⨆ b : bSet 𝔹, b ∈ᴮ y ⊓ pair a b ∈ᴮ f := by
          unfold is_total at h_total_f
          have h_imp : Θ ≤ lattice.imp (a ∈ᴮ S)
              (⨆ b : bSet 𝔹, b ∈ᴮ y ⊓ pair a b ∈ᴮ f) :=
            h_total_f.trans (iInf_le _ a)
          have hΦ₁_Θ : Φ₁ ≤ Θ := by dsimp [Φ₁, Φ]; exact inf_le_left.trans inf_le_left
          have hΦ₁_S : Φ₁ ≤ a ∈ᴮ S := by dsimp [Φ₁]; exact inf_le_right
          exact lattice.bv_context_apply (hΦ₁_Θ.trans h_imp) hΦ₁_S
        apply (le_inf le_rfl h_cases).trans
        apply lattice.bv_cases_right
        intro b
        let Φ₂ : 𝔹 := Φ₁ ⊓ (b ∈ᴮ y ⊓ pair a b ∈ᴮ f)
        apply lattice.bv_use b
        apply le_inf
        · dsimp [Φ₂]; exact inf_le_right.trans inf_le_left
        · dsimp [g]; rw [mem_subset.mk_iff₂]
          have ha_mem_x : Φ₂ ≤ a ∈ᴮ x := by
            dsimp [Φ₂, Φ₁, Φ]; exact (inf_le_left.trans inf_le_left).trans inf_le_right
          have hb_mem_y : Φ₂ ≤ b ∈ᴮ y := by dsimp [Φ₂]; exact inf_le_right.trans inf_le_left
          have h_pair_f : Φ₂ ≤ pair a b ∈ᴮ f := by dsimp [Φ₂]; exact inf_le_right.trans inf_le_right
          rw [mem_unfold] at ha_mem_x
          apply (le_inf le_rfl ha_mem_x).trans
          apply lattice.bv_cases_right
          intro i
          let Φ₃ : 𝔹 := Φ₂ ⊓ (x.bval i ⊓ a =ᴮ x.func i)
          rw [mem_unfold] at hb_mem_y
          apply (le_inf le_rfl (inf_le_left.trans hb_mem_y)).trans
          apply lattice.bv_cases_right
          intro j
          let Φ₄ : 𝔹 := Φ₃ ⊓ (y.bval j ⊓ b =ᴮ y.func j)
          apply lattice.bv_use (i, j)
          apply le_inf
          · dsimp [Φ₄, Φ₃, bSet.prod]
            exact le_inf
              ((inf_le_left.trans inf_le_right).trans inf_le_left)
              (inf_le_right.trans inf_le_left)
          · apply le_inf
            · have ha_eq : Φ₄ ≤ a =ᴮ x.func i := by
                dsimp [Φ₄, Φ₃]; exact (inf_le_left.trans inf_le_right).trans inf_le_right
              have hb_eq : Φ₄ ≤ b =ᴮ y.func j := by
                dsimp [Φ₄]; exact inf_le_right.trans inf_le_right
              exact pair_congr ha_eq hb_eq
            · have ha_eq : Φ₄ ≤ a =ᴮ x.func i := by
                dsimp [Φ₄, Φ₃]; exact (inf_le_left.trans inf_le_right).trans inf_le_right
              have hb_eq : Φ₄ ≤ b =ᴮ y.func j := by
                dsimp [Φ₄]; exact inf_le_right.trans inf_le_right
              have h_pair_f' : Φ₄ ≤ pair a b ∈ᴮ f :=
                (inf_le_left.trans inf_le_left).trans h_pair_f
              have h_pair_eq : Φ₄ ≤ pair a b =ᴮ pair (x.func i) (y.func j) :=
                pair_congr ha_eq hb_eq
              have h_inS_a : Φ₄ ≤ a ∈ᴮ S := by
                dsimp [Φ₄, Φ₃, Φ₂, Φ₁]
                exact ((inf_le_left.trans inf_le_left).trans inf_le_left).trans inf_le_right
              have h_inS_i : Φ₄ ≤ x.func i ∈ᴮ S :=
                subst_congr_mem_left' ha_eq h_inS_a
              have h_f_i_j : Φ₄ ≤ pair (x.func i) (y.func j) ∈ᴮ f :=
                subst_congr_mem_left' h_pair_eq h_pair_f'
              exact le_trans (le_inf h_inS_i h_f_i_j)
                (le_sup_left
                  (a := (x.func i ∈ᴮ S) ⊓ (pair (x.func i) (y.func j) ∈ᴮ f))
                  (b := ((x.func i ∈ᴮ S)ᶜ) ⊓ (y.func j =ᴮ z)))
      · -- a ∉ S: use the fixed witness z.
        let Φ₁ : 𝔹 := Φ ⊓ ((a ∈ᴮ S)ᶜ)
        apply lattice.bv_use z
        apply le_inf
        · dsimp [Φ₁, Φ]; exact (inf_le_left.trans inf_le_left).trans hz_mem
        · dsimp [g]; rw [mem_subset.mk_iff₂]
          have ha_mem_x : Φ₁ ≤ a ∈ᴮ x := by dsimp [Φ₁, Φ]; exact inf_le_left.trans inf_le_right
          rw [mem_unfold] at ha_mem_x
          apply (le_inf le_rfl ha_mem_x).trans
          apply lattice.bv_cases_right
          intro i
          let Φ₂ : 𝔹 := Φ₁ ⊓ (x.bval i ⊓ a =ᴮ x.func i)
          have hz_mem_y : Φ₂ ≤ z ∈ᴮ y := by
            dsimp [Φ₂, Φ₁, Φ]; exact ((inf_le_left.trans inf_le_left).trans inf_le_left).trans hz_mem
          rw [mem_unfold] at hz_mem_y
          apply (le_inf le_rfl hz_mem_y).trans
          apply lattice.bv_cases_right
          intro j
          let Φ₃ : 𝔹 := Φ₂ ⊓ (y.bval j ⊓ z =ᴮ y.func j)
          apply lattice.bv_use (i, j)
          apply le_inf
          · dsimp [Φ₃, Φ₂, bSet.prod]
            exact le_inf
              ((inf_le_left.trans inf_le_right).trans inf_le_left)
              (inf_le_right.trans inf_le_left)
          · apply le_inf
            · have ha_eq : Φ₃ ≤ a =ᴮ x.func i := by
                dsimp [Φ₃, Φ₂]; exact (inf_le_left.trans inf_le_right).trans inf_le_right
              have hz_eq : Φ₃ ≤ z =ᴮ y.func j := by
                dsimp [Φ₃]; exact inf_le_right.trans inf_le_right
              exact pair_congr ha_eq hz_eq
            · have ha_eq : Φ₃ ≤ a =ᴮ x.func i := by
                dsimp [Φ₃, Φ₂]; exact (inf_le_left.trans inf_le_right).trans inf_le_right
              have ha_not_S : Φ₃ ≤ (a ∈ᴮ S)ᶜ := by
                dsimp [Φ₃, Φ₂, Φ₁]; exact (inf_le_left.trans inf_le_left).trans inf_le_right
              have hi_not_S : Φ₃ ≤ (x.func i ∈ᴮ S)ᶜ := by
                rw [show (x.func i ∈ᴮ S)ᶜ = lattice.imp (x.func i ∈ᴮ S) ⊥ by simp [lattice.imp]]
                apply lattice.bv_imp_intro
                have h_mem_a : Φ₃ ⊓ (x.func i ∈ᴮ S) ≤ a ∈ᴮ S :=
                  subst_congr_mem_left' (inf_le_left.trans (bv_symm ha_eq)) inf_le_right
                have h_not_a : Φ₃ ⊓ (x.func i ∈ᴮ S) ≤ (a ∈ᴮ S)ᶜ :=
                  inf_le_left.trans ha_not_S
                calc
                  Φ₃ ⊓ (x.func i ∈ᴮ S) ≤ (a ∈ᴮ S) ⊓ (a ∈ᴮ S)ᶜ := le_inf h_mem_a h_not_a
                  _ = ⊥ := by simp
              have hz_eq : Φ₃ ≤ z =ᴮ y.func j := by
                dsimp [Φ₃]; exact inf_le_right.trans inf_le_right
              exact le_trans (le_inf hi_not_S (bv_symm hz_eq))
                (le_sup_right
                  (a := (x.func i ∈ᴮ S) ⊓ (pair (x.func i) (y.func j) ∈ᴮ f))
                  (b := ((x.func i ∈ᴮ S)ᶜ) ⊓ (y.func j =ᴮ z)))
  · -- Part 2: Θ ≤ is_surj x y g
    unfold is_surj
    apply le_iInf; intro v
    apply lattice.bv_imp_intro
    let Φ : 𝔹 := Θ ⊓ v ∈ᴮ y
    have h_surj_at_v : Θ ⊓ v ∈ᴮ y ≤ ⨆ w : bSet 𝔹, w ∈ᴮ S ⊓ pair w v ∈ᴮ f := by
      unfold is_surj at h_surj_Θ
      have h_imp : Θ ≤ lattice.imp (v ∈ᴮ y)
          (⨆ w : bSet 𝔹, w ∈ᴮ S ⊓ pair w v ∈ᴮ f) :=
        h_surj_Θ.trans (iInf_le _ v)
      exact lattice.bv_context_apply (inf_le_left.trans h_imp) inf_le_right
    have h_cases : Φ ≤ ⨆ w : bSet 𝔹, w ∈ᴮ S ⊓ pair w v ∈ᴮ f := by
      dsimp [Φ]; exact h_surj_at_v
    apply (le_inf le_rfl h_cases).trans
    apply lattice.bv_cases_right
    intro w
    let Ψ : 𝔹 := Φ ⊓ (w ∈ᴮ S ⊓ pair w v ∈ᴮ f)
    apply lattice.bv_use w
    apply le_inf
    · have hwS : Ψ ≤ w ∈ᴮ S := by dsimp [Ψ]; exact inf_le_right.trans inf_le_left
      have hΨ_sub : Ψ ≤ S ⊆ᴮ x := by dsimp [Ψ, Φ]; exact (inf_le_left.trans inf_le_left).trans h_sub_Θ
      exact mem_of_mem_subset' hΨ_sub hwS
    · dsimp [g]; rw [mem_subset.mk_iff₂]
      have hwS : Ψ ≤ w ∈ᴮ S := by dsimp [Ψ]; exact inf_le_right.trans inf_le_left
      have h_pair_f : Ψ ≤ pair w v ∈ᴮ f := by dsimp [Ψ]; exact inf_le_right.trans inf_le_right
      have hwx : Ψ ≤ w ∈ᴮ x :=
        mem_of_mem_subset' (by dsimp [Ψ, Φ]; exact (inf_le_left.trans inf_le_left).trans h_sub_Θ) hwS
      have hvy : Ψ ≤ v ∈ᴮ y := by dsimp [Ψ, Φ]; exact inf_le_left.trans inf_le_right
      rw [mem_unfold] at hwx
      apply (le_inf le_rfl hwx).trans
      apply lattice.bv_cases_right
      intro i
      let Ψ₂ : 𝔹 := Ψ ⊓ (x.bval i ⊓ w =ᴮ x.func i)
      rw [mem_unfold] at hvy
      apply (le_inf le_rfl (inf_le_left.trans hvy)).trans
      apply lattice.bv_cases_right
      intro j
      let Ψ₃ : 𝔹 := Ψ₂ ⊓ (y.bval j ⊓ v =ᴮ y.func j)
      apply lattice.bv_use (i, j)
      apply le_inf
      · dsimp [Ψ₃, Ψ₂, bSet.prod]
        exact le_inf
          ((inf_le_left.trans inf_le_right).trans inf_le_left)
          (inf_le_right.trans inf_le_left)
      · apply le_inf
        · have hw_eq : Ψ₃ ≤ w =ᴮ x.func i := by
            dsimp [Ψ₃, Ψ₂]; exact (inf_le_left.trans inf_le_right).trans inf_le_right
          have hv_eq : Ψ₃ ≤ v =ᴮ y.func j := by
            dsimp [Ψ₃]; exact inf_le_right.trans inf_le_right
          exact pair_congr hw_eq hv_eq
        · have hw_eq : Ψ₃ ≤ w =ᴮ x.func i := by
            dsimp [Ψ₃, Ψ₂]; exact (inf_le_left.trans inf_le_right).trans inf_le_right
          have hv_eq : Ψ₃ ≤ v =ᴮ y.func j := by
            dsimp [Ψ₃]; exact inf_le_right.trans inf_le_right
          have h_pair_f' : Ψ₃ ≤ pair w v ∈ᴮ f :=
            (inf_le_left.trans inf_le_left).trans h_pair_f
          have h_pair_eq : Ψ₃ ≤ pair w v =ᴮ pair (x.func i) (y.func j) :=
            pair_congr hw_eq hv_eq
          have h_f_i_j : Ψ₃ ≤ pair (x.func i) (y.func j) ∈ᴮ f :=
            subst_congr_mem_left' h_pair_eq h_pair_f'
          have h_wS' : Ψ₃ ≤ w ∈ᴮ S :=
            (inf_le_left.trans inf_le_left).trans hwS
          have h_iS : Ψ₃ ≤ x.func i ∈ᴮ S :=
            subst_congr_mem_left' hw_eq h_wS'
          exact le_trans (le_inf h_iS h_f_i_j)
            (le_sup_left
              (a := (x.func i ∈ᴮ S) ⊓ (pair (x.func i) (y.func j) ∈ᴮ f))
              (b := ((x.func i ∈ᴮ S)ᶜ) ⊓ (y.func j =ᴮ z)))

lemma AE_of_check_larger_than_check {x y : pSet.{u}} {Γ : 𝔹}
    (H_nonzero : ⊥ < Γ) (H : Γ ≤ larger_than (check x) (check y))
    (H_mem : ∃ z, z ∈ y) : ∃ f : bSet 𝔹, ∀ i : (check y : bSet 𝔹).type,
    ∃ j : (check x : bSet 𝔹).type,
    ⊥ < (is_func f) ⊓ (pair ((check x : bSet 𝔹).func j) ((check y : bSet 𝔹).func i) ∈ᴮ f) := by
  have h_exists_mem : Γ ≤ exists_mem (check y) := by
    rcases H_mem with ⟨z, hz⟩
    unfold exists_mem
    apply lattice.bv_use (check z)
    exact check_mem hz
  have h_surj : Γ ≤ surjects_onto (check x) (check y) :=
    surjects_onto_of_larger_than_and_exists_mem H h_exists_mem
  exact AE_of_check_larger_than_check' H_nonzero h_surj H_mem

end cardinal_preservation

section neg_CH

local notation "ℵ₀" => (omega : bSet 𝔹)
local notation "𝔠" => (bv_powerset ℵ₀ : bSet 𝔹)
local notation "𝔹₀" => (𝔹_cohen : Type)
local notation "ℵ₀₀" => (omega : bSet 𝔹₀)
local notation "𝔠₀" => (bv_powerset ℵ₀₀ : bSet 𝔹₀)

lemma uncountable_fiber_of_card_lt {α β : Type u} (hωα : cardinal.omega ≤ Cardinal.mk α)
    (hαβ : Cardinal.mk α < Cardinal.mk β) (g : β → α) :
    ∃ ξ : α, cardinal.omega < Cardinal.mk (g ⁻¹' ({ξ} : Set α)) := by
  have hωβ : cardinal.omega ≤ Cardinal.mk β := hωα.trans hαβ.le
  rcases Cardinal.infinite_pigeonhole_card_lt g hαβ hωβ with ⟨ξ, hξ⟩
  exact ⟨ξ, lt_of_le_of_lt hωα hξ⟩

lemma not_CCC_of_uncountable_fiber (η₁ η₂ : pSet.{u})
    (H_infinite : cardinal.omega ≤ Cardinal.mk η₁.Type)
    (H_inj₂ : ∀ x y : η₂.Type, x ≠ y → ¬ PSet.Equiv (η₂.Func x) (η₂.Func y))
    (f : bSet 𝔹) (g : η₂.Type → η₁.Type)
    (H : ∀ β : η₂.Type,
      ⊥ < (is_func f) ⊓
        (pair (check (η₁.Func (g β)) : bSet 𝔹) (check (η₂.Func β) : bSet 𝔹) ∈ᴮ f))
    (H_ex : ∃ ξ : η₁.Type, cardinal.omega < Cardinal.mk (g ⁻¹' ({ξ} : Set η₁.Type))) :
    ¬ BA_CCC (𝔹 : Type u) := by
  classical
  rcases H_ex with ⟨ξ, hξ⟩
  let A : (g ⁻¹' ({ξ} : Set η₁.Type)) → 𝔹 := fun β =>
    (is_func f) ⊓
      (pair (check (η₁.Func (g β.val)) : bSet 𝔹)
        (check (η₂.Func β.val) : bSet 𝔹) ∈ᴮ f)
  have hA_nonzero : ∀ β, A β ≠ ⊥ := by
    intro β hbot
    exact (ne_of_gt (H β.val)) hbot
  have hA_anti : ∀ β₁ β₂ : (g ⁻¹' ({ξ} : Set η₁.Type)),
      β₁ ≠ β₂ → A β₁ ⊓ A β₂ = ⊥ := by
    intro β₁ β₂ hne
    apply le_antisymm ?_ bot_le
    let Γ : 𝔹 := A β₁ ⊓ A β₂
    have hValNe : β₁.val ≠ β₂.val := by
      intro hval
      exact hne (Subtype.ext hval)
    have hFunc : Γ ≤ is_func f := by
      dsimp [Γ, A]
      exact inf_le_left.trans inf_le_left
    have hMem₁ : Γ ≤
        pair (check (η₁.Func (g β₁.val)) : bSet 𝔹)
          (check (η₂.Func β₁.val) : bSet 𝔹) ∈ᴮ f := by
      dsimp [Γ, A]
      exact inf_le_left.trans inf_le_right
    have hMem₂ : Γ ≤
        pair (check (η₁.Func (g β₂.val)) : bSet 𝔹)
          (check (η₂.Func β₂.val) : bSet 𝔹) ∈ᴮ f := by
      dsimp [Γ, A]
      exact inf_le_right.trans inf_le_right
    have hg₁ : g β₁.val = ξ := by
      exact Set.mem_singleton_iff.mp (show g β₁.val ∈ ({ξ} : Set η₁.Type) from β₁.property)
    have hg₂ : g β₂.val = ξ := by
      exact Set.mem_singleton_iff.mp (show g β₂.val ∈ ({ξ} : Set η₁.Type) from β₂.property)
    have hInput :
        Γ ≤ (check (η₁.Func (g β₁.val)) : bSet 𝔹) =ᴮ
          (check (η₁.Func (g β₂.val)) : bSet 𝔹) := by
      rw [hg₁, hg₂]
      exact bv_refl
    have hOutput :
        Γ ≤ (check (η₂.Func β₁.val) : bSet 𝔹) =ᴮ
          (check (η₂.Func β₂.val) : bSet 𝔹) :=
      eq_of_is_func_of_eq hFunc hInput hMem₁ hMem₂
    have hOutputBot :
        ((check (η₂.Func β₁.val) : bSet 𝔹) =ᴮ
          (check (η₂.Func β₂.val) : bSet 𝔹)) = ⊥ :=
      check_bv_eq_bot_of_not_equiv (H_inj₂ β₁.val β₂.val hValNe)
    rwa [hOutputBot] at hOutput
  intro hCCC
  let s : Set 𝔹 := Set.range A
  have hsNonzero : ∀ a ∈ s, a ≠ ⊥ := by
    intro a ha
    rcases ha with ⟨β, rfl⟩
    exact hA_nonzero β
  have hsDisj : ∀ a ∈ s, ∀ b ∈ s, a ≠ b → a ⊓ b = ⊥ := by
    intro a ha b hb hab
    rcases ha with ⟨β₁, rfl⟩
    rcases hb with ⟨β₂, rfl⟩
    have hne : β₁ ≠ β₂ := by
      intro hβ
      exact hab (by rw [hβ])
    exact hA_anti β₁ β₂ hne
  have hsCount : s.Countable := hCCC s hsNonzero hsDisj
  have hA_inj : Set.InjOn A (Set.univ : Set (g ⁻¹' ({ξ} : Set η₁.Type))) := by
    intro β₁ _ β₂ _ hEq
    by_contra hne
    have hbot := hA_anti β₁ β₂ hne
    rw [hEq] at hbot
    have hAβ₂Bot : A β₂ = ⊥ := by simpa using hbot
    exact hA_nonzero β₂ hAβ₂Bot
  have hFiberCount : (Set.univ : Set (g ⁻¹' ({ξ} : Set η₁.Type))).Countable :=
    Set.countable_of_injective_of_countable_image hA_inj (by
      simpa [s, Set.image_univ] using hsCount)
  haveI : Countable (g ⁻¹' ({ξ} : Set η₁.Type)) :=
    Set.countable_univ_iff.mp hFiberCount
  exact not_lt_of_ge (Cardinal.mk_le_aleph0 (α := g ⁻¹' ({ξ} : Set η₁.Type))) hξ

/-- Canonicalize a member index of `ℵ₂` by its represented ordinal.  This avoids depending on
raw indices of `Ordinal.toPSet`, which may contain extensionally equal representatives. -/
noncomputable def canonAlephTwoIndex (i : pSet.aleph_two.Type) : pSet.aleph_two.Type :=
  cast (by simp [pSet.aleph_two, pSet.card_ex])
    ((pSet.mkTypeEquiv (Cardinal.ord (Cardinal.aleph 2))).symm
      (Ordinal.ToType.mk
        ⟨pSet.ordOfMemMk (η := Cardinal.ord (Cardinal.aleph 2))
          (cast (by simp [pSet.aleph_two, pSet.card_ex]) i),
         pSet.ordOfMemMk_lt _⟩))

lemma canonAlephTwoIndex_eq_of_equiv {i j : pSet.aleph_two.Type}
    (h : PSet.Equiv (pSet.aleph_two.Func i) (pSet.aleph_two.Func j)) :
    canonAlephTwoIndex i = canonAlephTwoIndex j := by
  dsimp [canonAlephTwoIndex]
  congr 3
  apply Subtype.ext
  exact pSet.ordOfMemMk_eq_of_equiv (by
    simpa [pSet.aleph_two, pSet.card_ex] using h)

lemma ordOfMemMk_eq_of_canonAlephTwoIndex_eq {i j : pSet.aleph_two.Type}
    (h : canonAlephTwoIndex i = canonAlephTwoIndex j) :
    pSet.ordOfMemMk (η := Cardinal.ord (Cardinal.aleph 2))
        (cast (by simp [pSet.aleph_two, pSet.card_ex]) i) =
      pSet.ordOfMemMk (η := Cardinal.ord (Cardinal.aleph 2))
        (cast (by simp [pSet.aleph_two, pSet.card_ex]) j) := by
  have hToType := congrArg (fun x : pSet.aleph_two.Type =>
      (pSet.mkTypeEquiv (Cardinal.ord (Cardinal.aleph 2)))
        (cast (by simp [pSet.aleph_two, pSet.card_ex]) x)) h
  dsimp [canonAlephTwoIndex] at hToType
  have hIio := congrArg (Ordinal.ToType.mk (o := Cardinal.ord (Cardinal.aleph 2))).symm hToType
  simpa using (Subtype.ext_iff.mp hIio)

lemma alephTwo_func_equiv_of_canonAlephTwoIndex_eq {i j : pSet.aleph_two.Type}
    (h : canonAlephTwoIndex i = canonAlephTwoIndex j) :
    PSet.Equiv (pSet.aleph_two.Func i) (pSet.aleph_two.Func j) := by
  let i' : (ordinal.mk (Cardinal.ord (Cardinal.aleph 2))).Type :=
    cast (by simp [pSet.aleph_two, pSet.card_ex]) i
  let j' : (ordinal.mk (Cardinal.ord (Cardinal.aleph 2))).Type :=
    cast (by simp [pSet.aleph_two, pSet.card_ex]) j
  have hOrd :
      pSet.ordOfMemMk i' = pSet.ordOfMemMk j' := by
    dsimp [i', j']
    exact ordOfMemMk_eq_of_canonAlephTwoIndex_eq h
  have hi : PSet.Equiv (pSet.aleph_two.Func i) (ordinal.mk (pSet.ordOfMemMk i')) := by
    simpa [pSet.aleph_two, pSet.card_ex, i'] using
      pSet.func_equiv_ordOfMemMk (η := Cardinal.ord (Cardinal.aleph 2)) (i := i')
  have hj : PSet.Equiv (pSet.aleph_two.Func j) (ordinal.mk (pSet.ordOfMemMk j')) := by
    simpa [pSet.aleph_two, pSet.card_ex, j'] using
      pSet.func_equiv_ordOfMemMk (η := Cardinal.ord (Cardinal.aleph 2)) (i := j')
  exact hi.trans ((pSet.mk_equiv_of_eq hOrd).trans hj.symm)

noncomputable def neg_CH_func : bSet 𝔹₀ :=
  bSet.function.mk' (x := (check pSet.aleph_two : bSet 𝔹₀)) (y := 𝔠₀)
    (fun i : (check pSet.aleph_two : bSet 𝔹₀).type =>
      fun n : (omega : bSet 𝔹₀).type =>
        cohen_real.χ (canonAlephTwoIndex (check_cast i)) n.down)
    (fun _ => ⊤)

theorem ℵ₂_le_𝔠 {Γ : 𝔹₀} :
    Γ ≤ is_func' (check pSet.aleph_two : bSet 𝔹₀) 𝔠₀ neg_CH_func ⊓ is_inj neg_CH_func := by
  refine le_inf ?_ ?_
  · exact is_func'_of_is_function
      (bSet.function.mk'_is_function
        (x := (check pSet.aleph_two : bSet 𝔹₀)) (y := 𝔠₀)
        (fun i : (check pSet.aleph_two : bSet 𝔹₀).type =>
          fun n : (omega : bSet 𝔹₀).type =>
            cohen_real.χ (canonAlephTwoIndex (check_cast i)) n.down)
        (fun _ => ⊤)
        (by
          intro i j Γ' hEq
          by_cases hEquiv : PSet.Equiv (pSet.aleph_two.Func (check_cast i))
              (pSet.aleph_two.Func (check_cast j))
          · have hCanon : canonAlephTwoIndex (check_cast i) =
                canonAlephTwoIndex (check_cast j) :=
              canonAlephTwoIndex_eq_of_equiv hEquiv
            change Γ' ≤ cohen_real.mk (canonAlephTwoIndex (check_cast i)) =ᴮ
              cohen_real.mk (canonAlephTwoIndex (check_cast j))
            rw [hCanon]
            exact bv_refl
          · have hBot :
                ((check pSet.aleph_two : bSet 𝔹₀).func i =ᴮ
                  (check pSet.aleph_two : bSet 𝔹₀).func j) = ⊥ := by
              rw [check_func, check_func]
              exact check_bv_eq_bot_of_not_equiv hEquiv
            rw [hBot] at hEq
            exact hEq.trans bot_le)
        (by
          intro i Γ' hVal
          exact ⟨le_top, le_top⟩))
  · exact bSet.function.mk'_is_inj
      (x := (check pSet.aleph_two : bSet 𝔹₀)) (y := 𝔠₀)
      (fun i : (check pSet.aleph_two : bSet 𝔹₀).type =>
        fun n : (omega : bSet 𝔹₀).type =>
          cohen_real.χ (canonAlephTwoIndex (check_cast i)) n.down)
      (fun _ => ⊤)
      (by
        intro i j Γ' hEq
        by_cases hCanon : canonAlephTwoIndex (check_cast i) =
            canonAlephTwoIndex (check_cast j)
        · rw [check_func, check_func]
          exact check_eq (alephTwo_func_equiv_of_canonAlephTwoIndex_eq hCanon)
        · apply lattice.bv_exfalso
          change Γ' ≤ cohen_real.mk (canonAlephTwoIndex (check_cast i)) =ᴮ
            cohen_real.mk (canonAlephTwoIndex (check_cast j)) at hEq
          exact hEq.trans (cohen_real.inj hCanon))

theorem ℵ₂_injects_𝔠 {Γ : 𝔹₀} :
    Γ ≤ injects_into (check pSet.aleph_two : bSet 𝔹₀) 𝔠₀ := by
  unfold injects_into
  exact le_iSup_of_le neg_CH_func ℵ₂_le_𝔠

lemma larger_than_omega_aleph_one_compl {Γ : 𝔹₀} :
    Γ ≤ (larger_than (omega : bSet 𝔹₀) (check pSet.aleph_one : bSet 𝔹₀))ᶜ := by
  rw [le_compl_iff_disjoint_right, disjoint_iff]
  apply le_antisymm ?_ bot_le
  let Δ : 𝔹₀ := Γ ⊓ larger_than (omega : bSet 𝔹₀) (check pSet.aleph_one : bSet 𝔹₀)
  by_contra h_not_bot
  have h_nonzero : ⊥ < Δ := by
    refine Ne.bot_lt ?_
    intro h_eq
    apply h_not_bot
    exact le_of_eq h_eq
  have h_larger : Δ ≤ larger_than (omega : bSet 𝔹₀) (check pSet.aleph_one : bSet 𝔹₀) := inf_le_right
  have h_mem : ∃ z, z ∈ pSet.aleph_one := by
    simpa [pSet.aleph_one] using pSet.exists_mem_of_regular pSet.is_regular_aleph_one
  rcases AE_of_check_larger_than_check h_nonzero h_larger h_mem with ⟨f, hf⟩
  classical
    let g : pSet.aleph_one.Type → PSet.omega.Type := fun i =>
      cast check_type (Classical.choose (hf (cast check_type.symm i)))
    have hg : ∀ i : pSet.aleph_one.Type,
        ⊥ < (is_func f) ⊓ (pair (check (PSet.omega.Func (g i) : pSet))
          (check (pSet.aleph_one.Func i : pSet)) ∈ᴮ f) := by
      intro i
      let i' : (check pSet.aleph_one : bSet 𝔹₀).type := cast check_type.symm i
      have h_spec := Classical.choose_spec (hf i')
      simpa [g, i'] using h_spec
    have hCard : Cardinal.mk PSet.omega.Type < Cardinal.mk pSet.aleph_one.Type := by
      rw [pSet.mk_omega_eq]
      simpa [pSet.aleph_one] using pSet.omega_lt_aleph_one
    have hInfinite : cardinal.omega ≤ Cardinal.mk PSet.omega.Type := by
      rw [pSet.mk_omega_eq]
    rcases uncountable_fiber_of_card_lt hInfinite hCard g with ⟨ξ, hξ⟩
    have hExt : ∀ (i j : pSet.aleph_one.Type), i ≠ j →
        ¬ PSet.Equiv (pSet.aleph_one.Func i) (pSet.aleph_one.Func j) := by
      intro i j hne hequiv
      apply hne
      clear hne
      revert hequiv
      revert i j
      dsimp [pSet.aleph_one, pSet.card_ex, ordinal.mk]
      rw [Ordinal.toPSet.eq_1 (Cardinal.ord (Cardinal.aleph 1))]
      intro i j h
      apply Ordinal.ToType.mk.symm.injective
      apply Subtype.ext
      exact ordinal.mk_inj h
    have h_noCCC : ¬ BA_CCC 𝔹₀ :=
      not_CCC_of_uncountable_fiber PSet.omega pSet.aleph_one hInfinite hExt f g hg ⟨ξ, hξ⟩
    exact h_noCCC 𝔹_CCC

lemma larger_than_aleph_one_aleph_two_compl {Γ : 𝔹₀} :
    Γ ≤ (larger_than (check pSet.aleph_one : bSet 𝔹₀) (check pSet.aleph_two : bSet 𝔹₀))ᶜ := by
  rw [le_compl_iff_disjoint_right, disjoint_iff]
  apply le_antisymm ?_ bot_le
  let Δ : 𝔹₀ := Γ ⊓ larger_than (check pSet.aleph_one : bSet 𝔹₀) (check pSet.aleph_two : bSet 𝔹₀)
  by_contra h_not_bot
  have h_nonzero : ⊥ < Δ := by
    refine Ne.bot_lt ?_
    intro h_eq
    apply h_not_bot
    exact le_of_eq h_eq
  have h_larger : Δ ≤ larger_than (check pSet.aleph_one : bSet 𝔹₀) (check pSet.aleph_two : bSet 𝔹₀) := inf_le_right
  have h_mem : ∃ z, z ∈ pSet.aleph_two := by
    simpa [pSet.aleph_two] using pSet.exists_mem_of_regular pSet.is_regular_aleph_two
  rcases AE_of_check_larger_than_check h_nonzero h_larger h_mem with ⟨f, hf⟩
  classical
    let g : pSet.aleph_two.Type → pSet.aleph_one.Type := fun i =>
      cast check_type (Classical.choose (hf (cast check_type.symm i)))
    have hg : ∀ i : pSet.aleph_two.Type,
        ⊥ < (is_func f) ⊓ (pair (check (pSet.aleph_one.Func (g i) : pSet))
          (check (pSet.aleph_two.Func i : pSet)) ∈ᴮ f) := by
      intro i
      let i' : (check pSet.aleph_two : bSet 𝔹₀).type := cast check_type.symm i
      have h_spec := Classical.choose_spec (hf i')
      simpa [g, i'] using h_spec
    have hCard : Cardinal.mk pSet.aleph_one.Type < Cardinal.mk pSet.aleph_two.Type := by
      simpa [pSet.aleph_one, pSet.aleph_two] using pSet.aleph_one_lt_aleph_two
    have hInfinite : cardinal.omega ≤ Cardinal.mk pSet.aleph_one.Type := by
      simpa [pSet.aleph_one] using pSet.omega_lt_aleph_one.le
    rcases uncountable_fiber_of_card_lt hInfinite hCard g with ⟨ξ, hξ⟩
    have hExt : ∀ (i j : pSet.aleph_two.Type), i ≠ j →
        ¬ PSet.Equiv (pSet.aleph_two.Func i) (pSet.aleph_two.Func j) := by
      intro i j hne hequiv
      apply hne
      clear hne
      revert hequiv
      revert i j
      dsimp [pSet.aleph_two, pSet.card_ex, ordinal.mk]
      rw [Ordinal.toPSet.eq_1 (Cardinal.ord (Cardinal.aleph 2))]
      intro i j h
      apply Ordinal.ToType.mk.symm.injective
      apply Subtype.ext
      exact ordinal.mk_inj h
    have h_noCCC : ¬ BA_CCC 𝔹₀ :=
      not_CCC_of_uncountable_fiber pSet.aleph_one pSet.aleph_two hInfinite hExt f g hg ⟨ξ, hξ⟩
    exact h_noCCC 𝔹_CCC

theorem not_CH₂ {Γ : 𝔹₀} : Γ ≤ CH₂ᶜ := by
  dsimp [CH₂]
  simp
  apply le_iSup_of_le (check pSet.aleph_one : bSet 𝔹₀)
  refine le_inf ?_ ?_
  · refine le_inf ?_ ?_
    · exact check_Ord pSet.aleph_one_Ord
    · exact larger_than_omega_aleph_one_compl
  · exact not_larger_of_not_larger_and_injects larger_than_aleph_one_aleph_two_compl ℵ₂_injects_𝔠

end neg_CH

end Flypitch
