import Flypitch.BVM

universe u v

namespace Flypitch

/-!
Initial compatibility layer for upstream `bvm_extras.lean`.

This file starts with the small singleton and binary-intersection API used by the
later Boolean-valued well-ordering and `aleph_one` construction.
-/

set_option linter.missingDocs false
set_option linter.style.longLine false

namespace bSet

variable {𝔹 : Type u} [CompleteBooleanAlgebra 𝔹]

local infix:65 " ⟹ " => lattice.imp

instance instSingleton : Singleton (bSet 𝔹) (bSet 𝔹) :=
  ⟨fun x => insert x (∅ : bSet 𝔹)⟩

@[simp] theorem insert1_bval_none {u v : bSet 𝔹} :
    (bSet.insert1 u ({v} : bSet 𝔹)).bval none = ⊤ := rfl

@[simp] theorem insert1_bval_some {u v : bSet 𝔹} {i : ({v} : bSet 𝔹).type} :
    (bSet.insert1 u ({v} : bSet 𝔹)).bval (some i) = ({v} : bSet 𝔹).bval i := rfl

@[simp] theorem insert1_func_none {u v : bSet 𝔹} :
    (bSet.insert1 u ({v} : bSet 𝔹)).func none = u := rfl

@[simp] theorem insert1_func_some {u v : bSet 𝔹} {i : ({v} : bSet 𝔹).type} :
    (bSet.insert1 u ({v} : bSet 𝔹)).func (some i) = ({v} : bSet 𝔹).func i := rfl

theorem mem_singleton {x : bSet 𝔹} {Γ : 𝔹} : Γ ≤ x ∈ᴮ ({x} : bSet 𝔹) := by
  change Γ ≤ x ∈ᴮ insert x (∅ : bSet 𝔹)
  exact mem_insert_self

theorem eq_of_mem_singleton' {x y : bSet 𝔹} :
    y ∈ᴮ ({x} : bSet 𝔹) ≤ x =ᴮ y := by
  change y ∈ᴮ insert x (∅ : bSet 𝔹) ≤ x =ᴮ y
  rw [mem_insert_empty]
  exact le_of_eq bv_eq_symm

theorem eq_of_mem_singleton {x y : bSet 𝔹} {Γ : 𝔹}
    (h : Γ ≤ y ∈ᴮ ({x} : bSet 𝔹)) : Γ ≤ x =ᴮ y :=
  h.trans eq_of_mem_singleton'

theorem eq_mem_singleton {x y : bSet 𝔹} {Γ : 𝔹}
    (h : Γ ≤ y ∈ᴮ ({x} : bSet 𝔹)) : Γ ≤ y =ᴮ x :=
  bv_symm (eq_of_mem_singleton h)

theorem mem_singleton_of_eq {x y : bSet 𝔹} {Γ : 𝔹}
    (h : Γ ≤ x =ᴮ y) : Γ ≤ y ∈ᴮ ({x} : bSet 𝔹) := by
  change Γ ≤ y ∈ᴮ insert x (∅ : bSet 𝔹)
  exact mem_insert_of_eq (bv_symm h)

theorem eq_of_eq_singleton {x y : bSet 𝔹} {Γ : 𝔹}
    (h : Γ ≤ ({x} : bSet 𝔹) =ᴮ ({y} : bSet 𝔹)) : Γ ≤ x =ᴮ y := by
  have hxMem : Γ ≤ x ∈ᴮ ({x} : bSet 𝔹) := mem_singleton
  have hxMemY : Γ ≤ x ∈ᴮ ({y} : bSet 𝔹) :=
    subst_congr_mem_right' h hxMem
  exact bv_symm (eq_of_mem_singleton hxMemY)

theorem singleton_congr {x y : bSet 𝔹} {Γ : 𝔹}
    (h : Γ ≤ x =ᴮ y) : Γ ≤ ({x} : bSet 𝔹) =ᴮ ({y} : bSet 𝔹) := by
  apply subset_ext
  · change Γ ≤ insert x (∅ : bSet 𝔹) ⊆ᴮ insert y (∅ : bSet 𝔹)
    exact insert_empty_subset_iff.mpr (mem_singleton_of_eq (bv_symm h))
  · change Γ ≤ insert y (∅ : bSet 𝔹) ⊆ᴮ insert x (∅ : bSet 𝔹)
    exact insert_empty_subset_iff.mpr (mem_singleton_of_eq h)

theorem insert1_congr_left {x z y : bSet 𝔹} {Γ : 𝔹}
    (h : Γ ≤ x =ᴮ z) : Γ ≤ insert x y =ᴮ insert z y := by
  apply subset_ext
  · rw [insert_subset_iff]
    exact ⟨mem_insert_of_eq (x := x) (y := z) (z := y) h, subset_insert⟩
  · rw [insert_subset_iff]
    exact ⟨mem_insert_of_eq (x := z) (y := x) (z := y) (bv_symm h), subset_insert⟩

theorem insert1_congr_right {x y z : bSet 𝔹} {Γ : 𝔹}
    (h : Γ ≤ y =ᴮ z) : Γ ≤ insert x y =ᴮ insert x z := by
  apply subset_ext
  · rw [insert_subset_iff]
    exact ⟨mem_insert_self, subst_congr_subset_left' (bv_symm h) subset_insert⟩
  · rw [insert_subset_iff]
    exact ⟨mem_insert_self, subst_congr_subset_left' h subset_insert⟩

theorem insert1_congr {x z y w : bSet 𝔹} {Γ : 𝔹}
    (hx : Γ ≤ x =ᴮ z) (hy : Γ ≤ y =ᴮ w) :
    Γ ≤ insert x y =ᴮ insert z w :=
  bv_trans (insert1_congr_left hx) (insert1_congr_right hy)

/-- Binary intersection of Boolean-valued sets. -/
def binary_inter (x y : bSet 𝔹) : bSet 𝔹 :=
  mk x.type x.func (fun i => x.bval i ⊓ x.func i ∈ᴮ y)

@[simp] theorem binary_inter_type {x y : bSet 𝔹} :
    (binary_inter x y).type = x.type := rfl

@[simp] theorem binary_inter_func {x y : bSet 𝔹} {i : (binary_inter x y).type} :
    (binary_inter x y).func i = x.func i := rfl

@[simp] theorem binary_inter_bval {x y : bSet 𝔹} {i : x.type} :
    (binary_inter x y).bval i = x.bval i ⊓ x.func i ∈ᴮ y := rfl

theorem mem_binary_inter_iff {x y z : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ z ∈ᴮ binary_inter x y ↔ Γ ≤ z ∈ᴮ x ∧ Γ ≤ z ∈ᴮ y := by
  constructor
  · intro hz
    rw [mem_unfold] at hz
    constructor
    · apply (le_inf le_rfl hz).trans
      apply lattice.bv_cases_right
      intro i
      let Δ : 𝔹 := Γ ⊓ ((binary_inter x y).bval i ⊓ z =ᴮ (binary_inter x y).func i)
      change Δ ≤ z ∈ᴮ x
      have hmem : Δ ≤ x.func i ∈ᴮ x := by
        apply mem.mk''
        dsimp [Δ, binary_inter]
        exact inf_le_right.trans inf_le_left |>.trans inf_le_left
      have heq : Δ ≤ z =ᴮ x.func i := by
        dsimp [Δ, binary_inter]
        exact inf_le_right.trans inf_le_right
      exact subst_congr_mem_left' (bv_symm heq) hmem
    · apply (le_inf le_rfl hz).trans
      apply lattice.bv_cases_right
      intro i
      let Δ : 𝔹 := Γ ⊓ ((binary_inter x y).bval i ⊓ z =ᴮ (binary_inter x y).func i)
      change Δ ≤ z ∈ᴮ y
      have hmem : Δ ≤ x.func i ∈ᴮ y := by
        dsimp [Δ, binary_inter]
        exact inf_le_right.trans inf_le_left |>.trans inf_le_right
      have heq : Δ ≤ z =ᴮ x.func i := by
        dsimp [Δ, binary_inter]
        exact inf_le_right.trans inf_le_right
      exact subst_congr_mem_left' (bv_symm heq) hmem
  · rintro ⟨hzx, hzy⟩
    rw [mem_unfold] at hzx ⊢
    apply (le_inf le_rfl hzx).trans
    apply lattice.bv_cases_right
    intro i
    let Δ : 𝔹 := Γ ⊓ (x.bval i ⊓ z =ᴮ x.func i)
    change Δ ≤ z ∈ᴮ binary_inter x y
    have hmem : Δ ≤ (binary_inter x y).func i ∈ᴮ binary_inter x y := by
      apply mem.mk''
      apply le_inf
      · dsimp [Δ, binary_inter]
        exact inf_le_right.trans inf_le_left
      · have heq : Δ ≤ z =ᴮ x.func i := by
          dsimp [Δ]
          exact inf_le_right.trans inf_le_right
        exact subst_congr_mem_left' heq (inf_le_left.trans hzy)
    have heq : Δ ≤ z =ᴮ (binary_inter x y).func i := by
      dsimp [Δ, binary_inter]
      exact inf_le_right.trans inf_le_right
    exact subst_congr_mem_left' (bv_symm heq) hmem

theorem subset_binary_inter_iff {x y z : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ z ⊆ᴮ binary_inter x y ↔ Γ ≤ z ⊆ᴮ x ∧ Γ ≤ z ⊆ᴮ y := by
  constructor
  · intro hz
    constructor
    · apply subset_intro
      intro i
      exact (mem_binary_inter_iff.mp (subset_elim hz i)).1
    · apply subset_intro
      intro i
      exact (mem_binary_inter_iff.mp (subset_elim hz i)).2
  · rintro ⟨hzx, hzy⟩
    apply subset_intro
    intro i
    exact mem_binary_inter_iff.mpr ⟨subset_elim hzx i, subset_elim hzy i⟩

theorem binary_inter_subset_left {x y : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ binary_inter x y ⊆ᴮ x := by
  apply subset_intro
  intro i
  apply mem.mk''
  exact inf_le_right.trans inf_le_left

theorem binary_inter_subset_right {x y : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ binary_inter x y ⊆ᴮ y := by
  apply subset_intro
  intro i
  exact inf_le_right.trans inf_le_right

theorem binary_inter_symm {x y : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ binary_inter x y =ᴮ binary_inter y x := by
  apply mem_ext
  · apply le_iInf
    intro z
    apply lattice.bv_imp_intro
    exact mem_binary_inter_iff.mpr
      ⟨(mem_binary_inter_iff.mp inf_le_right).2,
        (mem_binary_inter_iff.mp inf_le_right).1⟩
  · apply le_iInf
    intro z
    apply lattice.bv_imp_intro
    exact mem_binary_inter_iff.mpr
      ⟨(mem_binary_inter_iff.mp inf_le_right).2,
        (mem_binary_inter_iff.mp inf_le_right).1⟩

theorem B_congr_binary_inter_left (z : bSet 𝔹) :
    B_congr (fun x : bSet 𝔹 => binary_inter x z) := by
  intro x y
  apply mem_ext
  · apply le_iInf
    intro w
    apply lattice.bv_imp_intro
    have hmem :
        (x =ᴮ y ⊓ w ∈ᴮ binary_inter x z) ≤ w ∈ᴮ binary_inter x z :=
      inf_le_right
    have hmem := mem_binary_inter_iff.mp hmem
    exact mem_binary_inter_iff.mpr
      ⟨subst_congr_mem_right' inf_le_left hmem.1, hmem.2⟩
  · apply le_iInf
    intro w
    apply lattice.bv_imp_intro
    have hmem :
        (x =ᴮ y ⊓ w ∈ᴮ binary_inter y z) ≤ w ∈ᴮ binary_inter y z :=
      inf_le_right
    have hmem := mem_binary_inter_iff.mp hmem
    exact mem_binary_inter_iff.mpr
      ⟨subst_congr_mem_right' (bv_symm inf_le_left) hmem.1, hmem.2⟩

theorem B_congr_binary_inter_right (x : bSet 𝔹) :
    B_congr (fun y : bSet 𝔹 => binary_inter x y) := by
  intro y z
  apply mem_ext
  · apply le_iInf
    intro w
    apply lattice.bv_imp_intro
    have hmem :
        (y =ᴮ z ⊓ w ∈ᴮ binary_inter x y) ≤ w ∈ᴮ binary_inter x y :=
      inf_le_right
    have hmem := mem_binary_inter_iff.mp hmem
    exact mem_binary_inter_iff.mpr
      ⟨hmem.1, subst_congr_mem_right' inf_le_left hmem.2⟩
  · apply le_iInf
    intro w
    apply lattice.bv_imp_intro
    have hmem :
        (y =ᴮ z ⊓ w ∈ᴮ binary_inter x z) ≤ w ∈ᴮ binary_inter x z :=
      inf_le_right
    have hmem := mem_binary_inter_iff.mp hmem
    exact mem_binary_inter_iff.mpr
      ⟨hmem.1, subst_congr_mem_right' (bv_symm inf_le_left) hmem.2⟩

/-- Binary union as the union of an unordered pair. -/
def binary_union (x y : bSet 𝔹) : bSet 𝔹 :=
  bv_union ({x, y} : bSet 𝔹)

theorem unordered_pair_symm (x y : bSet 𝔹) {Γ : 𝔹} :
    Γ ≤ ({x, y} : bSet 𝔹) =ᴮ ({y, x} : bSet 𝔹) := by
  apply subset_ext
  · change Γ ≤ insert x ({y} : bSet 𝔹) ⊆ᴮ insert y ({x} : bSet 𝔹)
    rw [insert_subset_iff]
    constructor
    · exact mem_insert_of_mem mem_singleton
    · change Γ ≤ insert y (∅ : bSet 𝔹) ⊆ᴮ insert y ({x} : bSet 𝔹)
      exact insert_empty_subset_iff.mpr mem_insert_self
  · change Γ ≤ insert y ({x} : bSet 𝔹) ⊆ᴮ insert x ({y} : bSet 𝔹)
    rw [insert_subset_iff]
    constructor
    · exact mem_insert_of_mem mem_singleton
    · change Γ ≤ insert x (∅ : bSet 𝔹) ⊆ᴮ insert x ({y} : bSet 𝔹)
      exact insert_empty_subset_iff.mpr mem_insert_self

theorem insert1_symm (x y : bSet 𝔹) {Γ : 𝔹} :
    Γ ≤ bSet.insert1 x ({y} : bSet 𝔹) =ᴮ bSet.insert1 y ({x} : bSet 𝔹) := by
  change Γ ≤ ({x, y} : bSet 𝔹) =ᴮ ({y, x} : bSet 𝔹)
  exact unordered_pair_symm x y

theorem eq_inserted_of_eq_singleton {x y z : bSet 𝔹} :
    ({x} : bSet 𝔹) =ᴮ bSet.insert1 y ({z} : bSet 𝔹) ≤ x =ᴮ y := by
  let Γ : 𝔹 := ({x} : bSet 𝔹) =ᴮ bSet.insert1 y ({z} : bSet 𝔹)
  have h : Γ ≤ ({x} : bSet 𝔹) =ᴮ bSet.insert1 y ({z} : bSet 𝔹) := le_rfl
  have hyMem : Γ ≤ y ∈ᴮ bSet.insert1 y ({z} : bSet 𝔹) := mem_insert_self
  have hyMemX : Γ ≤ y ∈ᴮ ({x} : bSet 𝔹) :=
    subst_congr_mem_right' (bv_symm h) hyMem
  exact eq_of_mem_singleton hyMemX

theorem eq_inserted_of_eq_singleton' {x y z : bSet 𝔹} :
    ({x} : bSet 𝔹) =ᴮ bSet.insert1 y ({z} : bSet 𝔹) ≤ x =ᴮ z := by
  let Γ : 𝔹 := ({x} : bSet 𝔹) =ᴮ bSet.insert1 y ({z} : bSet 𝔹)
  have h : Γ ≤ ({x} : bSet 𝔹) =ᴮ bSet.insert1 y ({z} : bSet 𝔹) := le_rfl
  have hzMem : Γ ≤ z ∈ᴮ bSet.insert1 y ({z} : bSet 𝔹) :=
    mem_insert_of_mem mem_singleton
  have hzMemX : Γ ≤ z ∈ᴮ ({x} : bSet 𝔹) :=
    subst_congr_mem_right' (bv_symm h) hzMem
  exact eq_of_mem_singleton hzMemX

theorem inserted_eq_of_insert_eq {y v w : bSet 𝔹} :
    ({v, y} : bSet 𝔹) =ᴮ ({v, w} : bSet 𝔹) ≤ y =ᴮ w := by
  let Γ : 𝔹 := ({v, y} : bSet 𝔹) =ᴮ ({v, w} : bSet 𝔹)
  have h : Γ ≤ ({v, y} : bSet 𝔹) =ᴮ ({v, w} : bSet 𝔹) := le_rfl
  have hyMemLeft : Γ ≤ y ∈ᴮ ({v, y} : bSet 𝔹) :=
    mem_insert_of_mem mem_singleton
  have hyMemRight : Γ ≤ y ∈ᴮ ({v, w} : bSet 𝔹) :=
    subst_congr_mem_right' h hyMemLeft
  rw [mem_insert1] at hyMemRight
  apply (le_inf le_rfl hyMemRight).trans
  apply lattice.bv_or_elim_right
  · let Δ : 𝔹 := Γ ⊓ y =ᴮ v
    change Δ ≤ y =ᴮ w
    have hyv : Δ ≤ y =ᴮ v := by
      dsimp [Δ]
      exact inf_le_right
    have hEq : Δ ≤ ({v, y} : bSet 𝔹) =ᴮ ({v, w} : bSet 𝔹) := by
      dsimp [Δ]
      exact inf_le_left.trans h
    have hwMemRight : Δ ≤ w ∈ᴮ ({v, w} : bSet 𝔹) :=
      mem_insert_of_mem mem_singleton
    have hwMemLeft : Δ ≤ w ∈ᴮ ({v, y} : bSet 𝔹) :=
      subst_congr_mem_right' (bv_symm hEq) hwMemRight
    rw [mem_insert1] at hwMemLeft
    apply (le_inf le_rfl hwMemLeft).trans
    apply lattice.bv_or_elim_right
    · have hyv' : Δ ⊓ w =ᴮ v ≤ y =ᴮ v := inf_le_left.trans hyv
      have hwv : Δ ⊓ w =ᴮ v ≤ w =ᴮ v := inf_le_right
      exact bv_trans hyv' (bv_symm hwv)
    · exact eq_of_mem_singleton inf_le_right
  · exact eq_mem_singleton inf_le_right

theorem binary_union_symm {x y : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ binary_union x y =ᴮ binary_union y x :=
  (unordered_pair_symm x y).trans
    (B_congr_bv_union ({x, y} : bSet 𝔹) ({y, x} : bSet 𝔹))

theorem B_congr_binary_union_left (y : bSet 𝔹) :
    B_congr (fun x : bSet 𝔹 => binary_union x y) := by
  intro x z
  have hpair : x =ᴮ z ≤ ({x, y} : bSet 𝔹) =ᴮ ({z, y} : bSet 𝔹) := by
    change x =ᴮ z ≤ insert x ({y} : bSet 𝔹) =ᴮ insert z ({y} : bSet 𝔹)
    exact insert1_congr_left (Γ := x =ᴮ z) le_rfl
  exact hpair.trans (B_congr_bv_union ({x, y} : bSet 𝔹) ({z, y} : bSet 𝔹))

theorem B_congr_binary_union_right (x : bSet 𝔹) :
    B_congr (fun y : bSet 𝔹 => binary_union x y) := by
  intro y z
  have hpair : y =ᴮ z ≤ ({x, y} : bSet 𝔹) =ᴮ ({x, z} : bSet 𝔹) := by
    change y =ᴮ z ≤ insert x ({y} : bSet 𝔹) =ᴮ insert x ({z} : bSet 𝔹)
    exact insert1_congr_right (Γ := y =ᴮ z) (singleton_congr le_rfl)
  exact hpair.trans (B_congr_bv_union ({x, y} : bSet 𝔹) ({x, z} : bSet 𝔹))

theorem binary_union_congr {x₁ x₂ y₁ y₂ : bSet 𝔹} {Γ : 𝔹}
    (hx : Γ ≤ x₁ =ᴮ x₂) (hy : Γ ≤ y₁ =ᴮ y₂) :
    Γ ≤ binary_union x₁ y₁ =ᴮ binary_union x₂ y₂ :=
  bv_trans (hx.trans (B_congr_binary_union_left y₁ x₁ x₂))
    (hy.trans (B_congr_binary_union_right x₂ y₁ y₂))

theorem B_ext_binary_union_left {φ : bSet 𝔹 → 𝔹} (hφ : B_ext φ) (y : bSet 𝔹) :
    B_ext (fun x : bSet 𝔹 => φ (binary_union x y)) := by
  intro x z
  have hUnion : x =ᴮ z ≤ binary_union x y =ᴮ binary_union z y :=
    B_congr_binary_union_left y x z
  exact (le_inf (inf_le_left.trans hUnion) inf_le_right).trans
    (hφ (binary_union x y) (binary_union z y))

theorem B_ext_binary_union_right {φ : bSet 𝔹 → 𝔹} (hφ : B_ext φ) (x : bSet 𝔹) :
    B_ext (fun y : bSet 𝔹 => φ (binary_union x y)) := by
  intro y z
  have hUnion : y =ᴮ z ≤ binary_union x y =ᴮ binary_union x z :=
    B_congr_binary_union_right x y z
  exact (le_inf (inf_le_left.trans hUnion) inf_le_right).trans
    (hφ (binary_union x y) (binary_union x z))

/-- Boolean-valued successor, used for von Neumann-style ordinals. -/
def succ (x : bSet 𝔹) : bSet 𝔹 :=
  insert x x

theorem subset_succ {x : bSet 𝔹} {Γ : 𝔹} : Γ ≤ x ⊆ᴮ succ x := by
  apply subset_intro
  intro i
  change Γ ⊓ x.bval i ≤ x.func i ∈ᴮ insert x x
  exact mem_insert_of_mem (mem.mk'' inf_le_right)

theorem succ_eq_binary_union {x : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ succ x =ᴮ binary_union ({x} : bSet 𝔹) x := by
  apply subset_ext
  · change Γ ≤ insert x x ⊆ᴮ binary_union ({x} : bSet 𝔹) x
    apply insert_subset
    · rw [binary_union, mem_bv_union_iff]
      apply lattice.bv_use ({x} : bSet 𝔹)
      exact le_inf mem_insert_self mem_singleton
    · apply subset_intro
      intro i
      change Γ ⊓ x.bval i ≤ x.func i ∈ᴮ binary_union ({x} : bSet 𝔹) x
      rw [binary_union, mem_bv_union_iff]
      apply lattice.bv_use x
      exact le_inf (mem_insert_of_mem mem_singleton) (mem.mk'' inf_le_right)
  · rw [subset_unfold']
    apply le_iInf
    intro z
    apply lattice.bv_imp_intro
    let Δ : 𝔹 := Γ ⊓ z ∈ᴮ binary_union ({x} : bSet 𝔹) x
    change Δ ≤ z ∈ᴮ succ x
    have hCases :
        Δ ≤ ⨆ y : bSet 𝔹,
          y ∈ᴮ ({({x} : bSet 𝔹), x} : bSet 𝔹) ⊓ z ∈ᴮ y := by
      exact (mem_bv_union_iff
        (x := ({({x} : bSet 𝔹), x} : bSet 𝔹)) (z := z)).mp inf_le_right
    apply (le_inf le_rfl hCases).trans
    apply lattice.bv_cases_right
    intro y
    let Θ : 𝔹 :=
      Δ ⊓ (y ∈ᴮ ({({x} : bSet 𝔹), x} : bSet 𝔹) ⊓ z ∈ᴮ y)
    change Θ ≤ z ∈ᴮ succ x
    have hyPair : Θ ≤ y ∈ᴮ ({({x} : bSet 𝔹), x} : bSet 𝔹) := by
      dsimp [Θ]
      exact inf_le_right.trans inf_le_left
    rw [mem_insert1] at hyPair
    apply (le_inf le_rfl hyPair).trans
    apply lattice.bv_or_elim_right
    · have hzy : Θ ⊓ y =ᴮ ({x} : bSet 𝔹) ≤ z ∈ᴮ y := by
        dsimp [Θ]
        exact inf_le_left.trans (inf_le_right.trans inf_le_right)
      have hzSingleton : Θ ⊓ y =ᴮ ({x} : bSet 𝔹) ≤ z ∈ᴮ ({x} : bSet 𝔹) :=
        subst_congr_mem_right' inf_le_right hzy
      exact mem_insert_of_eq (eq_mem_singleton hzSingleton)
    · have hzy : Θ ⊓ y ∈ᴮ ({x} : bSet 𝔹) ≤ z ∈ᴮ y := by
        dsimp [Θ]
        exact inf_le_left.trans (inf_le_right.trans inf_le_right)
      have hyx : Θ ⊓ y ∈ᴮ ({x} : bSet 𝔹) ≤ y =ᴮ x :=
        eq_mem_singleton inf_le_right
      exact mem_insert_of_mem (subst_congr_mem_right' hyx hzy)

theorem succ_eq_binary_union' {x : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ succ x =ᴮ binary_union x ({x} : bSet 𝔹) :=
  bv_trans succ_eq_binary_union binary_union_symm

/-- Kuratowski ordered pair of Boolean-valued sets. -/
def pair (x y : bSet 𝔹) : bSet 𝔹 :=
  ({{x}, {x, y}} : bSet 𝔹)

theorem subst_congr_pair_left {x z y : bSet 𝔹} {Γ : 𝔹}
    (h : Γ ≤ x =ᴮ z) : Γ ≤ pair x y =ᴮ pair z y := by
  have hsingle : Γ ≤ ({x} : bSet 𝔹) =ᴮ ({z} : bSet 𝔹) :=
    singleton_congr h
  have hpair : Γ ≤ ({x, y} : bSet 𝔹) =ᴮ ({z, y} : bSet 𝔹) := by
    change Γ ≤ insert x ({y} : bSet 𝔹) =ᴮ insert z ({y} : bSet 𝔹)
    exact insert1_congr_left h
  exact insert1_congr hsingle (singleton_congr hpair)

theorem subst_congr_pair_right {x y z : bSet 𝔹} {Γ : 𝔹}
    (h : Γ ≤ y =ᴮ z) : Γ ≤ pair x y =ᴮ pair x z := by
  have hpair : Γ ≤ ({x, y} : bSet 𝔹) =ᴮ ({x, z} : bSet 𝔹) := by
    change Γ ≤ insert x ({y} : bSet 𝔹) =ᴮ insert x ({z} : bSet 𝔹)
    exact insert1_congr_right (singleton_congr h)
  exact insert1_congr_right (x := ({x} : bSet 𝔹)) (singleton_congr hpair)

theorem pair_congr {x₁ x₂ y₁ y₂ : bSet 𝔹} {Γ : 𝔹}
    (h₁ : Γ ≤ x₁ =ᴮ y₁) (h₂ : Γ ≤ x₂ =ᴮ y₂) :
    Γ ≤ pair x₁ x₂ =ᴮ pair y₁ y₂ :=
  bv_trans (subst_congr_pair_left h₁) (subst_congr_pair_right h₂)

theorem B_congr_insert1_left (y : bSet 𝔹) :
    B_congr (fun x : bSet 𝔹 => insert x y) :=
  fun x z => insert1_congr_left (Γ := x =ᴮ z) le_rfl

theorem B_congr_insert1_right (x : bSet 𝔹) :
    B_congr (fun y : bSet 𝔹 => insert x y) :=
  fun y z => insert1_congr_right (Γ := y =ᴮ z) le_rfl

theorem B_congr_succ : B_congr (succ : bSet 𝔹 → bSet 𝔹) :=
  fun x y => insert1_congr (Γ := x =ᴮ y) le_rfl le_rfl

theorem B_congr_pair_left (y : bSet 𝔹) :
    B_congr (fun x : bSet 𝔹 => pair x y) :=
  fun x z => subst_congr_pair_left (Γ := x =ᴮ z) le_rfl

theorem B_congr_pair_right (x : bSet 𝔹) :
    B_congr (fun y : bSet 𝔹 => pair x y) :=
  fun y z => subst_congr_pair_right (Γ := y =ᴮ z) le_rfl

theorem B_ext_pair_left {φ : bSet 𝔹 → 𝔹} (hφ : B_ext φ) (x : bSet 𝔹) :
    B_ext (fun z : bSet 𝔹 => φ (pair z x)) := by
  intro z w
  have hpair : z =ᴮ w ≤ pair z x =ᴮ pair w x :=
    B_congr_pair_left x z w
  exact (le_inf (inf_le_left.trans hpair) inf_le_right).trans (hφ (pair z x) (pair w x))

theorem B_ext_pair_right {φ : bSet 𝔹 → 𝔹} (hφ : B_ext φ) (x : bSet 𝔹) :
    B_ext (fun z : bSet 𝔹 => φ (pair x z)) := by
  intro z w
  have hpair : z =ᴮ w ≤ pair x z =ᴮ pair x w :=
    B_congr_pair_right x z w
  exact (le_inf (inf_le_left.trans hpair) inf_le_right).trans (hφ (pair x z) (pair x w))

theorem B_ext_pair_mem_left {x y : bSet 𝔹} :
    B_ext (fun z : bSet 𝔹 => pair z x ∈ᴮ y) :=
  B_ext_pair_left (φ := fun w : bSet 𝔹 => w ∈ᴮ y) (B_ext_mem_left y) x

theorem B_ext_pair_mem_right {x y : bSet 𝔹} :
    B_ext (fun z : bSet 𝔹 => pair x z ∈ᴮ y) :=
  B_ext_pair_right (φ := fun w : bSet 𝔹 => w ∈ᴮ y) (B_ext_mem_left y) x

theorem eq_of_singleton_mem_pair_left {x v w : bSet 𝔹} {Γ : 𝔹}
    (h : Γ ≤ ({x} : bSet 𝔹) ∈ᴮ pair v w) : Γ ≤ x =ᴮ v := by
  change Γ ≤ ({x} : bSet 𝔹) ∈ᴮ insert ({v} : bSet 𝔹) ({({v, w} : bSet 𝔹)} : bSet 𝔹) at h
  rw [mem_insert1] at h
  apply (le_inf le_rfl h).trans
  apply lattice.bv_or_elim_right
  · exact eq_of_eq_singleton inf_le_right
  · have hPairSingleton :
        Γ ⊓ ({x} : bSet 𝔹) ∈ᴮ ({({v, w} : bSet 𝔹)} : bSet 𝔹) ≤
          ({v, w} : bSet 𝔹) =ᴮ ({x} : bSet 𝔹) :=
      eq_of_mem_singleton inf_le_right
    have hvMem : Γ ⊓ ({x} : bSet 𝔹) ∈ᴮ ({({v, w} : bSet 𝔹)} : bSet 𝔹) ≤
        v ∈ᴮ ({v, w} : bSet 𝔹) :=
      mem_insert_self
    have hvMemX :
        Γ ⊓ ({x} : bSet 𝔹) ∈ᴮ ({({v, w} : bSet 𝔹)} : bSet 𝔹) ≤
          v ∈ᴮ ({x} : bSet 𝔹) :=
      subst_congr_mem_right' hPairSingleton hvMem
    exact eq_of_mem_singleton hvMemX

theorem eq_of_eq_pair_left {x y v w : bSet 𝔹} :
    pair x y =ᴮ pair v w ≤ x =ᴮ v := by
  let Γ : 𝔹 := pair x y =ᴮ pair v w
  have h : Γ ≤ pair x y =ᴮ pair v w := le_rfl
  have hxPair : Γ ≤ ({x} : bSet 𝔹) ∈ᴮ pair x y := by
    change Γ ≤ ({x} : bSet 𝔹) ∈ᴮ
      insert ({x} : bSet 𝔹) ({({x, y} : bSet 𝔹)} : bSet 𝔹)
    exact mem_insert_self
  have hxPair' : Γ ≤ ({x} : bSet 𝔹) ∈ᴮ pair v w :=
    subst_congr_mem_right' h hxPair
  exact eq_of_singleton_mem_pair_left hxPair'

theorem eq_of_eq_pair_left' {x y v w : bSet 𝔹} {Γ : 𝔹}
    (h : Γ ≤ pair x y =ᴮ pair v w) : Γ ≤ x =ᴮ v :=
  h.trans eq_of_eq_pair_left

theorem eq_of_eq_pair'_right {x z y : bSet 𝔹} :
    pair y x =ᴮ pair y z ≤ x =ᴮ z := by
  let Γ : 𝔹 := pair y x =ᴮ pair y z
  have h : Γ ≤ pair y x =ᴮ pair y z := le_rfl
  have hSecondLeft : Γ ≤ ({y, x} : bSet 𝔹) ∈ᴮ pair y x := by
    change Γ ≤ ({y, x} : bSet 𝔹) ∈ᴮ
      insert ({y} : bSet 𝔹) ({({y, x} : bSet 𝔹)} : bSet 𝔹)
    exact mem_insert_of_mem mem_singleton
  have hSecondRight : Γ ≤ ({y, x} : bSet 𝔹) ∈ᴮ pair y z :=
    subst_congr_mem_right' h hSecondLeft
  change Γ ≤ ({y, x} : bSet 𝔹) ∈ᴮ
    insert ({y} : bSet 𝔹) ({({y, z} : bSet 𝔹)} : bSet 𝔹) at hSecondRight
  rw [mem_insert1] at hSecondRight
  apply (le_inf le_rfl hSecondRight).trans
  apply lattice.bv_or_elim_right
  · let Δ : 𝔹 := Γ ⊓ ({y, x} : bSet 𝔹) =ᴮ ({y} : bSet 𝔹)
    change Δ ≤ x =ᴮ z
    have hyx : Δ ≤ y =ᴮ x := by
      have hSingleton : Δ ≤ ({y} : bSet 𝔹) =ᴮ ({y, x} : bSet 𝔹) := by
        dsimp [Δ]
        exact bv_symm inf_le_right
      exact hSingleton.trans (eq_inserted_of_eq_singleton' (x := y) (y := y) (z := x))
    have hEqPair : Δ ≤ pair y x =ᴮ pair y z := by
      dsimp [Δ]
      exact inf_le_left.trans h
    have hSecondRight' : Δ ≤ ({y, z} : bSet 𝔹) ∈ᴮ pair y z := by
      change Δ ≤ ({y, z} : bSet 𝔹) ∈ᴮ
        insert ({y} : bSet 𝔹) ({({y, z} : bSet 𝔹)} : bSet 𝔹)
      exact mem_insert_of_mem mem_singleton
    have hSecondLeft' : Δ ≤ ({y, z} : bSet 𝔹) ∈ᴮ pair y x :=
      subst_congr_mem_right' (bv_symm hEqPair) hSecondRight'
    change Δ ≤ ({y, z} : bSet 𝔹) ∈ᴮ
      insert ({y} : bSet 𝔹) ({({y, x} : bSet 𝔹)} : bSet 𝔹) at hSecondLeft'
    rw [mem_insert1] at hSecondLeft'
    apply (le_inf le_rfl hSecondLeft').trans
    apply lattice.bv_or_elim_right
    · let Θ : 𝔹 := Δ ⊓ ({y, z} : bSet 𝔹) =ᴮ ({y} : bSet 𝔹)
      change Θ ≤ x =ᴮ z
      have hyz : Θ ≤ y =ᴮ z := by
        have hSingleton : Θ ≤ ({y} : bSet 𝔹) =ᴮ ({y, z} : bSet 𝔹) := by
          dsimp [Θ]
          exact bv_symm inf_le_right
        exact hSingleton.trans (eq_inserted_of_eq_singleton' (x := y) (y := y) (z := z))
      have hxy : Θ ≤ x =ᴮ y :=
        bv_symm (inf_le_left.trans hyx)
      exact bv_trans hxy hyz
    · have hPair : Δ ⊓ ({y, z} : bSet 𝔹) ∈ᴮ ({({y, x} : bSet 𝔹)} : bSet 𝔹) ≤
          ({y, x} : bSet 𝔹) =ᴮ ({y, z} : bSet 𝔹) :=
        eq_of_mem_singleton inf_le_right
      exact hPair.trans (inserted_eq_of_insert_eq (y := x) (v := y) (w := z))
  · have hPair : Γ ⊓ ({y, x} : bSet 𝔹) ∈ᴮ ({({y, z} : bSet 𝔹)} : bSet 𝔹) ≤
        ({y, z} : bSet 𝔹) =ᴮ ({y, x} : bSet 𝔹) :=
      eq_of_mem_singleton inf_le_right
    have hzx : Γ ⊓ ({y, x} : bSet 𝔹) ∈ᴮ ({({y, z} : bSet 𝔹)} : bSet 𝔹) ≤
        z =ᴮ x :=
      hPair.trans (inserted_eq_of_insert_eq (y := z) (v := y) (w := x))
    exact bv_symm hzx

theorem eq_of_eq_pair_right {x y v w : bSet 𝔹} :
    pair x y =ᴮ pair v w ≤ y =ᴮ w := by
  let Γ : 𝔹 := pair x y =ᴮ pair v w
  have h : Γ ≤ pair x y =ᴮ pair v w := le_rfl
  have hxv : Γ ≤ x =ᴮ v :=
    eq_of_eq_pair_left' h
  have hvwToXw : Γ ≤ pair v w =ᴮ pair x w :=
    subst_congr_pair_left (bv_symm hxv)
  have hSameLeft : Γ ≤ pair x y =ᴮ pair x w :=
    bv_trans h hvwToXw
  exact hSameLeft.trans (eq_of_eq_pair'_right (x := y) (z := w) (y := x))

theorem eq_of_eq_pair_right' {x y v w : bSet 𝔹} {Γ : 𝔹}
    (h : Γ ≤ pair x y =ᴮ pair v w) : Γ ≤ y =ᴮ w :=
  h.trans eq_of_eq_pair_right

theorem eq_of_eq_pair {x y v w : bSet 𝔹} {Γ : 𝔹}
    (h : Γ ≤ pair x y =ᴮ pair v w) : Γ ≤ x =ᴮ v ∧ Γ ≤ y =ᴮ w :=
  ⟨eq_of_eq_pair_left' h, eq_of_eq_pair_right' h⟩

theorem pair_eq_pair_iff {x y x' y' : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ pair x y =ᴮ pair x' y' ↔ Γ ≤ x =ᴮ x' ∧ Γ ≤ y =ᴮ y' :=
  ⟨fun h => eq_of_eq_pair h, fun h => pair_congr h.1 h.2⟩

/-- Cartesian product of Boolean-valued sets, encoded with Kuratowski pairs. -/
def prod (x y : bSet 𝔹) : bSet 𝔹 :=
  mk (x.type × y.type)
    (fun ij => pair (x.func ij.1) (y.func ij.2))
    (fun ij => x.bval ij.1 ⊓ y.bval ij.2)

@[simp] theorem prod_type {x y : bSet 𝔹} :
    (prod x y).type = (x.type × y.type) := rfl

@[simp] theorem prod_func {x y : bSet 𝔹} {ij : (prod x y).type} :
    (prod x y).func ij = pair (x.func ij.1) (y.func ij.2) := rfl

@[simp] theorem prod_bval {x y : bSet 𝔹} {ij : (prod x y).type} :
    (prod x y).bval ij = x.bval ij.1 ⊓ y.bval ij.2 := rfl

@[simp] theorem prod_type_forall {x y : bSet 𝔹} {φ : (prod x y).type → 𝔹} :
    (⨅ z : (prod x y).type, φ z) = ⨅ z : x.type × y.type, φ z := rfl

theorem prod_mem {v w x y : bSet 𝔹} {Γ : 𝔹}
    (hx : Γ ≤ x ∈ᴮ v) (hy : Γ ≤ y ∈ᴮ w) :
    Γ ≤ pair x y ∈ᴮ prod v w := by
  rw [mem_unfold] at hx ⊢
  apply (le_inf le_rfl hx).trans
  apply lattice.bv_cases_right
  intro i
  let Γi : 𝔹 := Γ ⊓ (v.bval i ⊓ x =ᴮ v.func i)
  change Γi ≤ pair x y ∈ᴮ prod v w
  have hyi : Γi ≤ y ∈ᴮ w :=
    inf_le_left.trans hy
  rw [mem_unfold] at hyi
  apply (le_inf le_rfl hyi).trans
  apply lattice.bv_cases_right
  intro j
  let Γij : 𝔹 := Γi ⊓ (w.bval j ⊓ y =ᴮ w.func j)
  change Γij ≤ pair x y ∈ᴮ prod v w
  rw [mem_unfold]
  apply lattice.bv_use (i, j)
  apply le_inf
  · dsimp [Γij, Γi, prod]
    exact le_inf
      (inf_le_left.trans (inf_le_right.trans inf_le_left))
      (inf_le_right.trans inf_le_left)
  · have hxi : Γij ≤ x =ᴮ v.func i := by
      dsimp [Γij, Γi]
      exact inf_le_left.trans (inf_le_right.trans inf_le_right)
    have hyj : Γij ≤ y =ᴮ w.func j := by
      dsimp [Γij]
      exact inf_le_right.trans inf_le_right
    exact pair_congr hxi hyj

theorem mem_prod {v w x y : bSet 𝔹} {Γ : 𝔹}
    (hx : Γ ≤ x ∈ᴮ v) (hy : Γ ≤ y ∈ᴮ w) :
    Γ ≤ pair x y ∈ᴮ prod v w :=
  prod_mem hx hy

theorem mem_left_of_prod_mem {v w x y : bSet 𝔹} {Γ : 𝔹}
    (h : Γ ≤ pair x y ∈ᴮ prod v w) : Γ ≤ x ∈ᴮ v := by
  rw [mem_unfold] at h
  apply (le_inf le_rfl h).trans
  apply lattice.bv_cases_right
  intro ij
  let Δ : 𝔹 := Γ ⊓ ((prod v w).bval ij ⊓ pair x y =ᴮ (prod v w).func ij)
  change Δ ≤ x ∈ᴮ v
  have hval : Δ ≤ v.bval ij.1 := by
    dsimp [Δ, prod]
    exact inf_le_right.trans inf_le_left |>.trans inf_le_left
  have hmem : Δ ≤ v.func ij.1 ∈ᴮ v :=
    mem.mk'' hval
  have heq : Δ ≤ x =ᴮ v.func ij.1 := by
    dsimp [Δ, prod]
    exact eq_of_eq_pair_left' (inf_le_right.trans inf_le_right)
  exact subst_congr_mem_left' (bv_symm heq) hmem

theorem mem_right_of_prod_mem {v w x y : bSet 𝔹} {Γ : 𝔹}
    (h : Γ ≤ pair x y ∈ᴮ prod v w) : Γ ≤ y ∈ᴮ w := by
  rw [mem_unfold] at h
  apply (le_inf le_rfl h).trans
  apply lattice.bv_cases_right
  intro ij
  let Δ : 𝔹 := Γ ⊓ ((prod v w).bval ij ⊓ pair x y =ᴮ (prod v w).func ij)
  change Δ ≤ y ∈ᴮ w
  have hval : Δ ≤ w.bval ij.2 := by
    dsimp [Δ, prod]
    exact inf_le_right.trans inf_le_left |>.trans inf_le_right
  have hmem : Δ ≤ w.func ij.2 ∈ᴮ w :=
    mem.mk'' hval
  have heq : Δ ≤ y =ᴮ w.func ij.2 := by
    dsimp [Δ, prod]
    exact eq_of_eq_pair_right' (inf_le_right.trans inf_le_right)
  exact subst_congr_mem_left' (bv_symm heq) hmem

theorem mem_prod_iff {v w x y : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ pair x y ∈ᴮ prod v w ↔ Γ ≤ x ∈ᴮ v ∧ Γ ≤ y ∈ᴮ w :=
  ⟨fun h => ⟨mem_left_of_prod_mem h, mem_right_of_prod_mem h⟩,
    fun h => prod_mem h.1 h.2⟩

theorem prod_ext {S₁ S₂ x y : bSet 𝔹} {Γ : 𝔹}
    (hS₁ : Γ ≤ S₁ ⊆ᴮ prod x y) (hS₂ : Γ ≤ S₂ ⊆ᴮ prod x y)
    (hProdExt : Γ ≤ ⨅ v : bSet 𝔹, lattice.imp (v ∈ᴮ x)
      (⨅ w : bSet 𝔹, lattice.imp (w ∈ᴮ y)
        (lattice.biimp (pair v w ∈ᴮ S₁) (pair v w ∈ᴮ S₂)))) :
    Γ ≤ S₁ =ᴮ S₂ := by
  apply mem_ext
  · apply le_iInf
    intro z
    apply lattice.bv_imp_intro
    let Δ : 𝔹 := Γ ⊓ z ∈ᴮ S₁
    change Δ ≤ z ∈ᴮ S₂
    have hzProd : Δ ≤ z ∈ᴮ prod x y :=
      mem_of_mem_subset' (inf_le_left.trans hS₁) inf_le_right
    rw [mem_unfold] at hzProd
    apply (le_inf le_rfl hzProd).trans
    apply lattice.bv_cases_right
    intro ij
    let Θ : 𝔹 := Δ ⊓ ((prod x y).bval ij ⊓ z =ᴮ (prod x y).func ij)
    change Θ ≤ z ∈ᴮ S₂
    have hΘΓ : Θ ≤ Γ := by
      dsimp [Θ, Δ]
      exact inf_le_left.trans inf_le_left
    have hxMem : Θ ≤ x.func ij.1 ∈ᴮ x := by
      apply mem.mk''
      dsimp [Θ, prod]
      exact inf_le_right.trans inf_le_left |>.trans inf_le_left
    have hyMem : Θ ≤ y.func ij.2 ∈ᴮ y := by
      apply mem.mk''
      dsimp [Θ, prod]
      exact inf_le_right.trans inf_le_left |>.trans inf_le_right
    have hAllV : Θ ≤ lattice.imp (x.func ij.1 ∈ᴮ x)
        (⨅ w : bSet 𝔹, lattice.imp (w ∈ᴮ y)
          (lattice.biimp (pair (x.func ij.1) w ∈ᴮ S₁)
            (pair (x.func ij.1) w ∈ᴮ S₂))) :=
      (hΘΓ.trans hProdExt).trans (iInf_le _ (x.func ij.1))
    have hAllW : Θ ≤ ⨅ w : bSet 𝔹, lattice.imp (w ∈ᴮ y)
        (lattice.biimp (pair (x.func ij.1) w ∈ᴮ S₁)
          (pair (x.func ij.1) w ∈ᴮ S₂)) :=
      lattice.bv_context_apply hAllV hxMem
    have hImpW : Θ ≤ lattice.imp (y.func ij.2 ∈ᴮ y)
        (lattice.biimp (pair (x.func ij.1) (y.func ij.2) ∈ᴮ S₁)
          (pair (x.func ij.1) (y.func ij.2) ∈ᴮ S₂)) :=
      hAllW.trans (iInf_le _ (y.func ij.2))
    have hBiimp : Θ ≤ lattice.biimp
        (pair (x.func ij.1) (y.func ij.2) ∈ᴮ S₁)
        (pair (x.func ij.1) (y.func ij.2) ∈ᴮ S₂) :=
      lattice.bv_context_apply hImpW hyMem
    have hzEq : Θ ≤ z =ᴮ pair (x.func ij.1) (y.func ij.2) := by
      dsimp [Θ, prod]
      exact inf_le_right.trans inf_le_right
    have hzS₁ : Θ ≤ z ∈ᴮ S₁ := by
      dsimp [Θ, Δ]
      exact inf_le_left.trans inf_le_right
    have hPairS₁ : Θ ≤ pair (x.func ij.1) (y.func ij.2) ∈ᴮ S₁ :=
      subst_congr_mem_left' hzEq hzS₁
    have hPairS₂ : Θ ≤ pair (x.func ij.1) (y.func ij.2) ∈ᴮ S₂ :=
      (lattice.bv_biimp_iff.mp hBiimp le_rfl).mp hPairS₁
    exact subst_congr_mem_left' (bv_symm hzEq) hPairS₂
  · apply le_iInf
    intro z
    apply lattice.bv_imp_intro
    let Δ : 𝔹 := Γ ⊓ z ∈ᴮ S₂
    change Δ ≤ z ∈ᴮ S₁
    have hzProd : Δ ≤ z ∈ᴮ prod x y :=
      mem_of_mem_subset' (inf_le_left.trans hS₂) inf_le_right
    rw [mem_unfold] at hzProd
    apply (le_inf le_rfl hzProd).trans
    apply lattice.bv_cases_right
    intro ij
    let Θ : 𝔹 := Δ ⊓ ((prod x y).bval ij ⊓ z =ᴮ (prod x y).func ij)
    change Θ ≤ z ∈ᴮ S₁
    have hΘΓ : Θ ≤ Γ := by
      dsimp [Θ, Δ]
      exact inf_le_left.trans inf_le_left
    have hxMem : Θ ≤ x.func ij.1 ∈ᴮ x := by
      apply mem.mk''
      dsimp [Θ, prod]
      exact inf_le_right.trans inf_le_left |>.trans inf_le_left
    have hyMem : Θ ≤ y.func ij.2 ∈ᴮ y := by
      apply mem.mk''
      dsimp [Θ, prod]
      exact inf_le_right.trans inf_le_left |>.trans inf_le_right
    have hAllV : Θ ≤ lattice.imp (x.func ij.1 ∈ᴮ x)
        (⨅ w : bSet 𝔹, lattice.imp (w ∈ᴮ y)
          (lattice.biimp (pair (x.func ij.1) w ∈ᴮ S₁)
            (pair (x.func ij.1) w ∈ᴮ S₂))) :=
      (hΘΓ.trans hProdExt).trans (iInf_le _ (x.func ij.1))
    have hAllW : Θ ≤ ⨅ w : bSet 𝔹, lattice.imp (w ∈ᴮ y)
        (lattice.biimp (pair (x.func ij.1) w ∈ᴮ S₁)
          (pair (x.func ij.1) w ∈ᴮ S₂)) :=
      lattice.bv_context_apply hAllV hxMem
    have hImpW : Θ ≤ lattice.imp (y.func ij.2 ∈ᴮ y)
        (lattice.biimp (pair (x.func ij.1) (y.func ij.2) ∈ᴮ S₁)
          (pair (x.func ij.1) (y.func ij.2) ∈ᴮ S₂)) :=
      hAllW.trans (iInf_le _ (y.func ij.2))
    have hBiimp : Θ ≤ lattice.biimp
        (pair (x.func ij.1) (y.func ij.2) ∈ᴮ S₁)
        (pair (x.func ij.1) (y.func ij.2) ∈ᴮ S₂) :=
      lattice.bv_context_apply hImpW hyMem
    have hzEq : Θ ≤ z =ᴮ pair (x.func ij.1) (y.func ij.2) := by
      dsimp [Θ, prod]
      exact inf_le_right.trans inf_le_right
    have hzS₂ : Θ ≤ z ∈ᴮ S₂ := by
      dsimp [Θ, Δ]
      exact inf_le_left.trans inf_le_right
    have hPairS₂ : Θ ≤ pair (x.func ij.1) (y.func ij.2) ∈ᴮ S₂ :=
      subst_congr_mem_left' hzEq hzS₂
    have hPairS₁ : Θ ≤ pair (x.func ij.1) (y.func ij.2) ∈ᴮ S₁ :=
      (lattice.bv_biimp_iff.mp hBiimp le_rfl).mpr hPairS₂
    exact subst_congr_mem_left' (bv_symm hzEq) hPairS₁

theorem check_singleton {x : pSet.{u}} {Γ : 𝔹} :
    Γ ≤ (check ({x} : pSet.{u}) : bSet 𝔹) =ᴮ ({check x} : bSet 𝔹) := by
  apply subset_ext
  · apply subset_intro
    intro i
    let i' : ({x} : pSet.{u}).Type :=
      cast (check_type (𝔹 := 𝔹) (x := ({x} : pSet.{u}))) i
    change Γ ⊓ (check ({x} : pSet.{u}) : bSet 𝔹).bval i ≤
      (check ({x} : pSet.{u}) : bSet 𝔹).func i ∈ᴮ ({check x} : bSet 𝔹)
    rw [check_bval, inf_top_eq, check_func]
    change Γ ≤ check (({x} : pSet.{u}).Func i') ∈ᴮ ({check x} : bSet 𝔹)
    have hiMem : ({x} : pSet.{u}).Func i' ∈ ({x} : pSet.{u}) :=
      pSet.mem_mk'
    have hiEq : PSet.Equiv (({x} : pSet.{u}).Func i') x :=
      PSet.mem_singleton.mp hiMem
    exact mem_singleton_of_eq (check_eq hiEq.symm)
  · change Γ ≤ insert (check x) (∅ : bSet 𝔹) ⊆ᴮ check ({x} : pSet.{u})
    rw [insert_empty_subset_iff]
    exact check_mem (PSet.mem_singleton.mpr PSet.Equiv.rfl)

theorem check_unordered_pair {x y : pSet.{u}} {Γ : 𝔹} :
    Γ ≤ (check ({x, y} : pSet.{u}) : bSet 𝔹) =ᴮ
      ({check x, check y} : bSet 𝔹) := by
  apply subset_ext
  · apply subset_intro
    intro i
    let i' : ({x, y} : pSet.{u}).Type :=
      cast (check_type (𝔹 := 𝔹) (x := ({x, y} : pSet.{u}))) i
    change Γ ⊓ (check ({x, y} : pSet.{u}) : bSet 𝔹).bval i ≤
      (check ({x, y} : pSet.{u}) : bSet 𝔹).func i ∈ᴮ
        ({check x, check y} : bSet 𝔹)
    rw [check_bval, inf_top_eq, check_func]
    change Γ ≤ check (({x, y} : pSet.{u}).Func i') ∈ᴮ
      ({check x, check y} : bSet 𝔹)
    have hiMem : ({x, y} : pSet.{u}).Func i' ∈ ({x, y} : pSet.{u}) :=
      pSet.mem_mk'
    rcases PSet.mem_pair.mp hiMem with hiEq | hiEq
    · exact mem_insert_of_eq (check_eq hiEq)
    · exact mem_insert_of_mem (mem_singleton_of_eq (check_eq hiEq.symm))
  · change Γ ≤ ({check x, check y} : bSet 𝔹) ⊆ᴮ check ({x, y} : pSet.{u})
    rw [insert_subset_iff]
    constructor
    · exact check_mem (PSet.mem_pair.mpr (Or.inl PSet.Equiv.rfl))
    · change Γ ≤ insert (check y) (∅ : bSet 𝔹) ⊆ᴮ check ({x, y} : pSet.{u})
      rw [insert_empty_subset_iff]
      exact check_mem (PSet.mem_pair.mpr (Or.inr PSet.Equiv.rfl))

theorem check_pair {x y : pSet.{u}} {Γ : 𝔹} :
    Γ ≤ (check (pSet.pair x y) : bSet 𝔹) =ᴮ pair (check x) (check y) := by
  have hPairCheck :
      Γ ≤ (check (pSet.pair x y) : bSet 𝔹) =ᴮ
        ({check ({x} : pSet.{u}), check ({x, y} : pSet.{u})} : bSet 𝔹) := by
    simpa [pSet.pair] using
      (check_unordered_pair (x := ({x} : pSet.{u})) (y := ({x, y} : pSet.{u})) (Γ := Γ))
  have hMembers :
      Γ ≤ ({check ({x} : pSet.{u}), check ({x, y} : pSet.{u})} : bSet 𝔹) =ᴮ
        pair (check x) (check y) := by
    change Γ ≤ insert (check ({x} : pSet.{u})) ({check ({x, y} : pSet.{u})} : bSet 𝔹) =ᴮ
      insert ({check x} : bSet 𝔹) ({({check x, check y} : bSet 𝔹)} : bSet 𝔹)
    exact insert1_congr check_singleton (singleton_congr check_unordered_pair)
  exact bv_trans hPairCheck hMembers

theorem check_prod {x y : pSet.{u}} {Γ : 𝔹} :
    Γ ≤ (check (pSet.prod x y) : bSet 𝔹) =ᴮ prod (check x) (check y) := by
  apply subset_ext
  · apply subset_intro
    intro ij
    let ij' : (pSet.prod x y).Type :=
      cast (check_type (𝔹 := 𝔹) (x := pSet.prod x y)) ij
    change Γ ⊓ (check (pSet.prod x y) : bSet 𝔹).bval ij ≤
      (check (pSet.prod x y) : bSet 𝔹).func ij ∈ᴮ prod (check x) (check y)
    rw [check_bval, inf_top_eq, check_func]
    change Γ ≤ check ((pSet.prod x y).Func ij') ∈ᴮ prod (check x) (check y)
    cases ij' with
    | mk i j =>
        change Γ ≤ check (pSet.pair (x.Func i) (y.Func j)) ∈ᴮ prod (check x) (check y)
        have hPair :
            Γ ≤ check (pSet.pair (x.Func i) (y.Func j)) =ᴮ
              pair (check (x.Func i)) (check (y.Func j)) :=
          check_pair
        have hxMem : Γ ≤ check (x.Func i) ∈ᴮ check x :=
          check_mem pSet.mem_mk'
        have hyMem : Γ ≤ check (y.Func j) ∈ᴮ check y :=
          check_mem pSet.mem_mk'
        exact subst_congr_mem_left' (bv_symm hPair) (prod_mem hxMem hyMem)
  · apply subset_intro
    intro ij
    change Γ ⊓ (prod (check x) (check y)).bval ij ≤
      (prod (check x) (check y)).func ij ∈ᴮ check (pSet.prod x y)
    cases ij with
    | mk i j =>
        let Δ : 𝔹 := Γ ⊓ ((check x).bval i ⊓ (check y).bval j)
        change Δ ≤ pair ((check x).func i) ((check y).func j) ∈ᴮ check (pSet.prod x y)
        have hPair :
            Δ ≤
              check (pSet.pair (x.Func (cast (check_type (𝔹 := 𝔹) (x := x)) i))
                (y.Func (cast (check_type (𝔹 := 𝔹) (x := y)) j))) =ᴮ
                pair ((check x).func i) ((check y).func j) := by
          rw [check_func, check_func]
          exact check_pair
        have hMemCheck :
            Δ ≤
              check (pSet.pair (x.Func (cast (check_type (𝔹 := 𝔹) (x := x)) i))
                (y.Func (cast (check_type (𝔹 := 𝔹) (x := y)) j))) ∈ᴮ
                check (pSet.prod x y) := by
          apply check_mem
          apply pSet.mem_prod_of_mem
          · exact pSet.mem_mk'
          · exact pSet.mem_mk'
        exact subst_congr_mem_left' hPair hMemCheck

@[simp] theorem check_mem_func {y : pSet.{u}} {i : y.Type} :
    ((check (y.Func i) : bSet 𝔹) ∈ᴮ check y) = ⊤ := by
  apply le_antisymm le_top
  exact check_mem pSet.mem_mk'

theorem check_eq_reflect {x y : pSet.{u}} {Γ : 𝔹}
    (hNonzero : ⊥ < Γ) (hEq : Γ ≤ (check x : bSet 𝔹) =ᴮ check y) :
    PSet.Equiv x y := by
  by_contra hneq
  have hBot : Γ ≤ ⊥ := by
    rw [check_bv_eq_bot_of_not_equiv hneq] at hEq
    exact hEq
  exact (not_le_of_gt hNonzero) hBot

theorem check_mem_reflect {x y : pSet.{u}} {Γ : 𝔹}
    (hNonzero : ⊥ < Γ) (hMem : Γ ≤ (check x : bSet 𝔹) ∈ᴮ check y) :
    x ∈ y := by
  by_contra hNotMem
  have hBot : Γ ≤ ⊥ :=
    check_not_mem hNotMem hMem
  exact (not_le_of_gt hNonzero) hBot

theorem check_succ_eq_succ_check {x : pSet.{u}} {Γ : 𝔹} :
    Γ ≤ (check (pSet.succ x) : bSet 𝔹) =ᴮ succ (check x) := by
  apply subset_ext
  · apply subset_intro
    intro i
    let i' : (pSet.succ x).Type :=
      cast (check_type (𝔹 := 𝔹) (x := pSet.succ x)) i
    change Γ ⊓ (check (pSet.succ x) : bSet 𝔹).bval i ≤
      (check (pSet.succ x) : bSet 𝔹).func i ∈ᴮ succ (check x)
    rw [check_bval, inf_top_eq, check_func]
    change Γ ≤ check ((pSet.succ x).Func i') ∈ᴮ succ (check x)
    have hiMem : (pSet.succ x).Func i' ∈ pSet.succ x :=
      pSet.mem_mk'
    rcases pSet.mem_insert hiMem with hiEq | hiMemX
    · change Γ ≤ check ((pSet.succ x).Func i') ∈ᴮ insert (check x) (check x)
      exact mem_insert_of_eq (check_eq hiEq)
    · change Γ ≤ check ((pSet.succ x).Func i') ∈ᴮ insert (check x) (check x)
      exact mem_insert_of_mem (check_mem hiMemX)
  · change Γ ≤ insert (check x) (check x) ⊆ᴮ check (pSet.succ x)
    rw [insert_subset_iff]
    constructor
    · exact check_mem (pSet.mem_succ x)
    · have hxSubsetSucc : x ⊆ pSet.succ x :=
        pSet.subset_of_all_mem fun z hz => PSet.mem_insert_of_mem x hz
      exact check_subset hxSubsetSucc

/-- A Boolean-valued relation is functional when equal inputs have equal outputs. -/
def is_func (f : bSet 𝔹) : 𝔹 :=
  ⨅ w₁ : bSet 𝔹, ⨅ w₂ : bSet 𝔹, ⨅ v₁ : bSet 𝔹, ⨅ v₂ : bSet 𝔹,
    lattice.imp (pair w₁ v₁ ∈ᴮ f ⊓ pair w₂ v₂ ∈ᴮ f)
      (lattice.imp (w₁ =ᴮ w₂) (v₁ =ᴮ v₂))

/-- Functional relations admit a Boolean-valued output witness for every input in their domain. -/
def is_functional (f : bSet 𝔹) : 𝔹 :=
  ⨅ z : bSet 𝔹, lattice.imp (⨆ w : bSet 𝔹, pair z w ∈ᴮ f)
    (⨆ w' : bSet 𝔹, ⨅ w'' : bSet 𝔹,
      lattice.imp (pair z w'' ∈ᴮ f) (w' =ᴮ w''))

/-- A Boolean-valued relation is total from `x` to `y`. -/
def is_total (x y f : bSet 𝔹) : 𝔹 :=
  ⨅ w₁ : bSet 𝔹, lattice.imp (w₁ ∈ᴮ x)
    (⨆ w₂ : bSet 𝔹, w₂ ∈ᴮ y ⊓ pair w₁ w₂ ∈ᴮ f)

/-- Indexed form of `is_total` over the concrete names for `x` and `y`. -/
def is_total' (x y f : bSet 𝔹) : 𝔹 :=
  ⨅ i : x.type, lattice.imp (x.bval i)
    (⨆ j : y.type, y.bval j ⊓ pair (x.func i) (y.func j) ∈ᴮ f)

/-- A relation contains a total functional graph from `x` to `y`. -/
def is_func' (x y f : bSet 𝔹) : 𝔹 :=
  is_func f ⊓ is_total x y f

theorem B_ext_is_func : B_ext (is_func : bSet 𝔹 → 𝔹) := by
  unfold is_func
  apply B_ext_iInf
  intro w₁
  apply B_ext_iInf
  intro w₂
  apply B_ext_iInf
  intro v₁
  apply B_ext_iInf
  intro v₂
  apply B_ext_imp
  · apply B_ext_inf
    · exact B_ext_mem_right (pair w₁ v₁)
    · exact B_ext_mem_right (pair w₂ v₂)
  · exact B_ext_const _

theorem B_ext_is_total_right (x y : bSet 𝔹) :
    B_ext (fun f : bSet 𝔹 => is_total x y f) := by
  unfold is_total
  apply B_ext_iInf
  intro w₁
  apply B_ext_imp
  · exact B_ext_const _
  · apply B_ext_iSup
    intro w₂
    apply B_ext_inf
    · exact B_ext_const _
    · exact B_ext_mem_right (pair w₁ w₂)

theorem B_ext_is_func'_right (x y : bSet 𝔹) :
    B_ext (fun f : bSet 𝔹 => is_func' x y f) :=
  B_ext_inf B_ext_is_func (B_ext_is_total_right x y)

theorem is_func_of_is_func' {x y f : bSet 𝔹} {Γ : 𝔹}
    (h : Γ ≤ is_func' x y f) : Γ ≤ is_func f :=
  h.trans inf_le_left

theorem is_total_of_is_func' {x y f : bSet 𝔹} {Γ : 𝔹}
    (h : Γ ≤ is_func' x y f) : Γ ≤ is_total x y f :=
  h.trans inf_le_right

theorem is_total_subset_of_is_total {S x y f : bSet 𝔹} {Γ : 𝔹}
    (hTotal : Γ ≤ is_total x y f) (hSubset : Γ ≤ S ⊆ᴮ x) :
    Γ ≤ is_total S y f := by
  unfold is_total
  apply le_iInf
  intro z
  apply lattice.bv_imp_intro
  let Δ : 𝔹 := Γ ⊓ z ∈ᴮ S
  change Δ ≤ ⨆ w₂ : bSet 𝔹, w₂ ∈ᴮ y ⊓ pair z w₂ ∈ᴮ f
  have hzX : Δ ≤ z ∈ᴮ x := by
    apply mem_of_mem_subset'
    · exact inf_le_left.trans hSubset
    · exact inf_le_right
  have hImp : Δ ≤ lattice.imp (z ∈ᴮ x)
      (⨆ w₂ : bSet 𝔹, w₂ ∈ᴮ y ⊓ pair z w₂ ∈ᴮ f) :=
    (inf_le_left.trans hTotal).trans (iInf_le _ z)
  exact lattice.bv_context_apply hImp hzX

theorem check_is_total {x y f : pSet.{u}} (hTotal : pSet.is_total x y f)
    {Γ : 𝔹} : Γ ≤ is_total (check x) (check y) (check f) := by
  unfold is_total
  apply le_iInf
  intro z
  apply lattice.bv_imp_intro
  let Δ : 𝔹 := Γ ⊓ z ∈ᴮ check x
  change Δ ≤ ⨆ w : bSet 𝔹, w ∈ᴮ check y ⊓ pair z w ∈ᴮ check f
  have hzMem : Δ ≤ z ∈ᴮ check x := by
    dsimp [Δ]
    exact inf_le_right
  rw [mem_unfold] at hzMem
  apply (le_inf le_rfl hzMem).trans
  apply lattice.bv_cases_right
  intro i
  let i' : x.Type := cast (check_type (𝔹 := 𝔹) (x := x)) i
  rcases hTotal (x.Func i') pSet.mem_mk' with ⟨w, hwY, hPairF⟩
  let Θ : 𝔹 := Δ ⊓ ((check x).bval i ⊓ z =ᴮ (check x).func i)
  change Θ ≤ ⨆ w : bSet 𝔹, w ∈ᴮ check y ⊓ pair z w ∈ᴮ check f
  apply lattice.bv_use (check w)
  apply le_inf
  · exact check_mem hwY
  · have hzEq : Θ ≤ z =ᴮ check (x.Func i') := by
      dsimp [Θ, i']
      rw [check_func]
      exact inf_le_right.trans inf_le_right
    have hPairEq : Θ ≤ pair z (check w) =ᴮ check (pSet.pair (x.Func i') w) := by
      have hLeft : Θ ≤ pair z (check w) =ᴮ pair (check (x.Func i')) (check w) :=
        subst_congr_pair_left hzEq
      have hCheck : Θ ≤ check (pSet.pair (x.Func i') w) =ᴮ
          pair (check (x.Func i')) (check w) :=
        check_pair
      exact bv_trans hLeft (bv_symm hCheck)
    exact subst_congr_mem_left' (bv_symm hPairEq) (check_mem hPairF)

theorem check_subset_prod_of_is_func {x y f : pSet.{u}}
    (hFunc : pSet.is_func x y f) {Γ : 𝔹} :
    Γ ≤ (check f : bSet 𝔹) ⊆ᴮ prod (check x) (check y) :=
  subst_congr_subset_right' check_prod
    (check_subset (pSet.subset_prod_of_is_func hFunc))

/-- A Boolean-valued function from `x` to `y`, as a functional total relation inside `x × y`. -/
def is_function (x y f : bSet 𝔹) : 𝔹 :=
  is_func' x y f ⊓ f ⊆ᴮ prod x y

theorem B_ext_is_function_right (x y : bSet 𝔹) :
    B_ext (fun f : bSet 𝔹 => is_function x y f) :=
  B_ext_inf (B_ext_is_func'_right x y) (B_ext_subset_left (prod x y))

theorem is_func'_of_is_function {x y f : bSet 𝔹} {Γ : 𝔹}
    (h : Γ ≤ is_function x y f) : Γ ≤ is_func' x y f :=
  h.trans inf_le_left

theorem subset_prod_of_is_function {x y f : bSet 𝔹} {Γ : 𝔹}
    (h : Γ ≤ is_function x y f) : Γ ≤ f ⊆ᴮ prod x y :=
  h.trans inf_le_right

theorem is_total_of_is_function {x y f : bSet 𝔹} {Γ : 𝔹}
    (h : Γ ≤ is_function x y f) : Γ ≤ is_total x y f :=
  is_total_of_is_func' (is_func'_of_is_function h)

theorem check_is_func {x y f : pSet.{u}} (hFunc : pSet.is_func x y f) {Γ : 𝔹} :
    Γ ≤ is_function (check x) (check y) (check f) := by
  apply le_inf
  · apply le_inf
    · unfold is_func
      apply le_iInf
      intro w₁
      apply le_iInf
      intro w₂
      apply le_iInf
      intro v₁
      apply le_iInf
      intro v₂
      apply lattice.bv_imp_intro
      let Δ₀ : 𝔹 := Γ ⊓ (pair w₁ v₁ ∈ᴮ check f ⊓ pair w₂ v₂ ∈ᴮ check f)
      change Δ₀ ≤ lattice.imp (w₁ =ᴮ w₂) (v₁ =ᴮ v₂)
      apply lattice.bv_imp_intro
      let Δ : 𝔹 := Δ₀ ⊓ w₁ =ᴮ w₂
      change Δ ≤ v₁ =ᴮ v₂
      have hSubset : Γ ≤ (check f : bSet 𝔹) ⊆ᴮ prod (check x) (check y) :=
        check_subset_prod_of_is_func hFunc
      have hMem₁ : Δ ≤ pair w₁ v₁ ∈ᴮ check f := by
        dsimp [Δ, Δ₀]
        exact inf_le_left.trans (inf_le_right.trans inf_le_left)
      have hMem₂ : Δ ≤ pair w₂ v₂ ∈ᴮ check f := by
        dsimp [Δ, Δ₀]
        exact inf_le_left.trans (inf_le_right.trans inf_le_right)
      have hProd₁ : Δ ≤ pair w₁ v₁ ∈ᴮ prod (check x) (check y) :=
        mem_of_mem_subset' (inf_le_left.trans inf_le_left |>.trans hSubset) hMem₁
      have hProd₂ : Δ ≤ pair w₂ v₂ ∈ᴮ prod (check x) (check y) :=
        mem_of_mem_subset' (inf_le_left.trans inf_le_left |>.trans hSubset) hMem₂
      have hw₁Mem : Δ ≤ w₁ ∈ᴮ check x := (mem_prod_iff.mp hProd₁).1
      have hv₁Mem : Δ ≤ v₁ ∈ᴮ check y := (mem_prod_iff.mp hProd₁).2
      have hw₂Mem : Δ ≤ w₂ ∈ᴮ check x := (mem_prod_iff.mp hProd₂).1
      have hv₂Mem : Δ ≤ v₂ ∈ᴮ check y := (mem_prod_iff.mp hProd₂).2
      rw [mem_unfold] at hw₁Mem
      apply (le_inf le_rfl hw₁Mem).trans
      apply lattice.bv_cases_right
      intro i₁
      let xi₁ : x.Type := cast (check_type (𝔹 := 𝔹) (x := x)) i₁
      let Δ₁ : 𝔹 := Δ ⊓ ((check x).bval i₁ ⊓ w₁ =ᴮ (check x).func i₁)
      change Δ₁ ≤ v₁ =ᴮ v₂
      rw [mem_unfold] at hv₁Mem
      have hv₁MemΔ₁ :
          Δ₁ ≤ ⨆ i : (check y).type, (check y).bval i ⊓ v₁ =ᴮ (check y).func i := by
        dsimp [Δ₁]
        exact inf_le_left.trans hv₁Mem
      apply (le_inf le_rfl hv₁MemΔ₁).trans
      apply lattice.bv_cases_right
      intro j₁
      let yj₁ : y.Type := cast (check_type (𝔹 := 𝔹) (x := y)) j₁
      let Δ₂ : 𝔹 := Δ₁ ⊓ ((check y).bval j₁ ⊓ v₁ =ᴮ (check y).func j₁)
      change Δ₂ ≤ v₁ =ᴮ v₂
      rw [mem_unfold] at hw₂Mem
      have hw₂MemΔ₂ :
          Δ₂ ≤ ⨆ i : (check x).type, (check x).bval i ⊓ w₂ =ᴮ (check x).func i := by
        dsimp [Δ₂, Δ₁]
        exact inf_le_left.trans (inf_le_left.trans hw₂Mem)
      apply (le_inf le_rfl hw₂MemΔ₂).trans
      apply lattice.bv_cases_right
      intro i₂
      let xi₂ : x.Type := cast (check_type (𝔹 := 𝔹) (x := x)) i₂
      let Δ₃ : 𝔹 := Δ₂ ⊓ ((check x).bval i₂ ⊓ w₂ =ᴮ (check x).func i₂)
      change Δ₃ ≤ v₁ =ᴮ v₂
      rw [mem_unfold] at hv₂Mem
      have hv₂MemΔ₃ :
          Δ₃ ≤ ⨆ i : (check y).type, (check y).bval i ⊓ v₂ =ᴮ (check y).func i := by
        dsimp [Δ₃, Δ₂, Δ₁]
        exact inf_le_left.trans (inf_le_left.trans (inf_le_left.trans hv₂Mem))
      apply (le_inf le_rfl hv₂MemΔ₃).trans
      apply lattice.bv_cases_right
      intro j₂
      let yj₂ : y.Type := cast (check_type (𝔹 := 𝔹) (x := y)) j₂
      let Θ : 𝔹 := Δ₃ ⊓ ((check y).bval j₂ ⊓ v₂ =ᴮ (check y).func j₂)
      change Θ ≤ v₁ =ᴮ v₂
      classical
      by_cases hNonzero : ⊥ < Θ
      · have hw₁Eq : Θ ≤ w₁ =ᴮ check (x.Func xi₁) := by
          dsimp [Θ, Δ₃, Δ₂, Δ₁, xi₁]
          rw [check_func]
          exact inf_le_left.trans (inf_le_left.trans (inf_le_left.trans inf_le_right)) |>.trans
            inf_le_right
        have hv₁Eq : Θ ≤ v₁ =ᴮ check (y.Func yj₁) := by
          dsimp [Θ, Δ₃, Δ₂, yj₁]
          rw [check_func]
          exact inf_le_left.trans (inf_le_left.trans inf_le_right) |>.trans inf_le_right
        have hw₂Eq : Θ ≤ w₂ =ᴮ check (x.Func xi₂) := by
          dsimp [Θ, Δ₃, xi₂]
          rw [check_func]
          exact inf_le_left.trans inf_le_right |>.trans inf_le_right
        have hv₂Eq : Θ ≤ v₂ =ᴮ check (y.Func yj₂) := by
          dsimp [Θ, yj₂]
          rw [check_func]
          exact inf_le_right.trans inf_le_right
        have hInputEqCtx : Θ ≤ w₁ =ᴮ w₂ := by
          dsimp [Θ, Δ₃, Δ₂, Δ₁, Δ]
          exact inf_le_left.trans (inf_le_left.trans (inf_le_left.trans (inf_le_left.trans inf_le_right)))
        have hPair₁Eq : Θ ≤ pair w₁ v₁ =ᴮ check (pSet.pair (x.Func xi₁) (y.Func yj₁)) := by
          have hPair : Θ ≤ pair w₁ v₁ =ᴮ
              pair (check (x.Func xi₁)) (check (y.Func yj₁)) :=
            pair_congr hw₁Eq hv₁Eq
          exact bv_trans hPair (bv_symm check_pair)
        have hPair₂Eq : Θ ≤ pair w₂ v₂ =ᴮ check (pSet.pair (x.Func xi₂) (y.Func yj₂)) := by
          have hPair : Θ ≤ pair w₂ v₂ =ᴮ
              pair (check (x.Func xi₂)) (check (y.Func yj₂)) :=
            pair_congr hw₂Eq hv₂Eq
          exact bv_trans hPair (bv_symm check_pair)
        have hMemF₁ : pSet.pair (x.Func xi₁) (y.Func yj₁) ∈ f := by
          apply check_mem_reflect hNonzero
          exact subst_congr_mem_left' hPair₁Eq
            (by
              dsimp [Θ, Δ₃, Δ₂, Δ₁]
              exact inf_le_left.trans
                (inf_le_left.trans (inf_le_left.trans (inf_le_left.trans hMem₁))))
        have hMemF₂ : pSet.pair (x.Func xi₂) (y.Func yj₂) ∈ f := by
          apply check_mem_reflect hNonzero
          exact subst_congr_mem_left' hPair₂Eq
            (by
              dsimp [Θ, Δ₃, Δ₂, Δ₁]
              exact inf_le_left.trans
                (inf_le_left.trans (inf_le_left.trans (inf_le_left.trans hMem₂))))
        have hInputEq : PSet.Equiv (x.Func xi₁) (x.Func xi₂) := by
          apply check_eq_reflect hNonzero
          exact bv_trans (bv_symm hw₁Eq) (bv_trans hInputEqCtx hw₂Eq)
        have hOutputEq : PSet.Equiv (y.Func yj₁) (y.Func yj₂) :=
          pSet.eq_of_is_func_of_eq hFunc hMemF₁ hMemF₂ hInputEq
        exact bv_trans hv₁Eq (bv_trans (check_eq hOutputEq) (bv_symm hv₂Eq))
      · apply lattice.bv_exfalso
        by_contra hNotLe
        exact hNonzero (lt_of_le_not_ge bot_le hNotLe)
    · exact check_is_total (pSet.is_total_of_is_func hFunc)
  · exact check_subset_prod_of_is_func hFunc

theorem eq_of_is_func_of_eq {x y f x' y' : bSet 𝔹} {Γ : 𝔹}
    (hFunc : Γ ≤ is_func f) (hEq : Γ ≤ x =ᴮ y)
    (hMem₁ : Γ ≤ pair x x' ∈ᴮ f) (hMem₂ : Γ ≤ pair y y' ∈ᴮ f) :
    Γ ≤ x' =ᴮ y' := by
  have h₁ : Γ ≤ lattice.imp (pair x x' ∈ᴮ f ⊓ pair y y' ∈ᴮ f)
      (lattice.imp (x =ᴮ y) (x' =ᴮ y')) :=
    ((((hFunc.trans (iInf_le _ x)).trans (iInf_le _ y)).trans (iInf_le _ x')).trans
      (iInf_le _ y'))
  have h₂ : Γ ≤ lattice.imp (x =ᴮ y) (x' =ᴮ y') :=
    lattice.bv_context_apply h₁ (le_inf hMem₁ hMem₂)
  exact lattice.bv_context_apply h₂ hEq

theorem eq_of_is_func'_of_eq {a b x y f x' y' : bSet 𝔹} {Γ : 𝔹}
    (hFunc : Γ ≤ is_func' a b f) (hEq : Γ ≤ x =ᴮ y)
    (hMem₁ : Γ ≤ pair x x' ∈ᴮ f) (hMem₂ : Γ ≤ pair y y' ∈ᴮ f) :
    Γ ≤ x' =ᴮ y' :=
  eq_of_is_func_of_eq (is_func_of_is_func' hFunc) hEq hMem₁ hMem₂

theorem is_func'_subset_of_is_func' {S x y f : bSet 𝔹} {Γ : 𝔹}
    (hFunc : Γ ≤ is_func' x y f) (hSubset : Γ ≤ S ⊆ᴮ x) :
    Γ ≤ is_func' S y f :=
  le_inf (is_func_of_is_func' hFunc)
    (is_total_subset_of_is_total (is_total_of_is_func' hFunc) hSubset)

theorem mem_domain_of_is_function {x y f z w : bSet 𝔹} {Γ : 𝔹}
    (hMem : Γ ≤ pair z w ∈ᴮ f) (hFunc : Γ ≤ is_function x y f) :
    Γ ≤ z ∈ᴮ x := by
  have hProd : Γ ≤ pair z w ∈ᴮ prod x y :=
    mem_of_mem_subset' (subset_prod_of_is_function hFunc) hMem
  exact (mem_prod_iff.mp hProd).1

theorem mem_codomain_of_is_function {x y f z w : bSet 𝔹} {Γ : 𝔹}
    (hMem : Γ ≤ pair z w ∈ᴮ f) (hFunc : Γ ≤ is_function x y f) :
    Γ ≤ w ∈ᴮ y := by
  have hProd : Γ ≤ pair z w ∈ᴮ prod x y :=
    mem_of_mem_subset' (subset_prod_of_is_function hFunc) hMem
  exact (mem_prod_iff.mp hProd).2

/-- Bounded image of a Boolean-valued relation from `x` into `y`. -/
def image (x y f : bSet 𝔹) : bSet 𝔹 :=
  subset.mk (x := y) (fun j : y.type =>
    ⨆ z : bSet 𝔹, z ∈ᴮ x ⊓ pair z (y.func j) ∈ᴮ f)

theorem image_subset {x y f : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ image x y f ⊆ᴮ y :=
  subset.mk_subset

theorem mem_image {x y a b f : bSet 𝔹} {Γ : 𝔹}
    (hMem : Γ ≤ pair a b ∈ᴮ f) (ha : Γ ≤ a ∈ᴮ x) (hb : Γ ≤ b ∈ᴮ y) :
    Γ ≤ b ∈ᴮ image x y f := by
  rw [image, mem_subset.mk_iff₂]
  rw [mem_unfold] at hb
  apply (le_inf le_rfl hb).trans
  apply lattice.bv_cases_right
  intro j
  let Δ : 𝔹 := Γ ⊓ (y.bval j ⊓ b =ᴮ y.func j)
  change Δ ≤
    ⨆ i : y.type,
      y.bval i ⊓
        (b =ᴮ y.func i ⊓
          ⨆ z : bSet 𝔹, z ∈ᴮ x ⊓ pair z (y.func i) ∈ᴮ f)
  apply lattice.bv_use j
  apply le_inf
  · dsimp [Δ]
    exact inf_le_right.trans inf_le_left
  · apply le_inf
    · dsimp [Δ]
      exact inf_le_right.trans inf_le_right
    · apply lattice.bv_use a
      apply le_inf
      · exact inf_le_left.trans ha
      · have hbEq : Δ ≤ b =ᴮ y.func j := by
          dsimp [Δ]
          exact inf_le_right.trans inf_le_right
        have hPairEq : Δ ≤ pair a b =ᴮ pair a (y.func j) :=
          subst_congr_pair_right hbEq
        have hPairMem : Δ ≤ pair a b ∈ᴮ f :=
          inf_le_left.trans hMem
        exact subst_congr_mem_left' hPairEq hPairMem

theorem mem_image_iff {x y b f : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ b ∈ᴮ image x y f ↔
      Γ ≤ b ∈ᴮ y ∧ Γ ≤ ⨆ z : bSet 𝔹, z ∈ᴮ x ⊓ pair z b ∈ᴮ f := by
  constructor
  · intro hbImg
    refine ⟨mem_of_mem_subset' image_subset hbImg, ?_⟩
    rw [image, mem_subset.mk_iff₂] at hbImg
    apply (le_inf le_rfl hbImg).trans
    apply lattice.bv_cases_right
    intro j
    let Δ : 𝔹 := Γ ⊓
      (y.bval j ⊓
        (b =ᴮ y.func j ⊓
          ⨆ z : bSet 𝔹, z ∈ᴮ x ⊓ pair z (y.func j) ∈ᴮ f))
    change Δ ≤ ⨆ z : bSet 𝔹, z ∈ᴮ x ⊓ pair z b ∈ᴮ f
    have hbEq : Δ ≤ b =ᴮ y.func j := by
      dsimp [Δ]
      exact inf_le_right.trans inf_le_right |>.trans inf_le_left
    have hCases : Δ ≤ ⨆ z : bSet 𝔹, z ∈ᴮ x ⊓ pair z (y.func j) ∈ᴮ f := by
      dsimp [Δ]
      exact inf_le_right.trans inf_le_right |>.trans inf_le_right
    apply (le_inf le_rfl hCases).trans
    apply lattice.bv_cases_right
    intro z
    apply lattice.bv_use z
    apply le_inf
    · exact inf_le_right.trans inf_le_left
    · have hPairMem : Δ ⊓ (z ∈ᴮ x ⊓ pair z (y.func j) ∈ᴮ f) ≤
          pair z (y.func j) ∈ᴮ f :=
        inf_le_right.trans inf_le_right
      have hPairEq : Δ ⊓ (z ∈ᴮ x ⊓ pair z (y.func j) ∈ᴮ f) ≤
          pair z (y.func j) =ᴮ pair z b :=
        subst_congr_pair_right (bv_symm (inf_le_left.trans hbEq))
      exact subst_congr_mem_left' hPairEq hPairMem
  · intro h
    apply (le_inf le_rfl h.2).trans
    apply lattice.bv_cases_right
    intro z
    exact mem_image (inf_le_right.trans inf_le_right)
      (inf_le_right.trans inf_le_left) (inf_le_left.trans h.1)

theorem factor_image_is_func' {x y f : bSet 𝔹} {Γ : 𝔹}
    (hFunc : Γ ≤ is_func' x y f) : Γ ≤ is_func' x (image x y f) f := by
  apply le_inf
  · exact is_func_of_is_func' hFunc
  · unfold is_total
    apply le_iInf
    intro w₁
    apply lattice.bv_imp_intro
    let Δ : 𝔹 := Γ ⊓ w₁ ∈ᴮ x
    change Δ ≤ ⨆ w₂ : bSet 𝔹, w₂ ∈ᴮ image x y f ⊓ pair w₁ w₂ ∈ᴮ f
    have hImp : Δ ≤ lattice.imp (w₁ ∈ᴮ x)
        (⨆ w₂ : bSet 𝔹, w₂ ∈ᴮ y ⊓ pair w₁ w₂ ∈ᴮ f) :=
      (inf_le_left.trans (is_total_of_is_func' hFunc)).trans (iInf_le _ w₁)
    have hCases : Δ ≤ ⨆ w₂ : bSet 𝔹, w₂ ∈ᴮ y ⊓ pair w₁ w₂ ∈ᴮ f :=
      lattice.bv_context_apply hImp inf_le_right
    apply (le_inf le_rfl hCases).trans
    apply lattice.bv_cases_right
    intro w₂
    apply lattice.bv_use w₂
    apply le_inf
    · exact mem_image (inf_le_right.trans inf_le_right) (inf_le_left.trans inf_le_right)
        (inf_le_right.trans inf_le_left)
    · exact inf_le_right.trans inf_le_right

theorem factor_image_is_function {x y f : bSet 𝔹} {Γ : 𝔹}
    (hFunc : Γ ≤ is_function x y f) : Γ ≤ is_function x (image x y f) f := by
  apply le_inf
  · exact factor_image_is_func' (is_func'_of_is_function hFunc)
  · apply subset_intro
    intro i
    let Δ : 𝔹 := Γ ⊓ f.bval i
    change Δ ≤ f.func i ∈ᴮ prod x (image x y f)
    have hMemF : Δ ≤ f.func i ∈ᴮ f := by
      exact mem.mk'' inf_le_right
    have hMemProd : Δ ≤ f.func i ∈ᴮ prod x y :=
      mem_of_mem_subset' (inf_le_left.trans (subset_prod_of_is_function hFunc)) hMemF
    rw [mem_unfold] at hMemProd
    apply (le_inf le_rfl hMemProd).trans
    apply lattice.bv_cases_right
    intro ij
    let Θ : 𝔹 := Δ ⊓ ((prod x y).bval ij ⊓ f.func i =ᴮ (prod x y).func ij)
    change Θ ≤ f.func i ∈ᴮ prod x (image x y f)
    have hx : Θ ≤ x.func ij.1 ∈ᴮ x := by
      apply mem.mk''
      dsimp [Θ, prod]
      exact inf_le_right.trans inf_le_left |>.trans inf_le_left
    have hy : Θ ≤ y.func ij.2 ∈ᴮ y := by
      apply mem.mk''
      dsimp [Θ, prod]
      exact inf_le_right.trans inf_le_left |>.trans inf_le_right
    have hEq : Θ ≤ f.func i =ᴮ pair (x.func ij.1) (y.func ij.2) := by
      dsimp [Θ, prod]
      exact inf_le_right.trans inf_le_right
    have hPairMemF : Θ ≤ pair (x.func ij.1) (y.func ij.2) ∈ᴮ f := by
      exact subst_congr_mem_left' hEq (inf_le_left.trans hMemF)
    have hImg : Θ ≤ y.func ij.2 ∈ᴮ image x y f :=
      mem_image hPairMemF hx hy
    have hPairProd : Θ ≤ pair (x.func ij.1) (y.func ij.2) ∈ᴮ prod x (image x y f) :=
      prod_mem hx hImg
    exact subst_congr_mem_left' (bv_symm hEq) hPairProd

/-- Bounded preimage of a Boolean-valued relation from `x` into `y`. -/
def preimage (x y f : bSet 𝔹) : bSet 𝔹 :=
  subset.mk (x := x) (fun i : x.type =>
    ⨆ b : bSet 𝔹, b ∈ᴮ y ⊓ pair (x.func i) b ∈ᴮ f)

theorem preimage_subset {x y f : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ preimage x y f ⊆ᴮ x :=
  subset.mk_subset

theorem mem_preimage {x y a b f : bSet 𝔹} {Γ : 𝔹}
    (hMem : Γ ≤ pair a b ∈ᴮ f) (ha : Γ ≤ a ∈ᴮ x) (hb : Γ ≤ b ∈ᴮ y) :
    Γ ≤ a ∈ᴮ preimage x y f := by
  rw [preimage, mem_subset.mk_iff₂]
  rw [mem_unfold] at ha
  apply (le_inf le_rfl ha).trans
  apply lattice.bv_cases_right
  intro i
  let Δ : 𝔹 := Γ ⊓ (x.bval i ⊓ a =ᴮ x.func i)
  change Δ ≤
    ⨆ i : x.type,
      x.bval i ⊓
        (a =ᴮ x.func i ⊓
          ⨆ b : bSet 𝔹, b ∈ᴮ y ⊓ pair (x.func i) b ∈ᴮ f)
  apply lattice.bv_use i
  apply le_inf
  · dsimp [Δ]
    exact inf_le_right.trans inf_le_left
  · apply le_inf
    · dsimp [Δ]
      exact inf_le_right.trans inf_le_right
    · apply lattice.bv_use b
      apply le_inf
      · exact inf_le_left.trans hb
      · have haEq : Δ ≤ a =ᴮ x.func i := by
          dsimp [Δ]
          exact inf_le_right.trans inf_le_right
        have hPairEq : Δ ≤ pair a b =ᴮ pair (x.func i) b :=
          subst_congr_pair_left haEq
        have hPairMem : Δ ≤ pair a b ∈ᴮ f :=
          inf_le_left.trans hMem
        exact subst_congr_mem_left' hPairEq hPairMem

/-- A Boolean-valued relation is injective when equal outputs imply equal inputs. -/
def is_inj (f : bSet 𝔹) : 𝔹 :=
  ⨅ w₁ : bSet 𝔹, ⨅ w₂ : bSet 𝔹, ⨅ v₁ : bSet 𝔹, ⨅ v₂ : bSet 𝔹,
    lattice.imp (pair w₁ v₁ ∈ᴮ f ⊓ pair w₂ v₂ ∈ᴮ f ⊓ v₁ =ᴮ v₂)
      (w₁ =ᴮ w₂)

/-- An injective Boolean-valued function from `x` to `y`. -/
def is_injective_function (x y f : bSet 𝔹) : 𝔹 :=
  is_function x y f ⊓ is_inj f

theorem is_function_of_is_injective_function {x y f : bSet 𝔹} {Γ : 𝔹}
    (h : Γ ≤ is_injective_function x y f) : Γ ≤ is_function x y f :=
  h.trans inf_le_left

theorem is_inj_of_is_injective_function {x y f : bSet 𝔹} {Γ : 𝔹}
    (h : Γ ≤ is_injective_function x y f) : Γ ≤ is_inj f :=
  h.trans inf_le_right

theorem is_func'_of_is_injective_function {x y f : bSet 𝔹} {Γ : 𝔹}
    (h : Γ ≤ is_injective_function x y f) : Γ ≤ is_func' x y f :=
  is_func'_of_is_function (is_function_of_is_injective_function h)

theorem check_is_injective_function {x y f : pSet.{u}}
    (hInj : pSet.is_injective_function x y f) {Γ : 𝔹} :
    Γ ≤ is_injective_function (check x) (check y) (check f) := by
  apply le_inf
  · exact check_is_func hInj.1
  · unfold is_inj
    apply le_iInf
    intro w₁
    apply le_iInf
    intro w₂
    apply le_iInf
    intro v₁
    apply le_iInf
    intro v₂
    apply lattice.bv_imp_intro
    let Δ : 𝔹 := Γ ⊓ (pair w₁ v₁ ∈ᴮ check f ⊓ pair w₂ v₂ ∈ᴮ check f ⊓ v₁ =ᴮ v₂)
    change Δ ≤ w₁ =ᴮ w₂
    have hSubset : Γ ≤ (check f : bSet 𝔹) ⊆ᴮ prod (check x) (check y) :=
      check_subset_prod_of_is_func hInj.1
    have hMem₁ : Δ ≤ pair w₁ v₁ ∈ᴮ check f := by
      dsimp [Δ]
      exact inf_le_right.trans (inf_le_left.trans inf_le_left)
    have hMem₂ : Δ ≤ pair w₂ v₂ ∈ᴮ check f := by
      dsimp [Δ]
      exact inf_le_right.trans (inf_le_left.trans inf_le_right)
    have hProd₁ : Δ ≤ pair w₁ v₁ ∈ᴮ prod (check x) (check y) :=
      mem_of_mem_subset' (inf_le_left.trans hSubset) hMem₁
    have hProd₂ : Δ ≤ pair w₂ v₂ ∈ᴮ prod (check x) (check y) :=
      mem_of_mem_subset' (inf_le_left.trans hSubset) hMem₂
    have hw₁Mem : Δ ≤ w₁ ∈ᴮ check x := (mem_prod_iff.mp hProd₁).1
    have hv₁Mem : Δ ≤ v₁ ∈ᴮ check y := (mem_prod_iff.mp hProd₁).2
    have hw₂Mem : Δ ≤ w₂ ∈ᴮ check x := (mem_prod_iff.mp hProd₂).1
    have hv₂Mem : Δ ≤ v₂ ∈ᴮ check y := (mem_prod_iff.mp hProd₂).2
    rw [mem_unfold] at hw₁Mem
    apply (le_inf le_rfl hw₁Mem).trans
    apply lattice.bv_cases_right
    intro i₁
    let xi₁ : x.Type := cast (check_type (𝔹 := 𝔹) (x := x)) i₁
    let Δ₁ : 𝔹 := Δ ⊓ ((check x).bval i₁ ⊓ w₁ =ᴮ (check x).func i₁)
    change Δ₁ ≤ w₁ =ᴮ w₂
    rw [mem_unfold] at hv₁Mem
    have hv₁MemΔ₁ :
        Δ₁ ≤ ⨆ i : (check y).type, (check y).bval i ⊓ v₁ =ᴮ (check y).func i := by
      dsimp [Δ₁]
      exact inf_le_left.trans hv₁Mem
    apply (le_inf le_rfl hv₁MemΔ₁).trans
    apply lattice.bv_cases_right
    intro j₁
    let yj₁ : y.Type := cast (check_type (𝔹 := 𝔹) (x := y)) j₁
    let Δ₂ : 𝔹 := Δ₁ ⊓ ((check y).bval j₁ ⊓ v₁ =ᴮ (check y).func j₁)
    change Δ₂ ≤ w₁ =ᴮ w₂
    rw [mem_unfold] at hw₂Mem
    have hw₂MemΔ₂ :
        Δ₂ ≤ ⨆ i : (check x).type, (check x).bval i ⊓ w₂ =ᴮ (check x).func i := by
      dsimp [Δ₂, Δ₁]
      exact inf_le_left.trans (inf_le_left.trans hw₂Mem)
    apply (le_inf le_rfl hw₂MemΔ₂).trans
    apply lattice.bv_cases_right
    intro i₂
    let xi₂ : x.Type := cast (check_type (𝔹 := 𝔹) (x := x)) i₂
    let Δ₃ : 𝔹 := Δ₂ ⊓ ((check x).bval i₂ ⊓ w₂ =ᴮ (check x).func i₂)
    change Δ₃ ≤ w₁ =ᴮ w₂
    rw [mem_unfold] at hv₂Mem
    have hv₂MemΔ₃ :
        Δ₃ ≤ ⨆ i : (check y).type, (check y).bval i ⊓ v₂ =ᴮ (check y).func i := by
      dsimp [Δ₃, Δ₂, Δ₁]
      exact inf_le_left.trans (inf_le_left.trans (inf_le_left.trans hv₂Mem))
    apply (le_inf le_rfl hv₂MemΔ₃).trans
    apply lattice.bv_cases_right
    intro j₂
    let yj₂ : y.Type := cast (check_type (𝔹 := 𝔹) (x := y)) j₂
    let Θ : 𝔹 := Δ₃ ⊓ ((check y).bval j₂ ⊓ v₂ =ᴮ (check y).func j₂)
    change Θ ≤ w₁ =ᴮ w₂
    classical
    by_cases hNonzero : ⊥ < Θ
    · have hw₁Eq : Θ ≤ w₁ =ᴮ check (x.Func xi₁) := by
        dsimp [Θ, Δ₃, Δ₂, Δ₁, xi₁]
        rw [check_func]
        exact inf_le_left.trans (inf_le_left.trans (inf_le_left.trans inf_le_right)) |>.trans
          inf_le_right
      have hv₁Eq : Θ ≤ v₁ =ᴮ check (y.Func yj₁) := by
        dsimp [Θ, Δ₃, Δ₂, yj₁]
        rw [check_func]
        exact inf_le_left.trans (inf_le_left.trans inf_le_right) |>.trans inf_le_right
      have hw₂Eq : Θ ≤ w₂ =ᴮ check (x.Func xi₂) := by
        dsimp [Θ, Δ₃, xi₂]
        rw [check_func]
        exact inf_le_left.trans inf_le_right |>.trans inf_le_right
      have hv₂Eq : Θ ≤ v₂ =ᴮ check (y.Func yj₂) := by
        dsimp [Θ, yj₂]
        rw [check_func]
        exact inf_le_right.trans inf_le_right
      have hOutputEqCtx : Θ ≤ v₁ =ᴮ v₂ := by
        dsimp [Θ, Δ₃, Δ₂, Δ₁, Δ]
        exact inf_le_left.trans (inf_le_left.trans (inf_le_left.trans (inf_le_left.trans
          (inf_le_right.trans inf_le_right))))
      have hPair₁Eq : Θ ≤ pair w₁ v₁ =ᴮ check (pSet.pair (x.Func xi₁) (y.Func yj₁)) := by
        have hPair : Θ ≤ pair w₁ v₁ =ᴮ
            pair (check (x.Func xi₁)) (check (y.Func yj₁)) :=
          pair_congr hw₁Eq hv₁Eq
        exact bv_trans hPair (bv_symm check_pair)
      have hPair₂Eq : Θ ≤ pair w₂ v₂ =ᴮ check (pSet.pair (x.Func xi₂) (y.Func yj₂)) := by
        have hPair : Θ ≤ pair w₂ v₂ =ᴮ
            pair (check (x.Func xi₂)) (check (y.Func yj₂)) :=
          pair_congr hw₂Eq hv₂Eq
        exact bv_trans hPair (bv_symm check_pair)
      have hMemF₁ : pSet.pair (x.Func xi₁) (y.Func yj₁) ∈ f := by
        apply check_mem_reflect hNonzero
        exact subst_congr_mem_left' hPair₁Eq
          (by
            dsimp [Θ, Δ₃, Δ₂, Δ₁]
            exact inf_le_left.trans
              (inf_le_left.trans (inf_le_left.trans (inf_le_left.trans hMem₁))))
      have hMemF₂ : pSet.pair (x.Func xi₂) (y.Func yj₂) ∈ f := by
        apply check_mem_reflect hNonzero
        exact subst_congr_mem_left' hPair₂Eq
          (by
            dsimp [Θ, Δ₃, Δ₂, Δ₁]
            exact inf_le_left.trans
              (inf_le_left.trans (inf_le_left.trans (inf_le_left.trans hMem₂))))
      have hOutputEq : PSet.Equiv (y.Func yj₁) (y.Func yj₂) := by
        apply check_eq_reflect hNonzero
        exact bv_trans (bv_symm hv₁Eq) (bv_trans hOutputEqCtx hv₂Eq)
      have hInputEq : PSet.Equiv (x.Func xi₁) (x.Func xi₂) :=
        hInj.2 (x.Func xi₁) (x.Func xi₂) (y.Func yj₁) (y.Func yj₂)
          hMemF₁ hMemF₂ hOutputEq
      exact bv_trans hw₁Eq (bv_trans (check_eq hInputEq) (bv_symm hw₂Eq))
    · apply lattice.bv_exfalso
      by_contra hNotLe
      exact hNonzero (lt_of_le_not_ge bot_le hNotLe)

theorem eq_of_is_inj_of_eq {w₁ w₂ v₁ v₂ f : bSet 𝔹} {Γ : 𝔹}
    (hInj : Γ ≤ is_inj f) (hEq : Γ ≤ v₁ =ᴮ v₂)
    (hMem₁ : Γ ≤ pair w₁ v₁ ∈ᴮ f) (hMem₂ : Γ ≤ pair w₂ v₂ ∈ᴮ f) :
    Γ ≤ w₁ =ᴮ w₂ := by
  have hSpec : Γ ≤ lattice.imp
      (pair w₁ v₁ ∈ᴮ f ⊓ pair w₂ v₂ ∈ᴮ f ⊓ v₁ =ᴮ v₂) (w₁ =ᴮ w₂) :=
    ((((hInj.trans (iInf_le _ w₁)).trans (iInf_le _ w₂)).trans (iInf_le _ v₁)).trans
      (iInf_le _ v₂))
  exact lattice.bv_context_apply hSpec (le_inf (le_inf hMem₁ hMem₂) hEq)

theorem factor_image_is_injective_function {x y f : bSet 𝔹} {Γ : 𝔹}
    (hInj : Γ ≤ is_injective_function x y f) :
    Γ ≤ is_injective_function x (image x y f) f :=
  le_inf (factor_image_is_function (is_function_of_is_injective_function hInj))
    (is_inj_of_is_injective_function hInj)

namespace function

/-- Graph of an indexed Boolean-valued function, bounded by `x × y`.

The index map `F` chooses an output index for each input index; `χ` is the Boolean domain
indicator for the graph. Extensionality and membership hypotheses are supplied to the structure
lemmas rather than stored in the graph term.
-/
def mk' {x y : bSet 𝔹} (F : x.type → y.type) (χ : x.type → 𝔹) : bSet 𝔹 :=
  subset.mk (x := prod x y)
    (fun pr : (prod x y).type => χ pr.1 ⊓ y.func pr.2 =ᴮ y.func (F pr.1))

@[simp] theorem mk'_type {x y : bSet 𝔹} {F : x.type → y.type} {χ : x.type → 𝔹} :
    (mk' F χ).type = (prod x y).type := rfl

@[simp] theorem mk'_func {x y : bSet 𝔹} {F : x.type → y.type} {χ : x.type → 𝔹}
    (pr : (mk' F χ).type) : (mk' F χ).func pr = (prod x y).func pr := rfl

@[simp] theorem mk'_bval {x y : bSet 𝔹} {F : x.type → y.type} {χ : x.type → 𝔹}
    (pr : (mk' F χ).type) :
    (mk' F χ).bval pr =
      (χ pr.1 ⊓ y.func pr.2 =ᴮ y.func (F pr.1)) ⊓ (prod x y).bval pr := rfl

@[simp] theorem mk'_type_forall {x y : bSet 𝔹} {F : x.type → y.type}
    {χ : x.type → 𝔹} {φ : (mk' F χ).type → 𝔹} :
    (⨅ z : (mk' F χ).type, φ z) = ⨅ z : (prod x y).type, φ z := rfl

theorem mk'_is_subset {x y : bSet 𝔹} {F : x.type → y.type} {χ : x.type → 𝔹}
    {Γ : 𝔹} : Γ ≤ mk' F χ ⊆ᴮ prod x y :=
  subset.mk_subset

theorem mk'_is_func {x y : bSet 𝔹} (F : x.type → y.type) (χ : x.type → 𝔹)
    (hExt : ∀ i j {Γ : 𝔹}, Γ ≤ x.func i =ᴮ x.func j →
      Γ ≤ y.func (F i) =ᴮ y.func (F j))
    {Γ : 𝔹} : Γ ≤ is_func (mk' F χ) := by
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
  let Δ₀ : 𝔹 := Γ ⊓ (pair w₁ v₁ ∈ᴮ mk' F χ ⊓ pair w₂ v₂ ∈ᴮ mk' F χ)
  change Δ₀ ≤ lattice.imp (w₁ =ᴮ w₂) (v₁ =ᴮ v₂)
  apply lattice.bv_imp_intro
  let Δ : 𝔹 := Δ₀ ⊓ w₁ =ᴮ w₂
  change Δ ≤ v₁ =ᴮ v₂
  have hMem₁ : Δ ≤ pair w₁ v₁ ∈ᴮ mk' F χ := by
    dsimp [Δ, Δ₀]
    exact inf_le_left.trans (inf_le_right.trans inf_le_left)
  have hMem₂ : Δ ≤ pair w₂ v₂ ∈ᴮ mk' F χ := by
    dsimp [Δ, Δ₀]
    exact inf_le_left.trans (inf_le_right.trans inf_le_right)
  rw [mem_unfold] at hMem₁
  apply (le_inf le_rfl hMem₁).trans
  apply lattice.bv_cases_right
  intro pr₁
  let Δ₁ : 𝔹 := Δ ⊓ ((mk' F χ).bval pr₁ ⊓ pair w₁ v₁ =ᴮ (mk' F χ).func pr₁)
  change Δ₁ ≤ v₁ =ᴮ v₂
  rw [mem_unfold] at hMem₂
  have hMem₂Δ₁ :
      Δ₁ ≤ ⨆ pr : (mk' F χ).type,
        (mk' F χ).bval pr ⊓ pair w₂ v₂ =ᴮ (mk' F χ).func pr := by
    dsimp [Δ₁]
    exact inf_le_left.trans hMem₂
  apply (le_inf le_rfl hMem₂Δ₁).trans
  apply lattice.bv_cases_right
  intro pr₂
  let Θ : 𝔹 := Δ₁ ⊓ ((mk' F χ).bval pr₂ ⊓ pair w₂ v₂ =ᴮ (mk' F χ).func pr₂)
  change Θ ≤ v₁ =ᴮ v₂
  cases pr₁ with
  | mk i j =>
      cases pr₂ with
      | mk i' j' =>
          have hPair₁ : Θ ≤ pair w₁ v₁ =ᴮ pair (x.func i) (y.func j) := by
            dsimp [Θ, Δ₁, mk', subset.mk, prod]
            exact inf_le_left.trans (inf_le_right.trans inf_le_right)
          have hPair₂ : Θ ≤ pair w₂ v₂ =ᴮ pair (x.func i') (y.func j') := by
            dsimp [Θ, mk', subset.mk, prod]
            exact inf_le_right.trans inf_le_right
          have hw₁ : Θ ≤ w₁ =ᴮ x.func i :=
            eq_of_eq_pair_left' hPair₁
          have hw₂ : Θ ≤ w₂ =ᴮ x.func i' :=
            eq_of_eq_pair_left' hPair₂
          have hv₁ : Θ ≤ v₁ =ᴮ y.func j :=
            eq_of_eq_pair_right' hPair₁
          have hv₂ : Θ ≤ v₂ =ᴮ y.func j' :=
            eq_of_eq_pair_right' hPair₂
          have hInput : Θ ≤ w₁ =ᴮ w₂ := by
            dsimp [Θ, Δ₁, Δ]
            exact inf_le_left.trans (inf_le_left.trans inf_le_right)
          have hXi : Θ ≤ x.func i =ᴮ x.func i' :=
            bv_trans (bv_symm hw₁) (bv_trans hInput hw₂)
          have hFi : Θ ≤ y.func (F i) =ᴮ y.func (F i') :=
            hExt i i' hXi
          have hjFi : Θ ≤ y.func j =ᴮ y.func (F i) := by
            dsimp [Θ, Δ₁, mk', subset.mk, prod]
            exact (inf_le_left.trans (inf_le_right.trans inf_le_left)).trans
              (inf_le_left.trans inf_le_right)
          have hj'Fi' : Θ ≤ y.func j' =ᴮ y.func (F i') := by
            dsimp [Θ, mk', subset.mk, prod]
            exact (inf_le_right.trans inf_le_left).trans
              (inf_le_left.trans inf_le_right)
          exact bv_trans hv₁
            (bv_trans hjFi
              (bv_trans hFi (bv_trans (bv_symm hj'Fi') (bv_symm hv₂))))

theorem mk'_is_total {x y : bSet 𝔹} (F : x.type → y.type) (χ : x.type → 𝔹)
    (hMem : ∀ i {Γ : 𝔹}, Γ ≤ x.bval i → Γ ≤ y.bval (F i) ∧ Γ ≤ χ i)
    {Γ : 𝔹} : Γ ≤ is_total x y (mk' F χ) := by
  unfold is_total
  apply le_iInf
  intro z
  apply lattice.bv_imp_intro
  let Δ : 𝔹 := Γ ⊓ z ∈ᴮ x
  change Δ ≤ ⨆ w₂ : bSet 𝔹, w₂ ∈ᴮ y ⊓ pair z w₂ ∈ᴮ mk' F χ
  have hzMem : Δ ≤ z ∈ᴮ x := by
    dsimp [Δ]
    exact inf_le_right
  rw [mem_unfold] at hzMem
  apply (le_inf le_rfl hzMem).trans
  apply lattice.bv_cases_right
  intro i
  let Θ : 𝔹 := Δ ⊓ (x.bval i ⊓ z =ᴮ x.func i)
  change Θ ≤ ⨆ w₂ : bSet 𝔹, w₂ ∈ᴮ y ⊓ pair z w₂ ∈ᴮ mk' F χ
  have hxVal : Θ ≤ x.bval i := by
    dsimp [Θ]
    exact inf_le_right.trans inf_le_left
  have hData := hMem i hxVal
  apply lattice.bv_use (y.func (F i))
  apply le_inf
  · exact mem.mk'' hData.1
  · rw [mem_unfold]
    apply lattice.bv_use (i, F i)
    apply le_inf
    · dsimp [mk', subset.mk, prod]
      exact le_inf (le_inf hData.2 bv_refl) (le_inf hxVal hData.1)
    · have hzEq : Θ ≤ z =ᴮ x.func i := by
        dsimp [Θ]
        exact inf_le_right.trans inf_le_right
      exact pair_congr hzEq bv_refl

theorem mk'_is_function {x y : bSet 𝔹} (F : x.type → y.type) (χ : x.type → 𝔹)
    (hExt : ∀ i j {Γ : 𝔹}, Γ ≤ x.func i =ᴮ x.func j →
      Γ ≤ y.func (F i) =ᴮ y.func (F j))
    (hMem : ∀ i {Γ : 𝔹}, Γ ≤ x.bval i → Γ ≤ y.bval (F i) ∧ Γ ≤ χ i)
    {Γ : 𝔹} : Γ ≤ is_function x y (mk' F χ) :=
  le_inf (le_inf (mk'_is_func F χ hExt) (mk'_is_total F χ hMem)) mk'_is_subset

theorem mk'_is_inj {x y : bSet 𝔹} (F : x.type → y.type) (χ : x.type → 𝔹)
    (hInj : ∀ i j {Γ' : 𝔹}, Γ' ≤ y.func (F i) =ᴮ y.func (F j) →
      Γ' ≤ x.func i =ᴮ x.func j)
    {Γ : 𝔹} : Γ ≤ is_inj (mk' F χ) := by
  unfold is_inj
  apply le_iInf
  intro w₁
  apply le_iInf
  intro w₂
  apply le_iInf
  intro v₁
  apply le_iInf
  intro v₂
  apply lattice.bv_imp_intro
  let Δ : 𝔹 := Γ ⊓ (pair w₁ v₁ ∈ᴮ mk' F χ ⊓ pair w₂ v₂ ∈ᴮ mk' F χ ⊓ v₁ =ᴮ v₂)
  change Δ ≤ w₁ =ᴮ w₂
  have hMem₁ : Δ ≤ pair w₁ v₁ ∈ᴮ mk' F χ := by
    dsimp [Δ]
    exact inf_le_right.trans (inf_le_left.trans inf_le_left)
  have hMem₂ : Δ ≤ pair w₂ v₂ ∈ᴮ mk' F χ := by
    dsimp [Δ]
    exact inf_le_right.trans (inf_le_left.trans inf_le_right)
  rw [mem_unfold] at hMem₁
  apply (le_inf le_rfl hMem₁).trans
  apply lattice.bv_cases_right
  intro pr₁
  let Δ₁ : 𝔹 := Δ ⊓ ((mk' F χ).bval pr₁ ⊓ pair w₁ v₁ =ᴮ (mk' F χ).func pr₁)
  change Δ₁ ≤ w₁ =ᴮ w₂
  rw [mem_unfold] at hMem₂
  have hMem₂Δ₁ :
      Δ₁ ≤ ⨆ pr : (mk' F χ).type,
        (mk' F χ).bval pr ⊓ pair w₂ v₂ =ᴮ (mk' F χ).func pr := by
    dsimp [Δ₁]
    exact inf_le_left.trans hMem₂
  apply (le_inf le_rfl hMem₂Δ₁).trans
  apply lattice.bv_cases_right
  intro pr₂
  let Θ : 𝔹 := Δ₁ ⊓ ((mk' F χ).bval pr₂ ⊓ pair w₂ v₂ =ᴮ (mk' F χ).func pr₂)
  change Θ ≤ w₁ =ᴮ w₂
  cases pr₁ with
  | mk i j =>
      cases pr₂ with
      | mk i' j' =>
          have hPair₁ : Θ ≤ pair w₁ v₁ =ᴮ pair (x.func i) (y.func j) := by
            dsimp [Θ, Δ₁, mk', subset.mk, prod]
            exact inf_le_left.trans (inf_le_right.trans inf_le_right)
          have hPair₂ : Θ ≤ pair w₂ v₂ =ᴮ pair (x.func i') (y.func j') := by
            dsimp [Θ, mk', subset.mk, prod]
            exact inf_le_right.trans inf_le_right
          have hw₁ : Θ ≤ w₁ =ᴮ x.func i :=
            eq_of_eq_pair_left' hPair₁
          have hw₂ : Θ ≤ w₂ =ᴮ x.func i' :=
            eq_of_eq_pair_left' hPair₂
          have hv₁ : Θ ≤ v₁ =ᴮ y.func j :=
            eq_of_eq_pair_right' hPair₁
          have hv₂ : Θ ≤ v₂ =ᴮ y.func j' :=
            eq_of_eq_pair_right' hPair₂
          have hOutput : Θ ≤ v₁ =ᴮ v₂ := by
            dsimp [Θ, Δ₁, Δ]
            exact inf_le_left.trans (inf_le_left.trans (inf_le_right.trans inf_le_right))
          have hjFi : Θ ≤ y.func j =ᴮ y.func (F i) := by
            dsimp [Θ, Δ₁, mk', subset.mk, prod]
            exact (inf_le_left.trans (inf_le_right.trans inf_le_left)).trans
              (inf_le_left.trans inf_le_right)
          have hj'Fi' : Θ ≤ y.func j' =ᴮ y.func (F i') := by
            dsimp [Θ, mk', subset.mk, prod]
            exact (inf_le_right.trans inf_le_left).trans
              (inf_le_left.trans inf_le_right)
          have hFi : Θ ≤ y.func (F i) =ᴮ y.func (F i') :=
            bv_trans (bv_symm hjFi)
              (bv_trans (bv_symm hv₁) (bv_trans hOutput (bv_trans hv₂ hj'Fi')))
          have hXi : Θ ≤ x.func i =ᴮ x.func i' :=
            hInj i i' hFi
          exact bv_trans hw₁ (bv_trans hXi (bv_symm hw₂))

end function

/-- The inverse graph of an injective Boolean-valued function, bounded by its image. -/
def inj_inverse {x y f : bSet 𝔹} {Γ : 𝔹}
    (hFunc : Γ ≤ is_func' x y f) (hInj : Γ ≤ is_inj f) : bSet 𝔹 :=
  let _keepFunc : Γ ≤ is_func' x y f := hFunc
  let _keepInj : Γ ≤ is_inj f := hInj
  subset.mk (x := prod (image x y f) x) (fun pr : (prod (image x y f) x).type =>
    pair (x.func pr.2) ((image x y f).func pr.1) ∈ᴮ f)

theorem mem_inj_inverse_components {x y f : bSet 𝔹} {Γ Γ' : 𝔹}
    {hFunc : Γ ≤ is_func' x y f} {hInj : Γ ≤ is_inj f} {b a : bSet 𝔹}
    (hMem : Γ' ≤ pair b a ∈ᴮ inj_inverse hFunc hInj) :
    Γ' ≤ a ∈ᴮ x ∧ Γ' ≤ b ∈ᴮ y ∧ Γ' ≤ pair a b ∈ᴮ f := by
  unfold inj_inverse at hMem
  rw [mem_subset.mk_iff₂] at hMem
  refine ⟨?_, ?_, ?_⟩
  · apply (le_inf le_rfl hMem).trans
    apply lattice.bv_cases_right
    intro pr
    let Δ : 𝔹 := Γ' ⊓
      ((prod (image x y f) x).bval pr ⊓
        (pair b a =ᴮ (prod (image x y f) x).func pr ⊓
          pair (x.func pr.2) ((image x y f).func pr.1) ∈ᴮ f))
    change Δ ≤ a ∈ᴮ x
    have hxVal : Δ ≤ x.bval pr.2 := by
      dsimp [Δ, prod]
      exact inf_le_right.trans inf_le_left |>.trans inf_le_right
    have hPairEq : Δ ≤ pair b a =ᴮ pair ((image x y f).func pr.1) (x.func pr.2) := by
      dsimp [Δ, prod]
      exact inf_le_right.trans inf_le_right |>.trans inf_le_left
    have haEq : Δ ≤ a =ᴮ x.func pr.2 :=
      eq_of_eq_pair_right' hPairEq
    have hxMem : Δ ≤ x.func pr.2 ∈ᴮ x :=
      mem.mk'' hxVal
    exact subst_congr_mem_left' (bv_symm haEq) hxMem
  · apply (le_inf le_rfl hMem).trans
    apply lattice.bv_cases_right
    intro pr
    let Δ : 𝔹 := Γ' ⊓
      ((prod (image x y f) x).bval pr ⊓
        (pair b a =ᴮ (prod (image x y f) x).func pr ⊓
          pair (x.func pr.2) ((image x y f).func pr.1) ∈ᴮ f))
    change Δ ≤ b ∈ᴮ y
    have hImgVal : Δ ≤ (image x y f).bval pr.1 := by
      dsimp [Δ, prod]
      exact inf_le_right.trans inf_le_left |>.trans inf_le_left
    have hPairEq : Δ ≤ pair b a =ᴮ pair ((image x y f).func pr.1) (x.func pr.2) := by
      dsimp [Δ, prod]
      exact inf_le_right.trans inf_le_right |>.trans inf_le_left
    have hbEq : Δ ≤ b =ᴮ (image x y f).func pr.1 :=
      eq_of_eq_pair_left' hPairEq
    have hImgMem : Δ ≤ (image x y f).func pr.1 ∈ᴮ image x y f :=
      mem.mk'' hImgVal
    have hyMem : Δ ≤ (image x y f).func pr.1 ∈ᴮ y :=
      mem_of_mem_subset' image_subset hImgMem
    exact subst_congr_mem_left' (bv_symm hbEq) hyMem
  · apply (le_inf le_rfl hMem).trans
    apply lattice.bv_cases_right
    intro pr
    let Δ : 𝔹 := Γ' ⊓
      ((prod (image x y f) x).bval pr ⊓
        (pair b a =ᴮ (prod (image x y f) x).func pr ⊓
          pair (x.func pr.2) ((image x y f).func pr.1) ∈ᴮ f))
    change Δ ≤ pair a b ∈ᴮ f
    have hPairEq : Δ ≤ pair b a =ᴮ pair ((image x y f).func pr.1) (x.func pr.2) := by
      dsimp [Δ, prod]
      exact inf_le_right.trans inf_le_right |>.trans inf_le_left
    have hbEq : Δ ≤ b =ᴮ (image x y f).func pr.1 :=
      eq_of_eq_pair_left' hPairEq
    have haEq : Δ ≤ a =ᴮ x.func pr.2 :=
      eq_of_eq_pair_right' hPairEq
    have hOrigMem : Δ ≤ pair (x.func pr.2) ((image x y f).func pr.1) ∈ᴮ f := by
      dsimp [Δ]
      exact inf_le_right.trans inf_le_right |>.trans inf_le_right
    have hEq : Δ ≤ pair a b =ᴮ pair (x.func pr.2) ((image x y f).func pr.1) :=
      pair_congr haEq hbEq
    exact subst_congr_mem_left' (bv_symm hEq) hOrigMem

theorem mem_inj_inverse {x y f : bSet 𝔹} {Γ Γ' : 𝔹}
    {hFunc : Γ ≤ is_func' x y f} {hInj : Γ ≤ is_inj f} {b a : bSet 𝔹}
    (ha : Γ' ≤ a ∈ᴮ x) (hb : Γ' ≤ b ∈ᴮ y) (hMem : Γ' ≤ pair a b ∈ᴮ f) :
    Γ' ≤ pair b a ∈ᴮ inj_inverse hFunc hInj := by
  rw [inj_inverse, mem_subset.mk_iff₂]
  rw [mem_unfold] at ha
  apply (le_inf le_rfl ha).trans
  apply lattice.bv_cases_right
  intro i
  let Δ : 𝔹 := Γ' ⊓ (x.bval i ⊓ a =ᴮ x.func i)
  have hbΔ : Δ ≤ b ∈ᴮ y := by
    exact inf_le_left.trans hb
  rw [mem_unfold] at hbΔ
  apply (le_inf le_rfl hbΔ).trans
  apply lattice.bv_cases_right
  intro j
  let Θ : 𝔹 := Δ ⊓ (y.bval j ⊓ b =ᴮ y.func j)
  change Θ ≤
    ⨆ pr : (prod (image x y f) x).type,
      (prod (image x y f) x).bval pr ⊓
        (pair b a =ᴮ (prod (image x y f) x).func pr ⊓
          pair (x.func pr.2) ((image x y f).func pr.1) ∈ᴮ f)
  apply lattice.bv_use (j, i)
  have hxVal : Θ ≤ x.bval i := by
    dsimp [Θ, Δ]
    exact inf_le_left.trans inf_le_right |>.trans inf_le_left
  have hyVal : Θ ≤ y.bval j := by
    dsimp [Θ]
    exact inf_le_right.trans inf_le_left
  have haEq : Θ ≤ a =ᴮ x.func i := by
    dsimp [Θ, Δ]
    exact inf_le_left.trans inf_le_right |>.trans inf_le_right
  have hbEq : Θ ≤ b =ᴮ y.func j := by
    dsimp [Θ]
    exact inf_le_right.trans inf_le_right
  have hPairMem : Θ ≤ pair (x.func i) (y.func j) ∈ᴮ f := by
    have hPairEq : Θ ≤ pair a b =ᴮ pair (x.func i) (y.func j) :=
      pair_congr haEq hbEq
    have hOrigMem : Θ ≤ pair a b ∈ᴮ f :=
      (inf_le_left.trans inf_le_left).trans hMem
    exact subst_congr_mem_left' hPairEq hOrigMem
  have hImgVal : Θ ≤ (image x y f).bval j := by
    dsimp [image, subset.mk]
    apply le_inf
    · apply lattice.bv_use (x.func i)
      apply le_inf
      · exact mem.mk'' hxVal
      · exact hPairMem
    · exact hyVal
  apply le_inf
  · dsimp [prod]
    exact le_inf hImgVal hxVal
  · apply le_inf
    · dsimp [prod]
      exact pair_congr hbEq haEq
    · simpa [image] using hPairMem

theorem inj_inverse_is_func {x y f : bSet 𝔹} {Γ : 𝔹}
    (hFunc : Γ ≤ is_func' x y f) (hInj : Γ ≤ is_inj f) :
    Γ ≤ is_func (inj_inverse hFunc hInj) := by
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
  let Δ : 𝔹 := Γ ⊓
    (pair w₁ v₁ ∈ᴮ inj_inverse hFunc hInj ⊓
      pair w₂ v₂ ∈ᴮ inj_inverse hFunc hInj)
  change Δ ≤ lattice.imp (w₁ =ᴮ w₂) (v₁ =ᴮ v₂)
  apply lattice.bv_imp_intro
  let Θ : 𝔹 := Δ ⊓ w₁ =ᴮ w₂
  change Θ ≤ v₁ =ᴮ v₂
  have hMem₁ : Θ ≤ pair w₁ v₁ ∈ᴮ inj_inverse hFunc hInj := by
    dsimp [Θ, Δ]
    exact inf_le_left.trans inf_le_right |>.trans inf_le_left
  have hMem₂ : Θ ≤ pair w₂ v₂ ∈ᴮ inj_inverse hFunc hInj := by
    dsimp [Θ, Δ]
    exact inf_le_left.trans inf_le_right |>.trans inf_le_right
  have hOrig₁ : Θ ≤ pair v₁ w₁ ∈ᴮ f :=
    (mem_inj_inverse_components hMem₁).2.2
  have hOrig₂ : Θ ≤ pair v₂ w₂ ∈ᴮ f :=
    (mem_inj_inverse_components hMem₂).2.2
  have hEq : Θ ≤ w₁ =ᴮ w₂ := by
    dsimp [Θ]
    exact inf_le_right
  have hSpec : Θ ≤ lattice.imp
      (pair v₁ w₁ ∈ᴮ f ⊓ pair v₂ w₂ ∈ᴮ f ⊓ w₁ =ᴮ w₂) (v₁ =ᴮ v₂) :=
    (((((inf_le_left.trans inf_le_left).trans hInj).trans (iInf_le _ v₁)).trans (iInf_le _ v₂)).trans
      (iInf_le _ w₁)).trans (iInf_le _ w₂)
  exact lattice.bv_context_apply hSpec (le_inf (le_inf hOrig₁ hOrig₂) hEq)

theorem inj_inverse_is_total {x y f : bSet 𝔹} {Γ : 𝔹}
    (hFunc : Γ ≤ is_func' x y f) (hInj : Γ ≤ is_inj f) :
    Γ ≤ is_total (image x y f) x (inj_inverse hFunc hInj) := by
  unfold is_total
  apply le_iInf
  intro z
  apply lattice.bv_imp_intro
  let Δ : 𝔹 := Γ ⊓ z ∈ᴮ image x y f
  change Δ ≤ ⨆ w₂ : bSet 𝔹, w₂ ∈ᴮ x ⊓ pair z w₂ ∈ᴮ inj_inverse hFunc hInj
  have hzImg : Δ ≤ z ∈ᴮ image x y f :=
    inf_le_right
  have hzInfo := (mem_image_iff.mp hzImg)
  apply (le_inf le_rfl hzInfo.2).trans
  apply lattice.bv_cases_right
  intro a
  apply lattice.bv_use a
  apply le_inf
  · exact inf_le_right.trans inf_le_left
  · exact mem_inj_inverse (inf_le_right.trans inf_le_left) (inf_le_left.trans hzInfo.1)
      (inf_le_right.trans inf_le_right)

theorem inj_inverse_is_func' {x y f : bSet 𝔹} {Γ : 𝔹}
    (hFunc : Γ ≤ is_func' x y f) (hInj : Γ ≤ is_inj f) :
    Γ ≤ is_func' (image x y f) x (inj_inverse hFunc hInj) :=
  le_inf (inj_inverse_is_func hFunc hInj) (inj_inverse_is_total hFunc hInj)

theorem inj_inverse_subset_prod {x y f : bSet 𝔹} {Γ : 𝔹}
    (hFunc : Γ ≤ is_func' x y f) (hInj : Γ ≤ is_inj f) :
    Γ ≤ inj_inverse hFunc hInj ⊆ᴮ prod (image x y f) x :=
  subset.mk_subset

theorem inj_inverse_is_function {x y f : bSet 𝔹} {Γ : 𝔹}
    (hFunc : Γ ≤ is_func' x y f) (hInj : Γ ≤ is_inj f) :
    Γ ≤ is_function (image x y f) x (inj_inverse hFunc hInj) :=
  le_inf (inj_inverse_is_func' hFunc hInj) (inj_inverse_subset_prod hFunc hInj)

theorem inj_inverse_is_inj {x y f : bSet 𝔹} {Γ : 𝔹}
    (hFunc : Γ ≤ is_func' x y f) (hInj : Γ ≤ is_inj f) :
    Γ ≤ is_inj (inj_inverse hFunc hInj) := by
  unfold is_inj
  apply le_iInf
  intro w₁
  apply le_iInf
  intro w₂
  apply le_iInf
  intro v₁
  apply le_iInf
  intro v₂
  apply lattice.bv_imp_intro
  let Δ : 𝔹 := Γ ⊓
    (pair w₁ v₁ ∈ᴮ inj_inverse hFunc hInj ⊓
      pair w₂ v₂ ∈ᴮ inj_inverse hFunc hInj ⊓ v₁ =ᴮ v₂)
  change Δ ≤ w₁ =ᴮ w₂
  have hMem₁ : Δ ≤ pair w₁ v₁ ∈ᴮ inj_inverse hFunc hInj := by
    dsimp [Δ]
    exact inf_le_right.trans inf_le_left |>.trans inf_le_left
  have hMem₂ : Δ ≤ pair w₂ v₂ ∈ᴮ inj_inverse hFunc hInj := by
    dsimp [Δ]
    exact inf_le_right.trans inf_le_left |>.trans inf_le_right
  have hEq : Δ ≤ v₁ =ᴮ v₂ := by
    dsimp [Δ]
    exact inf_le_right.trans inf_le_right
  have hOrig₁ : Δ ≤ pair v₁ w₁ ∈ᴮ f :=
    (mem_inj_inverse_components hMem₁).2.2
  have hOrig₂ : Δ ≤ pair v₂ w₂ ∈ᴮ f :=
    (mem_inj_inverse_components hMem₂).2.2
  exact eq_of_is_func'_of_eq (inf_le_left.trans hFunc) hEq hOrig₁ hOrig₂

/-- A Boolean-valued relation is surjective from `x` onto `y`. -/
def is_surj (x y f : bSet 𝔹) : 𝔹 :=
  ⨅ v : bSet 𝔹, lattice.imp (v ∈ᴮ y)
    (⨆ w : bSet 𝔹, w ∈ᴮ x ⊓ pair w v ∈ᴮ f)

/-- Restrict a total functional relation to the actual product `x × y`. -/
def function_of_func' {x y f : bSet 𝔹} {Γ : 𝔹}
    (h : Γ ≤ is_func' x y f) : bSet 𝔹 :=
  let _keep : Γ ≤ is_func' x y f := h
  binary_inter f (prod x y)

theorem function_of_func'_subset {x y f : bSet 𝔹} {Γ : 𝔹}
    {h : Γ ≤ is_func' x y f} :
    Γ ≤ function_of_func' h ⊆ᴮ f :=
  binary_inter_subset_left

theorem mem_function_of_func'_iff {x y f z : bSet 𝔹} {Γ Γ' : 𝔹}
    {h : Γ ≤ is_func' x y f} :
    Γ' ≤ z ∈ᴮ function_of_func' h ↔ Γ' ≤ z ∈ᴮ f ∧ Γ' ≤ z ∈ᴮ prod x y :=
  mem_binary_inter_iff

theorem function_of_func'_is_function {x y f : bSet 𝔹} {Γ : 𝔹}
    (h : Γ ≤ is_func' x y f) : Γ ≤ is_function x y (function_of_func' h) := by
  apply le_inf
  · apply le_inf
    · unfold is_func
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
      let Δ : 𝔹 := (Γ ⊓
        (pair w₁ v₁ ∈ᴮ function_of_func' h ⊓
          pair w₂ v₂ ∈ᴮ function_of_func' h)) ⊓ w₁ =ᴮ w₂
      change Δ ≤ v₁ =ᴮ v₂
      have hCtx : Δ ≤ Γ := by
        dsimp [Δ]
        exact inf_le_left.trans inf_le_left
      have hEq : Δ ≤ w₁ =ᴮ w₂ := by
        dsimp [Δ]
        exact inf_le_right
      have hMem₁ : Δ ≤ pair w₁ v₁ ∈ᴮ f := by
        have hMem : Δ ≤ pair w₁ v₁ ∈ᴮ function_of_func' h := by
          dsimp [Δ]
          exact inf_le_left.trans inf_le_right |>.trans inf_le_left
        exact (mem_function_of_func'_iff.mp hMem).1
      have hMem₂ : Δ ≤ pair w₂ v₂ ∈ᴮ f := by
        have hMem : Δ ≤ pair w₂ v₂ ∈ᴮ function_of_func' h := by
          dsimp [Δ]
          exact inf_le_left.trans inf_le_right |>.trans inf_le_right
        exact (mem_function_of_func'_iff.mp hMem).1
      exact eq_of_is_func'_of_eq (hCtx.trans h) hEq hMem₁ hMem₂
    · unfold is_total
      apply le_iInf
      intro a
      apply lattice.bv_imp_intro
      let Δ : 𝔹 := Γ ⊓ a ∈ᴮ x
      change Δ ≤ ⨆ b : bSet 𝔹, b ∈ᴮ y ⊓ pair a b ∈ᴮ function_of_func' h
      have hImp : Δ ≤ lattice.imp (a ∈ᴮ x)
          (⨆ b : bSet 𝔹, b ∈ᴮ y ⊓ pair a b ∈ᴮ f) :=
        (inf_le_left.trans (is_total_of_is_func' h)).trans (iInf_le _ a)
      have hCases : Δ ≤ ⨆ b : bSet 𝔹, b ∈ᴮ y ⊓ pair a b ∈ᴮ f :=
        lattice.bv_context_apply hImp inf_le_right
      apply (le_inf le_rfl hCases).trans
      apply lattice.bv_cases_right
      intro b
      let Θ : 𝔹 := Δ ⊓ (b ∈ᴮ y ⊓ pair a b ∈ᴮ f)
      apply lattice.bv_use b
      apply le_inf
      · exact inf_le_right.trans inf_le_left
      · apply mem_function_of_func'_iff.mpr
        constructor
        · exact inf_le_right.trans inf_le_right
        · exact prod_mem (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_left)
  · exact binary_inter_subset_right

theorem function_of_func'_surj_of_surj {x y f : bSet 𝔹} {Γ : 𝔹}
    (hFunc : Γ ≤ is_func' x y f) (hSurj : Γ ≤ is_surj x y f) :
    Γ ≤ is_surj x y (function_of_func' hFunc) := by
  unfold is_surj
  apply le_iInf
  intro b
  apply lattice.bv_imp_intro
  let Δ : 𝔹 := Γ ⊓ b ∈ᴮ y
  change Δ ≤ ⨆ a : bSet 𝔹, a ∈ᴮ x ⊓ pair a b ∈ᴮ function_of_func' hFunc
  have hImp : Δ ≤ lattice.imp (b ∈ᴮ y)
      (⨆ a : bSet 𝔹, a ∈ᴮ x ⊓ pair a b ∈ᴮ f) :=
    (inf_le_left.trans hSurj).trans (iInf_le _ b)
  have hCases : Δ ≤ ⨆ a : bSet 𝔹, a ∈ᴮ x ⊓ pair a b ∈ᴮ f :=
    lattice.bv_context_apply hImp inf_le_right
  apply (le_inf le_rfl hCases).trans
  apply lattice.bv_cases_right
  intro a
  let Θ : 𝔹 := Δ ⊓ (a ∈ᴮ x ⊓ pair a b ∈ᴮ f)
  apply lattice.bv_use a
  apply le_inf
  · exact inf_le_right.trans inf_le_left
  · apply mem_function_of_func'_iff.mpr
    constructor
    · exact inf_le_right.trans inf_le_right
    · exact prod_mem (inf_le_right.trans inf_le_left) (inf_le_left.trans inf_le_right)

theorem surj_image {x y f : bSet 𝔹} {Γ : 𝔹}
    (hFunc : Γ ≤ is_func' x y f) : Γ ≤ is_surj x (image x y f) f := by
  let _keep : Γ ≤ is_func' x y f := hFunc
  unfold is_surj
  apply le_iInf
  intro b
  apply lattice.bv_imp_intro
  let Δ : 𝔹 := Γ ⊓ b ∈ᴮ image x y f
  change Δ ≤ ⨆ a : bSet 𝔹, a ∈ᴮ x ⊓ pair a b ∈ᴮ f
  exact (mem_image_iff.mp inf_le_right).2

theorem image_eq_codomain_of_surj {x y f : bSet 𝔹} {Γ : 𝔹}
    (hSurj : Γ ≤ is_surj x y f) : Γ ≤ image x y f =ᴮ y := by
  apply subset_ext
  · exact image_subset
  · apply subset_intro
    intro i
    let Δ : 𝔹 := Γ ⊓ y.bval i
    change Δ ≤ y.func i ∈ᴮ image x y f
    rw [mem_image_iff]
    constructor
    · apply mem.mk''
      dsimp [Δ]
      exact inf_le_right
    · have hImp : Δ ≤ lattice.imp (y.func i ∈ᴮ y)
          (⨆ a : bSet 𝔹, a ∈ᴮ x ⊓ pair a (y.func i) ∈ᴮ f) :=
        (inf_le_left.trans hSurj).trans (iInf_le _ (y.func i))
      have hyMem : Δ ≤ y.func i ∈ᴮ y := by
        apply mem.mk''
        dsimp [Δ]
        exact inf_le_right
      exact lattice.bv_context_apply hImp hyMem

theorem function_of_func'_inj_of_inj {x y f : bSet 𝔹} {Γ : 𝔹}
    {hFunc : Γ ≤ is_func' x y f} (hInj : Γ ≤ is_inj f) :
    Γ ≤ is_inj (function_of_func' hFunc) := by
  unfold is_inj
  apply le_iInf
  intro w₁
  apply le_iInf
  intro w₂
  apply le_iInf
  intro v₁
  apply le_iInf
  intro v₂
  apply lattice.bv_imp_intro
  let Δ : 𝔹 := Γ ⊓
    (pair w₁ v₁ ∈ᴮ function_of_func' hFunc ⊓
      pair w₂ v₂ ∈ᴮ function_of_func' hFunc ⊓ v₁ =ᴮ v₂)
  change Δ ≤ w₁ =ᴮ w₂
  have hMem₁ : Δ ≤ pair w₁ v₁ ∈ᴮ f := by
    have hMem : Δ ≤ pair w₁ v₁ ∈ᴮ function_of_func' hFunc := by
      dsimp [Δ]
      exact inf_le_right.trans inf_le_left |>.trans inf_le_left
    exact (mem_function_of_func'_iff.mp hMem).1
  have hMem₂ : Δ ≤ pair w₂ v₂ ∈ᴮ f := by
    have hMem : Δ ≤ pair w₂ v₂ ∈ᴮ function_of_func' hFunc := by
      dsimp [Δ]
      exact inf_le_right.trans inf_le_left |>.trans inf_le_right
    exact (mem_function_of_func'_iff.mp hMem).1
  have hEq : Δ ≤ v₁ =ᴮ v₂ := by
    dsimp [Δ]
    exact inf_le_right.trans inf_le_right
  exact eq_of_is_inj_of_eq (inf_le_left.trans hInj) hEq hMem₁ hMem₂

theorem inj_inverse_is_surj {x y f : bSet 𝔹} {Γ : 𝔹}
    (hFunc : Γ ≤ is_func' x y f) (hInj : Γ ≤ is_inj f) :
    Γ ≤ is_surj (image x y f) x (inj_inverse hFunc hInj) := by
  unfold is_surj
  apply le_iInf
  intro z
  apply lattice.bv_imp_intro
  let Δ : 𝔹 := Γ ⊓ z ∈ᴮ x
  change Δ ≤ ⨆ w : bSet 𝔹, w ∈ᴮ image x y f ⊓ pair w z ∈ᴮ inj_inverse hFunc hInj
  have hImp : Δ ≤ lattice.imp (z ∈ᴮ x)
      (⨆ w₂ : bSet 𝔹, w₂ ∈ᴮ y ⊓ pair z w₂ ∈ᴮ f) :=
    (inf_le_left.trans (is_total_of_is_func' hFunc)).trans (iInf_le _ z)
  have hCases : Δ ≤ ⨆ w₂ : bSet 𝔹, w₂ ∈ᴮ y ⊓ pair z w₂ ∈ᴮ f :=
    lattice.bv_context_apply hImp inf_le_right
  apply (le_inf le_rfl hCases).trans
  apply lattice.bv_cases_right
  intro w
  apply lattice.bv_use w
  apply le_inf
  · exact mem_image (inf_le_right.trans inf_le_right) (inf_le_left.trans inf_le_right)
      (inf_le_right.trans inf_le_left)
  · exact mem_inj_inverse (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_left)
      (inf_le_right.trans inf_le_right)

/-- The inverse function associated to an injective Boolean-valued function. -/
def injective_function_inverse {x y f : bSet 𝔹} {Γ : 𝔹}
    (hInj : Γ ≤ is_injective_function x y f) : bSet 𝔹 :=
  inj_inverse (is_func'_of_is_injective_function hInj) (is_inj_of_is_injective_function hInj)

theorem injective_function_inverse_is_injective_function {x y f : bSet 𝔹} {Γ : 𝔹}
    {hInj : Γ ≤ is_injective_function x y f} :
    Γ ≤ is_injective_function (image x y f) x (injective_function_inverse hInj) :=
  le_inf
    (inj_inverse_is_function (is_func'_of_is_injective_function hInj)
      (is_inj_of_is_injective_function hInj))
    (inj_inverse_is_inj (is_func'_of_is_injective_function hInj)
      (is_inj_of_is_injective_function hInj))

theorem injective_function_inverse_is_inj {x y f : bSet 𝔹} {Γ : 𝔹}
    {hInj : Γ ≤ is_injective_function x y f} :
    Γ ≤ is_inj (injective_function_inverse hInj) :=
  is_inj_of_is_injective_function injective_function_inverse_is_injective_function

/-- A functional total relation from `x` to `y` that is surjective onto `y`. -/
def is_surj_onto (x y f : bSet 𝔹) : 𝔹 :=
  is_func' x y f ⊓ is_surj x y f

/-- There is an internal surjection from `x` onto `y`. -/
def surjects_onto (x y : bSet 𝔹) : 𝔹 :=
  ⨆ f : bSet 𝔹, is_surj_onto x y f

/-- `x` is internally larger than `y` when some subset of `x` surjects onto `y`. -/
def larger_than (x y : bSet 𝔹) : 𝔹 :=
  ⨆ S : bSet 𝔹, ⨆ f : bSet 𝔹, S ⊆ᴮ x ⊓ is_func' S y f ⊓ is_surj S y f

theorem exists_surjection_of_surjects_onto {x y : bSet 𝔹} {Γ : 𝔹}
    (hSurj : Γ ≤ surjects_onto x y) :
    Γ ≤ ⨆ f : bSet 𝔹, is_function x y f ⊓ is_surj x y f := by
  unfold surjects_onto at hSurj
  apply (le_inf le_rfl hSurj).trans
  apply lattice.bv_cases_right
  intro f
  let Δ : 𝔹 := Γ ⊓ is_surj_onto x y f
  have hFunc : Δ ≤ is_func' x y f := by
    dsimp [Δ]
    exact inf_le_right.trans inf_le_left
  have hSurjF : Δ ≤ is_surj x y f := by
    dsimp [Δ]
    exact inf_le_right.trans inf_le_right
  apply lattice.bv_use (function_of_func' hFunc)
  exact le_inf (function_of_func'_is_function hFunc)
    (function_of_func'_surj_of_surj hFunc hSurjF)

theorem larger_than_domain_subset {x y S : bSet 𝔹} {Γ : 𝔹}
    (h : Γ ≤ ⨆ f : bSet 𝔹, S ⊆ᴮ x ⊓ is_func' S y f ⊓ is_surj S y f) :
    Γ ≤ S ⊆ᴮ x := by
  apply (le_inf le_rfl h).trans
  apply lattice.bv_cases_right
  intro f
  exact inf_le_right.trans inf_le_left |>.trans inf_le_left

theorem larger_than_of_surjects_onto {x y : bSet 𝔹} {Γ : 𝔹}
    (hSurj : Γ ≤ surjects_onto x y) : Γ ≤ larger_than x y := by
  unfold surjects_onto at hSurj
  unfold larger_than
  apply (le_inf le_rfl hSurj).trans
  apply lattice.bv_cases_right
  intro f
  apply lattice.bv_use x
  apply lattice.bv_use f
  apply le_inf
  · apply le_inf
    · exact subset_self (x := x) (Γ := Γ ⊓ is_surj_onto x y f)
    · simpa [is_surj_onto] using
        (inf_le_right.trans inf_le_left :
          Γ ⊓ is_surj_onto x y f ≤ is_func' x y f)
  · simpa [is_surj_onto] using
      (inf_le_right.trans inf_le_right :
        Γ ⊓ is_surj_onto x y f ≤ is_surj x y f)

/-- There is an internal injection from `x` into `y`. -/
def injects_into (x y : bSet 𝔹) : 𝔹 :=
  ⨆ f : bSet 𝔹, is_func' x y f ⊓ is_inj f

/-- There is an internal injective function from `x` into `y`. -/
def injection_into (x y : bSet 𝔹) : 𝔹 :=
  ⨆ f : bSet 𝔹, is_injective_function x y f

theorem injection_into_of_injects_into {x y : bSet 𝔹} {Γ : 𝔹}
    (h : Γ ≤ injects_into x y) : Γ ≤ injection_into x y := by
  unfold injects_into at h
  unfold injection_into
  apply (le_inf le_rfl h).trans
  apply lattice.bv_cases_right
  intro f
  let Δ : 𝔹 := Γ ⊓ (is_func' x y f ⊓ is_inj f)
  have hFunc : Δ ≤ is_func' x y f := by
    dsimp [Δ]
    exact inf_le_right.trans inf_le_left
  have hInj : Δ ≤ is_inj f := by
    dsimp [Δ]
    exact inf_le_right.trans inf_le_right
  apply lattice.bv_use (function_of_func' hFunc)
  exact le_inf (function_of_func'_is_function hFunc) (function_of_func'_inj_of_inj hInj)

theorem injects_into_of_injection_into {x y : bSet 𝔹} {Γ : 𝔹}
    (h : Γ ≤ injection_into x y) : Γ ≤ injects_into x y := by
  unfold injection_into at h
  unfold injects_into
  apply (le_inf le_rfl h).trans
  apply lattice.bv_cases_right
  intro f
  apply lattice.bv_use f
  apply le_inf
  · exact is_func'_of_is_injective_function inf_le_right
  · exact is_inj_of_is_injective_function inf_le_right

theorem injects_into_iff_injection_into {x y : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ injects_into x y ↔ Γ ≤ injection_into x y :=
  ⟨injection_into_of_injects_into, injects_into_of_injection_into⟩

/-- Composition of two Boolean-valued functional relations, bounded by `x × z`. -/
def is_func'_comp {x y z f g : bSet 𝔹} {Γ : 𝔹}
    (hF : Γ ≤ is_func' x y f) (hG : Γ ≤ is_func' y z g) : bSet 𝔹 :=
  let _keepF : Γ ≤ is_func' x y f := hF
  let _keepG : Γ ≤ is_func' y z g := hG
  subset.mk (x := prod x z) (fun pr : (prod x z).type =>
    ⨆ b : bSet 𝔹,
      b ∈ᴮ y ⊓ pair (x.func pr.1) b ∈ᴮ f ⊓ pair b (z.func pr.2) ∈ᴮ g)

theorem is_func'_comp_subset_prod {x y z f g : bSet 𝔹} {Γ Γ' : 𝔹}
    (hF : Γ ≤ is_func' x y f) (hG : Γ ≤ is_func' y z g) :
    Γ' ≤ is_func'_comp hF hG ⊆ᴮ prod x z :=
  subset.mk_subset

theorem mem_is_func'_comp_components {x y z f g : bSet 𝔹} {Γ Γ' : 𝔹}
    {hF : Γ ≤ is_func' x y f} {hG : Γ ≤ is_func' y z g} {a c : bSet 𝔹}
    (hMem : Γ' ≤ pair a c ∈ᴮ is_func'_comp hF hG) :
    Γ' ≤ a ∈ᴮ x ∧ Γ' ≤ c ∈ᴮ z ∧
      Γ' ≤ ⨆ b : bSet 𝔹, b ∈ᴮ y ⊓ (pair a b ∈ᴮ f ⊓ pair b c ∈ᴮ g) := by
  refine ⟨?_, ?_, ?_⟩
  · have hProd : Γ' ≤ pair a c ∈ᴮ prod x z :=
      mem_of_mem_subset' (is_func'_comp_subset_prod hF hG) hMem
    exact (mem_prod_iff.mp hProd).1
  · have hProd : Γ' ≤ pair a c ∈ᴮ prod x z :=
      mem_of_mem_subset' (is_func'_comp_subset_prod hF hG) hMem
    exact (mem_prod_iff.mp hProd).2
  · rw [is_func'_comp, mem_subset.mk_iff₂] at hMem
    apply (le_inf le_rfl hMem).trans
    apply lattice.bv_cases_right
    intro pr
    let Δ : 𝔹 := Γ' ⊓
      ((prod x z).bval pr ⊓
        (pair a c =ᴮ (prod x z).func pr ⊓
          ⨆ b : bSet 𝔹,
            b ∈ᴮ y ⊓ pair (x.func pr.1) b ∈ᴮ f ⊓ pair b (z.func pr.2) ∈ᴮ g))
    change Δ ≤ ⨆ b : bSet 𝔹, b ∈ᴮ y ⊓ (pair a b ∈ᴮ f ⊓ pair b c ∈ᴮ g)
    have hPairEq : Δ ≤ pair a c =ᴮ pair (x.func pr.1) (z.func pr.2) := by
      dsimp [Δ, prod]
      exact inf_le_right.trans inf_le_right |>.trans inf_le_left
    have haEq : Δ ≤ a =ᴮ x.func pr.1 :=
      eq_of_eq_pair_left' hPairEq
    have hcEq : Δ ≤ c =ᴮ z.func pr.2 :=
      eq_of_eq_pair_right' hPairEq
    have hCases : Δ ≤ ⨆ b : bSet 𝔹,
        b ∈ᴮ y ⊓ pair (x.func pr.1) b ∈ᴮ f ⊓ pair b (z.func pr.2) ∈ᴮ g := by
      dsimp [Δ]
      exact inf_le_right.trans inf_le_right |>.trans inf_le_right
    apply (le_inf le_rfl hCases).trans
    apply lattice.bv_cases_right
    intro b
    apply lattice.bv_use b
    apply le_inf
    · exact inf_le_right.trans inf_le_left |>.trans inf_le_left
    · apply le_inf
      · have hOrig : Δ ⊓ (b ∈ᴮ y ⊓ pair (x.func pr.1) b ∈ᴮ f ⊓
            pair b (z.func pr.2) ∈ᴮ g) ≤ pair (x.func pr.1) b ∈ᴮ f :=
          inf_le_right.trans inf_le_left |>.trans inf_le_right
        have hEq : Δ ⊓ (b ∈ᴮ y ⊓ pair (x.func pr.1) b ∈ᴮ f ⊓
            pair b (z.func pr.2) ∈ᴮ g) ≤ pair (x.func pr.1) b =ᴮ pair a b :=
          subst_congr_pair_left (bv_symm (inf_le_left.trans haEq))
        exact subst_congr_mem_left' hEq hOrig
      · have hOrig : Δ ⊓ (b ∈ᴮ y ⊓ pair (x.func pr.1) b ∈ᴮ f ⊓
            pair b (z.func pr.2) ∈ᴮ g) ≤ pair b (z.func pr.2) ∈ᴮ g :=
          inf_le_right.trans inf_le_right
        have hEq : Δ ⊓ (b ∈ᴮ y ⊓ pair (x.func pr.1) b ∈ᴮ f ⊓
            pair b (z.func pr.2) ∈ᴮ g) ≤ pair b (z.func pr.2) =ᴮ pair b c :=
          subst_congr_pair_right (bv_symm (inf_le_left.trans hcEq))
        exact subst_congr_mem_left' hEq hOrig

theorem mem_is_func'_comp {x y z f g : bSet 𝔹} {Γ Γ' : 𝔹}
    {hF : Γ ≤ is_func' x y f} {hG : Γ ≤ is_func' y z g} {a c : bSet 𝔹}
    (ha : Γ' ≤ a ∈ᴮ x) (hc : Γ' ≤ c ∈ᴮ z)
    (hCases : Γ' ≤ ⨆ b : bSet 𝔹,
      b ∈ᴮ y ⊓ (pair a b ∈ᴮ f ⊓ pair b c ∈ᴮ g)) :
    Γ' ≤ pair a c ∈ᴮ is_func'_comp hF hG := by
  rw [is_func'_comp, mem_subset.mk_iff₂]
  rw [mem_unfold] at ha
  apply (le_inf le_rfl ha).trans
  apply lattice.bv_cases_right
  intro i
  let Δ : 𝔹 := Γ' ⊓ (x.bval i ⊓ a =ᴮ x.func i)
  have hcΔ : Δ ≤ c ∈ᴮ z :=
    inf_le_left.trans hc
  rw [mem_unfold] at hcΔ
  apply (le_inf le_rfl hcΔ).trans
  apply lattice.bv_cases_right
  intro k
  let Θ : 𝔹 := Δ ⊓ (z.bval k ⊓ c =ᴮ z.func k)
  change Θ ≤
    ⨆ pr : (prod x z).type,
      (prod x z).bval pr ⊓
        (pair a c =ᴮ (prod x z).func pr ⊓
          ⨆ b : bSet 𝔹,
            b ∈ᴮ y ⊓ pair (x.func pr.1) b ∈ᴮ f ⊓ pair b (z.func pr.2) ∈ᴮ g)
  apply lattice.bv_use (i, k)
  have hxVal : Θ ≤ x.bval i := by
    dsimp [Θ, Δ]
    exact inf_le_left.trans inf_le_right |>.trans inf_le_left
  have hzVal : Θ ≤ z.bval k := by
    dsimp [Θ]
    exact inf_le_right.trans inf_le_left
  have haEq : Θ ≤ a =ᴮ x.func i := by
    dsimp [Θ, Δ]
    exact inf_le_left.trans inf_le_right |>.trans inf_le_right
  have hcEq : Θ ≤ c =ᴮ z.func k := by
    dsimp [Θ]
    exact inf_le_right.trans inf_le_right
  have hCasesΘ : Θ ≤ ⨆ b : bSet 𝔹,
      b ∈ᴮ y ⊓ (pair a b ∈ᴮ f ⊓ pair b c ∈ᴮ g) :=
    (inf_le_left.trans inf_le_left).trans hCases
  apply le_inf
  · dsimp [prod]
    exact le_inf hxVal hzVal
  · apply le_inf
    · dsimp [prod]
      exact pair_congr haEq hcEq
    · apply (le_inf le_rfl hCasesΘ).trans
      apply lattice.bv_cases_right
      intro b
      apply lattice.bv_use b
      apply le_inf
      · apply le_inf
        · exact inf_le_right.trans inf_le_left
        · have hOrig : Θ ⊓ (b ∈ᴮ y ⊓ (pair a b ∈ᴮ f ⊓ pair b c ∈ᴮ g)) ≤
              pair a b ∈ᴮ f :=
            inf_le_right.trans inf_le_right |>.trans inf_le_left
          have hEq : Θ ⊓ (b ∈ᴮ y ⊓ (pair a b ∈ᴮ f ⊓ pair b c ∈ᴮ g)) ≤
              pair a b =ᴮ pair (x.func i) b :=
            subst_congr_pair_left (inf_le_left.trans haEq)
          exact subst_congr_mem_left' hEq hOrig
      · have hOrig : Θ ⊓ (b ∈ᴮ y ⊓ (pair a b ∈ᴮ f ⊓ pair b c ∈ᴮ g)) ≤
            pair b c ∈ᴮ g :=
          inf_le_right.trans inf_le_right |>.trans inf_le_right
        have hEq : Θ ⊓ (b ∈ᴮ y ⊓ (pair a b ∈ᴮ f ⊓ pair b c ∈ᴮ g)) ≤
            pair b c =ᴮ pair b (z.func k) :=
          subst_congr_pair_right (inf_le_left.trans hcEq)
        exact subst_congr_mem_left' hEq hOrig

theorem mem_is_func'_comp_iff {x y z f g : bSet 𝔹} {Γ Γ' : 𝔹}
    {hF : Γ ≤ is_func' x y f} {hG : Γ ≤ is_func' y z g} {a c : bSet 𝔹} :
    Γ' ≤ pair a c ∈ᴮ is_func'_comp hF hG ↔
      Γ' ≤ a ∈ᴮ x ∧ Γ' ≤ c ∈ᴮ z ∧
        Γ' ≤ ⨆ b : bSet 𝔹, b ∈ᴮ y ⊓ (pair a b ∈ᴮ f ⊓ pair b c ∈ᴮ g) :=
  ⟨mem_is_func'_comp_components,
    fun h => mem_is_func'_comp h.1 h.2.1 h.2.2⟩

theorem is_func'_comp_is_total {x y z f g : bSet 𝔹} {Γ : 𝔹}
    (hF : Γ ≤ is_func' x y f) (hG : Γ ≤ is_func' y z g) :
    Γ ≤ is_total x z (is_func'_comp hF hG) := by
  unfold is_total
  apply le_iInf
  intro a
  apply lattice.bv_imp_intro
  let Δ : 𝔹 := Γ ⊓ a ∈ᴮ x
  change Δ ≤ ⨆ c : bSet 𝔹, c ∈ᴮ z ⊓ pair a c ∈ᴮ is_func'_comp hF hG
  have hFImp : Δ ≤ lattice.imp (a ∈ᴮ x)
      (⨆ b : bSet 𝔹, b ∈ᴮ y ⊓ pair a b ∈ᴮ f) :=
    (inf_le_left.trans (is_total_of_is_func' hF)).trans (iInf_le _ a)
  have hFCases : Δ ≤ ⨆ b : bSet 𝔹, b ∈ᴮ y ⊓ pair a b ∈ᴮ f :=
    lattice.bv_context_apply hFImp inf_le_right
  apply (le_inf le_rfl hFCases).trans
  apply lattice.bv_cases_right
  intro b
  let Θ : 𝔹 := Δ ⊓ (b ∈ᴮ y ⊓ pair a b ∈ᴮ f)
  have hGImp : Θ ≤ lattice.imp (b ∈ᴮ y)
      (⨆ c : bSet 𝔹, c ∈ᴮ z ⊓ pair b c ∈ᴮ g) :=
    ((inf_le_left.trans inf_le_left).trans (is_total_of_is_func' hG)).trans (iInf_le _ b)
  have hGCases : Θ ≤ ⨆ c : bSet 𝔹, c ∈ᴮ z ⊓ pair b c ∈ᴮ g :=
    lattice.bv_context_apply hGImp (inf_le_right.trans inf_le_left)
  apply (le_inf le_rfl hGCases).trans
  apply lattice.bv_cases_right
  intro c
  apply lattice.bv_use c
  apply le_inf
  · exact inf_le_right.trans inf_le_left
  · apply mem_is_func'_comp
    · exact (inf_le_left.trans inf_le_left).trans inf_le_right
    · exact inf_le_right.trans inf_le_left
    · apply lattice.bv_use b
      apply le_inf
      · exact inf_le_left.trans inf_le_right |>.trans inf_le_left
      · apply le_inf
        · exact inf_le_left.trans inf_le_right |>.trans inf_le_right
        · exact inf_le_right.trans inf_le_right

theorem is_func'_comp_is_func {x y z f g : bSet 𝔹} {Γ : 𝔹}
    (hF : Γ ≤ is_func' x y f) (hG : Γ ≤ is_func' y z g) :
    Γ ≤ is_func (is_func'_comp hF hG) := by
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
  let Δ : 𝔹 := Γ ⊓
    (pair w₁ v₁ ∈ᴮ is_func'_comp hF hG ⊓
      pair w₂ v₂ ∈ᴮ is_func'_comp hF hG)
  change Δ ≤ lattice.imp (w₁ =ᴮ w₂) (v₁ =ᴮ v₂)
  apply lattice.bv_imp_intro
  let Θ : 𝔹 := Δ ⊓ w₁ =ᴮ w₂
  change Θ ≤ v₁ =ᴮ v₂
  have hMem₁ : Θ ≤ pair w₁ v₁ ∈ᴮ is_func'_comp hF hG := by
    dsimp [Θ, Δ]
    exact inf_le_left.trans inf_le_right |>.trans inf_le_left
  have hMem₂ : Θ ≤ pair w₂ v₂ ∈ᴮ is_func'_comp hF hG := by
    dsimp [Θ, Δ]
    exact inf_le_left.trans inf_le_right |>.trans inf_le_right
  have hInfo₁ := mem_is_func'_comp_components hMem₁
  have hInfo₂ := mem_is_func'_comp_components hMem₂
  have hCases₁ : Θ ≤ ⨆ b : bSet 𝔹,
      b ∈ᴮ y ⊓ (pair w₁ b ∈ᴮ f ⊓ pair b v₁ ∈ᴮ g) :=
    hInfo₁.2.2
  apply (le_inf le_rfl hCases₁).trans
  apply lattice.bv_cases_right
  intro b₁
  let Φ : 𝔹 := Θ ⊓ (b₁ ∈ᴮ y ⊓ (pair w₁ b₁ ∈ᴮ f ⊓ pair b₁ v₁ ∈ᴮ g))
  have hCases₂ : Φ ≤ ⨆ b : bSet 𝔹,
      b ∈ᴮ y ⊓ (pair w₂ b ∈ᴮ f ⊓ pair b v₂ ∈ᴮ g) :=
    inf_le_left.trans hInfo₂.2.2
  apply (le_inf le_rfl hCases₂).trans
  apply lattice.bv_cases_right
  intro b₂
  let Ψ : 𝔹 := Φ ⊓ (b₂ ∈ᴮ y ⊓ (pair w₂ b₂ ∈ᴮ f ⊓ pair b₂ v₂ ∈ᴮ g))
  change Ψ ≤ v₁ =ᴮ v₂
  have hCtx : Ψ ≤ Γ := by
    dsimp [Ψ, Φ, Θ, Δ]
    exact inf_le_left.trans inf_le_left |>.trans inf_le_left |>.trans inf_le_left
  have hInputEq : Ψ ≤ w₁ =ᴮ w₂ := by
    dsimp [Ψ, Φ, Θ]
    exact inf_le_left.trans inf_le_left |>.trans inf_le_right
  have hFPair₁ : Ψ ≤ pair w₁ b₁ ∈ᴮ f := by
    dsimp [Ψ, Φ]
    exact inf_le_left.trans inf_le_right |>.trans inf_le_right |>.trans inf_le_left
  have hFPair₂ : Ψ ≤ pair w₂ b₂ ∈ᴮ f := by
    dsimp [Ψ]
    exact inf_le_right.trans inf_le_right |>.trans inf_le_left
  have hMidEq : Ψ ≤ b₁ =ᴮ b₂ :=
    eq_of_is_func'_of_eq (hCtx.trans hF) hInputEq hFPair₁ hFPair₂
  have hGPair₁ : Ψ ≤ pair b₁ v₁ ∈ᴮ g := by
    dsimp [Ψ, Φ]
    exact inf_le_left.trans inf_le_right |>.trans inf_le_right |>.trans inf_le_right
  have hGPair₂ : Ψ ≤ pair b₂ v₂ ∈ᴮ g := by
    dsimp [Ψ]
    exact inf_le_right.trans inf_le_right |>.trans inf_le_right
  exact eq_of_is_func'_of_eq (hCtx.trans hG) hMidEq hGPair₁ hGPair₂

theorem is_func'_comp_is_func' {x y z f g : bSet 𝔹} {Γ : 𝔹}
    (hF : Γ ≤ is_func' x y f) (hG : Γ ≤ is_func' y z g) :
    Γ ≤ is_func' x z (is_func'_comp hF hG) :=
  le_inf (is_func'_comp_is_func hF hG) (is_func'_comp_is_total hF hG)

/-- Composition of two Boolean-valued functions. -/
def function_comp {x y z f g : bSet 𝔹} {Γ : 𝔹}
    (hF : Γ ≤ is_function x y f) (hG : Γ ≤ is_function y z g) : bSet 𝔹 :=
  is_func'_comp (is_func'_of_is_function hF) (is_func'_of_is_function hG)

theorem function_comp_is_function {x y z f g : bSet 𝔹} {Γ : 𝔹}
    {hF : Γ ≤ is_function x y f} {hG : Γ ≤ is_function y z g} :
    Γ ≤ is_function x z (function_comp hF hG) :=
  le_inf
    (is_func'_comp_is_func' (is_func'_of_is_function hF) (is_func'_of_is_function hG))
    (is_func'_comp_subset_prod (is_func'_of_is_function hF) (is_func'_of_is_function hG))

theorem is_func'_comp_inj {x y z f g : bSet 𝔹} {Γ : 𝔹}
    (hF : Γ ≤ is_func' x y f) (hG : Γ ≤ is_func' y z g)
    (hFInj : Γ ≤ is_inj f) (hGInj : Γ ≤ is_inj g) :
    Γ ≤ is_inj (is_func'_comp hF hG) := by
  unfold is_inj
  apply le_iInf
  intro w₁
  apply le_iInf
  intro w₂
  apply le_iInf
  intro v₁
  apply le_iInf
  intro v₂
  apply lattice.bv_imp_intro
  let Δ : 𝔹 := Γ ⊓
    (pair w₁ v₁ ∈ᴮ is_func'_comp hF hG ⊓
      pair w₂ v₂ ∈ᴮ is_func'_comp hF hG ⊓ v₁ =ᴮ v₂)
  change Δ ≤ w₁ =ᴮ w₂
  have hMem₁ : Δ ≤ pair w₁ v₁ ∈ᴮ is_func'_comp hF hG := by
    dsimp [Δ]
    exact inf_le_right.trans inf_le_left |>.trans inf_le_left
  have hMem₂ : Δ ≤ pair w₂ v₂ ∈ᴮ is_func'_comp hF hG := by
    dsimp [Δ]
    exact inf_le_right.trans inf_le_left |>.trans inf_le_right
  have hInfo₁ := mem_is_func'_comp_components hMem₁
  have hInfo₂ := mem_is_func'_comp_components hMem₂
  have hCases₁ : Δ ≤ ⨆ b : bSet 𝔹,
      b ∈ᴮ y ⊓ (pair w₁ b ∈ᴮ f ⊓ pair b v₁ ∈ᴮ g) :=
    hInfo₁.2.2
  apply (le_inf le_rfl hCases₁).trans
  apply lattice.bv_cases_right
  intro b₁
  let Φ : 𝔹 := Δ ⊓ (b₁ ∈ᴮ y ⊓ (pair w₁ b₁ ∈ᴮ f ⊓ pair b₁ v₁ ∈ᴮ g))
  have hCases₂ : Φ ≤ ⨆ b : bSet 𝔹,
      b ∈ᴮ y ⊓ (pair w₂ b ∈ᴮ f ⊓ pair b v₂ ∈ᴮ g) :=
    inf_le_left.trans hInfo₂.2.2
  apply (le_inf le_rfl hCases₂).trans
  apply lattice.bv_cases_right
  intro b₂
  let Ψ : 𝔹 := Φ ⊓ (b₂ ∈ᴮ y ⊓ (pair w₂ b₂ ∈ᴮ f ⊓ pair b₂ v₂ ∈ᴮ g))
  change Ψ ≤ w₁ =ᴮ w₂
  have hCtx : Ψ ≤ Γ := by
    dsimp [Ψ, Φ, Δ]
    exact inf_le_left.trans inf_le_left |>.trans inf_le_left
  have hOutEq : Ψ ≤ v₁ =ᴮ v₂ := by
    dsimp [Ψ, Φ, Δ]
    exact inf_le_left.trans inf_le_left |>.trans inf_le_right |>.trans inf_le_right
  have hGPair₁ : Ψ ≤ pair b₁ v₁ ∈ᴮ g := by
    dsimp [Ψ, Φ]
    exact inf_le_left.trans inf_le_right |>.trans inf_le_right |>.trans inf_le_right
  have hGPair₂ : Ψ ≤ pair b₂ v₂ ∈ᴮ g := by
    dsimp [Ψ]
    exact inf_le_right.trans inf_le_right |>.trans inf_le_right
  have hMidEq : Ψ ≤ b₁ =ᴮ b₂ :=
    eq_of_is_inj_of_eq (hCtx.trans hGInj) hOutEq hGPair₁ hGPair₂
  have hFPair₁ : Ψ ≤ pair w₁ b₁ ∈ᴮ f := by
    dsimp [Ψ, Φ]
    exact inf_le_left.trans inf_le_right |>.trans inf_le_right |>.trans inf_le_left
  have hFPair₂ : Ψ ≤ pair w₂ b₂ ∈ᴮ f := by
    dsimp [Ψ]
    exact inf_le_right.trans inf_le_right |>.trans inf_le_left
  exact eq_of_is_inj_of_eq (hCtx.trans hFInj) hMidEq hFPair₁ hFPair₂

/-- Composition of two injective Boolean-valued functions. -/
def injective_function_comp {x y z f g : bSet 𝔹} {Γ : 𝔹}
    (hF : Γ ≤ is_injective_function x y f)
    (hG : Γ ≤ is_injective_function y z g) : bSet 𝔹 :=
  is_func'_comp (is_func'_of_is_injective_function hF) (is_func'_of_is_injective_function hG)

theorem injective_function_comp_is_injective_function {x y z f g : bSet 𝔹} {Γ : 𝔹}
    {hF : Γ ≤ is_injective_function x y f}
    {hG : Γ ≤ is_injective_function y z g} :
    Γ ≤ is_injective_function x z (injective_function_comp hF hG) :=
  le_inf
    (le_inf
      (is_func'_comp_is_func'
        (is_func'_of_is_injective_function hF) (is_func'_of_is_injective_function hG))
      (is_func'_comp_subset_prod
        (is_func'_of_is_injective_function hF) (is_func'_of_is_injective_function hG)))
    (is_func'_comp_inj
      (is_func'_of_is_injective_function hF) (is_func'_of_is_injective_function hG)
      (is_inj_of_is_injective_function hF) (is_inj_of_is_injective_function hG))

theorem injective_function_comp_is_function {x y z f g : bSet 𝔹} {Γ : 𝔹}
    {hF : Γ ≤ is_injective_function x y f}
    {hG : Γ ≤ is_injective_function y z g} :
    Γ ≤ is_function x z (injective_function_comp hF hG) :=
  is_function_of_is_injective_function injective_function_comp_is_injective_function

theorem injects_into_trans {x y z : bSet 𝔹} {Γ : 𝔹}
    (hXY : Γ ≤ injects_into x y) (hYZ : Γ ≤ injects_into y z) :
    Γ ≤ injects_into x z := by
  unfold injects_into at hXY hYZ ⊢
  apply (le_inf le_rfl hXY).trans
  apply lattice.bv_cases_right
  intro f
  let Δ : 𝔹 := Γ ⊓ (is_func' x y f ⊓ is_inj f)
  have hYZΔ : Δ ≤ ⨆ g : bSet 𝔹, is_func' y z g ⊓ is_inj g :=
    inf_le_left.trans hYZ
  apply (le_inf le_rfl hYZΔ).trans
  apply lattice.bv_cases_right
  intro g
  let Θ : 𝔹 := Δ ⊓ (is_func' y z g ⊓ is_inj g)
  have hF : Θ ≤ is_func' x y f := by
    dsimp [Θ, Δ]
    exact inf_le_left.trans inf_le_right |>.trans inf_le_left
  have hFInj : Θ ≤ is_inj f := by
    dsimp [Θ, Δ]
    exact inf_le_left.trans inf_le_right |>.trans inf_le_right
  have hG : Θ ≤ is_func' y z g := by
    dsimp [Θ]
    exact inf_le_right.trans inf_le_left
  have hGInj : Θ ≤ is_inj g := by
    dsimp [Θ]
    exact inf_le_right.trans inf_le_right
  apply lattice.bv_use (is_func'_comp hF hG)
  exact le_inf (is_func'_comp_is_func' hF hG) (is_func'_comp_inj hF hG hFInj hGInj)

theorem is_func'_comp_surj {x y z f g : bSet 𝔹} {Γ : 𝔹}
    (hF : Γ ≤ is_func' x y f) (hG : Γ ≤ is_func' y z g)
    (hFSurj : Γ ≤ is_surj x y f) (hGSurj : Γ ≤ is_surj y z g) :
    Γ ≤ is_surj x z (is_func'_comp hF hG) := by
  unfold is_surj
  apply le_iInf
  intro wz
  apply lattice.bv_imp_intro
  let Δ : 𝔹 := Γ ⊓ wz ∈ᴮ z
  change Δ ≤ ⨆ wx : bSet 𝔹, wx ∈ᴮ x ⊓ pair wx wz ∈ᴮ is_func'_comp hF hG
  have hGImp : Δ ≤ lattice.imp (wz ∈ᴮ z)
      (⨆ wy : bSet 𝔹, wy ∈ᴮ y ⊓ pair wy wz ∈ᴮ g) :=
    (inf_le_left.trans hGSurj).trans (iInf_le _ wz)
  have hGCases : Δ ≤ ⨆ wy : bSet 𝔹, wy ∈ᴮ y ⊓ pair wy wz ∈ᴮ g :=
    lattice.bv_context_apply hGImp inf_le_right
  apply (le_inf le_rfl hGCases).trans
  apply lattice.bv_cases_right
  intro wy
  let Φ : 𝔹 := Δ ⊓ (wy ∈ᴮ y ⊓ pair wy wz ∈ᴮ g)
  have hFImp : Φ ≤ lattice.imp (wy ∈ᴮ y)
      (⨆ wx : bSet 𝔹, wx ∈ᴮ x ⊓ pair wx wy ∈ᴮ f) :=
    ((inf_le_left.trans inf_le_left).trans hFSurj).trans (iInf_le _ wy)
  have hFCases : Φ ≤ ⨆ wx : bSet 𝔹, wx ∈ᴮ x ⊓ pair wx wy ∈ᴮ f :=
    lattice.bv_context_apply hFImp (inf_le_right.trans inf_le_left)
  apply (le_inf le_rfl hFCases).trans
  apply lattice.bv_cases_right
  intro wx
  let Ψ : 𝔹 := Φ ⊓ (wx ∈ᴮ x ⊓ pair wx wy ∈ᴮ f)
  apply lattice.bv_use wx
  apply le_inf
  · exact inf_le_right.trans inf_le_left
  · apply mem_is_func'_comp
    · exact inf_le_right.trans inf_le_left
    · exact (inf_le_left.trans inf_le_left).trans inf_le_right
    · apply lattice.bv_use wy
      apply le_inf
      · exact inf_le_left.trans (inf_le_right.trans inf_le_left)
      · apply le_inf
        · exact inf_le_right.trans inf_le_right
        · exact inf_le_left.trans (inf_le_right.trans inf_le_right)

/-- Boolean-valued set of all functions from `x` to `y`. -/
def functions (x y : bSet 𝔹) : bSet 𝔹 :=
  set_of_indicator (x := bv_powerset (prod x y))
    (fun s : (bv_powerset (prod x y)).type =>
      is_function x y ((bv_powerset (prod x y)).func s))

@[simp] theorem functions_type {x y : bSet 𝔹} :
    (functions x y).type = (bv_powerset (prod x y)).type := rfl

@[simp] theorem functions_func {x y : bSet 𝔹} (i : (functions x y).type) :
    (functions x y).func i = (bv_powerset (prod x y)).func i := rfl

@[simp] theorem functions_bval {x y : bSet 𝔹} (i : (functions x y).type) :
    (functions x y).bval i =
      is_function x y ((bv_powerset (prod x y)).func i) := by
  change is_function x y ((bv_powerset (prod x y)).func i) ⊓ (⊤ : 𝔹) =
    is_function x y ((bv_powerset (prod x y)).func i)
  rw [inf_top_eq]

theorem mem_functions_iff {g x y : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ g ∈ᴮ functions x y ↔ Γ ≤ is_function x y g := by
  constructor
  · intro h
    rw [functions, mem_set_of_indicator_iff] at h
    apply (le_inf le_rfl h).trans
    apply lattice.bv_cases_right
    intro s
    let Δ : 𝔹 := Γ ⊓
      ((is_function x y ((bv_powerset (prod x y)).func s) ⊓
          (bv_powerset (prod x y)).bval s) ⊓
        g =ᴮ (bv_powerset (prod x y)).func s)
    change Δ ≤ is_function x y g
    have hFunc : Δ ≤ is_function x y ((bv_powerset (prod x y)).func s) := by
      dsimp [Δ]
      exact inf_le_right.trans inf_le_left |>.trans inf_le_left
    have hEq : Δ ≤ (bv_powerset (prod x y)).func s =ᴮ g := by
      dsimp [Δ]
      exact bv_symm (inf_le_right.trans inf_le_right)
    exact (le_inf hEq hFunc).trans
      (B_ext_is_function_right x y ((bv_powerset (prod x y)).func s) g)
  · intro h
    rw [functions, mem_set_of_indicator_iff]
    have hPow : Γ ≤ g ∈ᴮ bv_powerset (prod x y) :=
      (bv_powerset_spec.mp (subset_prod_of_is_function h))
    rw [mem_unfold] at hPow
    apply (le_inf le_rfl hPow).trans
    apply lattice.bv_cases_right
    intro s
    let Δ : 𝔹 := Γ ⊓
      ((bv_powerset (prod x y)).bval s ⊓ g =ᴮ (bv_powerset (prod x y)).func s)
    change Δ ≤ ⨆ i : (bv_powerset (prod x y)).type,
      (is_function x y ((bv_powerset (prod x y)).func i) ⊓
          (bv_powerset (prod x y)).bval i) ⊓
        g =ᴮ (bv_powerset (prod x y)).func i
    apply lattice.bv_use s
    apply le_inf
    · apply le_inf
      · have hEq : Δ ≤ g =ᴮ (bv_powerset (prod x y)).func s := by
          dsimp [Δ]
          exact inf_le_right.trans inf_le_right
        have hFunc : Δ ≤ is_function x y g := by
          dsimp [Δ]
          exact inf_le_left.trans h
        exact (le_inf hEq hFunc).trans
          (B_ext_is_function_right x y g ((bv_powerset (prod x y)).func s))
      · dsimp [Δ]
        exact inf_le_right.trans inf_le_left
    · dsimp [Δ]
      exact inf_le_right.trans inf_le_right

theorem functions_subset_powerset {x y : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ functions x y ⊆ᴮ bv_powerset (prod x y) :=
  subset.mk_subset

theorem check_powerset_subset_powerset (x : pSet.{u}) {Γ : 𝔹} :
    Γ ≤ (check (PSet.powerset x) : bSet 𝔹) ⊆ᴮ bv_powerset (check x) := by
  apply subset_intro
  intro i
  let i' : (PSet.powerset x).Type :=
    cast (check_type (𝔹 := 𝔹) (x := PSet.powerset x)) i
  change Γ ⊓ (check (PSet.powerset x) : bSet 𝔹).bval i ≤
    (check (PSet.powerset x) : bSet 𝔹).func i ∈ᴮ bv_powerset (check x)
  rw [check_bval, inf_top_eq, check_func]
  change Γ ≤ check ((PSet.powerset x).Func i') ∈ᴮ bv_powerset (check x)
  rw [← bv_powerset_spec]
  apply check_subset
  exact PSet.mem_powerset.mp (pSet.mem_mk' (x := PSet.powerset x) (i := i'))

theorem is_function_of_mem_functions {g x y : bSet 𝔹} {Γ : 𝔹}
    (h : Γ ≤ g ∈ᴮ functions x y) : Γ ≤ is_function x y g :=
  mem_functions_iff.mp h

theorem mem_functions {g x y : bSet 𝔹} {Γ : 𝔹}
    (h : Γ ≤ is_function x y g) : Γ ≤ g ∈ᴮ functions x y :=
  mem_functions_iff.mpr h

theorem check_functions_subset_functions {x y : pSet.{u}} {Γ : 𝔹} :
    Γ ≤ (check (pSet.functions x y) : bSet 𝔹) ⊆ᴮ functions (check x) (check y) := by
  apply subset_intro
  intro i
  let i' : (pSet.functions x y).Type :=
    cast (check_type (𝔹 := 𝔹) (x := pSet.functions x y)) i
  change Γ ⊓ (check (pSet.functions x y) : bSet 𝔹).bval i ≤
    (check (pSet.functions x y) : bSet 𝔹).func i ∈ᴮ functions (check x) (check y)
  rw [check_bval, inf_top_eq, check_func]
  change Γ ≤ check ((pSet.functions x y).Func i') ∈ᴮ functions (check x) (check y)
  apply mem_functions
  exact check_is_func (pSet.is_func_of_mem_functions (pSet.mem_mk' (x := pSet.functions x y) (i := i')))

namespace powerset_injects

/-- Characteristic-function index associated to a Boolean-valued subset indicator. -/
def F {x : bSet 𝔹} : (bv_powerset x).type → (functions x (2 : bSet 𝔹)).type :=
  fun χ pr =>
    (x.func pr.1 ∈ᴮ set_of_indicator χ ⊓ ((2 : bSet 𝔹).func pr.2 =ᴮ (0 : bSet 𝔹))) ⊔
      (x.func pr.1 ∈ᴮ subset.mk (x := x)
          (fun i : x.type => (x.func i ∈ᴮ set_of_indicator χ)ᶜ) ⊓
        ((2 : bSet 𝔹).func pr.2 =ᴮ (1 : bSet 𝔹)))

end powerset_injects

/-- Boolean-valued epsilon trichotomy on a name. -/
def epsilon_trichotomy (x : bSet 𝔹) : 𝔹 :=
  ⨅ y : bSet 𝔹, lattice.imp (y ∈ᴮ x)
    (⨅ z : bSet 𝔹, lattice.imp (z ∈ᴮ x) (y =ᴮ z ⊔ y ∈ᴮ z ⊔ z ∈ᴮ y))

/-- Boolean-valued epsilon well-foundedness on a name. -/
def epsilon_well_founded (x : bSet 𝔹) : 𝔹 :=
  ⨅ u : bSet 𝔹, lattice.imp (u ⊆ᴮ x)
    (lattice.imp ((u =ᴮ (∅ : bSet 𝔹))ᶜ)
      (⨆ y : bSet 𝔹, y ∈ᴮ u ⊓
        (⨅ z : bSet 𝔹, lattice.imp (z ∈ᴮ u) ((z ∈ᴮ y)ᶜ))))

/-- Boolean-valued epsilon well-order predicate. -/
def epsilon_well_orders (x : bSet 𝔹) : 𝔹 :=
  epsilon_trichotomy x ⊓ epsilon_well_founded x

/-- Abbreviation for the epsilon well-order predicate. -/
def ewo (x : bSet 𝔹) : 𝔹 :=
  epsilon_well_orders x

theorem B_ext_epsilon_trichotomy :
    B_ext (epsilon_trichotomy : bSet 𝔹 → 𝔹) := by
  unfold epsilon_trichotomy
  apply B_ext_iInf
  intro y
  apply B_ext_imp
  · exact B_ext_mem_right y
  · apply B_ext_iInf
    intro z
    apply B_ext_imp
    · exact B_ext_mem_right z
    · exact B_ext_const _

theorem B_ext_epsilon_well_founded :
    B_ext (epsilon_well_founded : bSet 𝔹 → 𝔹) := by
  unfold epsilon_well_founded
  apply B_ext_iInf
  intro u
  apply B_ext_imp
  · exact B_ext_subset_right u
  · exact B_ext_const _

theorem B_ext_ewo : B_ext (fun w : bSet 𝔹 => epsilon_well_orders w) :=
  B_ext_inf B_ext_epsilon_trichotomy B_ext_epsilon_well_founded

theorem epsilon_dichotomy (x y z : bSet 𝔹) :
    epsilon_well_orders x ≤ lattice.imp (y ∈ᴮ x)
      (lattice.imp (z ∈ᴮ x) (y =ᴮ z ⊔ y ∈ᴮ z ⊔ z ∈ᴮ y)) := by
  apply lattice.bv_imp_intro
  apply lattice.bv_imp_intro
  have hTri :
      (epsilon_well_orders x ⊓ y ∈ᴮ x) ⊓ z ∈ᴮ x ≤ epsilon_trichotomy x :=
    inf_le_left.trans inf_le_left |>.trans inf_le_left
  have hyMem :
      (epsilon_well_orders x ⊓ y ∈ᴮ x) ⊓ z ∈ᴮ x ≤ y ∈ᴮ x :=
    inf_le_left.trans inf_le_right
  have hAfterY :
      (epsilon_well_orders x ⊓ y ∈ᴮ x) ⊓ z ∈ᴮ x ≤
        ⨅ z' : bSet 𝔹,
          lattice.imp (z' ∈ᴮ x) (y =ᴮ z' ⊔ y ∈ᴮ z' ⊔ z' ∈ᴮ y) :=
    lattice.bv_context_apply (hTri.trans (iInf_le _ y)) hyMem
  have hzMem :
      (epsilon_well_orders x ⊓ y ∈ᴮ x) ⊓ z ∈ᴮ x ≤ z ∈ᴮ x :=
    inf_le_right
  exact lattice.bv_context_apply (hAfterY.trans (iInf_le _ z)) hzMem

/-- Boolean-valued transitivity of a name. -/
def is_transitive (x : bSet 𝔹) : 𝔹 :=
  ⨅ y : bSet 𝔹, lattice.imp (y ∈ᴮ x) (y ⊆ᴮ x)

theorem subset_of_mem_transitive {x w : bSet 𝔹} {Γ : 𝔹}
    (hTrans : Γ ≤ is_transitive x) (hMem : Γ ≤ w ∈ᴮ x) : Γ ≤ w ⊆ᴮ x :=
  lattice.bv_context_apply (hTrans.trans (iInf_le _ w)) hMem

theorem B_ext_is_transitive :
    B_ext (is_transitive : bSet 𝔹 → 𝔹) := by
  unfold is_transitive
  apply B_ext_iInf
  intro y
  apply B_ext_imp
  · exact B_ext_mem_right y
  · exact B_ext_subset_right y

/-- Boolean-valued ordinal predicate. -/
def Ord (x : bSet 𝔹) : 𝔹 :=
  epsilon_well_orders x ⊓ is_transitive x

theorem B_ext_Ord : B_ext (Ord : bSet 𝔹 → 𝔹) :=
  B_ext_inf B_ext_ewo B_ext_is_transitive

theorem epsilon_trichotomy_of_Ord {x a b : bSet 𝔹} {Γ : 𝔹}
    (haMem : Γ ≤ a ∈ᴮ x) (hbMem : Γ ≤ b ∈ᴮ x) (hOrd : Γ ≤ Ord x) :
    Γ ≤ a =ᴮ b ⊔ a ∈ᴮ b ⊔ b ∈ᴮ a := by
  have hEwo : Γ ≤ epsilon_well_orders x :=
    hOrd.trans inf_le_left
  have hImp :
      Γ ≤ lattice.imp (a ∈ᴮ x)
        (lattice.imp (b ∈ᴮ x) (a =ᴮ b ⊔ a ∈ᴮ b ⊔ b ∈ᴮ a)) :=
    hEwo.trans (epsilon_dichotomy x a b)
  exact lattice.bv_context_apply (lattice.bv_context_apply hImp haMem) hbMem

theorem B_congr_prod_left (y : bSet 𝔹) :
    B_congr (fun x : bSet 𝔹 => prod x y) := by
  intro x z
  apply subset_ext
  · apply subset_intro
    intro ij
    dsimp [prod]
    apply prod_mem
    · have hmem : x =ᴮ z ⊓ (x.bval ij.1 ⊓ y.bval ij.2) ≤ x.func ij.1 ∈ᴮ x := by
        apply mem.mk''
        exact inf_le_right.trans inf_le_left
      exact subst_congr_mem_right' inf_le_left hmem
    · apply mem.mk''
      exact inf_le_right.trans inf_le_right
  · apply subset_intro
    intro ij
    dsimp [prod]
    apply prod_mem
    · have hmem : x =ᴮ z ⊓ (z.bval ij.1 ⊓ y.bval ij.2) ≤ z.func ij.1 ∈ᴮ z := by
        apply mem.mk''
        exact inf_le_right.trans inf_le_left
      exact subst_congr_mem_right' (bv_symm inf_le_left) hmem
    · apply mem.mk''
      exact inf_le_right.trans inf_le_right

theorem B_congr_prod_right (x : bSet 𝔹) :
    B_congr (fun y : bSet 𝔹 => prod x y) := by
  intro y z
  apply subset_ext
  · apply subset_intro
    intro ij
    dsimp [prod]
    apply prod_mem
    · apply mem.mk''
      exact inf_le_right.trans inf_le_left
    · have hmem : y =ᴮ z ⊓ (x.bval ij.1 ⊓ y.bval ij.2) ≤ y.func ij.2 ∈ᴮ y := by
        apply mem.mk''
        exact inf_le_right.trans inf_le_right
      exact subst_congr_mem_right' inf_le_left hmem
  · apply subset_intro
    intro ij
    dsimp [prod]
    apply prod_mem
    · apply mem.mk''
      exact inf_le_right.trans inf_le_left
    · have hmem : y =ᴮ z ⊓ (x.bval ij.1 ⊓ z.bval ij.2) ≤ z.func ij.2 ∈ᴮ z := by
        apply mem.mk''
        exact inf_le_right.trans inf_le_right
      exact subst_congr_mem_right' (bv_symm inf_le_left) hmem

theorem prod_congr {x₁ x₂ y₁ y₂ : bSet 𝔹} {Γ : 𝔹}
    (hx : Γ ≤ x₁ =ᴮ x₂) (hy : Γ ≤ y₁ =ᴮ y₂) :
    Γ ≤ prod x₁ y₁ =ᴮ prod x₂ y₂ :=
  bv_trans (hx.trans (B_congr_prod_left y₁ x₁ x₂))
    (hy.trans (B_congr_prod_right x₂ y₁ y₂))

theorem B_ext_prod_left {φ : bSet 𝔹 → 𝔹} (hφ : B_ext φ) (y : bSet 𝔹) :
    B_ext (fun x : bSet 𝔹 => φ (prod x y)) := by
  intro x z
  have hProd : x =ᴮ z ≤ prod x y =ᴮ prod z y :=
    B_congr_prod_left y x z
  exact (le_inf (inf_le_left.trans hProd) inf_le_right).trans
    (hφ (prod x y) (prod z y))

theorem B_ext_prod_right {φ : bSet 𝔹 → 𝔹} (hφ : B_ext φ) (x : bSet 𝔹) :
    B_ext (fun y : bSet 𝔹 => φ (prod x y)) := by
  intro y z
  have hProd : y =ᴮ z ≤ prod x y =ᴮ prod x z :=
    B_congr_prod_right x y z
  exact (le_inf (inf_le_left.trans hProd) inf_le_right).trans
    (hφ (prod x y) (prod x z))

theorem B_ext_prod_mem_left {x y : bSet 𝔹} :
    B_ext (fun z : bSet 𝔹 => prod z x ∈ᴮ y) :=
  B_ext_prod_left (φ := fun w : bSet 𝔹 => w ∈ᴮ y) (B_ext_mem_left y) x

theorem B_ext_prod_mem_right {x y : bSet 𝔹} :
    B_ext (fun z : bSet 𝔹 => prod x z ∈ᴮ y) :=
  B_ext_prod_right (φ := fun w : bSet 𝔹 => w ∈ᴮ y) (B_ext_mem_left y) x

theorem prod_subset {x₁ x₂ y₁ y₂ : bSet 𝔹} {Γ : 𝔹}
    (hx : Γ ≤ x₁ ⊆ᴮ x₂) (hy : Γ ≤ y₁ ⊆ᴮ y₂) :
    Γ ≤ prod x₁ y₁ ⊆ᴮ prod x₂ y₂ := by
  apply subset_intro
  intro ij
  dsimp [prod]
  exact prod_mem
    (mem_of_mem_subset' (inf_le_left.trans hx)
      (mem.mk'' (inf_le_right.trans inf_le_left)))
    (mem_of_mem_subset' (inf_le_left.trans hy)
      (mem.mk'' (inf_le_right.trans inf_le_right)))

theorem prod_subset_left {x₁ x₂ y : bSet 𝔹} {Γ : 𝔹}
    (hx : Γ ≤ x₁ ⊆ᴮ x₂) : Γ ≤ prod x₁ y ⊆ᴮ prod x₂ y :=
  prod_subset hx subset_self

theorem prod_subset_right {x y₁ y₂ : bSet 𝔹} {Γ : 𝔹}
    (hy : Γ ≤ y₁ ⊆ᴮ y₂) : Γ ≤ prod x y₁ ⊆ᴮ prod x y₂ :=
  prod_subset subset_self hy

theorem subset_of_mem_Ord {x y : bSet 𝔹} {Γ : 𝔹}
    (hMem : Γ ≤ x ∈ᴮ y) (hOrd : Γ ≤ Ord y) : Γ ≤ x ⊆ᴮ y :=
  subset_of_mem_transitive (hOrd.trans inf_le_right) hMem

theorem mem_of_mem_Ord {x y z : bSet 𝔹} {Γ : 𝔹}
    (hMemXY : Γ ≤ x ∈ᴮ y) (hMemYZ : Γ ≤ y ∈ᴮ z) (hOrdZ : Γ ≤ Ord z) :
    Γ ≤ x ∈ᴮ z :=
  mem_of_mem_subset' (subset_of_mem_Ord hMemYZ hOrdZ) hMemXY

theorem transitive_union {u : bSet 𝔹} {Γ : 𝔹}
    (hTrans : Γ ≤ ⨅ z : bSet 𝔹, lattice.imp (z ∈ᴮ u) (is_transitive z)) :
    Γ ≤ is_transitive (bv_union u) := by
  unfold is_transitive
  apply le_iInf
  intro x
  apply lattice.bv_imp_intro
  apply subset_intro
  intro i
  let Δ : 𝔹 := Γ ⊓ x ∈ᴮ bv_union u
  change Δ ⊓ x.bval i ≤ x.func i ∈ᴮ bv_union u
  have hxUnion : Δ ≤ x ∈ᴮ bv_union u := by
    dsimp [Δ]
    exact inf_le_right
  rw [mem_bv_union_iff] at hxUnion
  have hxUnion' : Δ ⊓ x.bval i ≤ ⨆ y : bSet 𝔹, y ∈ᴮ u ⊓ x ∈ᴮ y :=
    inf_le_left.trans hxUnion
  apply (le_inf le_rfl hxUnion').trans
  apply lattice.bv_cases_right
  intro y
  let Θ : 𝔹 := (Δ ⊓ x.bval i) ⊓ (y ∈ᴮ u ⊓ x ∈ᴮ y)
  change Θ ≤ x.func i ∈ᴮ bv_union u
  rw [mem_bv_union_iff]
  apply lattice.bv_use y
  apply le_inf
  · dsimp [Θ, Δ]
    exact inf_le_right.trans inf_le_left
  · have hΘΓ : Θ ≤ Γ := by
      dsimp [Θ, Δ]
      exact inf_le_left.trans inf_le_left |>.trans inf_le_left
    have hΘVal : Θ ≤ x.bval i := by
      dsimp [Θ]
      exact inf_le_left.trans inf_le_right
    have hyMem : Θ ≤ y ∈ᴮ u := by
      dsimp [Θ]
      exact inf_le_right.trans inf_le_left
    have hxMemY : Θ ≤ x ∈ᴮ y := by
      dsimp [Θ]
      exact inf_le_right.trans inf_le_right
    have hyTrans : Θ ≤ is_transitive y :=
      lattice.bv_context_apply
        ((hΘΓ.trans hTrans).trans (iInf_le _ y)) hyMem
    have hxSubY : Θ ≤ x ⊆ᴮ y :=
      subset_of_mem_transitive hyTrans hxMemY
    exact (le_inf le_rfl hΘVal).trans (subset_elim hxSubY i)

theorem transitive_binary_inter {x y : bSet 𝔹} {Γ : 𝔹}
    (hOrdX : Γ ≤ Ord x) (hOrdY : Γ ≤ Ord y) :
    Γ ≤ is_transitive (binary_inter x y) := by
  unfold is_transitive
  apply le_iInf
  intro z
  apply lattice.bv_imp_intro
  apply subset_intro
  intro i
  let Δ : 𝔹 := Γ ⊓ z ∈ᴮ binary_inter x y
  let Θ : 𝔹 := Δ ⊓ z.bval i
  change Θ ≤ z.func i ∈ᴮ binary_inter x y
  have hzInter : Δ ≤ z ∈ᴮ binary_inter x y := by
    dsimp [Δ]
    exact inf_le_right
  rw [mem_binary_inter_iff] at hzInter
  rw [mem_binary_inter_iff]
  have hΘΔ : Θ ≤ Δ := by
    dsimp [Θ]
    exact inf_le_left
  have hΘΓ : Θ ≤ Γ := by
    dsimp [Θ, Δ]
    exact inf_le_left.trans inf_le_left
  have hΘVal : Θ ≤ z.bval i := by
    dsimp [Θ]
    exact inf_le_right
  constructor
  · exact mem_of_mem_subset'
      (subset_of_mem_Ord (hΘΔ.trans hzInter.1) (hΘΓ.trans hOrdX))
      (mem.mk'' hΘVal)
  · exact mem_of_mem_subset'
      (subset_of_mem_Ord (hΘΔ.trans hzInter.2) (hΘΓ.trans hOrdY))
      (mem.mk'' hΘVal)

theorem epsilon_trichotomy_binary_inter {x y : bSet 𝔹} {Γ : 𝔹}
    (hOrdX : Γ ≤ Ord x) : Γ ≤ epsilon_trichotomy (binary_inter x y) := by
  unfold epsilon_trichotomy
  apply le_iInf
  intro w
  apply lattice.bv_imp_intro
  apply le_iInf
  intro z
  apply lattice.bv_imp_intro
  let Δ : 𝔹 := (Γ ⊓ w ∈ᴮ binary_inter x y) ⊓ z ∈ᴮ binary_inter x y
  change Δ ≤ w =ᴮ z ⊔ w ∈ᴮ z ⊔ z ∈ᴮ w
  have hwInter : Δ ≤ w ∈ᴮ binary_inter x y := by
    dsimp [Δ]
    exact inf_le_left.trans inf_le_right
  have hzInter : Δ ≤ z ∈ᴮ binary_inter x y := by
    dsimp [Δ]
    exact inf_le_right
  rw [mem_binary_inter_iff] at hwInter hzInter
  exact epsilon_trichotomy_of_Ord hwInter.1 hzInter.1
    ((inf_le_left.trans inf_le_left).trans hOrdX)

theorem epsilon_well_founded_binary_inter {x y : bSet 𝔹} {Γ : 𝔹}
    (hOrdX : Γ ≤ Ord x) : Γ ≤ epsilon_well_founded (binary_inter x y) := by
  unfold epsilon_well_founded
  apply le_iInf
  intro w
  apply lattice.bv_imp_intro
  apply lattice.bv_imp_intro
  let Δ : 𝔹 := (Γ ⊓ w ⊆ᴮ binary_inter x y) ⊓ (w =ᴮ (∅ : bSet 𝔹))ᶜ
  change Δ ≤ ⨆ y' : bSet 𝔹, y' ∈ᴮ w ⊓
    (⨅ z : bSet 𝔹, lattice.imp (z ∈ᴮ w) ((z ∈ᴮ y')ᶜ))
  have hwSubInter : Δ ≤ w ⊆ᴮ binary_inter x y := by
    dsimp [Δ]
    exact inf_le_left.trans inf_le_right
  have hwSubX : Δ ≤ w ⊆ᴮ x :=
    (subset_binary_inter_iff.mp hwSubInter).1
  have hNonempty : Δ ≤ (w =ᴮ (∅ : bSet 𝔹))ᶜ := by
    dsimp [Δ]
    exact inf_le_right
  have hWF : Δ ≤ epsilon_well_founded x :=
    (inf_le_left.trans inf_le_left).trans (hOrdX.trans inf_le_left |>.trans inf_le_right)
  have hImpSub :
      Δ ≤ lattice.imp (w ⊆ᴮ x)
        (lattice.imp ((w =ᴮ (∅ : bSet 𝔹))ᶜ)
          (⨆ y' : bSet 𝔹, y' ∈ᴮ w ⊓
            (⨅ z : bSet 𝔹, lattice.imp (z ∈ᴮ w) ((z ∈ᴮ y')ᶜ)))) :=
    hWF.trans (iInf_le _ w)
  exact lattice.bv_context_apply (lattice.bv_context_apply hImpSub hwSubX) hNonempty

theorem Ord_binary_inter {x y : bSet 𝔹} {Γ : 𝔹}
    (hOrdX : Γ ≤ Ord x) (hOrdY : Γ ≤ Ord y) :
    Γ ≤ Ord (binary_inter x y) := by
  unfold Ord epsilon_well_orders
  exact le_inf
    (le_inf (epsilon_trichotomy_binary_inter hOrdX)
      (epsilon_well_founded_binary_inter hOrdX))
    (transitive_binary_inter hOrdX hOrdY)

/-- Boolean-valued relative complement of `y` inside `x`. -/
def compl (x y : bSet 𝔹) : bSet 𝔹 :=
  comprehend (fun z : bSet 𝔹 => (z ∈ᴮ y)ᶜ) x

theorem compl_subset {x y : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ compl x y ⊆ᴮ x :=
  comprehend_subset

theorem mem_compl_iff {x y z : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ z ∈ᴮ compl x y ↔ Γ ≤ z ∈ᴮ x ∧ Γ ≤ (z ∈ᴮ y)ᶜ := by
  constructor
  · intro h
    rw [compl, mem_comprehend_iff₂ (B_ext_compl (B_ext_mem_left y))] at h
    constructor
    · apply (le_inf le_rfl h).trans
      apply lattice.bv_cases_right
      intro w
      let Δ : 𝔹 := Γ ⊓ (w ∈ᴮ x ⊓ (z =ᴮ w ⊓ (w ∈ᴮ y)ᶜ))
      change Δ ≤ z ∈ᴮ x
      have hwMem : Δ ≤ w ∈ᴮ x := by
        dsimp [Δ]
        exact inf_le_right.trans inf_le_left
      have hEq : Δ ≤ z =ᴮ w := by
        dsimp [Δ]
        exact inf_le_right.trans inf_le_right |>.trans inf_le_left
      exact subst_congr_mem_left' (bv_symm hEq) hwMem
    · apply (le_inf le_rfl h).trans
      apply lattice.bv_cases_right
      intro w
      let Δ : 𝔹 := Γ ⊓ (w ∈ᴮ x ⊓ (z =ᴮ w ⊓ (w ∈ᴮ y)ᶜ))
      change Δ ≤ (z ∈ᴮ y)ᶜ
      have hEq : Δ ≤ w =ᴮ z := by
        dsimp [Δ]
        exact bv_symm (inf_le_right.trans inf_le_right |>.trans inf_le_left)
      have hNot : Δ ≤ (w ∈ᴮ y)ᶜ := by
        dsimp [Δ]
        exact inf_le_right.trans inf_le_right |>.trans inf_le_right
      exact (le_inf hEq hNot).trans ((B_ext_compl (B_ext_mem_left y)) w z)
  · intro h
    rw [compl, mem_comprehend_iff₂ (B_ext_compl (B_ext_mem_left y))]
    apply lattice.bv_use z
    exact le_inf h.1 (le_inf bv_refl h.2)

theorem compl_empty_of_subset {x y : bSet 𝔹} {Γ : 𝔹}
    (hSub : Γ ≤ x ⊆ᴮ y) : Γ ≤ compl x y =ᴮ (∅ : bSet 𝔹) := by
  apply subset_ext
  · apply subset_intro
    intro i
    rw [mem_empty]
    let Δ : 𝔹 := Γ ⊓ (compl x y).bval i
    change Δ ≤ ⊥
    have hMemCompl : Δ ≤ (compl x y).func i ∈ᴮ compl x y :=
      mem.mk'' inf_le_right
    have hMem := (mem_compl_iff.mp hMemCompl).1
    have hNot := (mem_compl_iff.mp hMemCompl).2
    have hMemY : Δ ≤ (compl x y).func i ∈ᴮ y :=
      mem_of_mem_subset' (inf_le_left.trans hSub) hMem
    have hBot : Δ ≤ ((compl x y).func i ∈ᴮ y) ⊓ (((compl x y).func i ∈ᴮ y)ᶜ) :=
      le_inf hMemY hNot
    simpa using hBot
  · exact empty_subset

theorem subset_of_compl_empty {x y : bSet 𝔹} {Γ : 𝔹}
    (hEmpty : Γ ≤ compl x y =ᴮ (∅ : bSet 𝔹)) : Γ ≤ x ⊆ᴮ y := by
  apply subset_intro
  intro i
  let A : 𝔹 := x.func i ∈ᴮ y
  let Δ : 𝔹 := Γ ⊓ x.bval i
  change Δ ≤ A
  have hBot : Δ ⊓ Aᶜ ≤ ⊥ := by
    let Θ : 𝔹 := Δ ⊓ Aᶜ
    have hMemX : Θ ≤ x.func i ∈ᴮ x := by
      apply mem.mk''
      dsimp [Θ, Δ]
      exact inf_le_left.trans inf_le_right
    have hNotY : Θ ≤ (x.func i ∈ᴮ y)ᶜ := by
      dsimp [Θ, A]
      exact inf_le_right
    have hMemCompl : Θ ≤ x.func i ∈ᴮ compl x y :=
      mem_compl_iff.mpr ⟨hMemX, hNotY⟩
    have hEqEmpty : Θ ≤ compl x y =ᴮ (∅ : bSet 𝔹) := by
      dsimp [Θ, Δ]
      exact (inf_le_left.trans inf_le_left).trans hEmpty
    have hMemEmpty : Θ ≤ x.func i ∈ᴮ (∅ : bSet 𝔹) :=
      subst_congr_mem_right' hEqEmpty hMemCompl
    simpa [mem_empty] using hMemEmpty
  calc
    Δ = Δ ⊓ (A ⊔ Aᶜ) := by rw [sup_compl_eq_top, inf_top_eq]
    _ = Δ ⊓ A ⊔ Δ ⊓ Aᶜ := by rw [inf_sup_left]
    _ ≤ A := sup_le inf_le_right (hBot.trans bot_le)

theorem eq_of_compl_empty {x y : bSet 𝔹} {Γ : 𝔹}
    (hXY : Γ ≤ compl x y =ᴮ (∅ : bSet 𝔹))
    (hYX : Γ ≤ compl y x =ᴮ (∅ : bSet 𝔹)) : Γ ≤ x =ᴮ y :=
  subset_ext (subset_of_compl_empty hXY) (subset_of_compl_empty hYX)

private theorem bv_absurd {a Γ : 𝔹} (ha : Γ ≤ a) (hna : Γ ≤ aᶜ) : Γ ≤ ⊥ := by
  have hBot : Γ ≤ a ⊓ aᶜ :=
    le_inf ha hna
  simpa using hBot

private theorem le_sup_compl_of_inf_inf_bot {a b c : 𝔹}
    (h : c ⊓ a ⊓ b ≤ ⊥) : c ≤ aᶜ ⊔ bᶜ := by
  calc
    c = c ⊓ ((aᶜ ⊔ bᶜ) ⊔ (aᶜ ⊔ bᶜ)ᶜ) := by
      rw [sup_compl_eq_top, inf_top_eq]
    _ = c ⊓ (aᶜ ⊔ bᶜ) ⊔ c ⊓ (aᶜ ⊔ bᶜ)ᶜ := by rw [inf_sup_left]
    _ ≤ aᶜ ⊔ bᶜ := by
      apply sup_le
      · exact inf_le_right
      · have hComp : c ⊓ (aᶜ ⊔ bᶜ)ᶜ ≤ ⊥ := by
          simpa [compl_sup, compl_compl, inf_assoc, inf_comm, inf_left_comm] using h
        exact hComp.trans bot_le

private theorem le_sup_of_inf_compl_inf_compl_bot {a b c : 𝔹}
    (h : c ⊓ aᶜ ⊓ bᶜ ≤ ⊥) : c ≤ a ⊔ b := by
  simpa [compl_compl] using le_sup_compl_of_inf_inf_bot (a := aᶜ) (b := bᶜ) h

private theorem le_sup_of_inf_compl_le {a b c : 𝔹}
    (h : c ⊓ aᶜ ≤ b) : c ≤ a ⊔ b := by
  calc
    c = c ⊓ (a ⊔ aᶜ) := by rw [sup_compl_eq_top, inf_top_eq]
    _ = c ⊓ a ⊔ c ⊓ aᶜ := by rw [inf_sup_left]
    _ ≤ a ⊔ b := sup_le (inf_le_right.trans le_sup_left) (h.trans le_sup_right)

private theorem le_compl_of_inf_le_bot {a c : 𝔹} (h : c ⊓ a ≤ ⊥) : c ≤ aᶜ := by
  calc
    c = c ⊓ (a ⊔ aᶜ) := by rw [sup_compl_eq_top, inf_top_eq]
    _ = c ⊓ a ⊔ c ⊓ aᶜ := by rw [inf_sup_left]
    _ ≤ aᶜ := sup_le (h.trans bot_le) inf_le_right

private theorem right_compl_of_sup_compl_left {a b c : 𝔹}
    (hSup : c ≤ aᶜ ⊔ bᶜ) (ha : c ≤ a) : c ≤ bᶜ := by
  apply (le_inf le_rfl hSup).trans
  apply lattice.bv_or_elim_right
  · apply lattice.bv_exfalso
    exact bv_absurd (inf_le_left.trans ha) inf_le_right
  · exact inf_le_right

theorem nonempty_compl_of_ne {x y : bSet 𝔹} {Γ : 𝔹}
    (hNe : Γ ≤ (x =ᴮ y)ᶜ) :
    Γ ≤ (compl x y =ᴮ (∅ : bSet 𝔹))ᶜ ⊔
      (compl y x =ᴮ (∅ : bSet 𝔹))ᶜ := by
  let A : 𝔹 := compl x y =ᴮ (∅ : bSet 𝔹)
  let B : 𝔹 := compl y x =ᴮ (∅ : bSet 𝔹)
  apply le_sup_compl_of_inf_inf_bot
  let Δ : 𝔹 := Γ ⊓ A ⊓ B
  change Δ ≤ ⊥
  have hEq : Δ ≤ x =ᴮ y := by
    apply eq_of_compl_empty
    · dsimp [Δ, A]
      exact inf_le_left.trans inf_le_right
    · dsimp [Δ, B]
      exact inf_le_right
  have hNotEq : Δ ≤ (x =ᴮ y)ᶜ := by
    dsimp [Δ]
    exact (inf_le_left.trans inf_le_left).trans hNe
  have hBot : Δ ≤ (x =ᴮ y) ⊓ (x =ᴮ y)ᶜ :=
    le_inf hEq hNotEq
  simpa using hBot

theorem B_ext_mem_self : B_ext (fun x : bSet 𝔹 => x ∈ᴮ x) := by
  intro x y
  let Γ : 𝔹 := x =ᴮ y ⊓ x ∈ᴮ x
  change Γ ≤ y ∈ᴮ y
  have hEq : Γ ≤ x =ᴮ y := by
    dsimp [Γ]
    exact inf_le_left
  have hMem : Γ ≤ x ∈ᴮ x := by
    dsimp [Γ]
    exact inf_le_right
  have hMemLeft : Γ ≤ y ∈ᴮ x :=
    subst_congr_mem_left' hEq hMem
  exact subst_congr_mem_right' hEq hMemLeft

/-- Auxiliary predicate for epsilon induction: a Boolean-valued set is not a member of itself. -/
def no_self_mem_pred (x : bSet 𝔹) : 𝔹 :=
  (x ∈ᴮ x)ᶜ

theorem B_ext_no_self_mem_pred :
    B_ext (no_self_mem_pred : bSet 𝔹 → 𝔹) := by
  unfold no_self_mem_pred
  exact B_ext_compl B_ext_mem_self

theorem not_mem_self (x : bSet 𝔹) {Γ : 𝔹} : Γ ≤ no_self_mem_pred x := by
  refine epsilon_induction (Γ := Γ) no_self_mem_pred B_ext_no_self_mem_pred ?_ x
  intro x
  apply lattice.bv_imp_intro
  let IH : 𝔹 := ⨅ y : bSet 𝔹, lattice.imp (y ∈ᴮ x) (no_self_mem_pred y)
  let Δ : 𝔹 := Γ ⊓ IH
  change Δ ≤ no_self_mem_pred x
  unfold no_self_mem_pred
  have hBot : Δ ⊓ x ∈ᴮ x ≤ ⊥ := by
    let Θ : 𝔹 := Δ ⊓ x ∈ᴮ x
    have hIH : Θ ≤ IH := by
      dsimp [Θ, Δ]
      exact inf_le_left.trans inf_le_right
    have hxMem : Θ ≤ x ∈ᴮ x := by
      dsimp [Θ]
      exact inf_le_right
    have hxNotMem : Θ ≤ no_self_mem_pred x :=
      lattice.bv_context_apply (hIH.trans (iInf_le _ x)) hxMem
    exact bv_absurd hxMem hxNotMem
  calc
    Δ = Δ ⊓ ((x ∈ᴮ x) ⊔ (x ∈ᴮ x)ᶜ) := by rw [sup_compl_eq_top, inf_top_eq]
    _ = Δ ⊓ (x ∈ᴮ x) ⊔ Δ ⊓ (x ∈ᴮ x)ᶜ := by rw [inf_sup_left]
    _ ≤ (x ∈ᴮ x)ᶜ := sup_le (hBot.trans bot_le) inf_le_right

theorem bot_of_mem_self {x : bSet 𝔹} {Γ : 𝔹} (hMem : Γ ≤ x ∈ᴮ x) : Γ ≤ ⊥ :=
  bv_absurd hMem (by simpa [no_self_mem_pred] using not_mem_self x)

theorem nonempty_iff_exists_mem {x : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ (x =ᴮ (∅ : bSet 𝔹))ᶜ ↔ Γ ≤ ⨆ y : bSet 𝔹, y ∈ᴮ x := by
  constructor
  · intro h
    have hEq : x =ᴮ (∅ : bSet 𝔹) = x ⊆ᴮ (∅ : bSet 𝔹) := by
      rw [eq_iff_subset_subset, empty_subset_eq_top, inf_top_eq]
    have hIdx : Γ ≤ ⨆ i : x.type, x.bval i := by
      simpa [hEq, subset_unfold, lattice.imp, mem_empty, compl_iInf] using h
    apply (le_inf le_rfl hIdx).trans
    apply lattice.bv_cases_right
    intro i
    apply lattice.bv_use (x.func i)
    exact mem.mk'' inf_le_right
  · intro h
    rw [le_compl_iff_disjoint_right, disjoint_iff]
    apply le_antisymm ?_ bot_le
    apply (le_inf le_rfl (inf_le_left.trans h)).trans
    apply lattice.bv_cases_right
    intro y
    let Δ : 𝔹 := (Γ ⊓ x =ᴮ (∅ : bSet 𝔹)) ⊓ y ∈ᴮ x
    change Δ ≤ ⊥
    have hEq : Δ ≤ x =ᴮ (∅ : bSet 𝔹) := by
      dsimp [Δ]
      exact inf_le_left.trans inf_le_right
    have hMemX : Δ ≤ y ∈ᴮ x := by
      dsimp [Δ]
      exact inf_le_right
    have hMemEmpty : Δ ≤ y ∈ᴮ (∅ : bSet 𝔹) :=
      subst_congr_mem_right' hEq hMemX
    simpa [mem_empty] using hMemEmpty

/-- `y` is epsilon-minimal in `u`: no member of `u` lies in `y`. -/
def epsilon_minimal_in (y u : bSet 𝔹) : 𝔹 :=
  ⨅ z : bSet 𝔹, lattice.imp (z ∈ᴮ u) ((z ∈ᴮ y)ᶜ)

/-- `u` has an epsilon-minimal member. -/
def exists_epsilon_minimal (u : bSet 𝔹) : 𝔹 :=
  ⨆ y : bSet 𝔹, y ∈ᴮ u ⊓ epsilon_minimal_in y u

/-- Auxiliary predicate used by epsilon induction to prove Boolean-valued regularity. -/
def regularity_aux_pred (x : bSet 𝔹) : 𝔹 :=
  ⨅ u : bSet 𝔹, lattice.imp (x ∈ᴮ u) (exists_epsilon_minimal u)

theorem B_ext_regularity_aux_pred :
    B_ext (regularity_aux_pred : bSet 𝔹 → 𝔹) := by
  unfold regularity_aux_pred
  apply B_ext_iInf
  intro u
  apply B_ext_imp
  · exact B_ext_mem_left u
  · exact B_ext_const _

theorem regularity_aux (x : bSet 𝔹) {Γ : 𝔹} :
    Γ ≤ regularity_aux_pred x := by
  refine epsilon_induction (Γ := Γ) regularity_aux_pred B_ext_regularity_aux_pred ?_ x
  intro x
  apply lattice.bv_imp_intro
  unfold regularity_aux_pred
  apply le_iInf
  intro u
  apply lattice.bv_imp_intro
  let IH : 𝔹 := ⨅ y : bSet 𝔹, lattice.imp (y ∈ᴮ x) (regularity_aux_pred y)
  let Δ : 𝔹 := (Γ ⊓ IH) ⊓ x ∈ᴮ u
  change Δ ≤ exists_epsilon_minimal u
  let M : 𝔹 := epsilon_minimal_in x u
  have hChooseX : Δ ⊓ M ≤ exists_epsilon_minimal u := by
    unfold exists_epsilon_minimal
    apply lattice.bv_use x
    dsimp [Δ, M]
    exact le_inf (inf_le_left.trans inf_le_right) inf_le_right
  have hUseMember : Δ ⊓ Mᶜ ≤ exists_epsilon_minimal u := by
    have hCases : Δ ⊓ Mᶜ ≤ ⨆ z : bSet 𝔹, z ∈ᴮ u ⊓ z ∈ᴮ x := by
      dsimp [M, epsilon_minimal_in]
      simp [lattice.imp, compl_iInf, compl_sup, compl_compl, inf_comm]
    apply (le_inf le_rfl hCases).trans
    apply lattice.bv_cases_right
    intro z
    let Θ : 𝔹 := (Δ ⊓ Mᶜ) ⊓ (z ∈ᴮ u ⊓ z ∈ᴮ x)
    change Θ ≤ exists_epsilon_minimal u
    have hIH : Θ ≤ IH := by
      dsimp [Θ, Δ]
      exact inf_le_left.trans inf_le_left |>.trans inf_le_left |>.trans inf_le_right
    have hzMemX : Θ ≤ z ∈ᴮ x := by
      dsimp [Θ]
      exact inf_le_right.trans inf_le_right
    have hzReg : Θ ≤ regularity_aux_pred z :=
      lattice.bv_context_apply (hIH.trans (iInf_le _ z)) hzMemX
    have hzMemU : Θ ≤ z ∈ᴮ u := by
      dsimp [Θ]
      exact inf_le_right.trans inf_le_left
    exact lattice.bv_context_apply (hzReg.trans (iInf_le _ u)) hzMemU
  calc
    Δ = Δ ⊓ (M ⊔ Mᶜ) := by rw [sup_compl_eq_top, inf_top_eq]
    _ = Δ ⊓ M ⊔ Δ ⊓ Mᶜ := by rw [inf_sup_left]
    _ ≤ exists_epsilon_minimal u := sup_le hChooseX hUseMember

theorem bSet_axiom_of_regularity (x : bSet 𝔹) {Γ : 𝔹}
    (hNonempty : Γ ≤ (x =ᴮ (∅ : bSet 𝔹))ᶜ) :
    Γ ≤ exists_epsilon_minimal x := by
  have hExists : Γ ≤ ⨆ y : bSet 𝔹, y ∈ᴮ x :=
    nonempty_iff_exists_mem.mp hNonempty
  apply (le_inf le_rfl hExists).trans
  apply lattice.bv_cases_right
  intro y
  let Δ : 𝔹 := Γ ⊓ y ∈ᴮ x
  change Δ ≤ exists_epsilon_minimal x
  have hyReg : Δ ≤ regularity_aux_pred y :=
    regularity_aux y
  have hyMem : Δ ≤ y ∈ᴮ x := by
    dsimp [Δ]
    exact inf_le_right
  exact lattice.bv_context_apply (hyReg.trans (iInf_le _ x)) hyMem

theorem bSet_axiom_of_regularity_unfolded (x : bSet 𝔹) {Γ : 𝔹}
    (hNonempty : Γ ≤ (x =ᴮ (∅ : bSet 𝔹))ᶜ) :
    Γ ≤ ⨆ y : bSet 𝔹, y ∈ᴮ x ⊓
      (⨅ z : bSet 𝔹, lattice.imp (z ∈ᴮ x) ((z ∈ᴮ y)ᶜ)) := by
  simpa [exists_epsilon_minimal, epsilon_minimal_in] using
    bSet_axiom_of_regularity x hNonempty

theorem is_epsilon_well_founded {x : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ epsilon_well_founded x := by
  unfold epsilon_well_founded
  apply le_iInf
  intro u
  apply lattice.bv_imp_intro
  apply lattice.bv_imp_intro
  let Δ : 𝔹 := (Γ ⊓ u ⊆ᴮ x) ⊓ (u =ᴮ (∅ : bSet 𝔹))ᶜ
  change Δ ≤ ⨆ y : bSet 𝔹, y ∈ᴮ u ⊓
    (⨅ z : bSet 𝔹, lattice.imp (z ∈ᴮ u) ((z ∈ᴮ y)ᶜ))
  exact bSet_axiom_of_regularity_unfolded u (by
    dsimp [Δ]
    exact inf_le_right)

theorem bot_of_mem_mem {x y : bSet 𝔹} {Γ : 𝔹}
    (hXY : Γ ≤ x ∈ᴮ y) (hYX : Γ ≤ y ∈ᴮ x) : Γ ≤ ⊥ := by
  let p : bSet 𝔹 := insert x ({y} : bSet 𝔹)
  have hxP : Γ ≤ x ∈ᴮ p := by
    dsimp [p]
    exact (mem_insert_self (x := x) (y := ({y} : bSet 𝔹)))
  have hyP : Γ ≤ y ∈ᴮ p := by
    dsimp [p]
    exact mem_insert_of_mem (x := y) (y := x) (z := ({y} : bSet 𝔹)) mem_singleton
  have hExists : Γ ≤ ⨆ z : bSet 𝔹, z ∈ᴮ p :=
    lattice.bv_use x hxP
  have hNonempty : Γ ≤ (p =ᴮ (∅ : bSet 𝔹))ᶜ :=
    nonempty_iff_exists_mem.mpr hExists
  have hMin : Γ ≤ exists_epsilon_minimal p :=
    bSet_axiom_of_regularity p hNonempty
  unfold exists_epsilon_minimal at hMin
  apply (le_inf le_rfl hMin).trans
  apply lattice.bv_cases_right
  intro m
  let Δ : 𝔹 := Γ ⊓ (m ∈ᴮ p ⊓ epsilon_minimal_in m p)
  change Δ ≤ ⊥
  have hmP : Δ ≤ m ∈ᴮ p := by
    dsimp [Δ]
    exact inf_le_right.trans inf_le_left
  have hmMin : Δ ≤ epsilon_minimal_in m p := by
    dsimp [Δ]
    exact inf_le_right.trans inf_le_right
  dsimp [p] at hmP
  rw [mem_insert, top_inf_eq] at hmP
  apply (le_inf le_rfl hmP).trans
  apply lattice.bv_or_elim_right
  · let Θ : 𝔹 := Δ ⊓ m =ᴮ x
    change Θ ≤ ⊥
    have hmEqX : Θ ≤ m =ᴮ x := by
      dsimp [Θ]
      exact inf_le_right
    have hyPΘ : Θ ≤ y ∈ᴮ p :=
      inf_le_left.trans inf_le_left |>.trans hyP
    have hyM : Θ ≤ y ∈ᴮ m :=
      subst_congr_mem_right' (bv_symm hmEqX) ((inf_le_left.trans inf_le_left).trans hYX)
    have hNoYMemM : Θ ≤ (y ∈ᴮ m)ᶜ :=
      lattice.bv_context_apply
        ((inf_le_left.trans hmMin).trans (iInf_le _ y)) hyPΘ
    exact bv_absurd hyM hNoYMemM
  · let Θ : 𝔹 := Δ ⊓ m ∈ᴮ ({y} : bSet 𝔹)
    change Θ ≤ ⊥
    have hmMemSingleton : Θ ≤ m ∈ᴮ ({y} : bSet 𝔹) := by
      dsimp [Θ]
      exact inf_le_right
    have hmEqY : Θ ≤ m =ᴮ y :=
      bv_symm (eq_of_mem_singleton hmMemSingleton)
    have hxPΘ : Θ ≤ x ∈ᴮ p :=
      inf_le_left.trans inf_le_left |>.trans hxP
    have hxM : Θ ≤ x ∈ᴮ m :=
      subst_congr_mem_right' (bv_symm hmEqY) ((inf_le_left.trans inf_le_left).trans hXY)
    have hNoXMemM : Θ ≤ (x ∈ᴮ m)ᶜ :=
      lattice.bv_context_apply
        ((inf_le_left.trans hmMin).trans (iInf_le _ x)) hxPΘ
    exact bv_absurd hxM hNoXMemM

theorem bot_of_mem_mem_mem {x y z : bSet 𝔹} {Γ : 𝔹}
    (hXY : Γ ≤ x ∈ᴮ y) (hYZ : Γ ≤ y ∈ᴮ z) (hZX : Γ ≤ z ∈ᴮ x) : Γ ≤ ⊥ := by
  let p : bSet 𝔹 := insert x (insert y ({z} : bSet 𝔹))
  let q : bSet 𝔹 := insert y ({z} : bSet 𝔹)
  have hxP : Γ ≤ x ∈ᴮ p := by
    dsimp [p]
    exact (mem_insert_self (x := x) (y := q))
  have hyQ : Γ ≤ y ∈ᴮ q := by
    dsimp [q]
    exact (mem_insert_self (x := y) (y := ({z} : bSet 𝔹)))
  have hyP : Γ ≤ y ∈ᴮ p := by
    dsimp [p]
    exact mem_insert_of_mem hyQ
  have hzQ : Γ ≤ z ∈ᴮ q := by
    dsimp [q]
    exact mem_insert_of_mem (x := z) (y := y) (z := ({z} : bSet 𝔹)) mem_singleton
  have hzP : Γ ≤ z ∈ᴮ p := by
    dsimp [p]
    exact mem_insert_of_mem hzQ
  have hExists : Γ ≤ ⨆ w : bSet 𝔹, w ∈ᴮ p :=
    lattice.bv_use x hxP
  have hNonempty : Γ ≤ (p =ᴮ (∅ : bSet 𝔹))ᶜ :=
    nonempty_iff_exists_mem.mpr hExists
  have hMin : Γ ≤ exists_epsilon_minimal p :=
    bSet_axiom_of_regularity p hNonempty
  unfold exists_epsilon_minimal at hMin
  apply (le_inf le_rfl hMin).trans
  apply lattice.bv_cases_right
  intro m
  let Δ : 𝔹 := Γ ⊓ (m ∈ᴮ p ⊓ epsilon_minimal_in m p)
  change Δ ≤ ⊥
  have hmP : Δ ≤ m ∈ᴮ p := by
    dsimp [Δ]
    exact inf_le_right.trans inf_le_left
  have hmMin : Δ ≤ epsilon_minimal_in m p := by
    dsimp [Δ]
    exact inf_le_right.trans inf_le_right
  dsimp [p] at hmP
  rw [mem_insert, top_inf_eq] at hmP
  apply (le_inf le_rfl hmP).trans
  apply lattice.bv_or_elim_right
  · let Θ : 𝔹 := Δ ⊓ m =ᴮ x
    change Θ ≤ ⊥
    have hmEqX : Θ ≤ m =ᴮ x := by
      dsimp [Θ]
      exact inf_le_right
    have hzPΘ : Θ ≤ z ∈ᴮ p :=
      inf_le_left.trans inf_le_left |>.trans hzP
    have hzM : Θ ≤ z ∈ᴮ m :=
      subst_congr_mem_right' (bv_symm hmEqX) ((inf_le_left.trans inf_le_left).trans hZX)
    have hNoZMemM : Θ ≤ (z ∈ᴮ m)ᶜ :=
      lattice.bv_context_apply
        ((inf_le_left.trans hmMin).trans (iInf_le _ z)) hzPΘ
    exact bv_absurd hzM hNoZMemM
  · let Θ : 𝔹 := Δ ⊓ m ∈ᴮ q
    change Θ ≤ ⊥
    have hmQ : Θ ≤ m ∈ᴮ q := by
      dsimp [Θ]
      exact inf_le_right
    dsimp [q] at hmQ
    rw [mem_insert, top_inf_eq] at hmQ
    apply (le_inf le_rfl hmQ).trans
    apply lattice.bv_or_elim_right
    · let Ω : 𝔹 := Θ ⊓ m =ᴮ y
      change Ω ≤ ⊥
      have hmEqY : Ω ≤ m =ᴮ y := by
        dsimp [Ω]
        exact inf_le_right
      have hxPΩ : Ω ≤ x ∈ᴮ p :=
        inf_le_left.trans inf_le_left |>.trans inf_le_left |>.trans hxP
      have hxM : Ω ≤ x ∈ᴮ m :=
        subst_congr_mem_right' (bv_symm hmEqY)
          (((inf_le_left.trans inf_le_left).trans inf_le_left).trans hXY)
      have hNoXMemM : Ω ≤ (x ∈ᴮ m)ᶜ :=
        lattice.bv_context_apply
          (((inf_le_left.trans inf_le_left).trans hmMin).trans (iInf_le _ x)) hxPΩ
      exact bv_absurd hxM hNoXMemM
    · let Ω : 𝔹 := Θ ⊓ m ∈ᴮ ({z} : bSet 𝔹)
      change Ω ≤ ⊥
      have hmMemSingleton : Ω ≤ m ∈ᴮ ({z} : bSet 𝔹) := by
        dsimp [Ω]
        exact inf_le_right
      have hmEqZ : Ω ≤ m =ᴮ z :=
        bv_symm (eq_of_mem_singleton hmMemSingleton)
      have hyPΩ : Ω ≤ y ∈ᴮ p :=
        inf_le_left.trans inf_le_left |>.trans inf_le_left |>.trans hyP
      have hyM : Ω ≤ y ∈ᴮ m :=
        subst_congr_mem_right' (bv_symm hmEqZ)
          (((inf_le_left.trans inf_le_left).trans inf_le_left).trans hYZ)
      have hNoYMemM : Ω ≤ (y ∈ᴮ m)ᶜ :=
        lattice.bv_context_apply
          (((inf_le_left.trans inf_le_left).trans hmMin).trans (iInf_le _ y)) hyPΩ
      exact bv_absurd hyM hNoYMemM

theorem Ord_of_mem_Ord {x z : bSet 𝔹} {Γ : 𝔹}
    (hMem : Γ ≤ x ∈ᴮ z) (hOrdZ : Γ ≤ Ord z) : Γ ≤ Ord x := by
  unfold Ord epsilon_well_orders
  apply le_inf
  · apply le_inf
    · unfold epsilon_trichotomy
      apply le_iInf
      intro y
      apply lattice.bv_imp_intro
      apply le_iInf
      intro w
      apply lattice.bv_imp_intro
      let Δ : 𝔹 := (Γ ⊓ y ∈ᴮ x) ⊓ w ∈ᴮ x
      change Δ ≤ y =ᴮ w ⊔ y ∈ᴮ w ⊔ w ∈ᴮ y
      have hΔΓ : Δ ≤ Γ := by
        dsimp [Δ]
        exact inf_le_left.trans inf_le_left
      have hyX : Δ ≤ y ∈ᴮ x := by
        dsimp [Δ]
        exact inf_le_left.trans inf_le_right
      have hwX : Δ ≤ w ∈ᴮ x := by
        dsimp [Δ]
        exact inf_le_right
      have hxZ : Δ ≤ x ∈ᴮ z :=
        hΔΓ.trans hMem
      have hyZ : Δ ≤ y ∈ᴮ z :=
        mem_of_mem_Ord hyX hxZ (hΔΓ.trans hOrdZ)
      have hwZ : Δ ≤ w ∈ᴮ z :=
        mem_of_mem_Ord hwX hxZ (hΔΓ.trans hOrdZ)
      exact epsilon_trichotomy_of_Ord hyZ hwZ (hΔΓ.trans hOrdZ)
    · exact is_epsilon_well_founded
  · unfold is_transitive
    apply le_iInf
    intro y
    apply lattice.bv_imp_intro
    apply subset_intro
    intro i
    let w : bSet 𝔹 := y.func i
    let Δ : 𝔹 := (Γ ⊓ y ∈ᴮ x) ⊓ y.bval i
    change Δ ≤ w ∈ᴮ x
    have hΔΓ : Δ ≤ Γ := by
      dsimp [Δ]
      exact inf_le_left.trans inf_le_left
    have hyX : Δ ≤ y ∈ᴮ x := by
      dsimp [Δ]
      exact inf_le_left.trans inf_le_right
    have hwY : Δ ≤ w ∈ᴮ y := by
      apply mem.mk''
      dsimp [Δ, w]
      exact inf_le_right
    have hxZ : Δ ≤ x ∈ᴮ z :=
      hΔΓ.trans hMem
    have hyZ : Δ ≤ y ∈ᴮ z :=
      mem_of_mem_Ord hyX hxZ (hΔΓ.trans hOrdZ)
    have hwZ : Δ ≤ w ∈ᴮ z :=
      mem_of_mem_Ord hwY hyZ (hΔΓ.trans hOrdZ)
    have hTri : Δ ≤ w =ᴮ x ⊔ w ∈ᴮ x ⊔ x ∈ᴮ w :=
      epsilon_trichotomy_of_Ord hwZ hxZ (hΔΓ.trans hOrdZ)
    apply (le_inf le_rfl hTri).trans
    apply lattice.bv_or_elim_right
    · apply lattice.bv_or_elim_right
      · let Θ : 𝔹 := Δ ⊓ w =ᴮ x
        change Θ ≤ w ∈ᴮ x
        have hwEqX : Θ ≤ w =ᴮ x := by
          dsimp [Θ]
          exact inf_le_right
        have hwYΘ : Θ ≤ w ∈ᴮ y :=
          inf_le_left.trans hwY
        have hxY : Θ ≤ x ∈ᴮ y :=
          subst_congr_mem_left' hwEqX hwYΘ
        have hyXΘ : Θ ≤ y ∈ᴮ x :=
          inf_le_left.trans hyX
        exact lattice.bv_exfalso (bot_of_mem_mem hxY hyXΘ)
      · exact inf_le_right
    · let Θ : 𝔹 := Δ ⊓ x ∈ᴮ w
      change Θ ≤ w ∈ᴮ x
      have hxW : Θ ≤ x ∈ᴮ w := by
        dsimp [Θ]
        exact inf_le_right
      have hwYΘ : Θ ≤ w ∈ᴮ y :=
        inf_le_left.trans hwY
      have hyXΘ : Θ ≤ y ∈ᴮ x :=
        inf_le_left.trans hyX
      exact lattice.bv_exfalso (bot_of_mem_mem_mem hxW hwYΘ hyXΘ)

theorem Ord.lt_of_ne_and_le {x y : bSet 𝔹} {Γ : 𝔹}
    (hOrdX : Γ ≤ Ord x) (hOrdY : Γ ≤ Ord y)
    (hNe : Γ ≤ (x =ᴮ y)ᶜ) (hLe : Γ ≤ x ⊆ᴮ y) : Γ ≤ x ∈ᴮ y := by
  have hComplNonempty : Γ ≤ (compl y x =ᴮ (∅ : bSet 𝔹))ᶜ :=
    right_compl_of_sup_compl_left (nonempty_compl_of_ne hNe) (compl_empty_of_subset hLe)
  have hExMin : Γ ≤ exists_epsilon_minimal (compl y x) :=
    bSet_axiom_of_regularity (compl y x) hComplNonempty
  unfold exists_epsilon_minimal at hExMin
  apply (le_inf le_rfl hExMin).trans
  apply lattice.bv_cases_right
  intro z
  let Δ : 𝔹 := Γ ⊓ (z ∈ᴮ compl y x ⊓ epsilon_minimal_in z (compl y x))
  change Δ ≤ x ∈ᴮ y
  have hzCompl : Δ ≤ z ∈ᴮ compl y x := by
    dsimp [Δ]
    exact inf_le_right.trans inf_le_left
  have hzY : Δ ≤ z ∈ᴮ y :=
    (mem_compl_iff.mp hzCompl).1
  have hzNotX : Δ ≤ (z ∈ᴮ x)ᶜ :=
    (mem_compl_iff.mp hzCompl).2
  have hzMin : Δ ≤ epsilon_minimal_in z (compl y x) := by
    dsimp [Δ]
    exact inf_le_right.trans inf_le_right
  have hEqXZ : Δ ≤ x =ᴮ z := by
    apply subset_ext
    · apply subset_intro
      intro i
      let a : bSet 𝔹 := x.func i
      let Θ : 𝔹 := Δ ⊓ x.bval i
      change Θ ≤ a ∈ᴮ z
      have haX : Θ ≤ a ∈ᴮ x := by
        apply mem.mk''
        dsimp [Θ, a]
        exact inf_le_right
      have haY : Θ ≤ a ∈ᴮ y :=
        mem_of_mem_subset' ((inf_le_left.trans inf_le_left).trans hLe) haX
      have hTri : Θ ≤ a =ᴮ z ⊔ a ∈ᴮ z ⊔ z ∈ᴮ a :=
        epsilon_trichotomy_of_Ord haY ((inf_le_left.trans hzY))
          ((inf_le_left.trans inf_le_left).trans hOrdY)
      apply (le_inf le_rfl hTri).trans
      apply lattice.bv_or_elim_right
      · apply lattice.bv_or_elim_right
        · let Ω : 𝔹 := Θ ⊓ a =ᴮ z
          change Ω ≤ a ∈ᴮ z
          have hEqAZ : Ω ≤ a =ᴮ z := by
            dsimp [Ω]
            exact inf_le_right
          have haXΩ : Ω ≤ a ∈ᴮ x :=
            inf_le_left.trans haX
          have hzX : Ω ≤ z ∈ᴮ x :=
            subst_congr_mem_left' hEqAZ haXΩ
          have hzNotXΩ : Ω ≤ (z ∈ᴮ x)ᶜ :=
            inf_le_left.trans inf_le_left |>.trans hzNotX
          exact lattice.bv_exfalso (bv_absurd hzX hzNotXΩ)
        · exact inf_le_right
      · let Ω : 𝔹 := Θ ⊓ z ∈ᴮ a
        change Ω ≤ a ∈ᴮ z
        have hzA : Ω ≤ z ∈ᴮ a := by
          dsimp [Ω]
          exact inf_le_right
        have haXΩ : Ω ≤ a ∈ᴮ x :=
          inf_le_left.trans haX
        have hzX : Ω ≤ z ∈ᴮ x :=
          mem_of_mem_Ord hzA haXΩ (((inf_le_left.trans inf_le_left).trans inf_le_left).trans hOrdX)
        have hzNotXΩ : Ω ≤ (z ∈ᴮ x)ᶜ :=
          inf_le_left.trans inf_le_left |>.trans hzNotX
        exact lattice.bv_exfalso (bv_absurd hzX hzNotXΩ)
    · apply subset_intro
      intro i
      let a : bSet 𝔹 := z.func i
      let Θ : 𝔹 := Δ ⊓ z.bval i
      change Θ ≤ a ∈ᴮ x
      have haZ : Θ ≤ a ∈ᴮ z := by
        apply mem.mk''
        dsimp [Θ, a]
        exact inf_le_right
      have hBot : Θ ⊓ (a ∈ᴮ x)ᶜ ≤ ⊥ := by
        let Ω : 𝔹 := Θ ⊓ (a ∈ᴮ x)ᶜ
        have haZΩ : Ω ≤ a ∈ᴮ z :=
          inf_le_left.trans haZ
        have haY : Ω ≤ a ∈ᴮ y :=
          mem_of_mem_Ord haZΩ (inf_le_left.trans inf_le_left |>.trans hzY)
            (((inf_le_left.trans inf_le_left).trans inf_le_left).trans hOrdY)
        have haNotX : Ω ≤ (a ∈ᴮ x)ᶜ := by
          dsimp [Ω]
          exact inf_le_right
        have haCompl : Ω ≤ a ∈ᴮ compl y x :=
          mem_compl_iff.mpr ⟨haY, haNotX⟩
        have hMinImp :
            Ω ≤ lattice.imp (a ∈ᴮ compl y x) ((a ∈ᴮ z)ᶜ) :=
          ((inf_le_left.trans inf_le_left).trans hzMin).trans (iInf_le _ a)
        have haNotZ : Ω ≤ (a ∈ᴮ z)ᶜ :=
          lattice.bv_context_apply hMinImp haCompl
        exact bv_absurd haZΩ haNotZ
      calc
        Θ = Θ ⊓ ((a ∈ᴮ x) ⊔ (a ∈ᴮ x)ᶜ) := by rw [sup_compl_eq_top, inf_top_eq]
        _ = Θ ⊓ (a ∈ᴮ x) ⊔ Θ ⊓ (a ∈ᴮ x)ᶜ := by rw [inf_sup_left]
        _ ≤ a ∈ᴮ x := sup_le inf_le_right (hBot.trans bot_le)
  exact subst_congr_mem_left' (bv_symm hEqXZ) hzY

theorem Ord.le_or_le {x y : bSet 𝔹} {Γ : 𝔹}
    (hOrdX : Γ ≤ Ord x) (hOrdY : Γ ≤ Ord y) : Γ ≤ x ⊆ᴮ y ⊔ y ⊆ᴮ x := by
  let w : bSet 𝔹 := binary_inter x y
  have hOrdW : Γ ≤ Ord w :=
    Ord_binary_inter hOrdX hOrdY
  have hEqOr : Γ ≤ w =ᴮ x ⊔ w =ᴮ y := by
    apply le_sup_of_inf_compl_inf_compl_bot
    let Δ : 𝔹 := Γ ⊓ (w =ᴮ x)ᶜ ⊓ (w =ᴮ y)ᶜ
    change Δ ≤ ⊥
    have hΔΓ : Δ ≤ Γ := by
      dsimp [Δ]
      exact inf_le_left.trans inf_le_left
    have hwxNe : Δ ≤ (w =ᴮ x)ᶜ := by
      dsimp [Δ]
      exact inf_le_left.trans inf_le_right
    have hwyNe : Δ ≤ (w =ᴮ y)ᶜ := by
      dsimp [Δ]
      exact inf_le_right
    have hwx : Δ ≤ w ∈ᴮ x :=
      Ord.lt_of_ne_and_le (hΔΓ.trans hOrdW) (hΔΓ.trans hOrdX) hwxNe binary_inter_subset_left
    have hwy : Δ ≤ w ∈ᴮ y :=
      Ord.lt_of_ne_and_le (hΔΓ.trans hOrdW) (hΔΓ.trans hOrdY) hwyNe binary_inter_subset_right
    have hww : Δ ≤ w ∈ᴮ w :=
      mem_binary_inter_iff.mpr ⟨hwx, hwy⟩
    exact bot_of_mem_self hww
  apply (le_inf le_rfl hEqOr).trans
  apply lattice.bv_or_elim_right
  · let Δ : 𝔹 := Γ ⊓ w =ᴮ x
    change Δ ≤ x ⊆ᴮ y ⊔ y ⊆ᴮ x
    apply lattice.bv_or_left
    have hEqWX : Δ ≤ w =ᴮ x := by
      dsimp [Δ]
      exact inf_le_right
    exact subst_congr_subset_left' hEqWX binary_inter_subset_right
  · let Δ : 𝔹 := Γ ⊓ w =ᴮ y
    change Δ ≤ x ⊆ᴮ y ⊔ y ⊆ᴮ x
    apply lattice.bv_or_right
    have hEqWY : Δ ≤ w =ᴮ y := by
      dsimp [Δ]
      exact inf_le_right
    exact subst_congr_subset_left' hEqWY binary_inter_subset_left

theorem Ord.trichotomy {x y : bSet 𝔹} {Γ : 𝔹}
    (hOrdX : Γ ≤ Ord x) (hOrdY : Γ ≤ Ord y) :
    Γ ≤ x =ᴮ y ⊔ x ∈ᴮ y ⊔ y ∈ᴮ x := by
  have hLeOr : Γ ≤ x ⊆ᴮ y ⊔ y ⊆ᴮ x :=
    Ord.le_or_le hOrdX hOrdY
  apply (le_inf le_rfl hLeOr).trans
  apply lattice.bv_or_elim_right
  · let Δ : 𝔹 := Γ ⊓ x ⊆ᴮ y
    change Δ ≤ x =ᴮ y ⊔ x ∈ᴮ y ⊔ y ∈ᴮ x
    have hPart : Δ ≤ x =ᴮ y ⊔ x ∈ᴮ y := by
      apply le_sup_of_inf_compl_le
      let Θ : 𝔹 := Δ ⊓ (x =ᴮ y)ᶜ
      change Θ ≤ x ∈ᴮ y
      have hΘΓ : Θ ≤ Γ := by
        dsimp [Θ, Δ]
        exact (inf_le_left.trans inf_le_left)
      have hNe : Θ ≤ (x =ᴮ y)ᶜ := by
        dsimp [Θ]
        exact inf_le_right
      have hSub : Θ ≤ x ⊆ᴮ y := by
        dsimp [Θ, Δ]
        exact inf_le_left.trans inf_le_right
      exact Ord.lt_of_ne_and_le (hΘΓ.trans hOrdX) (hΘΓ.trans hOrdY) hNe hSub
    exact hPart.trans le_sup_left
  · let Δ : 𝔹 := Γ ⊓ y ⊆ᴮ x
    change Δ ≤ x =ᴮ y ⊔ x ∈ᴮ y ⊔ y ∈ᴮ x
    have hPart : Δ ≤ x =ᴮ y ⊔ y ∈ᴮ x := by
      apply le_sup_of_inf_compl_le
      let Θ : 𝔹 := Δ ⊓ (x =ᴮ y)ᶜ
      change Θ ≤ y ∈ᴮ x
      have hΘΓ : Θ ≤ Γ := by
        dsimp [Θ, Δ]
        exact (inf_le_left.trans inf_le_left)
      have hNeXY : Θ ≤ (x =ᴮ y)ᶜ := by
        dsimp [Θ]
        exact inf_le_right
      have hNeYX : Θ ≤ (y =ᴮ x)ᶜ := by
        simpa [bv_eq_symm] using hNeXY
      have hSub : Θ ≤ y ⊆ᴮ x := by
        dsimp [Θ, Δ]
        exact inf_le_left.trans inf_le_right
      exact Ord.lt_of_ne_and_le (hΘΓ.trans hOrdY) (hΘΓ.trans hOrdX) hNeYX hSub
    exact hPart.trans (sup_le (le_sup_left.trans le_sup_left) le_sup_right)

theorem Ord.eq_iff_not_mem {x y : bSet 𝔹} {Γ : 𝔹}
    (hOrdX : Γ ≤ Ord x) (hOrdY : Γ ≤ Ord y) :
    Γ ≤ x =ᴮ y ↔ Γ ≤ (x ∈ᴮ y)ᶜ ∧ Γ ≤ (y ∈ᴮ x)ᶜ := by
  constructor
  · intro hEq
    constructor
    · apply le_compl_of_inf_le_bot
      let Δ : 𝔹 := Γ ⊓ x ∈ᴮ y
      change Δ ≤ ⊥
      have hEqΔ : Δ ≤ x =ᴮ y := by
        dsimp [Δ]
        exact inf_le_left.trans hEq
      have hMem : Δ ≤ x ∈ᴮ y := by
        dsimp [Δ]
        exact inf_le_right
      have hSelf : Δ ≤ y ∈ᴮ y :=
        subst_congr_mem_left' hEqΔ hMem
      exact bot_of_mem_self hSelf
    · apply le_compl_of_inf_le_bot
      let Δ : 𝔹 := Γ ⊓ y ∈ᴮ x
      change Δ ≤ ⊥
      have hEqΔ : Δ ≤ y =ᴮ x := by
        dsimp [Δ]
        exact bv_symm (inf_le_left.trans hEq)
      have hMem : Δ ≤ y ∈ᴮ x := by
        dsimp [Δ]
        exact inf_le_right
      have hSelf : Δ ≤ x ∈ᴮ x :=
        subst_congr_mem_left' hEqΔ hMem
      exact bot_of_mem_self hSelf
  · intro hNot
    have hTri : Γ ≤ x =ᴮ y ⊔ x ∈ᴮ y ⊔ y ∈ᴮ x :=
      Ord.trichotomy hOrdX hOrdY
    apply (le_inf le_rfl hTri).trans
    apply lattice.bv_or_elim_right
    · apply lattice.bv_or_elim_right
      · exact inf_le_right
      · let Δ : 𝔹 := Γ ⊓ x ∈ᴮ y
        change Δ ≤ x =ᴮ y
        have hMem : Δ ≤ x ∈ᴮ y := by
          dsimp [Δ]
          exact inf_le_right
        have hNotMem : Δ ≤ (x ∈ᴮ y)ᶜ := by
          dsimp [Δ]
          exact inf_le_left.trans hNot.1
        exact lattice.bv_exfalso (bv_absurd hMem hNotMem)
    · let Δ : 𝔹 := Γ ⊓ y ∈ᴮ x
      change Δ ≤ x =ᴮ y
      have hMem : Δ ≤ y ∈ᴮ x := by
        dsimp [Δ]
        exact inf_le_right
      have hNotMem : Δ ≤ (y ∈ᴮ x)ᶜ := by
        dsimp [Δ]
        exact inf_le_left.trans hNot.2
      exact lattice.bv_exfalso (bv_absurd hMem hNotMem)

theorem Ord.eq_of_not_mem {x y : bSet 𝔹} {Γ : 𝔹}
    (hOrdX : Γ ≤ Ord x) (hOrdY : Γ ≤ Ord y)
    (hNotXY : Γ ≤ (x ∈ᴮ y)ᶜ) (hNotYX : Γ ≤ (y ∈ᴮ x)ᶜ) : Γ ≤ x =ᴮ y :=
  (Ord.eq_iff_not_mem hOrdX hOrdY).mpr ⟨hNotXY, hNotYX⟩

theorem Ord.le_iff_lt_or_eq {x y : bSet 𝔹} {Γ : 𝔹}
    (hOrdX : Γ ≤ Ord x) (hOrdY : Γ ≤ Ord y) :
    Γ ≤ x ⊆ᴮ y ↔ Γ ≤ x ∈ᴮ y ⊔ x =ᴮ y := by
  constructor
  · intro hSub
    have hPart : Γ ≤ x =ᴮ y ⊔ x ∈ᴮ y := by
      apply le_sup_of_inf_compl_le
      let Δ : 𝔹 := Γ ⊓ (x =ᴮ y)ᶜ
      change Δ ≤ x ∈ᴮ y
      have hΔΓ : Δ ≤ Γ := by
        dsimp [Δ]
        exact inf_le_left
      have hNe : Δ ≤ (x =ᴮ y)ᶜ := by
        dsimp [Δ]
        exact inf_le_right
      have hSubΔ : Δ ≤ x ⊆ᴮ y :=
        hΔΓ.trans hSub
      exact Ord.lt_of_ne_and_le (hΔΓ.trans hOrdX) (hΔΓ.trans hOrdY) hNe hSubΔ
    simpa [sup_comm] using hPart
  · intro hLtOrEq
    apply (le_inf le_rfl hLtOrEq).trans
    apply lattice.bv_or_elim_right
    · let Δ : 𝔹 := Γ ⊓ x ∈ᴮ y
      change Δ ≤ x ⊆ᴮ y
      have hMem : Δ ≤ x ∈ᴮ y := by
        dsimp [Δ]
        exact inf_le_right
      exact subset_of_mem_Ord hMem (inf_le_left.trans hOrdY)
    · let Δ : 𝔹 := Γ ⊓ x =ᴮ y
      change Δ ≤ x ⊆ᴮ y
      have hEq : Δ ≤ x =ᴮ y := by
        dsimp [Δ]
        exact inf_le_right
      exact subset_of_eq hEq

theorem Ord.lt_of_not_le {x y : bSet 𝔹} {Γ : 𝔹}
    (hOrdX : Γ ≤ Ord x) (hOrdY : Γ ≤ Ord y)
    (hNotLe : Γ ≤ (x ⊆ᴮ y)ᶜ) : Γ ≤ y ∈ᴮ x := by
  have hTri : Γ ≤ x =ᴮ y ⊔ x ∈ᴮ y ⊔ y ∈ᴮ x :=
    Ord.trichotomy hOrdX hOrdY
  apply (le_inf le_rfl hTri).trans
  apply lattice.bv_or_elim_right
  · apply lattice.bv_or_elim_right
    · let Δ : 𝔹 := Γ ⊓ x =ᴮ y
      change Δ ≤ y ∈ᴮ x
      have hEq : Δ ≤ x =ᴮ y := by
        dsimp [Δ]
        exact inf_le_right
      have hSub : Δ ≤ x ⊆ᴮ y :=
        subset_of_eq hEq
      have hNotSub : Δ ≤ (x ⊆ᴮ y)ᶜ := by
        dsimp [Δ]
        exact inf_le_left.trans hNotLe
      exact lattice.bv_exfalso (bv_absurd hSub hNotSub)
    · let Δ : 𝔹 := Γ ⊓ x ∈ᴮ y
      change Δ ≤ y ∈ᴮ x
      have hMem : Δ ≤ x ∈ᴮ y := by
        dsimp [Δ]
        exact inf_le_right
      have hSub : Δ ≤ x ⊆ᴮ y :=
        subset_of_mem_Ord hMem (inf_le_left.trans hOrdY)
      have hNotSub : Δ ≤ (x ⊆ᴮ y)ᶜ := by
        dsimp [Δ]
        exact inf_le_left.trans hNotLe
      exact lattice.bv_exfalso (bv_absurd hSub hNotSub)
  · exact inf_le_right

theorem Ord.resolve_lt {x y : bSet 𝔹} {Γ : 𝔹}
    (hOrdX : Γ ≤ Ord x) (hOrdY : Γ ≤ Ord y)
    (hNotMem : Γ ≤ (x ∈ᴮ y)ᶜ) : Γ ≤ y ∈ᴮ x ⊔ y =ᴮ x := by
  have hTri : Γ ≤ x =ᴮ y ⊔ x ∈ᴮ y ⊔ y ∈ᴮ x :=
    Ord.trichotomy hOrdX hOrdY
  apply (le_inf le_rfl hTri).trans
  apply lattice.bv_or_elim_right
  · apply lattice.bv_or_elim_right
    · let Δ : 𝔹 := Γ ⊓ x =ᴮ y
      change Δ ≤ y ∈ᴮ x ⊔ y =ᴮ x
      apply lattice.bv_or_right
      have hEq : Δ ≤ x =ᴮ y := by
        dsimp [Δ]
        exact inf_le_right
      exact bv_symm hEq
    · let Δ : 𝔹 := Γ ⊓ x ∈ᴮ y
      change Δ ≤ y ∈ᴮ x ⊔ y =ᴮ x
      have hMem : Δ ≤ x ∈ᴮ y := by
        dsimp [Δ]
        exact inf_le_right
      have hNotMemΔ : Δ ≤ (x ∈ᴮ y)ᶜ := by
        dsimp [Δ]
        exact inf_le_left.trans hNotMem
      exact lattice.bv_exfalso (bv_absurd hMem hNotMemΔ)
  · apply lattice.bv_or_left
    exact inf_le_right

theorem epsilon_trichotomy_of_sub_Ord {u : bSet 𝔹} {Γ : 𝔹}
    (hOrd : Γ ≤ ⨅ x : bSet 𝔹, lattice.imp (x ∈ᴮ u) (Ord x)) :
    Γ ≤ ⨅ y : bSet 𝔹, lattice.imp (y ∈ᴮ u)
      (⨅ z : bSet 𝔹, lattice.imp (z ∈ᴮ u)
        (y =ᴮ z ⊔ y ∈ᴮ z ⊔ z ∈ᴮ y)) := by
  apply le_iInf
  intro y
  apply lattice.bv_imp_intro
  apply le_iInf
  intro z
  apply lattice.bv_imp_intro
  let Δ : 𝔹 := (Γ ⊓ y ∈ᴮ u) ⊓ z ∈ᴮ u
  change Δ ≤ y =ᴮ z ⊔ y ∈ᴮ z ⊔ z ∈ᴮ y
  have hyOrd : Δ ≤ Ord y :=
    lattice.bv_context_apply
      (((inf_le_left.trans inf_le_left).trans hOrd).trans (iInf_le _ y))
      (inf_le_left.trans inf_le_right)
  have hzOrd : Δ ≤ Ord z :=
    lattice.bv_context_apply
      (((inf_le_left.trans inf_le_left).trans hOrd).trans (iInf_le _ z))
      inf_le_right
  exact Ord.trichotomy hyOrd hzOrd

theorem epsilon_wf_of_sub_Ord (u : bSet 𝔹) {Γ : 𝔹} :
    Γ ≤ ⨅ x : bSet 𝔹, lattice.imp (x ⊆ᴮ u)
      (lattice.imp ((x =ᴮ (∅ : bSet 𝔹))ᶜ)
        (⨆ y : bSet 𝔹, y ∈ᴮ x ⊓
          (⨅ z' : bSet 𝔹, lattice.imp (z' ∈ᴮ x) ((z' ∈ᴮ y)ᶜ)))) := by
  simpa [epsilon_well_founded] using (is_epsilon_well_founded (x := u) (Γ := Γ))

/-- Boolean-valued predicate saying that an ordinal name is a nonzero limit ordinal. -/
def is_limit (η : bSet 𝔹) : 𝔹 :=
  ((∅ : bSet 𝔹) ∈ᴮ η) ⊓
    (⨅ x : bSet 𝔹, lattice.imp (x ∈ᴮ η)
      (⨆ y : bSet 𝔹, y ∈ᴮ η ⊓ x ∈ᴮ y))

theorem Ord_succ {η : bSet 𝔹} {Γ : 𝔹} (hOrd : Γ ≤ Ord η) :
    Γ ≤ Ord (succ η) := by
  unfold Ord epsilon_well_orders
  apply le_inf
  · apply le_inf
    · unfold epsilon_trichotomy
      apply le_iInf
      intro y
      apply lattice.bv_imp_intro
      apply le_iInf
      intro z
      apply lattice.bv_imp_intro
      let Δ : 𝔹 := (Γ ⊓ y ∈ᴮ succ η) ⊓ z ∈ᴮ succ η
      change Δ ≤ y =ᴮ z ⊔ y ∈ᴮ z ⊔ z ∈ᴮ y
      have hySucc : Δ ≤ y ∈ᴮ succ η := by
        dsimp [Δ]
        exact inf_le_left.trans inf_le_right
      have hzSucc : Δ ≤ z ∈ᴮ succ η := by
        dsimp [Δ]
        exact inf_le_right
      rw [succ, mem_insert1] at hySucc hzSucc
      apply (le_inf le_rfl hySucc).trans
      apply lattice.bv_or_elim_right
      · let Θ : 𝔹 := Δ ⊓ y =ᴮ η
        change Θ ≤ y =ᴮ z ⊔ y ∈ᴮ z ⊔ z ∈ᴮ y
        have hyEq : Θ ≤ y =ᴮ η := by
          dsimp [Θ]
          exact inf_le_right
        have hzSuccΘ : Θ ≤ z =ᴮ η ⊔ z ∈ᴮ η :=
          inf_le_left.trans hzSucc
        apply (le_inf le_rfl hzSuccΘ).trans
        apply lattice.bv_or_elim_right
        · let Ω : 𝔹 := Θ ⊓ z =ᴮ η
          change Ω ≤ y =ᴮ z ⊔ y ∈ᴮ z ⊔ z ∈ᴮ y
          have hyEqΩ : Ω ≤ y =ᴮ η :=
            inf_le_left.trans hyEq
          have hzEq : Ω ≤ z =ᴮ η := by
            dsimp [Ω]
            exact inf_le_right
          have hyz : Ω ≤ y =ᴮ z :=
            bv_trans hyEqΩ (bv_symm hzEq)
          exact lattice.bv_or_left (lattice.bv_or_left hyz)
        · let Ω : 𝔹 := Θ ⊓ z ∈ᴮ η
          change Ω ≤ y =ᴮ z ⊔ y ∈ᴮ z ⊔ z ∈ᴮ y
          have hyEqΩ : Ω ≤ y =ᴮ η :=
            inf_le_left.trans hyEq
          have hzη : Ω ≤ z ∈ᴮ η := by
            dsimp [Ω]
            exact inf_le_right
          have hzy : Ω ≤ z ∈ᴮ y :=
            subst_congr_mem_right' (bv_symm hyEqΩ) hzη
          exact lattice.bv_or_right hzy
      · let Θ : 𝔹 := Δ ⊓ y ∈ᴮ η
        change Θ ≤ y =ᴮ z ⊔ y ∈ᴮ z ⊔ z ∈ᴮ y
        have hyη : Θ ≤ y ∈ᴮ η := by
          dsimp [Θ]
          exact inf_le_right
        have hzSuccΘ : Θ ≤ z =ᴮ η ⊔ z ∈ᴮ η :=
          inf_le_left.trans hzSucc
        apply (le_inf le_rfl hzSuccΘ).trans
        apply lattice.bv_or_elim_right
        · let Ω : 𝔹 := Θ ⊓ z =ᴮ η
          change Ω ≤ y =ᴮ z ⊔ y ∈ᴮ z ⊔ z ∈ᴮ y
          have hzEq : Ω ≤ z =ᴮ η := by
            dsimp [Ω]
            exact inf_le_right
          have hyηΩ : Ω ≤ y ∈ᴮ η :=
            inf_le_left.trans hyη
          have hyz : Ω ≤ y ∈ᴮ z :=
            subst_congr_mem_right' (bv_symm hzEq) hyηΩ
          exact lattice.bv_or_left (lattice.bv_or_right hyz)
        · let Ω : 𝔹 := Θ ⊓ z ∈ᴮ η
          change Ω ≤ y =ᴮ z ⊔ y ∈ᴮ z ⊔ z ∈ᴮ y
          have hyηΩ : Ω ≤ y ∈ᴮ η :=
            inf_le_left.trans hyη
          have hzη : Ω ≤ z ∈ᴮ η := by
            dsimp [Ω]
            exact inf_le_right
          exact epsilon_trichotomy_of_Ord hyηΩ hzη
            ((((inf_le_left.trans inf_le_left).trans inf_le_left).trans inf_le_left).trans hOrd)
    · exact is_epsilon_well_founded
  · unfold is_transitive
    apply le_iInf
    intro z
    apply lattice.bv_imp_intro
    let Δ : 𝔹 := Γ ⊓ z ∈ᴮ succ η
    change Δ ≤ z ⊆ᴮ succ η
    have hzSucc : Δ ≤ z ∈ᴮ succ η := by
      dsimp [Δ]
      exact inf_le_right
    rw [succ, mem_insert1] at hzSucc
    apply (le_inf le_rfl hzSucc).trans
    apply lattice.bv_or_elim_right
    · let Θ : 𝔹 := Δ ⊓ z =ᴮ η
      change Θ ≤ z ⊆ᴮ succ η
      have hzEq : Θ ≤ z =ᴮ η := by
        dsimp [Θ]
        exact inf_le_right
      exact subst_congr_subset_left' (bv_symm hzEq) subset_succ
    · let Θ : 𝔹 := Δ ⊓ z ∈ᴮ η
      change Θ ≤ z ⊆ᴮ succ η
      apply subset_intro
      intro i
      let w : bSet 𝔹 := z.func i
      let Ω : 𝔹 := Θ ⊓ z.bval i
      change Ω ≤ w ∈ᴮ succ η
      have hwz : Ω ≤ w ∈ᴮ z := by
        apply mem.mk''
        dsimp [Ω, w]
        exact inf_le_right
      have hzη : Ω ≤ z ∈ᴮ η := by
        dsimp [Ω, Θ]
        exact inf_le_left.trans inf_le_right
      have hwη : Ω ≤ w ∈ᴮ η :=
        mem_of_mem_Ord hwz hzη
          (((inf_le_left.trans inf_le_left).trans inf_le_left).trans hOrd)
      change Ω ≤ w ∈ᴮ bSet.insert1 η η
      exact mem_insert_of_mem hwη

theorem Ord.succ_le_of_lt {η ρ : bSet 𝔹} {Γ : 𝔹}
    (hOrdρ : Γ ≤ Ord ρ) (hLt : Γ ≤ η ∈ᴮ ρ) : Γ ≤ succ η ⊆ᴮ ρ := by
  apply subset_intro
  intro i
  let w : bSet 𝔹 := (succ η).func i
  let Δ : 𝔹 := Γ ⊓ (succ η).bval i
  change Δ ≤ w ∈ᴮ ρ
  have hwSucc : Δ ≤ w ∈ᴮ succ η := by
    apply mem.mk''
    dsimp [Δ]
    exact inf_le_right
  rw [succ, mem_insert1] at hwSucc
  apply (le_inf le_rfl hwSucc).trans
  apply lattice.bv_or_elim_right
  · let Θ : 𝔹 := Δ ⊓ w =ᴮ η
    change Θ ≤ w ∈ᴮ ρ
    have hwEq : Θ ≤ w =ᴮ η := by
      dsimp [Θ]
      exact inf_le_right
    have hηρ : Θ ≤ η ∈ᴮ ρ :=
      (inf_le_left.trans inf_le_left).trans hLt
    exact subst_congr_mem_left' (bv_symm hwEq) hηρ
  · let Θ : 𝔹 := Δ ⊓ w ∈ᴮ η
    change Θ ≤ w ∈ᴮ ρ
    have hwη : Θ ≤ w ∈ᴮ η := by
      dsimp [Θ]
      exact inf_le_right
    have hηρ : Θ ≤ η ∈ᴮ ρ :=
      (inf_le_left.trans inf_le_left).trans hLt
    exact mem_of_mem_Ord hwη hηρ ((inf_le_left.trans inf_le_left).trans hOrdρ)

theorem Ord_empty {Γ : 𝔹} : Γ ≤ Ord (∅ : bSet 𝔹) := by
  unfold Ord epsilon_well_orders
  apply le_inf
  · apply le_inf
    · unfold epsilon_trichotomy
      apply le_iInf
      intro y
      apply lattice.bv_imp_intro
      apply le_iInf
      intro z
      apply lattice.bv_imp_intro
      let Δ : 𝔹 := (Γ ⊓ y ∈ᴮ (∅ : bSet 𝔹)) ⊓ z ∈ᴮ (∅ : bSet 𝔹)
      change Δ ≤ y =ᴮ z ⊔ y ∈ᴮ z ⊔ z ∈ᴮ y
      have hyEmpty : Δ ≤ y ∈ᴮ (∅ : bSet 𝔹) := by
        dsimp [Δ]
        exact inf_le_left.trans inf_le_right
      exact lattice.bv_exfalso (by simpa [mem_empty] using hyEmpty)
    · exact is_epsilon_well_founded
  · unfold is_transitive
    apply le_iInf
    intro y
    apply lattice.bv_imp_intro
    let Δ : 𝔹 := Γ ⊓ y ∈ᴮ (∅ : bSet 𝔹)
    change Δ ≤ y ⊆ᴮ (∅ : bSet 𝔹)
    have hyEmpty : Δ ≤ y ∈ᴮ (∅ : bSet 𝔹) := by
      dsimp [Δ]
      exact inf_le_right
    exact lattice.bv_exfalso (by simpa [mem_empty] using hyEmpty)

theorem ofNat_succ_eq_succ (n : Nat) {Γ : 𝔹} :
    Γ ≤ ofNat (n + 1) =ᴮ succ (ofNat n : bSet 𝔹) := by
  rw [ofNat, pSet.of_nat_succ]
  exact check_succ_eq_succ_check

theorem ofNat_inj {n k : Nat} (hneq : n ≠ k) :
    ((ofNat n : bSet 𝔹) =ᴮ ofNat k) = ⊥ := by
  change ((check (PSet.ofNat.{u} n) : bSet 𝔹) =ᴮ check (PSet.ofNat.{u} k)) = ⊥
  exact check_bv_eq_bot_of_not_equiv (pSet.of_nat_inj hneq)

theorem ofNat_mem_of_lt {k₁ k₂ : Nat} (hLt : k₁ < k₂) {Γ : 𝔹} :
    Γ ≤ (ofNat k₁ : bSet 𝔹) ∈ᴮ (ofNat k₂ : bSet 𝔹) := by
  change Γ ≤ (check (PSet.ofNat.{u} k₁) : bSet 𝔹) ∈ᴮ check (PSet.ofNat.{u} k₂)
  exact check_mem (pSet.of_nat_mem_of_lt hLt)

theorem Ord_zero {Γ : 𝔹} : Γ ≤ Ord (0 : bSet 𝔹) := by
  change Γ ≤ Ord (ofNat 0 : bSet 𝔹)
  exact (le_inf (bv_symm ofNat_zero_eq_empty) Ord_empty).trans (B_ext_Ord _ _)

theorem Ord_ofNat (n : Nat) {Γ : 𝔹} : Γ ≤ Ord (ofNat n : bSet 𝔹) := by
  induction n with
  | zero =>
      exact Ord_zero
  | succ n ih =>
      have hEq : Γ ≤ ofNat (n + 1) =ᴮ succ (ofNat n : bSet 𝔹) :=
        ofNat_succ_eq_succ n
      have hOrdSucc : Γ ≤ Ord (succ (ofNat n : bSet 𝔹)) :=
        Ord_succ ih
      exact (le_inf (bv_symm hEq) hOrdSucc).trans (B_ext_Ord _ _)

theorem Ord_one {Γ : 𝔹} : Γ ≤ Ord (1 : bSet 𝔹) := by
  change Γ ≤ Ord (ofNat 1 : bSet 𝔹)
  exact Ord_ofNat 1

theorem zero_mem_one {Γ : 𝔹} : Γ ≤ (0 : bSet 𝔹) ∈ᴮ (1 : bSet 𝔹) := by
  change Γ ≤ (ofNat 0 : bSet 𝔹) ∈ᴮ (ofNat 1 : bSet 𝔹)
  simpa [ofNat] using
    (check_mem (pSet.of_nat_mem_of_lt (k₁ := 0) (k₂ := 1) (by decide)) :
      Γ ≤ (check (PSet.ofNat.{u} 0) : bSet 𝔹) ∈ᴮ
        (check (PSet.ofNat.{u} 1) : bSet 𝔹))

theorem eq_zero_of_mem_one {x : bSet 𝔹} {Γ : 𝔹}
    (hMem : Γ ≤ x ∈ᴮ (1 : bSet 𝔹)) : Γ ≤ x =ᴮ (0 : bSet 𝔹) := by
  change Γ ≤ x =ᴮ (ofNat 0 : bSet 𝔹)
  have hSucc : Γ ≤ x ∈ᴮ succ (ofNat 0 : bSet 𝔹) := by
    exact subst_congr_mem_right' (ofNat_succ_eq_succ 0) (by simpa using hMem)
  rw [succ, mem_insert1] at hSucc
  apply (le_inf le_rfl hSucc).trans
  apply lattice.bv_or_elim_right
  · exact inf_le_right
  · let Δ : 𝔹 := Γ ⊓ x ∈ᴮ (ofNat 0 : bSet 𝔹)
    change Δ ≤ x =ᴮ (ofNat 0 : bSet 𝔹)
    have hMemZero : Δ ≤ x ∈ᴮ (ofNat 0 : bSet 𝔹) := by
      dsimp [Δ]
      exact inf_le_right
    have hEqEmpty : Δ ≤ (ofNat 0 : bSet 𝔹) =ᴮ (∅ : bSet 𝔹) :=
      inf_le_left.trans ofNat_zero_eq_empty
    have hMemEmpty : Δ ≤ x ∈ᴮ (∅ : bSet 𝔹) :=
      subst_congr_mem_right' hEqEmpty hMemZero
    exact lattice.bv_exfalso (by simpa [mem_empty] using hMemEmpty)

namespace powerset_injects

theorem mem_F_zero_of_mem_indicator {x : bSet 𝔹} {χ : (bv_powerset x).type}
    {z : bSet 𝔹} {Γ : 𝔹} (hMem : Γ ≤ z ∈ᴮ set_of_indicator χ) :
    Γ ≤ pair z (0 : bSet 𝔹) ∈ᴮ (functions x (2 : bSet 𝔹)).func (F χ) := by
  change Γ ≤ pair z (0 : bSet 𝔹) ∈ᴮ set_of_indicator (F χ)
  rw [mem_set_of_indicator_iff] at hMem ⊢
  apply (le_inf le_rfl hMem).trans
  apply lattice.bv_cases_right
  intro i
  let Δ : 𝔹 := Γ ⊓ ((χ i ⊓ x.bval i) ⊓ z =ᴮ x.func i)
  change Δ ≤ ⨆ pr : (prod x (2 : bSet 𝔹)).type,
    (F χ pr ⊓ (prod x (2 : bSet 𝔹)).bval pr) ⊓
      pair z (0 : bSet 𝔹) =ᴮ (prod x (2 : bSet 𝔹)).func pr
  have hZeroTwo : Δ ≤ (0 : bSet 𝔹) ∈ᴮ (2 : bSet 𝔹) :=
    ofNat_mem_of_lt (k₁ := 0) (k₂ := 2) (by decide)
  rw [mem_unfold] at hZeroTwo
  apply (le_inf le_rfl hZeroTwo).trans
  apply lattice.bv_cases_right
  intro j
  let Θ : 𝔹 := Δ ⊓ ((2 : bSet 𝔹).bval j ⊓ (0 : bSet 𝔹) =ᴮ (2 : bSet 𝔹).func j)
  change Θ ≤ ⨆ pr : (prod x (2 : bSet 𝔹)).type,
    (F χ pr ⊓ (prod x (2 : bSet 𝔹)).bval pr) ⊓
      pair z (0 : bSet 𝔹) =ᴮ (prod x (2 : bSet 𝔹)).func pr
  apply lattice.bv_use (i, j)
  apply le_inf
  · apply le_inf
    · dsimp [F]
      apply le_trans ?_ le_sup_left
      apply le_inf
      · rw [mem_set_of_indicator_iff]
        apply lattice.bv_use i
        apply le_inf
        · apply le_inf
          · dsimp [Θ, Δ]
            exact inf_le_left.trans inf_le_right |>.trans inf_le_left |>.trans inf_le_left
          · dsimp [Θ, Δ]
            exact inf_le_left.trans inf_le_right |>.trans inf_le_left |>.trans inf_le_right
        · exact bv_refl
      · exact bv_symm (by
          dsimp [Θ]
          exact inf_le_right.trans inf_le_right)
    · apply le_inf
      · dsimp [Θ, Δ]
        exact inf_le_left.trans inf_le_right |>.trans inf_le_left |>.trans inf_le_right
      · dsimp [Θ]
        exact inf_le_right.trans inf_le_left
  · apply pair_congr
    · dsimp [Θ, Δ]
      exact inf_le_left.trans inf_le_right |>.trans inf_le_right
    · dsimp [Θ]
      exact inf_le_right.trans inf_le_right

theorem mem_F_one_of_not_mem_indicator {x : bSet 𝔹} {χ : (bv_powerset x).type}
    {z : bSet 𝔹} {Γ : 𝔹} (hzX : Γ ≤ z ∈ᴮ x)
    (hzNot : Γ ≤ (z ∈ᴮ set_of_indicator χ)ᶜ) :
    Γ ≤ pair z (1 : bSet 𝔹) ∈ᴮ (functions x (2 : bSet 𝔹)).func (F χ) := by
  change Γ ≤ pair z (1 : bSet 𝔹) ∈ᴮ set_of_indicator (F χ)
  rw [mem_unfold] at hzX
  apply (le_inf le_rfl hzX).trans
  apply lattice.bv_cases_right
  intro i
  let Δ : 𝔹 := Γ ⊓ (x.bval i ⊓ z =ᴮ x.func i)
  change Δ ≤ pair z (1 : bSet 𝔹) ∈ᴮ set_of_indicator (F χ)
  have hzEq : Δ ≤ z =ᴮ x.func i := by
    dsimp [Δ]
    exact inf_le_right.trans inf_le_right
  have hNotXi : Δ ≤ (x.func i ∈ᴮ set_of_indicator χ)ᶜ := by
    have hNotZ : Δ ≤ (z ∈ᴮ set_of_indicator χ)ᶜ := by
      dsimp [Δ]
      exact inf_le_left.trans hzNot
    exact (le_inf hzEq hNotZ).trans
      ((B_ext_compl (B_ext_mem_left (set_of_indicator χ))) z (x.func i))
  rw [mem_set_of_indicator_iff]
  have hOneTwo : Δ ≤ (1 : bSet 𝔹) ∈ᴮ (2 : bSet 𝔹) :=
    ofNat_mem_of_lt (k₁ := 1) (k₂ := 2) (by decide)
  rw [mem_unfold] at hOneTwo
  apply (le_inf le_rfl hOneTwo).trans
  apply lattice.bv_cases_right
  intro j
  let Θ : 𝔹 := Δ ⊓ ((2 : bSet 𝔹).bval j ⊓ (1 : bSet 𝔹) =ᴮ (2 : bSet 𝔹).func j)
  change Θ ≤ ⨆ pr : (prod x (2 : bSet 𝔹)).type,
    (F χ pr ⊓ (prod x (2 : bSet 𝔹)).bval pr) ⊓
      pair z (1 : bSet 𝔹) =ᴮ (prod x (2 : bSet 𝔹)).func pr
  apply lattice.bv_use (i, j)
  apply le_inf
  · apply le_inf
    · dsimp [F]
      apply le_trans ?_ le_sup_right
      apply le_inf
      · rw [mem_subset.mk_iff₂]
        apply lattice.bv_use i
        apply le_inf
        · dsimp [Θ, Δ]
          exact inf_le_left.trans inf_le_right |>.trans inf_le_left
        · apply le_inf
          · exact bv_refl
          · exact inf_le_left.trans hNotXi
      · exact bv_symm (by
          dsimp [Θ]
          exact inf_le_right.trans inf_le_right)
    · apply le_inf
      · dsimp [Θ, Δ]
        exact inf_le_left.trans inf_le_right |>.trans inf_le_left
      · dsimp [Θ]
        exact inf_le_right.trans inf_le_left
  · apply pair_congr
    · exact inf_le_left.trans hzEq
    · dsimp [Θ]
      exact inf_le_right.trans inf_le_right

theorem mem_F_zero_iff {x : bSet 𝔹} {χ : (bv_powerset x).type}
    {z : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ pair z (0 : bSet 𝔹) ∈ᴮ (functions x (2 : bSet 𝔹)).func (F χ) ↔
      Γ ≤ z ∈ᴮ set_of_indicator χ := by
  constructor
  · intro hMem
    change Γ ≤ pair z (0 : bSet 𝔹) ∈ᴮ set_of_indicator (F χ) at hMem
    rw [mem_set_of_indicator_iff] at hMem ⊢
    apply (le_inf le_rfl hMem).trans
    apply lattice.bv_cases_right
    intro pr
    cases pr with
    | mk i j =>
        let Δ : 𝔹 := Γ ⊓
          ((F χ (i, j) ⊓ (prod x (2 : bSet 𝔹)).bval (i, j)) ⊓
            pair z (0 : bSet 𝔹) =ᴮ (prod x (2 : bSet 𝔹)).func (i, j))
        change Δ ≤ ⨆ k : x.type, (χ k ⊓ x.bval k) ⊓ z =ᴮ x.func k
        have hF : Δ ≤ F χ (i, j) := by
          dsimp [Δ]
          exact inf_le_right.trans inf_le_left |>.trans inf_le_left
        have hPair : Δ ≤ pair z (0 : bSet 𝔹) =ᴮ
            pair (x.func i) ((2 : bSet 𝔹).func j) := by
          dsimp [Δ, prod]
          exact inf_le_right.trans inf_le_right
        have hzEq : Δ ≤ z =ᴮ x.func i :=
          eq_of_eq_pair_left' hPair
        have hZeroEq : Δ ≤ (0 : bSet 𝔹) =ᴮ (2 : bSet 𝔹).func j :=
          eq_of_eq_pair_right' hPair
        dsimp [F] at hF
        apply (le_inf le_rfl hF).trans
        apply lattice.bv_or_elim_right
        · let Θ : 𝔹 := Δ ⊓
            (x.func i ∈ᴮ set_of_indicator χ ⊓
              (2 : bSet 𝔹).func j =ᴮ (0 : bSet 𝔹))
          change Θ ≤ ⨆ k : x.type, (χ k ⊓ x.bval k) ⊓ z =ᴮ x.func k
          have hxMem : Θ ≤ x.func i ∈ᴮ set_of_indicator χ := by
            dsimp [Θ]
            exact inf_le_right.trans inf_le_left
          have hzMem : Θ ≤ z ∈ᴮ set_of_indicator χ :=
            subst_congr_mem_left' (bv_symm (inf_le_left.trans hzEq)) hxMem
          rw [mem_set_of_indicator_iff] at hzMem
          exact hzMem
        · let Θ : 𝔹 := Δ ⊓
            (x.func i ∈ᴮ subset.mk (x := x)
                (fun k : x.type => (x.func k ∈ᴮ set_of_indicator χ)ᶜ) ⊓
              (2 : bSet 𝔹).func j =ᴮ (1 : bSet 𝔹))
          change Θ ≤ ⨆ k : x.type, (χ k ⊓ x.bval k) ⊓ z =ᴮ x.func k
          have hOneEq : Θ ≤ (2 : bSet 𝔹).func j =ᴮ (1 : bSet 𝔹) := by
            dsimp [Θ]
            exact inf_le_right.trans inf_le_right
          have hZeroEq' : Θ ≤ (0 : bSet 𝔹) =ᴮ (2 : bSet 𝔹).func j :=
            inf_le_left.trans hZeroEq
          have hZeroOne : Θ ≤ (0 : bSet 𝔹) =ᴮ (1 : bSet 𝔹) :=
            bv_trans hZeroEq' hOneEq
          have hBot : Θ ≤ ⊥ := by
            have hEqBot : ((0 : bSet 𝔹) =ᴮ (1 : bSet 𝔹)) = ⊥ := by
              simpa using (ofNat_inj (𝔹 := 𝔹) (n := 0) (k := 1) (by decide))
            exact hZeroOne.trans (le_of_eq hEqBot)
          exact lattice.bv_exfalso hBot
  · intro hMem
    exact mem_F_zero_of_mem_indicator hMem

theorem F_inj {x : bSet 𝔹} {χ₁ χ₂ : (bv_powerset x).type} {Γ : 𝔹}
    (hEq : Γ ≤ (functions x (2 : bSet 𝔹)).func (F χ₁) =ᴮ
      (functions x (2 : bSet 𝔹)).func (F χ₂)) :
    Γ ≤ (bv_powerset x).func χ₁ =ᴮ (bv_powerset x).func χ₂ := by
  change Γ ≤ set_of_indicator χ₁ =ᴮ set_of_indicator χ₂
  apply mem_ext
  · apply le_iInf
    intro z
    apply lattice.bv_imp_intro
    let Δ : 𝔹 := Γ ⊓ z ∈ᴮ set_of_indicator χ₁
    change Δ ≤ z ∈ᴮ set_of_indicator χ₂
    have hPair₁ : Δ ≤ pair z (0 : bSet 𝔹) ∈ᴮ
        (functions x (2 : bSet 𝔹)).func (F χ₁) :=
      mem_F_zero_of_mem_indicator inf_le_right
    have hPair₂ : Δ ≤ pair z (0 : bSet 𝔹) ∈ᴮ
        (functions x (2 : bSet 𝔹)).func (F χ₂) :=
      subst_congr_mem_right' (inf_le_left.trans hEq) hPair₁
    exact mem_F_zero_iff.mp hPair₂
  · apply le_iInf
    intro z
    apply lattice.bv_imp_intro
    let Δ : 𝔹 := Γ ⊓ z ∈ᴮ set_of_indicator χ₂
    change Δ ≤ z ∈ᴮ set_of_indicator χ₁
    have hPair₂ : Δ ≤ pair z (0 : bSet 𝔹) ∈ᴮ
        (functions x (2 : bSet 𝔹)).func (F χ₂) :=
      mem_F_zero_of_mem_indicator inf_le_right
    have hPair₁ : Δ ≤ pair z (0 : bSet 𝔹) ∈ᴮ
        (functions x (2 : bSet 𝔹)).func (F χ₁) :=
      subst_congr_mem_right' (bv_symm (inf_le_left.trans hEq)) hPair₂
    exact mem_F_zero_iff.mp hPair₁

theorem mem_indicator_compl_of_subset {x : bSet 𝔹} {χ₁ χ₂ : (bv_powerset x).type}
    {z : bSet 𝔹} {Γ : 𝔹}
    (hSub : Γ ≤ set_of_indicator χ₂ ⊆ᴮ set_of_indicator χ₁)
    (hMem : Γ ≤ z ∈ᴮ subset.mk (x := x)
      (fun i : x.type => (x.func i ∈ᴮ set_of_indicator χ₁)ᶜ)) :
    Γ ≤ z ∈ᴮ subset.mk (x := x)
      (fun i : x.type => (x.func i ∈ᴮ set_of_indicator χ₂)ᶜ) := by
  rw [mem_subset.mk_iff₂] at hMem ⊢
  apply (le_inf le_rfl hMem).trans
  apply lattice.bv_cases_right
  intro i
  let Δ : 𝔹 := Γ ⊓
    (x.bval i ⊓ (z =ᴮ x.func i ⊓ (x.func i ∈ᴮ set_of_indicator χ₁)ᶜ))
  change Δ ≤ ⨆ j : x.type,
    x.bval j ⊓ (z =ᴮ x.func j ⊓ (x.func j ∈ᴮ set_of_indicator χ₂)ᶜ)
  apply lattice.bv_use i
  apply le_inf
  · dsimp [Δ]
    exact inf_le_right.trans inf_le_left
  · apply le_inf
    · dsimp [Δ]
      exact inf_le_right.trans inf_le_right |>.trans inf_le_left
    · rw [le_compl_iff_disjoint_right, disjoint_iff]
      let Θ : 𝔹 := Δ ⊓ x.func i ∈ᴮ set_of_indicator χ₂
      apply le_antisymm
      · change Θ ≤ ⊥
        have hΘΓ : Θ ≤ Γ := by
          dsimp [Θ, Δ]
          exact inf_le_left.trans inf_le_left
        have hMem₂ : Θ ≤ x.func i ∈ᴮ set_of_indicator χ₂ := by
          dsimp [Θ]
          exact inf_le_right
        have hMem₁ : Θ ≤ x.func i ∈ᴮ set_of_indicator χ₁ :=
          mem_of_mem_subset' (hΘΓ.trans hSub) hMem₂
        have hNot₁ : Θ ≤ (x.func i ∈ᴮ set_of_indicator χ₁)ᶜ := by
          dsimp [Θ, Δ]
          exact inf_le_left.trans inf_le_right |>.trans inf_le_right |>.trans inf_le_right
        exact bv_absurd hMem₁ hNot₁
      · exact bot_le

theorem not_mem_indicator_of_mem_indicator_compl {x : bSet 𝔹}
    {χ : (bv_powerset x).type} {z : bSet 𝔹} {Γ : 𝔹}
    (hMem : Γ ≤ z ∈ᴮ subset.mk (x := x)
      (fun i : x.type => (x.func i ∈ᴮ set_of_indicator χ)ᶜ)) :
    Γ ≤ (z ∈ᴮ set_of_indicator χ)ᶜ := by
  rw [mem_subset.mk_iff₂] at hMem
  apply (le_inf le_rfl hMem).trans
  apply lattice.bv_cases_right
  intro i
  let Δ : 𝔹 := Γ ⊓
    (x.bval i ⊓ (z =ᴮ x.func i ⊓ (x.func i ∈ᴮ set_of_indicator χ)ᶜ))
  change Δ ≤ (z ∈ᴮ set_of_indicator χ)ᶜ
  rw [le_compl_iff_disjoint_right, disjoint_iff]
  let Θ : 𝔹 := Δ ⊓ z ∈ᴮ set_of_indicator χ
  apply le_antisymm
  · change Θ ≤ ⊥
    have hzEq : Θ ≤ z =ᴮ x.func i := by
      dsimp [Θ, Δ]
      exact inf_le_left.trans inf_le_right |>.trans inf_le_right |>.trans inf_le_left
    have hzMem : Θ ≤ z ∈ᴮ set_of_indicator χ := by
      dsimp [Θ]
      exact inf_le_right
    have hxiMem : Θ ≤ x.func i ∈ᴮ set_of_indicator χ :=
      subst_congr_mem_left' hzEq hzMem
    have hxiNot : Θ ≤ (x.func i ∈ᴮ set_of_indicator χ)ᶜ := by
      dsimp [Θ, Δ]
      exact inf_le_left.trans inf_le_right |>.trans inf_le_right |>.trans inf_le_right
    exact bv_absurd hxiMem hxiNot
  · exact bot_le

theorem F_subset {x : bSet 𝔹} {χ₁ χ₂ : (bv_powerset x).type} {Γ : 𝔹}
    (h₁₂ : Γ ≤ set_of_indicator χ₁ ⊆ᴮ set_of_indicator χ₂)
    (h₂₁ : Γ ≤ set_of_indicator χ₂ ⊆ᴮ set_of_indicator χ₁) :
    Γ ≤ (functions x (2 : bSet 𝔹)).func (F χ₁) ⊆ᴮ
      (functions x (2 : bSet 𝔹)).func (F χ₂) := by
  change Γ ≤ set_of_indicator (x := prod x (2 : bSet 𝔹)) (F χ₁) ⊆ᴮ
    set_of_indicator (x := prod x (2 : bSet 𝔹)) (F χ₂)
  apply subset_intro
  intro pr
  cases pr with
  | mk i j =>
      let Δ : 𝔹 := Γ ⊓
        (set_of_indicator (x := prod x (2 : bSet 𝔹)) (F χ₁)).bval (i, j)
      change Δ ≤ pair (x.func i) ((2 : bSet 𝔹).func j) ∈ᴮ
        set_of_indicator (x := prod x (2 : bSet 𝔹)) (F χ₂)
      have hF₁ : Δ ≤ F χ₁ (i, j) := by
        dsimp [Δ, set_of_indicator, subset.mk]
        exact inf_le_right.trans inf_le_left
      have hProd : Δ ≤ (prod x (2 : bSet 𝔹)).bval (i, j) := by
        dsimp [Δ, set_of_indicator, subset.mk]
        exact inf_le_right.trans inf_le_right
      rw [mem_set_of_indicator_iff]
      apply lattice.bv_use (i, j)
      apply le_inf
      · apply le_inf
        · dsimp [F] at hF₁ ⊢
          apply (le_inf le_rfl hF₁).trans
          apply lattice.bv_or_elim_right
          · let Θ : 𝔹 := Δ ⊓
              (x.func i ∈ᴮ set_of_indicator χ₁ ⊓
                (2 : bSet 𝔹).func j =ᴮ (0 : bSet 𝔹))
            change Θ ≤
              x.func i ∈ᴮ set_of_indicator χ₂ ⊓
                  (2 : bSet 𝔹).func j =ᴮ (0 : bSet 𝔹) ⊔
                (x.func i ∈ᴮ subset.mk (x := x)
                    (fun k : x.type => (x.func k ∈ᴮ set_of_indicator χ₂)ᶜ) ⊓
                  (2 : bSet 𝔹).func j =ᴮ (1 : bSet 𝔹))
            apply le_trans ?_ le_sup_left
            apply le_inf
            · have hΘΓ : Θ ≤ Γ := by
                dsimp [Θ, Δ]
                exact inf_le_left.trans inf_le_left
              have hMem₁ : Θ ≤ x.func i ∈ᴮ set_of_indicator χ₁ := by
                dsimp [Θ]
                exact inf_le_right.trans inf_le_left
              exact mem_of_mem_subset' (hΘΓ.trans h₁₂) hMem₁
            · dsimp [Θ]
              exact inf_le_right.trans inf_le_right
          · let Θ : 𝔹 := Δ ⊓
              (x.func i ∈ᴮ subset.mk (x := x)
                  (fun k : x.type => (x.func k ∈ᴮ set_of_indicator χ₁)ᶜ) ⊓
                (2 : bSet 𝔹).func j =ᴮ (1 : bSet 𝔹))
            change Θ ≤
              x.func i ∈ᴮ set_of_indicator χ₂ ⊓
                  (2 : bSet 𝔹).func j =ᴮ (0 : bSet 𝔹) ⊔
                (x.func i ∈ᴮ subset.mk (x := x)
                    (fun k : x.type => (x.func k ∈ᴮ set_of_indicator χ₂)ᶜ) ⊓
                  (2 : bSet 𝔹).func j =ᴮ (1 : bSet 𝔹))
            apply le_trans ?_ le_sup_right
            apply le_inf
            · have hΘΓ : Θ ≤ Γ := by
                dsimp [Θ, Δ]
                exact inf_le_left.trans inf_le_left
              have hComp₁ : Θ ≤ x.func i ∈ᴮ subset.mk (x := x)
                  (fun k : x.type => (x.func k ∈ᴮ set_of_indicator χ₁)ᶜ) := by
                dsimp [Θ]
                exact inf_le_right.trans inf_le_left
              exact mem_indicator_compl_of_subset (hΘΓ.trans h₂₁) hComp₁
            · dsimp [Θ]
              exact inf_le_right.trans inf_le_right
        · exact hProd
      · exact bv_refl

theorem F_ext {x : bSet 𝔹} {χ₁ χ₂ : (bv_powerset x).type} {Γ : 𝔹}
    (hEq : Γ ≤ (bv_powerset x).func χ₁ =ᴮ (bv_powerset x).func χ₂) :
    Γ ≤ (functions x (2 : bSet 𝔹)).func (F χ₁) =ᴮ
      (functions x (2 : bSet 𝔹)).func (F χ₂) := by
  change Γ ≤ set_of_indicator χ₁ =ᴮ set_of_indicator χ₂ at hEq
  change Γ ≤ set_of_indicator (x := prod x (2 : bSet 𝔹)) (F χ₁) =ᴮ
    set_of_indicator (x := prod x (2 : bSet 𝔹)) (F χ₂)
  rw [eq_iff_subset_subset] at hEq
  have h₁₂ : Γ ≤ set_of_indicator χ₁ ⊆ᴮ set_of_indicator χ₂ :=
    hEq.trans inf_le_left
  have h₂₁ : Γ ≤ set_of_indicator χ₂ ⊆ᴮ set_of_indicator χ₁ :=
    hEq.trans inf_le_right
  exact subset_ext (F_subset h₁₂ h₂₁) (F_subset h₂₁ h₁₂)

theorem F_subset_prod {x : bSet 𝔹} {χ : (bv_powerset x).type} {Γ : 𝔹} :
    Γ ≤ (functions x (2 : bSet 𝔹)).func (F χ) ⊆ᴮ prod x (2 : bSet 𝔹) := by
  change Γ ≤ set_of_indicator (x := prod x (2 : bSet 𝔹)) (F χ) ⊆ᴮ
    prod x (2 : bSet 𝔹)
  exact subset.mk_subset

theorem F_is_total {x : bSet 𝔹} {χ : (bv_powerset x).type} {Γ : 𝔹} :
    Γ ≤ is_total x (2 : bSet 𝔹) ((functions x (2 : bSet 𝔹)).func (F χ)) := by
  change Γ ≤ is_total x (2 : bSet 𝔹)
    (set_of_indicator (x := prod x (2 : bSet 𝔹)) (F χ))
  unfold is_total
  apply le_iInf
  intro z
  apply lattice.bv_imp_intro
  let Δ : 𝔹 := Γ ⊓ z ∈ᴮ x
  change Δ ≤ ⨆ w₂ : bSet 𝔹,
    w₂ ∈ᴮ (2 : bSet 𝔹) ⊓
      pair z w₂ ∈ᴮ set_of_indicator (x := prod x (2 : bSet 𝔹)) (F χ)
  have hSplit : Δ =
      Δ ⊓ ((z ∈ᴮ set_of_indicator χ) ⊔ (z ∈ᴮ set_of_indicator χ)ᶜ) := by
    rw [sup_compl_eq_top, inf_top_eq]
  rw [hSplit, inf_sup_left]
  apply sup_le
  · let Θ : 𝔹 := Δ ⊓ z ∈ᴮ set_of_indicator χ
    change Θ ≤ ⨆ w₂ : bSet 𝔹,
      w₂ ∈ᴮ (2 : bSet 𝔹) ⊓
        pair z w₂ ∈ᴮ set_of_indicator (x := prod x (2 : bSet 𝔹)) (F χ)
    apply lattice.bv_use (0 : bSet 𝔹)
    apply le_inf
    · exact ofNat_mem_of_lt (k₁ := 0) (k₂ := 2) (by decide)
    · exact mem_F_zero_of_mem_indicator inf_le_right
  · let Θ : 𝔹 := Δ ⊓ (z ∈ᴮ set_of_indicator χ)ᶜ
    change Θ ≤ ⨆ w₂ : bSet 𝔹,
      w₂ ∈ᴮ (2 : bSet 𝔹) ⊓
        pair z w₂ ∈ᴮ set_of_indicator (x := prod x (2 : bSet 𝔹)) (F χ)
    have hzX : Θ ≤ z ∈ᴮ x := by
      dsimp [Θ, Δ]
      exact inf_le_left.trans inf_le_right
    apply lattice.bv_use (1 : bSet 𝔹)
    apply le_inf
    · exact ofNat_mem_of_lt (k₁ := 1) (k₂ := 2) (by decide)
    · exact mem_F_one_of_not_mem_indicator hzX inf_le_right

theorem F_is_func {x : bSet 𝔹} {χ : (bv_powerset x).type} {Γ : 𝔹} :
    Γ ≤ is_func ((functions x (2 : bSet 𝔹)).func (F χ)) := by
  change Γ ≤ is_func (set_of_indicator (x := prod x (2 : bSet 𝔹)) (F χ))
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
  let Δ₀ : 𝔹 := Γ ⊓
    (pair w₁ v₁ ∈ᴮ set_of_indicator (x := prod x (2 : bSet 𝔹)) (F χ) ⊓
      pair w₂ v₂ ∈ᴮ set_of_indicator (x := prod x (2 : bSet 𝔹)) (F χ))
  change Δ₀ ≤ lattice.imp (w₁ =ᴮ w₂) (v₁ =ᴮ v₂)
  apply lattice.bv_imp_intro
  let Δ : 𝔹 := Δ₀ ⊓ w₁ =ᴮ w₂
  change Δ ≤ v₁ =ᴮ v₂
  have hMem₁ : Δ ≤ pair w₁ v₁ ∈ᴮ
      set_of_indicator (x := prod x (2 : bSet 𝔹)) (F χ) := by
    dsimp [Δ, Δ₀]
    exact inf_le_left.trans (inf_le_right.trans inf_le_left)
  have hMem₂ : Δ ≤ pair w₂ v₂ ∈ᴮ
      set_of_indicator (x := prod x (2 : bSet 𝔹)) (F χ) := by
    dsimp [Δ, Δ₀]
    exact inf_le_left.trans (inf_le_right.trans inf_le_right)
  rw [mem_set_of_indicator_iff] at hMem₁
  apply (le_inf le_rfl hMem₁).trans
  apply lattice.bv_cases_right
  intro pr₁
  cases pr₁ with
  | mk i₁ j₁ =>
      let Δ₁ : 𝔹 := Δ ⊓
        ((F χ (i₁, j₁) ⊓ (prod x (2 : bSet 𝔹)).bval (i₁, j₁)) ⊓
          pair w₁ v₁ =ᴮ (prod x (2 : bSet 𝔹)).func (i₁, j₁))
      change Δ₁ ≤ v₁ =ᴮ v₂
      rw [mem_set_of_indicator_iff] at hMem₂
      have hMem₂Δ₁ : Δ₁ ≤ ⨆ pr : (prod x (2 : bSet 𝔹)).type,
          (F χ pr ⊓ (prod x (2 : bSet 𝔹)).bval pr) ⊓
            pair w₂ v₂ =ᴮ (prod x (2 : bSet 𝔹)).func pr := by
        dsimp [Δ₁]
        exact inf_le_left.trans hMem₂
      apply (le_inf le_rfl hMem₂Δ₁).trans
      apply lattice.bv_cases_right
      intro pr₂
      cases pr₂ with
      | mk i₂ j₂ =>
          let Θ : 𝔹 := Δ₁ ⊓
            ((F χ (i₂, j₂) ⊓ (prod x (2 : bSet 𝔹)).bval (i₂, j₂)) ⊓
              pair w₂ v₂ =ᴮ (prod x (2 : bSet 𝔹)).func (i₂, j₂))
          change Θ ≤ v₁ =ᴮ v₂
          have hF₁ : Θ ≤ F χ (i₁, j₁) := by
            dsimp [Θ, Δ₁]
            exact inf_le_left.trans (inf_le_right.trans (inf_le_left.trans inf_le_left))
          have hF₂ : Θ ≤ F χ (i₂, j₂) := by
            dsimp [Θ]
            exact inf_le_right.trans (inf_le_left.trans inf_le_left)
          have hPair₁ : Θ ≤ pair w₁ v₁ =ᴮ pair (x.func i₁) ((2 : bSet 𝔹).func j₁) := by
            dsimp [Θ, Δ₁, prod]
            exact inf_le_left.trans (inf_le_right.trans inf_le_right)
          have hPair₂ : Θ ≤ pair w₂ v₂ =ᴮ pair (x.func i₂) ((2 : bSet 𝔹).func j₂) := by
            dsimp [Θ, prod]
            exact inf_le_right.trans inf_le_right
          have hw₁ : Θ ≤ w₁ =ᴮ x.func i₁ :=
            eq_of_eq_pair_left' hPair₁
          have hw₂ : Θ ≤ w₂ =ᴮ x.func i₂ :=
            eq_of_eq_pair_left' hPair₂
          have hv₁ : Θ ≤ v₁ =ᴮ (2 : bSet 𝔹).func j₁ :=
            eq_of_eq_pair_right' hPair₁
          have hv₂ : Θ ≤ v₂ =ᴮ (2 : bSet 𝔹).func j₂ :=
            eq_of_eq_pair_right' hPair₂
          have hInput : Θ ≤ w₁ =ᴮ w₂ := by
            dsimp [Θ, Δ₁, Δ]
            exact inf_le_left.trans (inf_le_left.trans inf_le_right)
          have hXiEq : Θ ≤ x.func i₁ =ᴮ x.func i₂ :=
            bv_trans (bv_symm hw₁) (bv_trans hInput hw₂)
          dsimp [F] at hF₁ hF₂
          apply (le_inf le_rfl hF₁).trans
          apply lattice.bv_or_elim_right
          · let Φ : 𝔹 := Θ ⊓
              (x.func i₁ ∈ᴮ set_of_indicator χ ⊓
                (2 : bSet 𝔹).func j₁ =ᴮ (0 : bSet 𝔹))
            change Φ ≤ v₁ =ᴮ v₂
            have hF₂Φ : Φ ≤
                x.func i₂ ∈ᴮ set_of_indicator χ ⊓
                    (2 : bSet 𝔹).func j₂ =ᴮ (0 : bSet 𝔹) ⊔
                  (x.func i₂ ∈ᴮ subset.mk (x := x)
                      (fun k : x.type => (x.func k ∈ᴮ set_of_indicator χ)ᶜ) ⊓
                    (2 : bSet 𝔹).func j₂ =ᴮ (1 : bSet 𝔹)) :=
              inf_le_left.trans hF₂
            apply (le_inf le_rfl hF₂Φ).trans
            apply lattice.bv_or_elim_right
            · let Ψ : 𝔹 := Φ ⊓
                (x.func i₂ ∈ᴮ set_of_indicator χ ⊓
                  (2 : bSet 𝔹).func j₂ =ᴮ (0 : bSet 𝔹))
              change Ψ ≤ v₁ =ᴮ v₂
              have hΨΘ : Ψ ≤ Θ := by
                dsimp [Ψ, Φ]
                exact inf_le_left.trans inf_le_left
              have hv₁Zero : Ψ ≤ v₁ =ᴮ (0 : bSet 𝔹) :=
                bv_trans (hΨΘ.trans hv₁)
                  (by
                    dsimp [Ψ, Φ]
                    exact inf_le_left.trans inf_le_right |>.trans inf_le_right)
              have hv₂Zero : Ψ ≤ v₂ =ᴮ (0 : bSet 𝔹) :=
                bv_trans (hΨΘ.trans hv₂)
                  (by
                    dsimp [Ψ]
                    exact inf_le_right.trans inf_le_right)
              exact bv_trans hv₁Zero (bv_symm hv₂Zero)
            · let Ψ : 𝔹 := Φ ⊓
                (x.func i₂ ∈ᴮ subset.mk (x := x)
                    (fun k : x.type => (x.func k ∈ᴮ set_of_indicator χ)ᶜ) ⊓
                  (2 : bSet 𝔹).func j₂ =ᴮ (1 : bSet 𝔹))
              change Ψ ≤ v₁ =ᴮ v₂
              have hΨΘ : Ψ ≤ Θ := by
                dsimp [Ψ, Φ]
                exact inf_le_left.trans inf_le_left
              have hMemχ₁ : Ψ ≤ x.func i₁ ∈ᴮ set_of_indicator χ := by
                dsimp [Ψ, Φ]
                exact inf_le_left.trans inf_le_right |>.trans inf_le_left
              have hMemχ₂ : Ψ ≤ x.func i₂ ∈ᴮ set_of_indicator χ :=
                subst_congr_mem_left' (hΨΘ.trans hXiEq) hMemχ₁
              have hNotχ₂ : Ψ ≤ (x.func i₂ ∈ᴮ set_of_indicator χ)ᶜ :=
                not_mem_indicator_of_mem_indicator_compl (by
                  dsimp [Ψ]
                  exact inf_le_right.trans inf_le_left)
              exact lattice.bv_exfalso (bv_absurd hMemχ₂ hNotχ₂)
          · let Φ : 𝔹 := Θ ⊓
              (x.func i₁ ∈ᴮ subset.mk (x := x)
                  (fun k : x.type => (x.func k ∈ᴮ set_of_indicator χ)ᶜ) ⊓
                (2 : bSet 𝔹).func j₁ =ᴮ (1 : bSet 𝔹))
            change Φ ≤ v₁ =ᴮ v₂
            have hF₂Φ : Φ ≤
                x.func i₂ ∈ᴮ set_of_indicator χ ⊓
                    (2 : bSet 𝔹).func j₂ =ᴮ (0 : bSet 𝔹) ⊔
                  (x.func i₂ ∈ᴮ subset.mk (x := x)
                      (fun k : x.type => (x.func k ∈ᴮ set_of_indicator χ)ᶜ) ⊓
                    (2 : bSet 𝔹).func j₂ =ᴮ (1 : bSet 𝔹)) :=
              inf_le_left.trans hF₂
            apply (le_inf le_rfl hF₂Φ).trans
            apply lattice.bv_or_elim_right
            · let Ψ : 𝔹 := Φ ⊓
                (x.func i₂ ∈ᴮ set_of_indicator χ ⊓
                  (2 : bSet 𝔹).func j₂ =ᴮ (0 : bSet 𝔹))
              change Ψ ≤ v₁ =ᴮ v₂
              have hΨΘ : Ψ ≤ Θ := by
                dsimp [Ψ, Φ]
                exact inf_le_left.trans inf_le_left
              have hMemχ₂ : Ψ ≤ x.func i₂ ∈ᴮ set_of_indicator χ := by
                dsimp [Ψ]
                exact inf_le_right.trans inf_le_left
              have hMemχ₁ : Ψ ≤ x.func i₁ ∈ᴮ set_of_indicator χ :=
                subst_congr_mem_left' (bv_symm (hΨΘ.trans hXiEq)) hMemχ₂
              have hNotχ₁ : Ψ ≤ (x.func i₁ ∈ᴮ set_of_indicator χ)ᶜ :=
                not_mem_indicator_of_mem_indicator_compl (by
                  dsimp [Ψ, Φ]
                  exact inf_le_left.trans inf_le_right |>.trans inf_le_left)
              exact lattice.bv_exfalso (bv_absurd hMemχ₁ hNotχ₁)
            · let Ψ : 𝔹 := Φ ⊓
                (x.func i₂ ∈ᴮ subset.mk (x := x)
                    (fun k : x.type => (x.func k ∈ᴮ set_of_indicator χ)ᶜ) ⊓
                  (2 : bSet 𝔹).func j₂ =ᴮ (1 : bSet 𝔹))
              change Ψ ≤ v₁ =ᴮ v₂
              have hΨΘ : Ψ ≤ Θ := by
                dsimp [Ψ, Φ]
                exact inf_le_left.trans inf_le_left
              have hv₁One : Ψ ≤ v₁ =ᴮ (1 : bSet 𝔹) :=
                bv_trans (hΨΘ.trans hv₁)
                  (by
                    dsimp [Ψ, Φ]
                    exact inf_le_left.trans inf_le_right |>.trans inf_le_right)
              have hv₂One : Ψ ≤ v₂ =ᴮ (1 : bSet 𝔹) :=
                bv_trans (hΨΘ.trans hv₂)
                  (by
                    dsimp [Ψ]
                    exact inf_le_right.trans inf_le_right)
              exact bv_trans hv₁One (bv_symm hv₂One)

theorem F_is_func' {x : bSet 𝔹} {χ : (bv_powerset x).type} {Γ : 𝔹} :
    Γ ≤ is_func' x (2 : bSet 𝔹) ((functions x (2 : bSet 𝔹)).func (F χ)) :=
  le_inf F_is_func F_is_total

theorem F_is_function {x : bSet 𝔹} {χ : (bv_powerset x).type} {Γ : 𝔹} :
    Γ ≤ is_function x (2 : bSet 𝔹) ((functions x (2 : bSet 𝔹)).func (F χ)) :=
  le_inf F_is_func' F_subset_prod

theorem F_mem {x : bSet 𝔹} (χ : (bv_powerset x).type) {Γ : 𝔹} :
    Γ ≤ (functions x (2 : bSet 𝔹)).bval (F χ) ∧ Γ ≤ (⊤ : 𝔹) := by
  constructor
  · simpa [functions_bval] using (F_is_function (x := x) (χ := χ) (Γ := Γ))
  · exact le_top

/-- The internal characteristic-function map from `bv_powerset x` to `functions x 2`. -/
def f (x : bSet 𝔹) : bSet 𝔹 :=
  function.mk' (x := bv_powerset x) (y := functions x (2 : bSet 𝔹))
    (F (x := x)) (fun _ => (⊤ : 𝔹))

theorem f_is_function {x : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ is_function (bv_powerset x) (functions x (2 : bSet 𝔹)) (f x) :=
  function.mk'_is_function (x := bv_powerset x) (y := functions x (2 : bSet 𝔹))
    (F (x := x)) (fun _ => (⊤ : 𝔹))
    (fun _ _ {Γ} h => F_ext (Γ := Γ) h) (fun i {Γ} _ => F_mem (Γ := Γ) i)

theorem f_is_inj {x : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ is_inj (f x) :=
  function.mk'_is_inj (x := bv_powerset x) (y := functions x (2 : bSet 𝔹))
    (F (x := x)) (fun _ => (⊤ : 𝔹)) (fun _ _ {Γ} h => F_inj (Γ := Γ) h)

theorem powerset_injects_into_functions {x : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ injects_into (bv_powerset x) (functions x (2 : bSet 𝔹)) := by
  unfold injects_into
  apply lattice.bv_use (f x)
  exact le_inf (is_func'_of_is_function f_is_function) f_is_inj

end powerset_injects

/-- Every member of `η` has another member of `η` comparable with it by epsilon. -/
def exists_two (η : bSet 𝔹) : 𝔹 :=
  ⨅ x : bSet 𝔹, lattice.imp (x ∈ᴮ η)
    (⨆ z : bSet 𝔹, z ∈ᴮ η ⊓ (x ∈ᴮ z ⊔ z ∈ᴮ x))

theorem B_ext_exists_two : B_ext (exists_two : bSet 𝔹 → 𝔹) := by
  unfold exists_two
  apply B_ext_iInf
  intro x
  apply B_ext_imp
  · exact B_ext_mem_right x
  · apply B_ext_iSup
    intro z
    apply B_ext_inf
    · exact B_ext_mem_right z
    · exact B_ext_const _

theorem one_mem_of_not_zero_and_not_one {η : bSet 𝔹} {Γ : 𝔹}
    (hOrd : Γ ≤ Ord η) (hNotZero : Γ ≤ (η =ᴮ (0 : bSet 𝔹))ᶜ)
    (hNotOne : Γ ≤ (η =ᴮ (1 : bSet 𝔹))ᶜ) : Γ ≤ (1 : bSet 𝔹) ∈ᴮ η := by
  have hTri : Γ ≤ η =ᴮ (1 : bSet 𝔹) ⊔ η ∈ᴮ (1 : bSet 𝔹) ⊔
      (1 : bSet 𝔹) ∈ᴮ η :=
    Ord.trichotomy hOrd Ord_one
  apply (le_inf le_rfl hTri).trans
  apply lattice.bv_or_elim_right
  · apply lattice.bv_or_elim_right
    · let Δ : 𝔹 := Γ ⊓ η =ᴮ (1 : bSet 𝔹)
      change Δ ≤ (1 : bSet 𝔹) ∈ᴮ η
      have hEq : Δ ≤ η =ᴮ (1 : bSet 𝔹) := by
        dsimp [Δ]
        exact inf_le_right
      have hNot : Δ ≤ (η =ᴮ (1 : bSet 𝔹))ᶜ := by
        dsimp [Δ]
        exact inf_le_left.trans hNotOne
      exact lattice.bv_exfalso (bv_absurd hEq hNot)
    · let Δ : 𝔹 := Γ ⊓ η ∈ᴮ (1 : bSet 𝔹)
      change Δ ≤ (1 : bSet 𝔹) ∈ᴮ η
      have hMemOne : Δ ≤ η ∈ᴮ (1 : bSet 𝔹) := by
        dsimp [Δ]
        exact inf_le_right
      have hEqZero : Δ ≤ η =ᴮ (0 : bSet 𝔹) :=
        eq_zero_of_mem_one hMemOne
      have hNotZero : Δ ≤ (η =ᴮ (0 : bSet 𝔹))ᶜ := by
        dsimp [Δ]
        exact inf_le_left.trans hNotZero
      exact lattice.bv_exfalso (bv_absurd hEqZero hNotZero)
  · exact inf_le_right

theorem not_one_of_exists_two {η : bSet 𝔹} {Γ : 𝔹}
    (hExists : Γ ≤ exists_two η) : Γ ≤ (η =ᴮ (1 : bSet 𝔹))ᶜ := by
  apply le_compl_of_inf_le_bot
  let Δ : 𝔹 := Γ ⊓ η =ᴮ (1 : bSet 𝔹)
  change Δ ≤ ⊥
  have hEqOne : Δ ≤ η =ᴮ (1 : bSet 𝔹) := by
    dsimp [Δ]
    exact inf_le_right
  have hZeroη : Δ ≤ (0 : bSet 𝔹) ∈ᴮ η :=
    subst_congr_mem_right' (bv_symm hEqOne) zero_mem_one
  have hImp :
      Δ ≤ lattice.imp ((0 : bSet 𝔹) ∈ᴮ η)
        (⨆ z : bSet 𝔹, z ∈ᴮ η ⊓ ((0 : bSet 𝔹) ∈ᴮ z ⊔ z ∈ᴮ (0 : bSet 𝔹))) := by
    unfold exists_two at hExists
    exact (inf_le_left.trans hExists).trans (iInf_le _ (0 : bSet 𝔹))
  have hWitness :
      Δ ≤ ⨆ z : bSet 𝔹, z ∈ᴮ η ⊓
        ((0 : bSet 𝔹) ∈ᴮ z ⊔ z ∈ᴮ (0 : bSet 𝔹)) :=
    lattice.bv_context_apply hImp hZeroη
  apply (le_inf le_rfl hWitness).trans
  apply lattice.bv_cases_right
  intro z
  let Θ : 𝔹 := Δ ⊓ (z ∈ᴮ η ⊓ ((0 : bSet 𝔹) ∈ᴮ z ⊔ z ∈ᴮ (0 : bSet 𝔹)))
  change Θ ≤ ⊥
  have hzη : Θ ≤ z ∈ᴮ η := by
    dsimp [Θ]
    exact inf_le_right.trans inf_le_left
  have hzOne : Θ ≤ z ∈ᴮ (1 : bSet 𝔹) :=
    subst_congr_mem_right' (inf_le_left.trans hEqOne) hzη
  have hzEqZero : Θ ≤ z =ᴮ (0 : bSet 𝔹) :=
    eq_zero_of_mem_one hzOne
  have hComparable : Θ ≤ (0 : bSet 𝔹) ∈ᴮ z ⊔ z ∈ᴮ (0 : bSet 𝔹) := by
    dsimp [Θ]
    exact inf_le_right.trans inf_le_right
  apply (le_inf le_rfl hComparable).trans
  apply lattice.bv_or_elim_right
  · let Ω : 𝔹 := Θ ⊓ (0 : bSet 𝔹) ∈ᴮ z
    change Ω ≤ ⊥
    have hZeroMemZ : Ω ≤ (0 : bSet 𝔹) ∈ᴮ z := by
      dsimp [Ω]
      exact inf_le_right
    have hEq : Ω ≤ z =ᴮ (0 : bSet 𝔹) :=
      inf_le_left.trans hzEqZero
    have hZeroMemZero : Ω ≤ (0 : bSet 𝔹) ∈ᴮ (0 : bSet 𝔹) :=
      subst_congr_mem_right' hEq hZeroMemZ
    exact bot_of_mem_self hZeroMemZero
  · let Ω : 𝔹 := Θ ⊓ z ∈ᴮ (0 : bSet 𝔹)
    change Ω ≤ ⊥
    have hzMemZero : Ω ≤ z ∈ᴮ (0 : bSet 𝔹) := by
      dsimp [Ω]
      exact inf_le_right
    have hZeroEmpty : Ω ≤ (0 : bSet 𝔹) =ᴮ (∅ : bSet 𝔹) :=
      (inf_le_left.trans inf_le_left).trans ofNat_zero_eq_empty
    have hzMemEmpty : Ω ≤ z ∈ᴮ (∅ : bSet 𝔹) :=
      subst_congr_mem_right' hZeroEmpty hzMemZero
    simpa [mem_empty] using hzMemEmpty

theorem exists_two_witness {η x z : bSet 𝔹} {Γ : 𝔹}
    (hzη : Γ ≤ z ∈ᴮ η) (hComparable : Γ ≤ x ∈ᴮ z ⊔ z ∈ᴮ x) :
    Γ ≤ ⨆ z : bSet 𝔹, z ∈ᴮ η ⊓ (x ∈ᴮ z ⊔ z ∈ᴮ x) :=
  (le_inf hzη hComparable).trans
    (le_iSup (fun z : bSet 𝔹 => z ∈ᴮ η ⊓ (x ∈ᴮ z ⊔ z ∈ᴮ x)) z)

theorem exists_two_of_not_one {η : bSet 𝔹} {Γ : 𝔹}
    (hOrd : Γ ≤ Ord η) (hNotOne : Γ ≤ (η =ᴮ (1 : bSet 𝔹))ᶜ) :
    Γ ≤ exists_two η := by
  have hZeroCases : Γ ≤ η =ᴮ (0 : bSet 𝔹) ⊔ (η =ᴮ (0 : bSet 𝔹))ᶜ := by
    calc
      Γ ≤ ⊤ := le_top
      _ = η =ᴮ (0 : bSet 𝔹) ⊔ (η =ᴮ (0 : bSet 𝔹))ᶜ := by
        rw [sup_compl_eq_top]
  apply (le_inf le_rfl hZeroCases).trans
  apply lattice.bv_or_elim_right
  · let Γ₀ : 𝔹 := Γ ⊓ η =ᴮ (0 : bSet 𝔹)
    change Γ₀ ≤ exists_two η
    unfold exists_two
    apply le_iInf
    intro x
    apply lattice.bv_imp_intro
    let Δ : 𝔹 := Γ₀ ⊓ x ∈ᴮ η
    change Δ ≤ ⨆ z : bSet 𝔹, z ∈ᴮ η ⊓ (x ∈ᴮ z ⊔ z ∈ᴮ x)
    have hηZero : Δ ≤ η =ᴮ (0 : bSet 𝔹) := by
      dsimp [Δ, Γ₀]
      exact inf_le_left.trans inf_le_right
    have hxη : Δ ≤ x ∈ᴮ η := by
      dsimp [Δ]
      exact inf_le_right
    have hxZero : Δ ≤ x ∈ᴮ (0 : bSet 𝔹) :=
      subst_congr_mem_right' hηZero hxη
    have hZeroEmpty : Δ ≤ (0 : bSet 𝔹) =ᴮ (∅ : bSet 𝔹) :=
      ofNat_zero_eq_empty
    have hxEmpty : Δ ≤ x ∈ᴮ (∅ : bSet 𝔹) :=
      subst_congr_mem_right' hZeroEmpty hxZero
    exact lattice.bv_exfalso (by simpa [mem_empty] using hxEmpty)
  · let Γₙ : 𝔹 := Γ ⊓ (η =ᴮ (0 : bSet 𝔹))ᶜ
    change Γₙ ≤ exists_two η
    have hOneη : Γₙ ≤ (1 : bSet 𝔹) ∈ᴮ η :=
      one_mem_of_not_zero_and_not_one
        (inf_le_left.trans hOrd) inf_le_right (inf_le_left.trans hNotOne)
    unfold exists_two
    apply le_iInf
    intro x
    apply lattice.bv_imp_intro
    let Δ : 𝔹 := Γₙ ⊓ x ∈ᴮ η
    change Δ ≤ ⨆ z : bSet 𝔹, z ∈ᴮ η ⊓ (x ∈ᴮ z ⊔ z ∈ᴮ x)
    have hΔΓₙ : Δ ≤ Γₙ := by
      dsimp [Δ]
      exact inf_le_left
    have hΔΓ : Δ ≤ Γ := by
      dsimp [Γₙ] at hΔΓₙ
      exact hΔΓₙ.trans inf_le_left
    have hxη : Δ ≤ x ∈ᴮ η := by
      dsimp [Δ]
      exact inf_le_right
    have hOrdη : Δ ≤ Ord η :=
      hΔΓ.trans hOrd
    have hOrdX : Δ ≤ Ord x :=
      Ord_of_mem_Ord hxη hOrdη
    have hTri : Δ ≤ x =ᴮ (1 : bSet 𝔹) ⊔ x ∈ᴮ (1 : bSet 𝔹) ⊔
        (1 : bSet 𝔹) ∈ᴮ x :=
      Ord.trichotomy hOrdX Ord_one
    apply (le_inf le_rfl hTri).trans
    apply lattice.bv_or_elim_right
    · apply lattice.bv_or_elim_right
      · let Θ : 𝔹 := Δ ⊓ x =ᴮ (1 : bSet 𝔹)
        change Θ ≤ ⨆ z : bSet 𝔹, z ∈ᴮ η ⊓ (x ∈ᴮ z ⊔ z ∈ᴮ x)
        have hΘΓₙ : Θ ≤ Γₙ := by
          dsimp [Θ]
          exact inf_le_left.trans hΔΓₙ
        have hΘΓ : Θ ≤ Γ := by
          dsimp [Γₙ] at hΘΓₙ
          exact hΘΓₙ.trans inf_le_left
        have hEqOne : Θ ≤ x =ᴮ (1 : bSet 𝔹) := by
          dsimp [Θ]
          exact inf_le_right
        have hOneηΘ : Θ ≤ (1 : bSet 𝔹) ∈ᴮ η :=
          hΘΓₙ.trans hOneη
        have hZeroη : Θ ≤ (0 : bSet 𝔹) ∈ᴮ η :=
          mem_of_mem_Ord zero_mem_one hOneηΘ (hΘΓ.trans hOrd)
        have hZeroX : Θ ≤ (0 : bSet 𝔹) ∈ᴮ x :=
          subst_congr_mem_right' (bv_symm hEqOne) zero_mem_one
        exact exists_two_witness hZeroη (hZeroX.trans le_sup_right)
      · let Θ : 𝔹 := Δ ⊓ x ∈ᴮ (1 : bSet 𝔹)
        change Θ ≤ ⨆ z : bSet 𝔹, z ∈ᴮ η ⊓ (x ∈ᴮ z ⊔ z ∈ᴮ x)
        have hΘΓₙ : Θ ≤ Γₙ := by
          dsimp [Θ]
          exact inf_le_left.trans hΔΓₙ
        have hxOne : Θ ≤ x ∈ᴮ (1 : bSet 𝔹) := by
          dsimp [Θ]
          exact inf_le_right
        have hOneηΘ : Θ ≤ (1 : bSet 𝔹) ∈ᴮ η :=
          hΘΓₙ.trans hOneη
        exact exists_two_witness hOneηΘ (hxOne.trans le_sup_left)
    · let Θ : 𝔹 := Δ ⊓ (1 : bSet 𝔹) ∈ᴮ x
      change Θ ≤ ⨆ z : bSet 𝔹, z ∈ᴮ η ⊓ (x ∈ᴮ z ⊔ z ∈ᴮ x)
      have hΘΓₙ : Θ ≤ Γₙ := by
        dsimp [Θ]
        exact inf_le_left.trans hΔΓₙ
      have hOneX : Θ ≤ (1 : bSet 𝔹) ∈ᴮ x := by
        dsimp [Θ]
        exact inf_le_right
      have hOneηΘ : Θ ≤ (1 : bSet 𝔹) ∈ᴮ η :=
        hΘΓₙ.trans hOneη
      exact exists_two_witness hOneηΘ (hOneX.trans le_sup_right)

theorem exists_two_iff {η : bSet 𝔹} {Γ : 𝔹} (hOrd : Γ ≤ Ord η) :
    Γ ≤ exists_two η ↔ Γ ≤ (η =ᴮ (1 : bSet 𝔹))ᶜ :=
  ⟨not_one_of_exists_two, exists_two_of_not_one hOrd⟩

/-- A function preserves and reflects the epsilon relation between members of `x` and `y`. -/
def strong_eps_hom (x y f : bSet 𝔹) : 𝔹 :=
  ⨅ z₁ : bSet 𝔹, lattice.imp (z₁ ∈ᴮ x)
    (⨅ z₂ : bSet 𝔹, lattice.imp (z₂ ∈ᴮ x)
      (⨅ w₁ : bSet 𝔹, lattice.imp (w₁ ∈ᴮ y)
        (⨅ w₂ : bSet 𝔹, lattice.imp (w₂ ∈ᴮ y)
          (lattice.imp (pair z₁ w₁ ∈ᴮ f)
            (lattice.imp (pair z₂ w₂ ∈ᴮ f)
              (lattice.biimp (z₁ ∈ᴮ z₂) (w₁ ∈ᴮ w₂)))))))

/-- A surjective Boolean-valued epsilon isomorphism from `x` to `y`. -/
def eps_iso (x y f : bSet 𝔹) : 𝔹 :=
  (is_function x y f ⊓ strong_eps_hom x y f) ⊓ is_surj x y f

theorem is_surj_of_eps_iso {x y f : bSet 𝔹} {Γ : 𝔹}
    (h : Γ ≤ eps_iso x y f) : Γ ≤ is_surj x y f :=
  h.trans inf_le_right

theorem is_function_of_eps_iso {x y f : bSet 𝔹} {Γ : 𝔹}
    (h : Γ ≤ eps_iso x y f) : Γ ≤ is_function x y f :=
  (h.trans inf_le_left).trans inf_le_left

theorem strong_eps_hom_of_eps_iso {x y f : bSet 𝔹} {Γ : 𝔹}
    (h : Γ ≤ eps_iso x y f) : Γ ≤ strong_eps_hom x y f :=
  (h.trans inf_le_left).trans inf_le_right

/-- Unfolding lemma: `strong_eps_hom` as a forall over context refinements. -/
theorem strong_eps_hom_iff {x y f : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ strong_eps_hom x y f ↔
      (∀ (Γ' : 𝔹), Γ' ≤ Γ →
        ∀ (z₁ : bSet 𝔹), (Γ' ≤ z₁ ∈ᴮ x) → ∀ (z₂ : bSet 𝔹), (Γ' ≤ z₂ ∈ᴮ x) →
        ∀ (w₁ : bSet 𝔹), (Γ' ≤ w₁ ∈ᴮ y) → ∀ (w₂ : bSet 𝔹), (Γ' ≤ w₂ ∈ᴮ y) →
        (Γ' ≤ pair z₁ w₁ ∈ᴮ f) → (Γ' ≤ pair z₂ w₂ ∈ᴮ f) →
        ((Γ' ≤ z₁ ∈ᴮ z₂) ↔ (Γ' ≤ w₁ ∈ᴮ w₂))) := by
  constructor
  · -- Forward: unpack the strong_eps_hom iInf/imp chain
    intro h Γ' hLe z₁ hz₁ z₂ hz₂ w₁ hw₁ w₂ hw₂ hpr₁ hpr₂
    have h' : Γ' ≤ strong_eps_hom x y f := hLe.trans h
    unfold strong_eps_hom at h'
    -- Peel the ⨅ z₁ layer
    have hz₁i : Γ' ≤ lattice.imp (z₁ ∈ᴮ x)
        (⨅ (z₂' : bSet 𝔹), lattice.imp (z₂' ∈ᴮ x)
          (⨅ (w₁' : bSet 𝔹), lattice.imp (w₁' ∈ᴮ y)
            (⨅ (w₂' : bSet 𝔹), lattice.imp (w₂' ∈ᴮ y)
              (lattice.imp (pair z₁ w₁' ∈ᴮ f)
                (lattice.imp (pair z₂' w₂' ∈ᴮ f)
                  (lattice.biimp (z₁ ∈ᴮ z₂') (w₁' ∈ᴮ w₂'))))))) :=
      h'.trans (iInf_le (fun t : bSet 𝔹 =>
        lattice.imp (t ∈ᴮ x) (⨅ (z₂' : bSet 𝔹), lattice.imp (z₂' ∈ᴮ x)
          (⨅ (w₁' : bSet 𝔹), lattice.imp (w₁' ∈ᴮ y)
            (⨅ (w₂' : bSet 𝔹), lattice.imp (w₂' ∈ᴮ y)
              (lattice.imp (pair t w₁' ∈ᴮ f)
                (lattice.imp (pair z₂' w₂' ∈ᴮ f)
                  (lattice.biimp (t ∈ᴮ z₂') (w₁' ∈ᴮ w₂')))))))) z₁)
    -- Apply z₁ ∈ᴮ x
    have hz₁b : Γ' ≤ ⨅ (z₂' : bSet 𝔹), lattice.imp (z₂' ∈ᴮ x)
        (⨅ (w₁' : bSet 𝔹), lattice.imp (w₁' ∈ᴮ y)
          (⨅ (w₂' : bSet 𝔹), lattice.imp (w₂' ∈ᴮ y)
            (lattice.imp (pair z₁ w₁' ∈ᴮ f)
              (lattice.imp (pair z₂' w₂' ∈ᴮ f)
                (lattice.biimp (z₁ ∈ᴮ z₂') (w₁' ∈ᴮ w₂')))))) :=
      lattice.bv_context_apply hz₁i hz₁
    -- Peel ⨅ z₂' layer at z₂
    have hz₂i : Γ' ≤ lattice.imp (z₂ ∈ᴮ x)
        (⨅ (w₁' : bSet 𝔹), lattice.imp (w₁' ∈ᴮ y)
          (⨅ (w₂' : bSet 𝔹), lattice.imp (w₂' ∈ᴮ y)
            (lattice.imp (pair z₁ w₁' ∈ᴮ f)
              (lattice.imp (pair z₂ w₂' ∈ᴮ f)
                (lattice.biimp (z₁ ∈ᴮ z₂) (w₁' ∈ᴮ w₂')))))) :=
      hz₁b.trans (iInf_le (fun t : bSet 𝔹 =>
        lattice.imp (t ∈ᴮ x) (⨅ (w₁' : bSet 𝔹), lattice.imp (w₁' ∈ᴮ y)
          (⨅ (w₂' : bSet 𝔹), lattice.imp (w₂' ∈ᴮ y)
            (lattice.imp (pair z₁ w₁' ∈ᴮ f)
              (lattice.imp (pair t w₂' ∈ᴮ f)
                (lattice.biimp (z₁ ∈ᴮ t) (w₁' ∈ᴮ w₂'))))))) z₂)
    -- Apply z₂ ∈ᴮ x
    have hz₂b : Γ' ≤ ⨅ (w₁' : bSet 𝔹), lattice.imp (w₁' ∈ᴮ y)
        (⨅ (w₂' : bSet 𝔹), lattice.imp (w₂' ∈ᴮ y)
          (lattice.imp (pair z₁ w₁' ∈ᴮ f)
            (lattice.imp (pair z₂ w₂' ∈ᴮ f)
              (lattice.biimp (z₁ ∈ᴮ z₂) (w₁' ∈ᴮ w₂'))))) :=
      lattice.bv_context_apply hz₂i hz₂
    -- Peel ⨅ w₁' layer at w₁
    have hw₁i : Γ' ≤ lattice.imp (w₁ ∈ᴮ y)
        (⨅ (w₂' : bSet 𝔹), lattice.imp (w₂' ∈ᴮ y)
          (lattice.imp (pair z₁ w₁ ∈ᴮ f)
            (lattice.imp (pair z₂ w₂' ∈ᴮ f)
              (lattice.biimp (z₁ ∈ᴮ z₂) (w₁ ∈ᴮ w₂'))))) :=
      hz₂b.trans (iInf_le (fun t : bSet 𝔹 =>
        lattice.imp (t ∈ᴮ y) (⨅ (w₂' : bSet 𝔹), lattice.imp (w₂' ∈ᴮ y)
          (lattice.imp (pair z₁ t ∈ᴮ f)
            (lattice.imp (pair z₂ w₂' ∈ᴮ f)
              (lattice.biimp (z₁ ∈ᴮ z₂) (t ∈ᴮ w₂')))))) w₁)
    -- Apply w₁ ∈ᴮ y
    have hw₁b : Γ' ≤ ⨅ (w₂' : bSet 𝔹), lattice.imp (w₂' ∈ᴮ y)
        (lattice.imp (pair z₁ w₁ ∈ᴮ f)
          (lattice.imp (pair z₂ w₂' ∈ᴮ f)
            (lattice.biimp (z₁ ∈ᴮ z₂) (w₁ ∈ᴮ w₂')))) :=
      lattice.bv_context_apply hw₁i hw₁
    -- Peel ⨅ w₂' layer at w₂
    have hw₂i : Γ' ≤ lattice.imp (w₂ ∈ᴮ y)
        (lattice.imp (pair z₁ w₁ ∈ᴮ f)
          (lattice.imp (pair z₂ w₂ ∈ᴮ f)
            (lattice.biimp (z₁ ∈ᴮ z₂) (w₁ ∈ᴮ w₂)))) :=
      hw₁b.trans (iInf_le (fun t : bSet 𝔹 =>
        lattice.imp (t ∈ᴮ y) (lattice.imp (pair z₁ w₁ ∈ᴮ f)
          (lattice.imp (pair z₂ t ∈ᴮ f)
            (lattice.biimp (z₁ ∈ᴮ z₂) (w₁ ∈ᴮ t))))) w₂)
    -- Apply w₂ ∈ᴮ y
    have hw₂b : Γ' ≤ lattice.imp (pair z₁ w₁ ∈ᴮ f)
        (lattice.imp (pair z₂ w₂ ∈ᴮ f)
          (lattice.biimp (z₁ ∈ᴮ z₂) (w₁ ∈ᴮ w₂))) :=
      lattice.bv_context_apply hw₂i hw₂
    -- Apply pair z₁ w₁ ∈ f
    have hpr₁b : Γ' ≤ lattice.imp (pair z₂ w₂ ∈ᴮ f)
        (lattice.biimp (z₁ ∈ᴮ z₂) (w₁ ∈ᴮ w₂)) :=
      lattice.bv_context_apply hw₂b hpr₁
    -- Apply pair z₂ w₂ ∈ f, get the biimp
    have h_biimp : Γ' ≤ lattice.biimp (z₁ ∈ᴮ z₂) (w₁ ∈ᴮ w₂) :=
      lattice.bv_context_apply hpr₁b hpr₂
    exact (lattice.bv_biimp_iff.mp h_biimp) le_rfl
  · -- Reverse: pack up using le_iInf and bv_imp_intro
    intro H
    unfold strong_eps_hom
    apply le_iInf; intro z₁
    apply lattice.bv_imp_intro
    apply le_iInf; intro z₂
    apply lattice.bv_imp_intro
    apply le_iInf; intro w₁
    apply lattice.bv_imp_intro
    apply le_iInf; intro w₂
    apply lattice.bv_imp_intro
    apply lattice.bv_imp_intro
    apply lattice.bv_imp_intro
    -- Goal: Δ ≤ biimp (z₁ ∈ z₂) (w₁ ∈ w₂) where Δ is the accumulated infs
    rw [lattice.bv_biimp_iff]
    intro Γ' hΔ
    -- hΔ : Γ' ≤ Γ ⊓ (z₁∈x) ⊓ (z₂∈x) ⊓ (w₁∈y) ⊓ (w₂∈y) ⊓ (pair z₁ w₁ ∈ f) ⊓ (pair z₂ w₂ ∈ f)
    -- We need: (Γ' ≤ z₁ ∈ z₂) ↔ (Γ' ≤ w₁ ∈ w₂)
    -- Extract each condition from hΔ via inf projections.
    -- BIG = Γ ⊓ (z₁∈x) ⊓ (z₂∈x) ⊓ (w₁∈y) ⊓ (w₂∈y) ⊓ (pr₁∈f) ⊓ (pr₂∈f), left-assoc.
    -- We peel rightmost infs with inf_le_left, then extract the target with inf_le_right.
    have hΓ'Γ : Γ' ≤ Γ :=
      hΔ.trans (by
        calc
          _ ≤ Γ ⊓ (z₁ ∈ᴮ x) ⊓ (z₂ ∈ᴮ x) ⊓ (w₁ ∈ᴮ y) ⊓ (w₂ ∈ᴮ y) ⊓ (pair z₁ w₁ ∈ᴮ f) := inf_le_left
          _ ≤ Γ ⊓ (z₁ ∈ᴮ x) ⊓ (z₂ ∈ᴮ x) ⊓ (w₁ ∈ᴮ y) ⊓ (w₂ ∈ᴮ y) := inf_le_left
          _ ≤ Γ ⊓ (z₁ ∈ᴮ x) ⊓ (z₂ ∈ᴮ x) ⊓ (w₁ ∈ᴮ y) := inf_le_left
          _ ≤ Γ ⊓ (z₁ ∈ᴮ x) ⊓ (z₂ ∈ᴮ x) := inf_le_left
          _ ≤ Γ ⊓ (z₁ ∈ᴮ x) := inf_le_left
          _ ≤ Γ := inf_le_left)
    have hz₁mem : Γ' ≤ z₁ ∈ᴮ x :=
      hΔ.trans (by
        calc
          _ ≤ Γ ⊓ (z₁ ∈ᴮ x) ⊓ (z₂ ∈ᴮ x) ⊓ (w₁ ∈ᴮ y) ⊓ (w₂ ∈ᴮ y) ⊓ (pair z₁ w₁ ∈ᴮ f) := inf_le_left
          _ ≤ Γ ⊓ (z₁ ∈ᴮ x) ⊓ (z₂ ∈ᴮ x) ⊓ (w₁ ∈ᴮ y) ⊓ (w₂ ∈ᴮ y) := inf_le_left
          _ ≤ Γ ⊓ (z₁ ∈ᴮ x) ⊓ (z₂ ∈ᴮ x) ⊓ (w₁ ∈ᴮ y) := inf_le_left
          _ ≤ Γ ⊓ (z₁ ∈ᴮ x) ⊓ (z₂ ∈ᴮ x) := inf_le_left
          _ ≤ Γ ⊓ (z₁ ∈ᴮ x) := inf_le_left
          _ ≤ z₁ ∈ᴮ x := inf_le_right)
    have hz₂mem : Γ' ≤ z₂ ∈ᴮ x :=
      hΔ.trans (by
        calc
          _ ≤ Γ ⊓ (z₁ ∈ᴮ x) ⊓ (z₂ ∈ᴮ x) ⊓ (w₁ ∈ᴮ y) ⊓ (w₂ ∈ᴮ y) ⊓ (pair z₁ w₁ ∈ᴮ f) := inf_le_left
          _ ≤ Γ ⊓ (z₁ ∈ᴮ x) ⊓ (z₂ ∈ᴮ x) ⊓ (w₁ ∈ᴮ y) ⊓ (w₂ ∈ᴮ y) := inf_le_left
          _ ≤ Γ ⊓ (z₁ ∈ᴮ x) ⊓ (z₂ ∈ᴮ x) ⊓ (w₁ ∈ᴮ y) := inf_le_left
          _ ≤ Γ ⊓ (z₁ ∈ᴮ x) ⊓ (z₂ ∈ᴮ x) := inf_le_left
          _ ≤ z₂ ∈ᴮ x := inf_le_right)
    have hw₁mem : Γ' ≤ w₁ ∈ᴮ y :=
      hΔ.trans (by
        calc
          _ ≤ Γ ⊓ (z₁ ∈ᴮ x) ⊓ (z₂ ∈ᴮ x) ⊓ (w₁ ∈ᴮ y) ⊓ (w₂ ∈ᴮ y) ⊓ (pair z₁ w₁ ∈ᴮ f) := inf_le_left
          _ ≤ Γ ⊓ (z₁ ∈ᴮ x) ⊓ (z₂ ∈ᴮ x) ⊓ (w₁ ∈ᴮ y) ⊓ (w₂ ∈ᴮ y) := inf_le_left
          _ ≤ Γ ⊓ (z₁ ∈ᴮ x) ⊓ (z₂ ∈ᴮ x) ⊓ (w₁ ∈ᴮ y) := inf_le_left
          _ ≤ w₁ ∈ᴮ y := inf_le_right)
    have hw₂mem : Γ' ≤ w₂ ∈ᴮ y :=
      hΔ.trans (by
        calc
          _ ≤ Γ ⊓ (z₁ ∈ᴮ x) ⊓ (z₂ ∈ᴮ x) ⊓ (w₁ ∈ᴮ y) ⊓ (w₂ ∈ᴮ y) ⊓ (pair z₁ w₁ ∈ᴮ f) := inf_le_left
          _ ≤ Γ ⊓ (z₁ ∈ᴮ x) ⊓ (z₂ ∈ᴮ x) ⊓ (w₁ ∈ᴮ y) ⊓ (w₂ ∈ᴮ y) := inf_le_left
          _ ≤ w₂ ∈ᴮ y := inf_le_right)
    have hpr₁mem : Γ' ≤ pair z₁ w₁ ∈ᴮ f :=
      hΔ.trans (by
        calc
          _ ≤ Γ ⊓ (z₁ ∈ᴮ x) ⊓ (z₂ ∈ᴮ x) ⊓ (w₁ ∈ᴮ y) ⊓ (w₂ ∈ᴮ y) ⊓ (pair z₁ w₁ ∈ᴮ f) := inf_le_left
          _ ≤ pair z₁ w₁ ∈ᴮ f := inf_le_right)
    have hpr₂mem : Γ' ≤ pair z₂ w₂ ∈ᴮ f :=
      hΔ.trans (by
        calc
          _ ≤ pair z₂ w₂ ∈ᴮ f := inf_le_right)
    exact H Γ' hΓ'Γ z₁ hz₁mem z₂ hz₂mem w₁ hw₁mem w₂ hw₂mem hpr₁mem hpr₂mem

/-- Direct unfolding of `strong_eps_hom` at a fixed context level. -/
theorem strong_eps_hom_unfold {x y f : bSet 𝔹} {Γ : 𝔹}
    (h : Γ ≤ strong_eps_hom x y f) (z₁ : bSet 𝔹) (hz₁ : Γ ≤ z₁ ∈ᴮ x)
    (z₂ : bSet 𝔹) (hz₂ : Γ ≤ z₂ ∈ᴮ x) (w₁ : bSet 𝔹) (hw₁ : Γ ≤ w₁ ∈ᴮ y)
    (w₂ : bSet 𝔹) (hw₂ : Γ ≤ w₂ ∈ᴮ y)
    (hpr₁ : Γ ≤ pair z₁ w₁ ∈ᴮ f) (hpr₂ : Γ ≤ pair z₂ w₂ ∈ᴮ f) :
    Γ ≤ z₁ ∈ᴮ z₂ ↔ Γ ≤ w₁ ∈ᴮ w₂ :=
  (strong_eps_hom_iff.mp h) Γ le_rfl z₁ hz₁ z₂ hz₂ w₁ hw₁ w₂ hw₂ hpr₁ hpr₂

/-- `eps_iso` preserves membership from left to right. -/
theorem eps_iso_mem {x y f z₁ z₂ : bSet 𝔹} {Γ : 𝔹}
    (hIso : Γ ≤ eps_iso x y f) (hz₁ : Γ ≤ z₁ ∈ᴮ x) (hz₂ : Γ ≤ z₂ ∈ᴮ x)
    (hzMem : Γ ≤ z₁ ∈ᴮ z₂) (w₁ : bSet 𝔹) (hw₁ : Γ ≤ w₁ ∈ᴮ y)
    (hpr₁ : Γ ≤ pair z₁ w₁ ∈ᴮ f) (w₂ : bSet 𝔹) (hw₂ : Γ ≤ w₂ ∈ᴮ y)
    (hpr₂ : Γ ≤ pair z₂ w₂ ∈ᴮ f) : Γ ≤ w₁ ∈ᴮ w₂ :=
  ((strong_eps_hom_unfold (strong_eps_hom_of_eps_iso hIso)
    z₁ hz₁ z₂ hz₂ w₁ hw₁ w₂ hw₂ hpr₁ hpr₂).mp hzMem)

/-- `eps_iso` preserves membership from right to left. -/
theorem eps_iso_mem' {x y f z₁ z₂ : bSet 𝔹} {Γ : 𝔹}
    (hIso : Γ ≤ eps_iso x y f) (hz₁ : Γ ≤ z₁ ∈ᴮ x) (hz₂ : Γ ≤ z₂ ∈ᴮ x)
    (w₁ : bSet 𝔹) (hw₁ : Γ ≤ w₁ ∈ᴮ y) (hpr₁ : Γ ≤ pair z₁ w₁ ∈ᴮ f)
    (w₂ : bSet 𝔹) (hw₂ : Γ ≤ w₂ ∈ᴮ y) (hpr₂ : Γ ≤ pair z₂ w₂ ∈ᴮ f)
    (hwMem : Γ ≤ w₁ ∈ᴮ w₂) : Γ ≤ z₁ ∈ᴮ z₂ :=
  ((strong_eps_hom_unfold (strong_eps_hom_of_eps_iso hIso)
    z₁ hz₁ z₂ hz₂ w₁ hw₁ w₂ hw₂ hpr₁ hpr₂).mpr hwMem)

/-- `eps_iso` preserves non-membership from left to right. -/
theorem eps_iso_not_mem {x y f z₁ z₂ : bSet 𝔹} {Γ : 𝔹}
    (hIso : Γ ≤ eps_iso x y f) (hz₁ : Γ ≤ z₁ ∈ᴮ x) (hz₂ : Γ ≤ z₂ ∈ᴮ x)
    (hzNotMem : Γ ≤ (z₁ ∈ᴮ z₂)ᶜ) (w₁ : bSet 𝔹) (hw₁ : Γ ≤ w₁ ∈ᴮ y)
    (hpr₁ : Γ ≤ pair z₁ w₁ ∈ᴮ f) (w₂ : bSet 𝔹) (hw₂ : Γ ≤ w₂ ∈ᴮ y)
    (hpr₂ : Γ ≤ pair z₂ w₂ ∈ᴮ f) : Γ ≤ (w₁ ∈ᴮ w₂)ᶜ := by
  rw [le_compl_iff_disjoint_right, disjoint_iff]
  let Δ := Γ ⊓ (w₁ ∈ᴮ w₂)
  apply eq_bot_iff.mpr
  have hSEH : Δ ≤ strong_eps_hom x y f :=
    inf_le_left.trans (strong_eps_hom_of_eps_iso hIso)
  have hEquiv : Δ ≤ z₁ ∈ᴮ z₂ ↔ Δ ≤ w₁ ∈ᴮ w₂ :=
    strong_eps_hom_unfold hSEH z₁ (inf_le_left.trans hz₁) z₂ (inf_le_left.trans hz₂)
      w₁ (inf_le_left.trans hw₁) w₂ (inf_le_left.trans hw₂)
      (inf_le_left.trans hpr₁) (inf_le_left.trans hpr₂)
  have hFwd : Δ ≤ z₁ ∈ᴮ z₂ := hEquiv.mpr inf_le_right
  have hCompl : Δ ≤ (z₁ ∈ᴮ z₂)ᶜ := inf_le_left.trans hzNotMem
  calc
    Δ ≤ (z₁ ∈ᴮ z₂) ⊓ (z₁ ∈ᴮ z₂)ᶜ := le_inf hFwd hCompl
    _ = ⊥ := inf_compl_eq_bot

/-- `eps_iso` preserves non-membership from right to left. -/
theorem eps_iso_not_mem' {x y f z₁ z₂ : bSet 𝔹} {Γ : 𝔹}
    (hIso : Γ ≤ eps_iso x y f) (hz₁ : Γ ≤ z₁ ∈ᴮ x) (hz₂ : Γ ≤ z₂ ∈ᴮ x)
    (w₁ : bSet 𝔹) (hw₁ : Γ ≤ w₁ ∈ᴮ y) (hpr₁ : Γ ≤ pair z₁ w₁ ∈ᴮ f)
    (w₂ : bSet 𝔹) (hw₂ : Γ ≤ w₂ ∈ᴮ y) (hpr₂ : Γ ≤ pair z₂ w₂ ∈ᴮ f)
    (hwNotMem : Γ ≤ (w₁ ∈ᴮ w₂)ᶜ) : Γ ≤ (z₁ ∈ᴮ z₂)ᶜ := by
  rw [le_compl_iff_disjoint_right, disjoint_iff]
  let Δ := Γ ⊓ (z₁ ∈ᴮ z₂)
  apply eq_bot_iff.mpr
  have hSEH : Δ ≤ strong_eps_hom x y f :=
    inf_le_left.trans (strong_eps_hom_of_eps_iso hIso)
  have hEquiv : Δ ≤ z₁ ∈ᴮ z₂ ↔ Δ ≤ w₁ ∈ᴮ w₂ :=
    strong_eps_hom_unfold hSEH z₁ (inf_le_left.trans hz₁) z₂ (inf_le_left.trans hz₂)
      w₁ (inf_le_left.trans hw₁) w₂ (inf_le_left.trans hw₂)
      (inf_le_left.trans hpr₁) (inf_le_left.trans hpr₂)
  have hBwd : Δ ≤ w₁ ∈ᴮ w₂ := hEquiv.mp inf_le_right
  have hCompl : Δ ≤ (w₁ ∈ᴮ w₂)ᶜ := inf_le_left.trans hwNotMem
  calc
    Δ ≤ (w₁ ∈ᴮ w₂) ⊓ (w₁ ∈ᴮ w₂)ᶜ := le_inf hBwd hCompl
    _ = ⊥ := inf_compl_eq_bot

/-- An epsilon-isomorphism between ordinals is injective. -/
theorem eps_iso_inj_of_Ord {x y f : bSet 𝔹} {Γ : 𝔹}
    (hxOrd : Γ ≤ Ord x) (hyOrd : Γ ≤ Ord y) (hIso : Γ ≤ eps_iso x y f) :
    Γ ≤ is_inj f := by
  unfold is_inj
  apply le_iInf; intro w₁; apply le_iInf; intro w₂
  apply le_iInf; intro v₁; apply le_iInf; intro v₂
  apply lattice.bv_imp_intro
  let Δ : 𝔹 := Γ ⊓ (pair w₁ v₁ ∈ᴮ f ⊓ pair w₂ v₂ ∈ᴮ f ⊓ v₁ =ᴮ v₂)
  change Δ ≤ w₁ =ᴮ w₂
  have hFunc : Δ ≤ is_function x y f :=
    inf_le_left.trans (is_function_of_eps_iso hIso)
  have hMem₁ : Δ ≤ pair w₁ v₁ ∈ᴮ f :=
    (by dsimp [Δ]; exact inf_le_right.trans inf_le_left |>.trans inf_le_left)
  have hMem₂ : Δ ≤ pair w₂ v₂ ∈ᴮ f :=
    (by dsimp [Δ]; exact inf_le_right.trans inf_le_left |>.trans inf_le_right)
  have hvEq : Δ ≤ v₁ =ᴮ v₂ :=
    (by dsimp [Δ]; exact inf_le_right.trans inf_le_right)
  have hw₁Mem : Δ ≤ w₁ ∈ᴮ x := mem_domain_of_is_function hMem₁ hFunc
  have hw₂Mem : Δ ≤ w₂ ∈ᴮ x := mem_domain_of_is_function hMem₂ hFunc
  have hv₁Mem : Δ ≤ v₁ ∈ᴮ y := mem_codomain_of_is_function hMem₁ hFunc
  have hv₂Mem : Δ ≤ v₂ ∈ᴮ y := mem_codomain_of_is_function hMem₂ hFunc
  have hw₁Ord : Δ ≤ Ord w₁ :=
    Ord_of_mem_Ord hw₁Mem (inf_le_left.trans hxOrd)
  have hw₂Ord : Δ ≤ Ord w₂ :=
    Ord_of_mem_Ord hw₂Mem (inf_le_left.trans hxOrd)
  have hv₁Ord : Δ ≤ Ord v₁ :=
    Ord_of_mem_Ord hv₁Mem (inf_le_left.trans hyOrd)
  have hv₂Ord : Δ ≤ Ord v₂ :=
    Ord_of_mem_Ord hv₂Mem (inf_le_left.trans hyOrd)
  -- From v₁ = v₂ and ordinality, v₁ ∉ v₂ and v₂ ∉ v₁
  have hvEqParts := (Ord.eq_iff_not_mem hv₁Ord hv₂Ord).mp hvEq
  -- Combine with eps_iso_not_mem' to get w₁ ∉ w₂ and w₂ ∉ w₁
  have hNotMem₁ : Δ ≤ (w₁ ∈ᴮ w₂)ᶜ :=
    eps_iso_not_mem' (inf_le_left.trans hIso) hw₁Mem hw₂Mem
      v₁ hv₁Mem hMem₁ v₂ hv₂Mem hMem₂ hvEqParts.1
  have hNotMem₂ : Δ ≤ (w₂ ∈ᴮ w₁)ᶜ :=
    eps_iso_not_mem' (inf_le_left.trans hIso) hw₂Mem hw₁Mem
      v₂ hv₂Mem hMem₂ v₁ hv₁Mem hMem₁ hvEqParts.2
  -- Ord.eq_iff_not_mem gives equality from mutual non-membership
  exact (Ord.eq_of_not_mem hw₁Ord hw₂Ord hNotMem₁ hNotMem₂)

/-- The inverse of an epsilon-isomorphism, defined via `inj_inverse`. -/
def eps_iso_inv {x y f : bSet 𝔹} {Γ : 𝔹}
    (hxOrd : Γ ≤ Ord x) (hyOrd : Γ ≤ Ord y) (hIso : Γ ≤ eps_iso x y f) :
    bSet 𝔹 :=
  inj_inverse
    (is_func'_of_is_function (is_function_of_eps_iso hIso))
    (eps_iso_inj_of_Ord hxOrd hyOrd hIso)

theorem eps_iso_inv_is_surj {x y f : bSet 𝔹} {Γ : 𝔹}
    (hxOrd : Γ ≤ Ord x) (hyOrd : Γ ≤ Ord y) (hIso : Γ ≤ eps_iso x y f) :
    Γ ≤ is_surj y x (eps_iso_inv hxOrd hyOrd hIso) := by
  let hFunc' : Γ ≤ is_func' x y f :=
    is_func'_of_is_function (is_function_of_eps_iso hIso)
  let hInj' : Γ ≤ is_inj f := eps_iso_inj_of_Ord hxOrd hyOrd hIso
  have hSurj : Γ ≤ is_surj x y f := is_surj_of_eps_iso hIso
  have hEq : Γ ≤ image x y f =ᴮ y := image_eq_codomain_of_surj hSurj
  dsimp [eps_iso_inv]
  have hInvSurj : Γ ≤ is_surj (image x y f) x (inj_inverse hFunc' hInj') :=
    inj_inverse_is_surj hFunc' hInj'
  -- Use inf_iSup distributivity to rewrite the domain from image to y
  unfold is_surj
  apply le_iInf; intro v
  apply lattice.bv_imp_intro
  let Δ := Γ ⊓ (v ∈ᴮ x)
  -- From hInvSurj, peel at v to get Γ ≤ imp (v∈x) (⨆ w, w∈image ∧ pair w v ∈ inv)
  have h_imp : Γ ≤ lattice.imp (v ∈ᴮ x)
      (⨆ w : bSet 𝔹, w ∈ᴮ (image x y f) ⊓ pair w v ∈ᴮ (inj_inverse hFunc' hInj')) :=
    hInvSurj.trans (iInf_le _ v)
  -- Apply at context Δ = Γ ⊓ (v ∈ᴮ x)
  have hV : Δ ≤ ⨆ i : bSet 𝔹, i ∈ᴮ (image x y f) ⊓ pair i v ∈ᴮ (inj_inverse hFunc' hInj') :=
    lattice.bv_context_apply (inf_le_left.trans h_imp) inf_le_right
  have hEqΔ : Δ ≤ image x y f =ᴮ y := inf_le_left.trans hEq
  -- For each w, Δ ⊓ w ∈ image ≤ w ∈ y via subst_congr_mem_right
  have hStep (i : bSet 𝔹) : Δ ⊓ i ∈ᴮ (image x y f) ⊓ pair i v ∈ᴮ (inj_inverse hFunc' hInj') ≤
      i ∈ᴮ y ⊓ pair i v ∈ᴮ (inj_inverse hFunc' hInj') := by
    have hmem : Δ ⊓ i ∈ᴮ (image x y f) ≤ i ∈ᴮ y :=
      calc
        Δ ⊓ i ∈ᴮ (image x y f) ≤ (image x y f =ᴮ y) ⊓ i ∈ᴮ (image x y f) :=
          inf_le_inf hEqΔ (le_refl _)
        _ ≤ i ∈ᴮ y := subst_congr_mem_right
    exact inf_le_inf hmem (le_refl _)
  have hSup : (⨆ i : bSet 𝔹, Δ ⊓ i ∈ᴮ (image x y f) ⊓ pair i v ∈ᴮ (inj_inverse hFunc' hInj')) ≤
      (⨆ i : bSet 𝔹, i ∈ᴮ y ⊓ pair i v ∈ᴮ (inj_inverse hFunc' hInj')) :=
    iSup_mono hStep
  have hDistrib : Δ ⊓ (⨆ i : bSet 𝔹, i ∈ᴮ (image x y f) ⊓ pair i v ∈ᴮ (inj_inverse hFunc' hInj'))
      = ⨆ i : bSet 𝔹, Δ ⊓ i ∈ᴮ (image x y f) ⊓ pair i v ∈ᴮ (inj_inverse hFunc' hInj') := by
    simpa [inf_assoc] using inf_iSup_eq Δ (fun (i : bSet 𝔹) => i ∈ᴮ (image x y f) ⊓ pair i v ∈ᴮ (inj_inverse hFunc' hInj'))
  have hStep1 : Δ ≤ Δ ⊓ (⨆ i : bSet 𝔹, i ∈ᴮ (image x y f) ⊓ pair i v ∈ᴮ (inj_inverse hFunc' hInj')) :=
    le_inf (le_refl _) hV
  calc
    Δ ≤ Δ ⊓ (⨆ i : bSet 𝔹, i ∈ᴮ (image x y f) ⊓ pair i v ∈ᴮ (inj_inverse hFunc' hInj')) := hStep1
    _ = ⨆ i : bSet 𝔹, Δ ⊓ i ∈ᴮ (image x y f) ⊓ pair i v ∈ᴮ (inj_inverse hFunc' hInj') := hDistrib
    _ ≤ ⨆ i : bSet 𝔹, i ∈ᴮ y ⊓ pair i v ∈ᴮ (inj_inverse hFunc' hInj') := hSup

theorem eps_iso_inv_is_function {x y f : bSet 𝔹} {Γ : 𝔹}
    (hxOrd : Γ ≤ Ord x) (hyOrd : Γ ≤ Ord y) (hIso : Γ ≤ eps_iso x y f) :
    Γ ≤ is_function y x (eps_iso_inv hxOrd hyOrd hIso) := by
  let hFunc' : Γ ≤ is_func' x y f :=
    is_func'_of_is_function (is_function_of_eps_iso hIso)
  let hInj' : Γ ≤ is_inj f := eps_iso_inj_of_Ord hxOrd hyOrd hIso
  have hSurj : Γ ≤ is_surj x y f := is_surj_of_eps_iso hIso
  have hEqImY : Γ ≤ image x y f =ᴮ y := image_eq_codomain_of_surj hSurj
  dsimp [eps_iso_inv]
  have hInvFunc : Γ ≤ is_function (image x y f) x (inj_inverse hFunc' hInj') :=
    inj_inverse_is_function hFunc' hInj'
  -- Build B_ext proof for is_function in its domain argument
  have hB_is_total : B_ext (fun (z : bSet 𝔹) => is_total z x (inj_inverse hFunc' hInj')) := by
    unfold is_total
    apply B_ext_iInf; intro v
    apply B_ext_imp
    · exact B_ext_mem_right v
    · apply B_ext_const
  have hB_is_func' : B_ext (fun (z : bSet 𝔹) => is_func' z x (inj_inverse hFunc' hInj')) :=
    B_ext_inf (B_ext_const _) hB_is_total
  have hB_subset : B_ext (fun (z : bSet 𝔹) => (inj_inverse hFunc' hInj') ⊆ᴮ prod z x) :=
    B_ext_prod_left (B_ext_subset_right (inj_inverse hFunc' hInj')) x
  have hB_func : B_ext (fun (z : bSet 𝔹) => is_function z x (inj_inverse hFunc' hInj')) :=
    B_ext_inf hB_is_func' hB_subset
  -- Γ ≤ (image =ᴮ y) ⊓ φ(image) ≤ φ(y)
  exact (le_inf hEqImY hInvFunc).trans (hB_func (image x y f) y)

/-- The inverse of an eps_iso is also an eps_iso (for ordinals). -/
theorem eps_iso_eps_iso_inv {x y f : bSet 𝔹} {Γ : 𝔹}
    (hxOrd : Γ ≤ Ord x) (hyOrd : Γ ≤ Ord y) (hIso : Γ ≤ eps_iso x y f) :
    Γ ≤ eps_iso y x (eps_iso_inv hxOrd hyOrd hIso) := by
  apply le_inf
  · apply le_inf
    · exact eps_iso_inv_is_function hxOrd hyOrd hIso
    · apply (strong_eps_hom_iff (x := y) (y := x)
        (f := eps_iso_inv hxOrd hyOrd hIso)).mpr
      intro Γ' hLe
      intro z₁ hz₁  -- Γ' ≤ z₁ ∈ᴮ y  (eps_iso_inv domain is y)
      intro z₂ hz₂
      intro w₁ hw₁  -- Γ' ≤ w₁ ∈ᴮ x  (eps_iso_inv codomain is x)
      intro w₂ hw₂ hpr₁ hpr₂
      have hFunc' : Γ ≤ is_func' x y f :=
        is_func'_of_is_function (is_function_of_eps_iso hIso)
      have hInj' : Γ ≤ is_inj f :=
        eps_iso_inj_of_Ord hxOrd hyOrd hIso
      -- mem_inj_inverse_components: pair b a ∈ inv → a ∈ x ∧ b ∈ y ∧ pair a b ∈ f
      -- For pair z₁ w₁ ∈ inv: b=z₁, a=w₁ → w₁∈x, z₁∈y, pair w₁ z₁∈f
      have hInv₁ := mem_inj_inverse_components (hFunc := hFunc') (hInj := hInj')
        (by simpa [eps_iso_inv] using hpr₁)
      have hInv₂ := mem_inj_inverse_components (hFunc := hFunc') (hInj := hInj')
        (by simpa [eps_iso_inv] using hpr₂)
      have hSEH : Γ' ≤ strong_eps_hom x y f :=
        hLe.trans (strong_eps_hom_of_eps_iso hIso)
      -- strong_eps_hom_unfold on x y f, swapping z/w roles to match eps_iso_inv:
      --   z roles filled by w₁,w₂ (∈ x), w roles filled by z₁,z₂ (∈ y)
      --   pairs are pair w₁ z₁ ∈ f, pair w₂ z₂ ∈ f (swapped by inv)
      -- Result: (w₁ ∈ w₂) ↔ (z₁ ∈ z₂); symm gives (z₁ ∈ z₂) ↔ (w₁ ∈ w₂)
      exact ((strong_eps_hom_unfold hSEH
        w₁ hInv₁.1 w₂ hInv₂.1
        z₁ hInv₁.2.1 z₂ hInv₂.2.1
        hInv₁.2.2 hInv₂.2.2).symm)
  · exact eps_iso_inv_is_surj hxOrd hyOrd hIso

/-- B_ext for `Ord`. -/
theorem B_ext_Ord' : B_ext (Ord : bSet 𝔹 → 𝔹) :=
  B_ext_Ord

/-!
## Mixing lemma and maximum principle
-/

/-- Mix names with antichain weights. -/
def mixture {ι : Type u} (a : ι → 𝔹) (u : ι → bSet 𝔹) : bSet 𝔹 :=
  bSet.mk (Σ(i : ι), (u i).type) (fun x => (u x.fst).func x.snd)
    (fun x => ⨆(j:ι), a j ⊓ ((u x.fst).func x.snd) ∈ᴮ u j)

@[simp] lemma mixture_bval {ι : Type u} {a : ι → 𝔹} {u : ι → bSet 𝔹} :
    (mixture a u).bval = fun x => ⨆(j:ι), a j ⊓ ((u x.fst).func x.snd) ∈ᴮ u j := rfl

lemma mixing_lemma' {ι : Type u} (a : ι → 𝔹) (τ : ι → bSet 𝔹)
    (h_star : ∀ i j : ι, a i ⊓ a j ≤ τ i =ᴮ τ j) :
    ∀ i : ι, a i ≤ (mixture a τ) =ᴮ τ i := by
  intro i
  rw [bv_eq_unfold]
  apply le_inf
  · -- show a i ≤ (mixture a τ) ⊆ᴮ τ i
    have hsub := subset_unfold (x := mixture a τ) (y := τ i)
    have hgoal :
        a i ≤ ⨅ p : (mixture a τ).type,
          lattice.imp ((mixture a τ).bval p) ((mixture a τ).func p ∈ᴮ τ i) := by
      apply le_iInf
      intro p
      rw [lattice.le_imp_iff]
      cases p with
      | mk k z =>
          change a i ⊓ (⨆ j : ι, a j ⊓ (τ k).func z ∈ᴮ τ j) ≤
            (τ k).func z ∈ᴮ τ i
          apply lattice.bv_cases_right
          intro j
          let Δ : 𝔹 := a i ⊓ (a j ⊓ (τ k).func z ∈ᴮ τ j)
          change Δ ≤ (τ k).func z ∈ᴮ τ i
          have hEq : Δ ≤ τ j =ᴮ τ i := by
            apply bv_symm
            exact (le_inf inf_le_left (inf_le_right.trans inf_le_left)).trans (h_star i j)
          have hMem : Δ ≤ (τ k).func z ∈ᴮ τ j := by
            dsimp [Δ]
            exact inf_le_right.trans inf_le_right
          exact subst_congr_mem_right' hEq hMem
    simpa [hsub] using hgoal
  · -- show a i ≤ τ i ⊆ᴮ (mixture a τ)
    have hsub := subset_unfold (x := τ i) (y := mixture a τ)
    have hgoal : a i ≤ ⨅ i_z : (τ i).type, lattice.imp ((τ i).bval i_z) ((τ i).func i_z ∈ᴮ (mixture a τ)) := by
      apply le_iInf
      intro i_z
      -- Goal: a i ≤ lattice.imp ((τ i).bval i_z) ((τ i).func i_z ∈ᴮ (mixture a τ))
      rw [lattice.le_imp_iff]
      -- Goal: a i ⊓ (τ i).bval i_z ≤ (τ i).func i_z ∈ᴮ (mixture a τ)
      have h1 : a i ⊓ (τ i).bval i_z ≤ a i ⊓ ((τ i).func i_z ∈ᴮ τ i) :=
        inf_le_inf le_rfl (mem.mk' (τ i) i_z)
      have h2 : a i ⊓ ((τ i).func i_z ∈ᴮ τ i) ≤ ⨆ (j : ι), a j ⊓ (τ i).func i_z ∈ᴮ τ j :=
        le_iSup_of_le i le_rfl
      have h3 : ⨆ (j : ι), a j ⊓ (τ i).func i_z ∈ᴮ τ j = (mixture a τ).bval (Sigma.mk i i_z) := by
        simp [mixture, bSet.bval]
      have h4 : (mixture a τ).bval (Sigma.mk i i_z) ≤ (τ i).func i_z ∈ᴮ (mixture a τ) := by
        rw [bSet.mem_unfold]
        have h_func : (mixture a τ).func (Sigma.mk i i_z) = (τ i).func i_z := by
          simp [mixture, bSet.func]
        have h_term_eq : (mixture a τ).bval (Sigma.mk i i_z) ⊓ (τ i).func i_z =ᴮ (mixture a τ).func (Sigma.mk i i_z)
            = (mixture a τ).bval (Sigma.mk i i_z) := by
          simp [h_func, bv_eq_refl, inf_top_eq]
        rw [← h_term_eq]
        exact le_iSup (fun p => (mixture a τ).bval p ⊓ (τ i).func i_z =ᴮ (mixture a τ).func p) (Sigma.mk i i_z)
      exact h1.trans (h2.trans (h3.le.trans h4))
    simpa [hsub] using hgoal

lemma mixing_lemma {ι : Type u} (a : ι → 𝔹) (τ : ι → bSet 𝔹)
    (h_star : ∀ i j : ι, a i ⊓ a j ≤ τ i =ᴮ τ j) :
    ∃ x, ∀ i : ι, a i ≤ x =ᴮ τ i :=
  ⟨mixture a τ, mixing_lemma' a τ h_star⟩

section maximum_principle
variable {ϕ : bSet 𝔹 → 𝔹}

noncomputable def fiber_lift (ϕ : bSet 𝔹 → 𝔹) (b : Subtype (ϕ '' Set.univ)) : {a : bSet 𝔹 // ϕ a = b.val} := by
  let hprop : b.val ∈ ϕ '' Set.univ := b.property
  have hmem := (Set.mem_image ϕ Set.univ (b.val)).mp hprop
  let w := Classical.choose hmem
  have hw_spec : ϕ w = b.val := by
    have := Classical.choose_spec hmem
    exact this.2
  exact ⟨w, hw_spec⟩

noncomputable def B_small_witness (ϕ : bSet 𝔹 → 𝔹) : bSet 𝔹 :=
  bSet.mk (Subtype (ϕ '' Set.univ)) (fun b => (fiber_lift ϕ b).val) (fun _ => ⊤)

@[simp] lemma B_small_witness_spec (ϕ : bSet 𝔹 → 𝔹) : ∀ b, ϕ ((B_small_witness ϕ : bSet 𝔹).func b) = b.val := by
  intro b
  dsimp [B_small_witness, fiber_lift]
  exact (fiber_lift ϕ b).property

lemma B_small_witness_supr (ϕ : bSet 𝔹 → 𝔹) : (⨆(x : bSet 𝔹), ϕ x) =
    ⨆(b : (B_small_witness ϕ : bSet 𝔹).type), ϕ ((B_small_witness ϕ).func b) := by
  apply le_antisymm
  · apply iSup_le; intro x
    let b : Subtype (ϕ '' Set.univ) := ⟨ϕ x, Set.mem_image_of_mem ϕ (Set.mem_univ x)⟩
    -- (B_small_witness ϕ).func b equals (fiber_lift ϕ b).val
    -- (fiber_lift ϕ b).property: ϕ ((fiber_lift ϕ b).val) = b.val
    -- b.val = ϕ x by definition
    have h_eq_val : ϕ ((B_small_witness ϕ).func b) = ϕ x := by
      calc
        ϕ ((B_small_witness ϕ).func b) = ϕ ((fiber_lift ϕ b).val) := by
          simp [B_small_witness, bSet.func]
        _ = b.val := (fiber_lift ϕ b).property
        _ = ϕ x := rfl
    -- Now use h_eq_val to rewrite the goal
    simpa [h_eq_val] using le_iSup (fun (b' : (B_small_witness ϕ : bSet 𝔹).type) => ϕ ((B_small_witness ϕ).func b')) b
  · apply iSup_le; intro b
    -- (B_small_witness ϕ).func b is already a bSet 𝔹, use le_iSup directly
    simpa using le_iSup (fun (x : bSet 𝔹) => ϕ x) ((B_small_witness ϕ).func b)


lemma maximum_principle (ϕ : bSet 𝔹 → 𝔹) (h_congr : B_ext ϕ) :
    ∃ u, (⨆(x:bSet 𝔹), ϕ x) = ϕ u := by
  classical
  let w := B_small_witness (ϕ := ϕ)
  have h_well : ∃ (r : w.type → w.type → Prop), IsWellOrder w.type r := by
    rcases exists_wellOrder w.type with ⟨hLT⟩
    refine ⟨(· < ·), ?_⟩
    infer_instance
  rcases h_well with ⟨r, hr⟩
  haveI : IsWellOrder w.type r := hr
  let witness_antichain : w.type → 𝔹 :=
    fun b => b.val \ (⨆ (b' : {x // r x b}), b'.val.val)
  have witness_antichain_index : ∀ i j : w.type, i ≠ j → witness_antichain i ⊓ witness_antichain j = ⊥ := by
    intro i j h_ne
    dsimp [witness_antichain]
    rw [sdiff_eq, sdiff_eq]
    rw [compl_iSup, compl_iSup]
    -- Goal: (i.val ⊓ ⨅ b', (b'.val.val)ᶜ) ⊓ (j.val ⊓ ⨅ b', (b'.val.val)ᶜ) = ⊥
    -- The trichotomy of the well-order r gives r i j or i = j or r j i
    have h_trich := trichotomous (r := r) i j
    rcases h_trich with (h_ij | heq | h_ji)
    · -- r i j: use the inf for i's complement from the right factor
      have hi_mem : (⨅ (b' : {x // r x j}), (b'.val.val)ᶜ) ≤ (i.val)ᶜ :=
        iInf_le_of_le ⟨i, h_ij⟩ le_rfl
      have h_le : (i.val ⊓ ⨅ (b' : {x // r x i}), (b'.val.val)ᶜ) ⊓ (j.val ⊓ ⨅ (b' : {x // r x j}), (b'.val.val)ᶜ) ≤ ⊥ := by
        calc
          (i.val ⊓ ⨅ (b' : {x // r x i}), (b'.val.val)ᶜ) ⊓ (j.val ⊓ ⨅ (b' : {x // r x j}), (b'.val.val)ᶜ)
              ≤ i.val ⊓ (⨅ (b' : {x // r x j}), (b'.val.val)ᶜ) := by
            have h₁ : (i.val ⊓ ⨅ (b' : {x // r x i}), (b'.val.val)ᶜ) ⊓
                      (j.val ⊓ ⨅ (b' : {x // r x j}), (b'.val.val)ᶜ) ≤ i.val :=
              (inf_le_left (a := i.val ⊓ ⨅ (b' : {x // r x i}), (b'.val.val)ᶜ)
                (b := j.val ⊓ ⨅ (b' : {x // r x j}), (b'.val.val)ᶜ)).trans inf_le_left
            have h₂ : (i.val ⊓ ⨅ (b' : {x // r x i}), (b'.val.val)ᶜ) ⊓
                      (j.val ⊓ ⨅ (b' : {x // r x j}), (b'.val.val)ᶜ) ≤
                      ⨅ (b' : {x // r x j}), (b'.val.val)ᶜ :=
              (inf_le_right (a := i.val ⊓ ⨅ (b' : {x // r x i}), (b'.val.val)ᶜ)
                (b := j.val ⊓ ⨅ (b' : {x // r x j}), (b'.val.val)ᶜ)).trans inf_le_right
            exact le_inf h₁ h₂
          _ ≤ i.val ⊓ (i.val)ᶜ := inf_le_inf le_rfl hi_mem
          _ = ⊥ := by simp
      exact le_antisymm h_le bot_le
    · -- i = j case, contradicting h_ne
      exact absurd heq h_ne
    · -- r j i: use the inf for j's complement from the left factor
      have hj_mem : (⨅ (b' : {x // r x i}), (b'.val.val)ᶜ) ≤ (j.val)ᶜ :=
        iInf_le_of_le ⟨j, h_ji⟩ le_rfl
      have h_le : (i.val ⊓ ⨅ (b' : {x // r x i}), (b'.val.val)ᶜ) ⊓ (j.val ⊓ ⨅ (b' : {x // r x j}), (b'.val.val)ᶜ) ≤ ⊥ := by
        calc
          (i.val ⊓ ⨅ (b' : {x // r x i}), (b'.val.val)ᶜ) ⊓ (j.val ⊓ ⨅ (b' : {x // r x j}), (b'.val.val)ᶜ)
              ≤ (⨅ (b' : {x // r x i}), (b'.val.val)ᶜ) ⊓ j.val := by
            have h₁ : (i.val ⊓ ⨅ (b' : {x // r x i}), (b'.val.val)ᶜ) ⊓
                      (j.val ⊓ ⨅ (b' : {x // r x j}), (b'.val.val)ᶜ) ≤
                      ⨅ (b' : {x // r x i}), (b'.val.val)ᶜ :=
              (inf_le_left (a := i.val ⊓ ⨅ (b' : {x // r x i}), (b'.val.val)ᶜ)
                (b := j.val ⊓ ⨅ (b' : {x // r x j}), (b'.val.val)ᶜ)).trans inf_le_right
            have h₂ : (i.val ⊓ ⨅ (b' : {x // r x i}), (b'.val.val)ᶜ) ⊓
                      (j.val ⊓ ⨅ (b' : {x // r x j}), (b'.val.val)ᶜ) ≤ j.val :=
              (inf_le_right (a := i.val ⊓ ⨅ (b' : {x // r x i}), (b'.val.val)ᶜ)
                (b := j.val ⊓ ⨅ (b' : {x // r x j}), (b'.val.val)ᶜ)).trans inf_le_left
            exact le_inf h₁ h₂
          _ ≤ (j.val)ᶜ ⊓ j.val := inf_le_inf hj_mem le_rfl
          _ = ⊥ := by simp
      exact le_antisymm h_le bot_le
  have witness_antichain_property : ∀ b : w.type, witness_antichain b ≤ b.val := by
    intro b; dsimp [witness_antichain]; exact sdiff_le
  have h_star : ∀ i j : w.type, witness_antichain i ⊓ witness_antichain j ≤
      (w.func i) =ᴮ (w.func j) := by
    intro i j
    by_cases h_eq : i = j
    · subst h_eq; simp
    · have h_bot := witness_antichain_index i j h_eq
      rw [h_bot]; exact bot_le
  rcases mixing_lemma witness_antichain w.func h_star with ⟨u, Hu⟩
  refine ⟨u, ?_⟩
  apply le_antisymm
  · have hCoverPoint : ∀ i : w.type, i.val ≤ ⨆ b : w.type, witness_antichain b := by
      intro i
      refine WellFounded.induction
        (C := fun i : w.type => i.val ≤ ⨆ b : w.type, witness_antichain b)
        (IsWellFounded.wf (r := r)) i ?_
      intro i ih
      let predSup : 𝔹 := ⨆ j : {x // r x i}, j.val.val
      have hSplit : i.val ≤ witness_antichain i ⊔ predSup := by
        dsimp [witness_antichain, predSup]
        rw [sdiff_eq]
        calc
          i.val = i.val ⊓ predSup ⊔ i.val ⊓ predSupᶜ := (sup_inf_inf_compl (x := i.val) (y := predSup)).symm
          _ ≤ (i.val ⊓ predSupᶜ) ⊔ predSup := by
            apply sup_le
            · exact inf_le_right.trans le_sup_right
            · exact le_sup_left
      have hPred : predSup ≤ ⨆ b : w.type, witness_antichain b := by
        dsimp [predSup]
        apply iSup_le
        intro j
        exact ih j.val j.property
      exact hSplit.trans (sup_le (le_iSup (fun b : w.type => witness_antichain b) i) hPred)
    have hCover : (⨆ b : w.type, b.val) ≤ ⨆ b : w.type, witness_antichain b := by
      apply iSup_le
      intro b
      exact hCoverPoint b
    have hAntichainLe : (⨆ b : w.type, witness_antichain b) ≤ ϕ u := by
      apply iSup_le
      intro b
      have hVal : witness_antichain b ≤ ϕ (w.func b) := by
        simpa [w, B_small_witness_spec] using witness_antichain_property b
      have hCtx : witness_antichain b ≤ (w.func b =ᴮ u) ⊓ ϕ (w.func b) :=
        le_inf (bv_symm (Hu b)) hVal
      exact hCtx.trans (h_congr (w.func b) u)
    rw [B_small_witness_supr]
    have hCoverPhi : (⨆ b : w.type, ϕ (w.func b)) ≤ ⨆ b : w.type, witness_antichain b := by
      simpa [w, B_small_witness_spec] using hCover
    exact hCoverPhi.trans hAntichainLe
  · apply le_iSup

lemma exists_convert {ϕ : bSet 𝔹 → 𝔹} {Γ : 𝔹} (H : Γ ≤ ⨆x, ϕ x) (H_congr : B_ext ϕ) :
    ∃ u, Γ ≤ ϕ u := by
  classical
  rcases maximum_principle ϕ H_congr with ⟨u, hu⟩
  refine ⟨u, ?_⟩
  rw [← hu]; exact H

end maximum_principle

/-!
## Exists mem and related lemmas
-/

@[reducible] def exists_mem (x : bSet 𝔹) : 𝔹 := ⨆ (y : bSet 𝔹), y ∈ᴮ x

@[simp] lemma check_exists_mem {y : pSet} (H_exists_mem : ∃ z, z ∈ y) {Γ : 𝔹} : Γ ≤ exists_mem (check y : bSet 𝔹) := by
  rcases H_exists_mem with ⟨z, Hz⟩
  apply lattice.bv_use (check z)
  simpa using check_mem Hz

/-!
## Natural numbers in bSet
-/

@[reducible] def of_nat : ℕ → bSet 𝔹 := fun n => (PSet.ofNat n)̌

lemma of_nat_omega_definite {n : ℕ} {Γ : 𝔹} : Γ ≤ of_nat n ∈ᴮ omega := by
  simpa [of_nat] using omega_definite (n := n)

lemma of_nat_mem_omega {n : ℕ} {Γ : 𝔹} : Γ ≤ of_nat n ∈ᴮ omega := of_nat_omega_definite

/-!
## B_ext lemmas for is_function and is_surj
-/

@[simp] lemma B_ext_is_function_left {y f : bSet 𝔹} : B_ext (fun x => is_function x y f) := by
  unfold is_function
  apply B_ext_inf
  · -- B_ext (fun x => is_func' x y f)
    unfold is_func'
    apply B_ext_inf
    · -- B_ext (fun x => is_func f) → constant in x
      exact B_ext_const (is_func f)
    · -- B_ext (fun x => is_total x y f)
      unfold is_total
      apply B_ext_iInf; intro w₁
      apply B_ext_imp
      · -- B_ext (fun x => w₁ ∈ᴮ x)
        exact B_ext_mem_right w₁
      · apply B_ext_iSup; intro w₂
        apply B_ext_inf
        · exact B_ext_const (w₂ ∈ᴮ y)
        · exact B_ext_const (pair w₁ w₂ ∈ᴮ f)
  · -- B_ext (fun x => f ⊆ᴮ prod x y)
    exact B_ext_prod_left (B_ext_subset_right f) y

@[simp] lemma B_ext_is_surj_right {x y : bSet 𝔹} : B_ext (fun f => is_surj x y f) := by
  unfold is_surj
  apply B_ext_iInf; intro v
  apply B_ext_imp
  · exact B_ext_const (v ∈ᴮ y)
  · apply B_ext_iSup; intro w
    apply B_ext_inf
    · exact B_ext_const (w ∈ᴮ x)
    · exact B_ext_mem_right (pair w v)

@[simp] lemma B_ext_strong_eps_hom_right {x y : bSet 𝔹} : B_ext (fun f => strong_eps_hom x y f) := by
  unfold strong_eps_hom
  apply B_ext_iInf; intro z₁
  apply B_ext_imp
  · exact B_ext_const (z₁ ∈ᴮ x)
  · apply B_ext_iInf; intro z₂
    apply B_ext_imp
    · exact B_ext_const (z₂ ∈ᴮ x)
    · apply B_ext_iInf; intro w₁
      apply B_ext_imp
      · exact B_ext_const (w₁ ∈ᴮ y)
      · apply B_ext_iInf; intro w₂
        apply B_ext_imp
        · exact B_ext_const (w₂ ∈ᴮ y)
        · apply B_ext_imp
          · exact B_ext_mem_right (pair z₁ w₁)
          · apply B_ext_imp
            · exact B_ext_mem_right (pair z₂ w₂)
            · exact B_ext_const _

@[simp] lemma B_ext_larger_than_right {y : bSet 𝔹} : B_ext (fun z => larger_than y z) := by
  unfold larger_than
  apply B_ext_iSup; intro S
  apply B_ext_iSup; intro f
  -- Goal: B_ext (fun z => (S ⊆ᴮ y ⊓ is_func' S z f) ⊓ is_surj S z f)
  -- Note: ⊓ is left-associative
  apply B_ext_inf
  · -- B_ext (fun z => S ⊆ᴮ y ⊓ is_func' S z f)
    apply B_ext_inf
    · -- B_ext (fun z => S ⊆ᴮ y) -- constant in z
      exact B_ext_const (S ⊆ᴮ y)
    · -- B_ext (fun z => is_func' S z f)
      unfold is_func'
      apply B_ext_inf
      · exact B_ext_const (is_func f)
      · -- B_ext (fun z => is_total S z f)
        unfold is_total
        apply B_ext_iInf; intro w₁
        apply B_ext_imp
        · exact B_ext_const (w₁ ∈ᴮ S)
        · apply B_ext_iSup; intro w₂
          apply B_ext_inf
          · exact B_ext_mem_right w₂
          · exact B_ext_const (pair w₁ w₂ ∈ᴮ f)
  · -- B_ext (fun z => is_surj S z f)
    unfold is_surj
    apply B_ext_iInf; intro v
    apply B_ext_imp
    · exact B_ext_mem_right v
    · apply B_ext_iSup; intro w
      apply B_ext_inf
      · exact B_ext_const (w ∈ᴮ S)
      · exact B_ext_const (pair w v ∈ᴮ f)

@[simp] lemma B_ext_larger_than_left {y : bSet 𝔹} : B_ext (fun z => larger_than z y) := by
  unfold larger_than
  apply B_ext_iSup; intro S
  apply B_ext_iSup; intro f
  -- Goal: B_ext (fun z => (S ⊆ᴮ z ⊓ is_func' S y f) ⊓ is_surj S y f)
  -- Note: ⊓ is left-associative
  apply B_ext_inf
  · -- B_ext (fun z => S ⊆ᴮ z ⊓ is_func' S y f)
    apply B_ext_inf
    · -- B_ext (fun z => S ⊆ᴮ z)
      exact B_ext_subset_right S
    · -- B_ext (fun z => is_func' S y f) -- constant in z
      exact B_ext_const (is_func' S y f)
  · -- B_ext (fun z => is_surj S y f) -- constant in z
    exact B_ext_const (is_surj S y f)

@[simp] lemma B_ext_injects_into_left {y : bSet 𝔹} : B_ext (fun z => injects_into z y) := by
  unfold injects_into
  apply B_ext_iSup; intro f
  apply B_ext_inf
  · -- B_ext (fun z => is_func' z y f)
    unfold is_func'
    apply B_ext_inf
    · exact B_ext_const (is_func f)
    · -- B_ext (fun z => is_total z y f)
      unfold is_total
      apply B_ext_iInf; intro w₁
      apply B_ext_imp
      · exact B_ext_mem_right w₁
      · apply B_ext_iSup; intro w₂
        apply B_ext_inf
        · exact B_ext_const (w₂ ∈ᴮ y)
        · exact B_ext_const (pair w₁ w₂ ∈ᴮ f)
  · exact B_ext_const (is_inj f)

@[simp] lemma B_ext_injects_into_right {y : bSet 𝔹} : B_ext (fun z => injects_into y z) := by
  unfold injects_into
  apply B_ext_iSup; intro f
  apply B_ext_inf
  · -- B_ext (fun z => is_func' y z f)
    unfold is_func'
    apply B_ext_inf
    · exact B_ext_const (is_func f)
    · -- B_ext (fun z => is_total y z f)
      unfold is_total
      apply B_ext_iInf; intro w₁
      apply B_ext_imp
      · exact B_ext_const (w₁ ∈ᴮ y)
      · apply B_ext_iSup; intro w₂
        apply B_ext_inf
        · exact B_ext_mem_right w₂
        · exact B_ext_const (pair w₁ w₂ ∈ᴮ f)
  · exact B_ext_const (is_inj f)

/-!
## Check-name reflection of Ord properties
-/

lemma check_is_transitive {x : pSet} (H : pSet.is_transitive x) {Γ : 𝔹} : Γ ≤ is_transitive (check x : bSet 𝔹) := by
  unfold is_transitive
  apply le_iInf
  intro y
  apply lattice.bv_imp_intro
  rw [mem_unfold]
  apply lattice.bv_cases_right
  intro i
  let Δ : 𝔹 := Γ ⊓ ((check x : bSet 𝔹).bval i ⊓ y =ᴮ (check x : bSet 𝔹).func i)
  change Δ ≤ y ⊆ᴮ check x
  let i' : x.Type := cast (check_type (𝔹 := 𝔹) (x := x)) i
  have hEq : Δ ≤ y =ᴮ (check (x.Func i') : bSet 𝔹) := by
    dsimp [Δ, i']
    simpa [check_func] using inf_le_right.trans inf_le_right
  have hSub : Δ ≤ (check (x.Func i') : bSet 𝔹) ⊆ᴮ check x := by
    exact check_subset (H (x.Func i') pSet.mem_mk')
  exact (le_inf (bv_symm hEq) hSub).trans subst_congr_subset_left

lemma check_ewo_left {x : pSet} (H : pSet.epsilon_well_orders x) {Γ : 𝔹} : Γ ≤ (⨅ (y : bSet 𝔹), y ∈ᴮ (check x : bSet 𝔹) ⟹
  (⨅ (z : bSet 𝔹), z ∈ᴮ (check x : bSet 𝔹) ⟹ (y =ᴮ z ⊔ y ∈ᴮ z ⊔ z ∈ᴮ y))) := by
  apply le_iInf
  intro y
  apply lattice.bv_imp_intro
  apply le_iInf
  intro z
  apply lattice.bv_imp_intro
  let Δ : 𝔹 := (Γ ⊓ y ∈ᴮ (check x : bSet 𝔹)) ⊓ z ∈ᴮ (check x : bSet 𝔹)
  change Δ ≤ y =ᴮ z ⊔ y ∈ᴮ z ⊔ z ∈ᴮ y
  have hyMem : Δ ≤ y ∈ᴮ (check x : bSet 𝔹) := by
    dsimp [Δ]
    exact inf_le_left.trans inf_le_right
  rw [mem_unfold] at hyMem
  apply (le_inf le_rfl hyMem).trans
  apply lattice.bv_cases_right
  intro i
  let Θ : 𝔹 := Δ ⊓ ((check x : bSet 𝔹).bval i ⊓ y =ᴮ (check x : bSet 𝔹).func i)
  have hzMem : Θ ≤ z ∈ᴮ (check x : bSet 𝔹) := by
    dsimp [Θ, Δ]
    exact inf_le_left.trans inf_le_right
  rw [mem_unfold] at hzMem
  apply (le_inf le_rfl hzMem).trans
  apply lattice.bv_cases_right
  intro j
  let Ψ : 𝔹 := Θ ⊓ ((check x : bSet 𝔹).bval j ⊓ z =ᴮ (check x : bSet 𝔹).func j)
  change Ψ ≤ y =ᴮ z ⊔ y ∈ᴮ z ⊔ z ∈ᴮ y
  let i' : x.Type := cast (check_type (𝔹 := 𝔹) (x := x)) i
  let j' : x.Type := cast (check_type (𝔹 := 𝔹) (x := x)) j
  have hyEq : Ψ ≤ y =ᴮ (check (x.Func i') : bSet 𝔹) := by
    have hΨΘ : Ψ ≤ Θ := inf_le_left
    have hΘi : Θ ≤ (check x : bSet 𝔹).bval i ⊓ y =ᴮ (check x : bSet 𝔹).func i :=
      inf_le_right
    have hRaw : Ψ ≤ y =ᴮ (check x : bSet 𝔹).func i :=
      hΨΘ.trans (hΘi.trans inf_le_right)
    simpa [i', check_func] using hRaw
  have hzEq : Ψ ≤ z =ᴮ (check (x.Func j') : bSet 𝔹) := by
    have hRaw : Ψ ≤ z =ᴮ (check x : bSet 𝔹).func j :=
      inf_le_right.trans inf_le_right
    simpa [j', check_func] using hRaw
  rcases H.1 (x.Func i') pSet.mem_mk' (x.Func j') pSet.mem_mk' with hij | hij | hji
  · have hEq : Ψ ≤ y =ᴮ z :=
      bv_trans hyEq (bv_trans (check_eq hij) (bv_symm hzEq))
    exact lattice.bv_or_left (lattice.bv_or_left hEq)
  · have hMemCheck : Ψ ≤ (check (x.Func i') : bSet 𝔹) ∈ᴮ check (x.Func j') :=
      check_mem hij
    have hMemLeft : Ψ ≤ y ∈ᴮ check (x.Func j') :=
      subst_congr_mem_left' (bv_symm hyEq) hMemCheck
    have hMem : Ψ ≤ y ∈ᴮ z :=
      subst_congr_mem_right' (bv_symm hzEq) hMemLeft
    exact lattice.bv_or_left (lattice.bv_or_right hMem)
  · have hMemCheck : Ψ ≤ (check (x.Func j') : bSet 𝔹) ∈ᴮ check (x.Func i') :=
      check_mem hji
    have hMemLeft : Ψ ≤ z ∈ᴮ check (x.Func i') :=
      subst_congr_mem_left' (bv_symm hzEq) hMemCheck
    have hMem : Ψ ≤ z ∈ᴮ y :=
      subst_congr_mem_right' (bv_symm hyEq) hMemLeft
    exact lattice.bv_or_right hMem

lemma check_ewo_right {x : pSet} (H : pSet.epsilon_well_orders x) {Γ : 𝔹} : Γ ≤ (⨅ (u : bSet 𝔹), u ⊆ᴮ (check x : bSet 𝔹) ⟹ ((u =ᴮ ∅)ᶜ ⟹ ⨆ (y : bSet 𝔹), y ∈ᴮ u ⊓ (⨅ (z' : bSet 𝔹), z' ∈ᴮ u ⟹ (z' ∈ᴮ y)ᶜ))) := by
  simpa [epsilon_well_founded] using
    (is_epsilon_well_founded (x := (check x : bSet 𝔹)) (Γ := Γ))

lemma check_ewo {x : pSet} (H : pSet.epsilon_well_orders x) {Γ : 𝔹} : Γ ≤ epsilon_well_orders (check x : bSet 𝔹) :=
  le_inf (check_ewo_left H) (check_ewo_right H)

@[simp] lemma check_Ord {x : pSet} (H : pSet.Ord x) {Γ : 𝔹} : Γ ≤ Ord (check x : bSet 𝔹) := by
  have hEwo : Γ ≤ epsilon_well_orders (check x : bSet 𝔹) :=
    check_ewo H.left
  have hTrans : Γ ≤ is_transitive (check x : bSet 𝔹) :=
    check_is_transitive H.right
  exact le_inf hEwo hTrans

lemma check_injects_into {x y : pSet.{u}} (H_inj : pSet.injects_into x y) {Γ : 𝔹} :
    Γ ≤ bSet.injects_into (check x) (check y) := by
  rcases H_inj with ⟨f, hfn⟩
  unfold injects_into
  apply le_iSup_of_le (check f)
  have h_fn := check_is_injective_function (Γ := Γ) hfn
  refine le_inf ?_ (lattice.bv_and.right h_fn)
  exact is_func'_of_is_function (lattice.bv_and.left h_fn)

@[simp] lemma Ord_omega {Γ : 𝔹} : Γ ≤ Ord (omega : bSet 𝔹) :=
  le_inf (check_ewo pSet.is_ewo_omega) (check_is_transitive pSet.is_transitive_omega)

lemma Ord_of_nat {Γ : 𝔹} {n : ℕ} : Γ ≤ Ord (of_nat n) :=
  Ord_of_mem_Ord of_nat_mem_omega Ord_omega

lemma of_nat_subset_omega {n : ℕ} {Γ : 𝔹} : Γ ≤ of_nat n ⊆ᴮ omega :=
  subset_of_mem_transitive (lattice.bv_and.right Ord_omega) of_nat_mem_omega

/-!
## Check cast for check names
-/

/-- Reinterpret an index of `check x` as an index of `x`. -/
@[reducible, simp] def check_cast {x : pSet} (i : (check x : bSet 𝔹).type) : x.Type :=
  cast (by simp [check_type]) i

/-- Reinterpret an index of `x` as an index of `check x`. -/
@[reducible, simp] def check_cast.symm {x : pSet} (i : x.Type) : (check x : bSet 𝔹).type :=
  cast (by simp [check_type]) i

/-!
## Empty set and self-membership lemmas
-/

lemma empty_iff_forall_not_mem {u : bSet 𝔹} {Γ : 𝔹} : Γ ≤ u =ᴮ ∅ ↔ Γ ≤ ⨅ x, (x ∈ᴮ u)ᶜ := by
  rw [eq_iff_subset_subset]
  refine ⟨?_, ?_⟩
  · intro h
    have hsub : Γ ≤ u ⊆ᴮ ∅ := h.trans inf_le_left
    apply le_iInf; intro x
    apply le_compl_of_inf_le_bot
    have hmemEmpty : Γ ⊓ x ∈ᴮ u ≤ x ∈ᴮ (∅ : bSet 𝔹) :=
      mem_of_mem_subset' (inf_le_left.trans hsub) inf_le_right
    simpa [mem_empty] using hmemEmpty
  · intro h
    have hsub : Γ ≤ u ⊆ᴮ ∅ := by
      apply subset_intro
      intro i
      have hmem : Γ ⊓ u.bval i ≤ u.func i ∈ᴮ u :=
        inf_le_right.trans (mem.mk' u i)
      have hnot : Γ ⊓ u.bval i ≤ (u.func i ∈ᴮ u)ᶜ :=
        (inf_le_left.trans h).trans (iInf_le _ (u.func i))
      simpa [mem_empty] using bv_absurd hmem hnot
    have hempty : Γ ≤ (∅ : bSet 𝔹) ⊆ᴮ u := by
      rw [empty_subset_eq_top u]; exact le_top
    exact le_inf hsub hempty

lemma bot_of_mem_self' {x : bSet 𝔹} {Γ : 𝔹} (H : Γ ≤ x ∈ᴮ x) : Γ ≤ ⊥ :=
  bot_of_mem_self H

lemma bot_of_mem_empty {x : bSet 𝔹} {Γ : 𝔹} (h : Γ ≤ x ∈ᴮ ∅) : Γ ≤ ⊥ := by
  simpa [mem_empty] using h

lemma is_func'_empty {Γ : 𝔹} {x : bSet 𝔹} : Γ ≤ is_func' (∅ : bSet 𝔹) x ∅ := by
  unfold is_func'
  refine le_inf ?_ ?_
  · -- Γ ≤ is_func ∅
    unfold is_func
    apply le_iInf; intro w₁
    apply le_iInf; intro w₂
    apply le_iInf; intro v₁
    apply le_iInf; intro v₂
    apply lattice.bv_imp_intro
    simp [mem_empty]
  · -- Γ ≤ is_total ∅ x ∅
    unfold is_total
    apply le_iInf; intro w₁
    apply lattice.bv_imp_intro
    simp [mem_empty]

lemma is_surj_empty {Γ : 𝔹} : Γ ≤ is_surj (∅ : bSet 𝔹) ∅ ∅ := by
  unfold is_surj
  apply le_iInf; intro z
  apply lattice.bv_imp_intro
  simp [mem_empty]

/-!
## Inverse function membership lemma
-/

lemma mem_inj_inverse_iff {Γ Γ' : 𝔹} {b a : bSet 𝔹} {x y f : bSet 𝔹}
    {hFunc : Γ ≤ is_func' x y f} {hInj : Γ ≤ is_inj f} :
    Γ' ≤ pair b a ∈ᴮ inj_inverse hFunc hInj ↔
    Γ' ≤ a ∈ᴮ x ∧ Γ' ≤ b ∈ᴮ y ∧ Γ' ≤ pair a b ∈ᴮ f := by
  constructor
  · intro h
    exact mem_inj_inverse_components h
  · rintro ⟨ha, hb, hMem⟩
    exact mem_inj_inverse ha hb hMem

/-!
## Subset-to-injection lemmas
-/

lemma injects_into_of_subset {x y : bSet 𝔹} {Γ : 𝔹} (H : Γ ≤ x ⊆ᴮ y) : Γ ≤ injects_into x y := by
  let f : bSet 𝔹 :=
    set_of_indicator (x := prod x y)
      (fun pr : (prod x y).type =>
        x.func pr.1 =ᴮ y.func pr.2 ⊓ x.bval pr.1 ⊓ y.bval pr.2)
  have hMemF {Γ' : 𝔹} {a b : bSet 𝔹} (ha : Γ' ≤ a ∈ᴮ x) (hb : Γ' ≤ b ∈ᴮ y)
      (hab : Γ' ≤ a =ᴮ b) : Γ' ≤ pair a b ∈ᴮ f := by
    dsimp [f]
    rw [mem_set_of_indicator_iff]
    rw [mem_unfold] at ha
    apply (le_inf le_rfl ha).trans
    apply lattice.bv_cases_right
    intro i
    let Δ : 𝔹 := Γ' ⊓ (x.bval i ⊓ a =ᴮ x.func i)
    have hbΔ : Δ ≤ b ∈ᴮ y := by
      dsimp [Δ]
      exact inf_le_left.trans hb
    rw [mem_unfold] at hbΔ
    apply (le_inf le_rfl hbΔ).trans
    apply lattice.bv_cases_right
    intro j
    let Θ : 𝔹 := Δ ⊓ (y.bval j ⊓ b =ᴮ y.func j)
    change Θ ≤
      ⨆ pr : (prod x y).type,
        ((x.func pr.1 =ᴮ y.func pr.2 ⊓ x.bval pr.1 ⊓ y.bval pr.2) ⊓
          (prod x y).bval pr) ⊓ pair a b =ᴮ (prod x y).func pr
    apply lattice.bv_use (i, j)
    have hxi : Θ ≤ a =ᴮ x.func i := by
      dsimp [Θ, Δ]
      exact inf_le_left.trans inf_le_right |>.trans inf_le_right
    have hyj : Θ ≤ b =ᴮ y.func j := by
      dsimp [Θ]
      exact inf_le_right.trans inf_le_right
    have hxi_yj : Θ ≤ x.func i =ᴮ y.func j := by
      exact bv_trans (bv_symm hxi) (bv_trans (inf_le_left.trans (inf_le_left.trans hab)) hyj)
    have hPair : Θ ≤ pair a b =ᴮ (prod x y).func (i, j) := by
      change Θ ≤ pair a b =ᴮ pair (x.func i) (y.func j)
      exact pair_congr hxi hyj
    have hxVal : Θ ≤ x.bval i := by
      dsimp [Θ, Δ]
      exact inf_le_left.trans inf_le_right |>.trans inf_le_left
    have hyVal : Θ ≤ y.bval j := by
      dsimp [Θ]
      exact inf_le_right.trans inf_le_left
    apply le_inf
    · apply le_inf
      · exact le_inf (le_inf hxi_yj hxVal) hyVal
      · dsimp [prod]
        exact le_inf hxVal hyVal
    · exact hPair
  unfold injects_into
  apply lattice.bv_use f
  apply le_inf
  · unfold is_func'
    apply le_inf
    · unfold is_func
      apply le_iInf
      intro w₁
      apply le_iInf
      intro w₂
      apply le_iInf
      intro v₁
      apply le_iInf
      intro v₂
      apply lattice.bv_imp_intro
      let Δ : 𝔹 := Γ ⊓ (pair w₁ v₁ ∈ᴮ f ⊓ pair w₂ v₂ ∈ᴮ f)
      change Δ ≤ lattice.imp (w₁ =ᴮ w₂) (v₁ =ᴮ v₂)
      apply lattice.bv_imp_intro
      let Θ : 𝔹 := Δ ⊓ w₁ =ᴮ w₂
      change Θ ≤ v₁ =ᴮ v₂
      have hMem₁ : Θ ≤ pair w₁ v₁ ∈ᴮ f := by
        dsimp [Θ, Δ]
        exact inf_le_left.trans inf_le_right |>.trans inf_le_left
      have hMem₂ : Θ ≤ pair w₂ v₂ ∈ᴮ f := by
        dsimp [Θ, Δ]
        exact inf_le_left.trans inf_le_right |>.trans inf_le_right
      have hwEq : Θ ≤ w₁ =ᴮ w₂ := by
        dsimp [Θ]
        exact inf_le_right
      dsimp [f] at hMem₁ hMem₂
      rw [mem_set_of_indicator_iff] at hMem₁
      apply (le_inf le_rfl hMem₁).trans
      apply lattice.bv_cases_right
      intro p₁
      let Θ₁ : 𝔹 := Θ ⊓
        (((x.func p₁.1 =ᴮ y.func p₁.2 ⊓ x.bval p₁.1 ⊓ y.bval p₁.2) ⊓
          (prod x y).bval p₁) ⊓ pair w₁ v₁ =ᴮ (prod x y).func p₁)
      change Θ₁ ≤ v₁ =ᴮ v₂
      rw [mem_set_of_indicator_iff] at hMem₂
      have hMem₂Θ₁ : Θ₁ ≤
          ⨆ p : (prod x y).type,
            ((x.func p.1 =ᴮ y.func p.2 ⊓ x.bval p.1 ⊓ y.bval p.2) ⊓
              (prod x y).bval p) ⊓ pair w₂ v₂ =ᴮ (prod x y).func p := by
        dsimp [Θ₁]
        exact inf_le_left.trans hMem₂
      apply (le_inf le_rfl hMem₂Θ₁).trans
      apply lattice.bv_cases_right
      intro p₂
      let Ω : 𝔹 := Θ₁ ⊓
        (((x.func p₂.1 =ᴮ y.func p₂.2 ⊓ x.bval p₂.1 ⊓ y.bval p₂.2) ⊓
          (prod x y).bval p₂) ⊓ pair w₂ v₂ =ᴮ (prod x y).func p₂)
      change Ω ≤ v₁ =ᴮ v₂
      have hPair₁ : Ω ≤ pair w₁ v₁ =ᴮ pair (x.func p₁.1) (y.func p₁.2) := by
        dsimp [Ω, Θ₁]
        exact inf_le_left.trans inf_le_right |>.trans inf_le_right
      have hPair₂ : Ω ≤ pair w₂ v₂ =ᴮ pair (x.func p₂.1) (y.func p₂.2) := by
        dsimp [Ω]
        exact inf_le_right.trans inf_le_right
      have hw₁ : Ω ≤ w₁ =ᴮ x.func p₁.1 :=
        eq_of_eq_pair_left' hPair₁
      have hv₁ : Ω ≤ v₁ =ᴮ y.func p₁.2 :=
        eq_of_eq_pair_right' hPair₁
      have hw₂ : Ω ≤ w₂ =ᴮ x.func p₂.1 :=
        eq_of_eq_pair_left' hPair₂
      have hv₂ : Ω ≤ v₂ =ᴮ y.func p₂.2 :=
        eq_of_eq_pair_right' hPair₂
      have hx₁y₁ : Ω ≤ x.func p₁.1 =ᴮ y.func p₁.2 := by
        have hB₁ : Ω ≤
            (((x.func p₁.1 =ᴮ y.func p₁.2 ⊓ x.bval p₁.1 ⊓ y.bval p₁.2) ⊓
              (prod x y).bval p₁) ⊓ pair w₁ v₁ =ᴮ (prod x y).func p₁) := by
          dsimp [Ω, Θ₁]
          exact inf_le_left.trans inf_le_right
        exact hB₁.trans (inf_le_left.trans (inf_le_left.trans (inf_le_left.trans inf_le_left)))
      have hx₂y₂ : Ω ≤ x.func p₂.1 =ᴮ y.func p₂.2 := by
        have hB₂ : Ω ≤
            (((x.func p₂.1 =ᴮ y.func p₂.2 ⊓ x.bval p₂.1 ⊓ y.bval p₂.2) ⊓
              (prod x y).bval p₂) ⊓ pair w₂ v₂ =ᴮ (prod x y).func p₂) := by
          dsimp [Ω]
          exact inf_le_right
        exact hB₂.trans (inf_le_left.trans (inf_le_left.trans (inf_le_left.trans inf_le_left)))
      have hx₁x₂ : Ω ≤ x.func p₁.1 =ᴮ x.func p₂.1 := by
        exact bv_trans (bv_symm hw₁)
          (bv_trans (inf_le_left.trans (inf_le_left.trans hwEq)) hw₂)
      exact bv_trans hv₁ (bv_trans (bv_symm hx₁y₁)
        (bv_trans hx₁x₂ (bv_trans hx₂y₂ (bv_symm hv₂))))
    · unfold is_total
      apply le_iInf
      intro w₁
      apply lattice.bv_imp_intro
      let Δ : 𝔹 := Γ ⊓ w₁ ∈ᴮ x
      change Δ ≤ ⨆ w₂ : bSet 𝔹, w₂ ∈ᴮ y ⊓ pair w₁ w₂ ∈ᴮ f
      have hwX : Δ ≤ w₁ ∈ᴮ x := inf_le_right
      have hwY : Δ ≤ w₁ ∈ᴮ y := mem_of_mem_subset' (inf_le_left.trans H) hwX
      apply lattice.bv_use w₁
      exact le_inf hwY (hMemF hwX hwY bv_refl)
  · unfold is_inj
    apply le_iInf
    intro w₁
    apply le_iInf
    intro w₂
    apply le_iInf
    intro v₁
    apply le_iInf
    intro v₂
    apply lattice.bv_imp_intro
    let Δ : 𝔹 := Γ ⊓ (pair w₁ v₁ ∈ᴮ f ⊓ pair w₂ v₂ ∈ᴮ f ⊓ v₁ =ᴮ v₂)
    change Δ ≤ w₁ =ᴮ w₂
    have hMem₁ : Δ ≤ pair w₁ v₁ ∈ᴮ f := by
      dsimp [Δ]
      exact inf_le_right.trans inf_le_left |>.trans inf_le_left
    have hMem₂ : Δ ≤ pair w₂ v₂ ∈ᴮ f := by
      dsimp [Δ]
      exact inf_le_right.trans inf_le_left |>.trans inf_le_right
    have hvEq : Δ ≤ v₁ =ᴮ v₂ := by
      dsimp [Δ]
      exact inf_le_right.trans inf_le_right
    dsimp [f] at hMem₁ hMem₂
    rw [mem_set_of_indicator_iff] at hMem₁
    apply (le_inf le_rfl hMem₁).trans
    apply lattice.bv_cases_right
    intro p₁
    let Δ₁ : 𝔹 := Δ ⊓
      (((x.func p₁.1 =ᴮ y.func p₁.2 ⊓ x.bval p₁.1 ⊓ y.bval p₁.2) ⊓
        (prod x y).bval p₁) ⊓ pair w₁ v₁ =ᴮ (prod x y).func p₁)
    change Δ₁ ≤ w₁ =ᴮ w₂
    rw [mem_set_of_indicator_iff] at hMem₂
    have hMem₂Δ₁ : Δ₁ ≤
        ⨆ p : (prod x y).type,
          ((x.func p.1 =ᴮ y.func p.2 ⊓ x.bval p.1 ⊓ y.bval p.2) ⊓
            (prod x y).bval p) ⊓ pair w₂ v₂ =ᴮ (prod x y).func p := by
      dsimp [Δ₁]
      exact inf_le_left.trans hMem₂
    apply (le_inf le_rfl hMem₂Δ₁).trans
    apply lattice.bv_cases_right
    intro p₂
    let Ω : 𝔹 := Δ₁ ⊓
      (((x.func p₂.1 =ᴮ y.func p₂.2 ⊓ x.bval p₂.1 ⊓ y.bval p₂.2) ⊓
        (prod x y).bval p₂) ⊓ pair w₂ v₂ =ᴮ (prod x y).func p₂)
    change Ω ≤ w₁ =ᴮ w₂
    have hPair₁ : Ω ≤ pair w₁ v₁ =ᴮ pair (x.func p₁.1) (y.func p₁.2) := by
      dsimp [Ω, Δ₁]
      exact inf_le_left.trans inf_le_right |>.trans inf_le_right
    have hPair₂ : Ω ≤ pair w₂ v₂ =ᴮ pair (x.func p₂.1) (y.func p₂.2) := by
      dsimp [Ω]
      exact inf_le_right.trans inf_le_right
    have hw₁ : Ω ≤ w₁ =ᴮ x.func p₁.1 :=
      eq_of_eq_pair_left' hPair₁
    have hv₁ : Ω ≤ v₁ =ᴮ y.func p₁.2 :=
      eq_of_eq_pair_right' hPair₁
    have hw₂ : Ω ≤ w₂ =ᴮ x.func p₂.1 :=
      eq_of_eq_pair_left' hPair₂
    have hv₂ : Ω ≤ v₂ =ᴮ y.func p₂.2 :=
      eq_of_eq_pair_right' hPair₂
    have hx₁y₁ : Ω ≤ x.func p₁.1 =ᴮ y.func p₁.2 := by
      have hB₁ : Ω ≤
          (((x.func p₁.1 =ᴮ y.func p₁.2 ⊓ x.bval p₁.1 ⊓ y.bval p₁.2) ⊓
            (prod x y).bval p₁) ⊓ pair w₁ v₁ =ᴮ (prod x y).func p₁) := by
        dsimp [Ω, Δ₁]
        exact inf_le_left.trans inf_le_right
      exact hB₁.trans (inf_le_left.trans (inf_le_left.trans (inf_le_left.trans inf_le_left)))
    have hx₂y₂ : Ω ≤ x.func p₂.1 =ᴮ y.func p₂.2 := by
      have hB₂ : Ω ≤
          (((x.func p₂.1 =ᴮ y.func p₂.2 ⊓ x.bval p₂.1 ⊓ y.bval p₂.2) ⊓
            (prod x y).bval p₂) ⊓ pair w₂ v₂ =ᴮ (prod x y).func p₂) := by
        dsimp [Ω]
        exact inf_le_right
      exact hB₂.trans (inf_le_left.trans (inf_le_left.trans (inf_le_left.trans inf_le_left)))
    have hy₁y₂ : Ω ≤ y.func p₁.2 =ᴮ y.func p₂.2 := by
      exact bv_trans (bv_symm hv₁)
        (bv_trans (inf_le_left.trans (inf_le_left.trans hvEq)) hv₂)
    exact bv_trans hw₁ (bv_trans hx₁y₁
      (bv_trans hy₁y₂ (bv_trans (bv_symm hx₂y₂) (bv_symm hw₂))))

lemma injection_into_of_subset {x y : bSet 𝔹} {Γ : 𝔹} (H : Γ ≤ x ⊆ᴮ y) : Γ ≤ injection_into x y :=
  injects_into_iff_injection_into.mp (injects_into_of_subset H)

/-!
## Surjection from injection lemma
-/

lemma surjects_onto_of_injects_into {x y : bSet 𝔹} {Γ : 𝔹}
    (H_inj : Γ ≤ injects_into x y) (H_exists_mem : Γ ≤ exists_mem x) :
    Γ ≤ surjects_onto y x := by
  -- Uses the inverse function construction; port TBD
  exact sorry

/-!
## Aleph-one ordinal specification
-/

@[reducible] def aleph_one_Ord_spec (x : bSet 𝔹) : 𝔹 :=
  ((injects_into x bSet.omega)ᶜ) ⊓ ((Ord x) ⊓
    (⨅ (y : bSet 𝔹), (Ord y) ⟹ (((injects_into y bSet.omega)ᶜ) ⟹ x ⊆ᴮ y)))

@[simp] lemma aleph_one_check_exists_mem {Γ : 𝔹} :
    Γ ≤ exists_mem ((pSet.card_ex (Cardinal.aleph 1))̌ : bSet 𝔹) := by
  have h_exists : ∃ z, z ∈ pSet.card_ex (Cardinal.aleph 1) :=
    pSet.exists_mem_of_regular pSet.is_regular_aleph_one
  simpa using check_exists_mem h_exists

@[reducible] def le_of_omega_lt (x : bSet 𝔹) : 𝔹 :=
  ⨅ (z : bSet 𝔹), Ord z ⟹ (((larger_than bSet.omega z)ᶜ) ⟹ (injects_into x z))

@[simp] lemma B_ext_le_of_omega_lt : B_ext (le_of_omega_lt : bSet 𝔹 → 𝔹) := by
  unfold le_of_omega_lt
  apply B_ext_iInf; intro z
  apply B_ext_imp
  · exact B_ext_const (Ord z)
  · apply B_ext_imp
    · exact B_ext_const ((larger_than bSet.omega z)ᶜ)
    · exact B_ext_injects_into_left (y := z)

/-!
## Epsilon-isomorphism extension lemmas
-/

lemma eps_iso_symm {x y : bSet 𝔹} {Γ : 𝔹} (H₁ : Γ ≤ Ord x) (H₂ : Γ ≤ Ord y) :
    (Γ ≤ ⨆ f, eps_iso x y f) ↔ (Γ ≤ ⨆ f, eps_iso y x f) := by
  refine ⟨?_, ?_⟩
  · intro H
    rcases exists_convert H (by
      unfold eps_iso; apply B_ext_inf
      · apply B_ext_inf
        · exact B_ext_is_function_right x y
        · exact B_ext_strong_eps_hom_right (x := x) (y := y)
      · exact B_ext_is_surj_right (x := x) (y := y)) with ⟨f, Hf⟩
    apply lattice.bv_use (eps_iso_inv H₁ H₂ Hf)
    exact eps_iso_eps_iso_inv H₁ H₂ Hf
  · intro H
    rcases exists_convert H (by
      unfold eps_iso; apply B_ext_inf
      · apply B_ext_inf
        · exact B_ext_is_function_right y x
        · exact B_ext_strong_eps_hom_right (x := y) (y := x)
      · exact B_ext_is_surj_right (x := y) (y := x)) with ⟨f, Hf⟩
    apply lattice.bv_use (eps_iso_inv H₂ H₁ Hf)
    exact eps_iso_eps_iso_inv H₂ H₁ Hf

lemma eps_iso_mono {x y z f : bSet 𝔹} {Γ : 𝔹}
    (H₁ : Γ ≤ Ord y) (H₂ : Γ ≤ z ⊆ᴮ y) (H₃ : Γ ≤ eps_iso y z f)
    (H₄ : Γ ≤ x ∈ᴮ y) (w' : bSet 𝔹) (Hw' : Γ ≤ pair x w' ∈ᴮ f) : Γ ≤ x ⊆ᴮ w' := by
  -- Complex proof using regularity; port TBD
  exact sorry

lemma eq_of_Ord_eps_iso_aux {x y : bSet 𝔹} {Γ : 𝔹}
    (Hx_ord : Γ ≤ Ord x) (Hy_ord : Γ ≤ Ord y)
    (H_eps_iso : Γ ≤ ⨆ f, eps_iso y x f) (H_mem : Γ ≤ x ∈ᴮ y) : Γ ≤ ⊥ := by
  apply (le_inf le_rfl H_eps_iso).trans
  apply lattice.bv_cases_right
  intro f
  let Γf : 𝔹 := Γ ⊓ eps_iso y x f
  change Γf ≤ ⊥
  have hIso : Γf ≤ eps_iso y x f := by
    dsimp [Γf]
    exact inf_le_right
  have hFunc : Γf ≤ is_function y x f :=
    is_function_of_eps_iso hIso
  have hTotal : Γf ≤ is_total y x f :=
    is_total_of_is_function hFunc
  have hxMemY : Γf ≤ x ∈ᴮ y := by
    dsimp [Γf]
    exact inf_le_left.trans H_mem
  have hTotalX : Γf ≤ lattice.imp (x ∈ᴮ y)
      (⨆ w : bSet 𝔹, w ∈ᴮ x ⊓ pair x w ∈ᴮ f) :=
    hTotal.trans (iInf_le _ x)
  have hWitnesses : Γf ≤ ⨆ w : bSet 𝔹, w ∈ᴮ x ⊓ pair x w ∈ᴮ f :=
    lattice.bv_context_apply hTotalX hxMemY
  apply (le_inf le_rfl hWitnesses).trans
  apply lattice.bv_cases_right
  intro w
  let Δ : 𝔹 := Γf ⊓ (w ∈ᴮ x ⊓ pair x w ∈ᴮ f)
  change Δ ≤ ⊥
  have hwMemX : Δ ≤ w ∈ᴮ x := by
    dsimp [Δ]
    exact inf_le_right.trans inf_le_left
  have hxPair : Δ ≤ pair x w ∈ᴮ f := by
    dsimp [Δ]
    exact inf_le_right.trans inf_le_right
  have hΔΓ : Δ ≤ Γ := by
    dsimp [Δ, Γf]
    exact inf_le_left.trans inf_le_left
  have hxSubY : Δ ≤ x ⊆ᴮ y :=
    subset_of_mem_Ord (hΔΓ.trans H_mem) (hΔΓ.trans Hy_ord)
  have hxSubW : Δ ≤ x ⊆ᴮ w :=
    eps_iso_mono (hΔΓ.trans Hy_ord) hxSubY (inf_le_left.trans hIso)
      (hΔΓ.trans H_mem) w hxPair
  have hxOrdΔ : Δ ≤ Ord x := hΔΓ.trans Hx_ord
  have hwOrdΔ : Δ ≤ Ord w :=
    Ord_of_mem_Ord hwMemX hxOrdΔ
  have hLtOrEq : Δ ≤ x ∈ᴮ w ⊔ x =ᴮ w :=
    (Ord.le_iff_lt_or_eq hxOrdΔ hwOrdΔ).mp hxSubW
  apply (le_inf le_rfl hLtOrEq).trans
  apply lattice.bv_or_elim_right
  · let Θ : 𝔹 := Δ ⊓ x ∈ᴮ w
    change Θ ≤ ⊥
    exact bot_of_mem_mem inf_le_right (inf_le_left.trans hwMemX)
  · let Θ : 𝔹 := Δ ⊓ x =ᴮ w
    change Θ ≤ ⊥
    have hxEqW : Θ ≤ x =ᴮ w := by
      dsimp [Θ]
      exact inf_le_right
    have hwMemXΘ : Θ ≤ w ∈ᴮ x := by
      dsimp [Θ]
      exact inf_le_left.trans hwMemX
    exact bot_of_mem_self (subst_congr_mem_right' hxEqW hwMemXΘ)

lemma eq_of_Ord_eps_iso {x y : bSet 𝔹} {Γ : 𝔹}
    (Hx_ord : Γ ≤ Ord x) (Hy_ord : Γ ≤ Ord y)
    (H_eps_iso : Γ ≤ ⨆ f, eps_iso x y f) : Γ ≤ x =ᴮ y := by
  have h_trich := Ord.trichotomy Hx_ord Hy_ord
  -- h_trich : Γ ≤ (x =ᴮ y ⊔ x ∈ᴮ y) ⊔ y ∈ᴮ x  (⊔ is left-assoc)
  -- Use bv_or_elim_right with inf twice to analyze the disjunction
  have h_goal : Γ ⊓ ((x =ᴮ y ⊔ x ∈ᴮ y) ⊔ y ∈ᴮ x) ≤ x =ᴮ y := by
    apply lattice.bv_or_elim_right
    · -- Γ ⊓ (x =ᴮ y ⊔ x ∈ᴮ y) ≤ x =ᴮ y
      apply lattice.bv_or_elim_right
      · -- Γ ⊓ (x =ᴮ y) ≤ x =ᴮ y
        exact inf_le_right
      · -- Γ ⊓ (x ∈ᴮ y) ≤ x =ᴮ y
        rw [eps_iso_symm Hx_ord Hy_ord] at H_eps_iso
        have h_bot : Γ ⊓ (x ∈ᴮ y) ≤ ⊥ := eq_of_Ord_eps_iso_aux
          (le_trans inf_le_left Hx_ord) (le_trans inf_le_left Hy_ord)
          (le_trans inf_le_left H_eps_iso) inf_le_right
        exact le_trans h_bot bot_le
    · -- Γ ⊓ (y ∈ᴮ x) ≤ x =ᴮ y
      have h_bot : Γ ⊓ (y ∈ᴮ x) ≤ ⊥ := eq_of_Ord_eps_iso_aux
        (le_trans inf_le_left Hy_ord) (le_trans inf_le_left Hx_ord)
        (le_trans inf_le_left H_eps_iso) inf_le_right
      exact le_trans h_bot bot_le
  have : Γ ≤ Γ ⊓ ((x =ᴮ y ⊔ x ∈ᴮ y) ⊔ y ∈ᴮ x) := le_inf le_rfl h_trich
  exact le_trans this h_goal

/-!
## CH predicates
-/

def CH : 𝔹 := (⨆ x, Ord x ⊓ ⨆ y,
    (larger_than bSet.omega x)ᶜ ⊓ (larger_than x y)ᶜ ⊓ (injects_into y (bv_powerset bSet.omega)))ᶜ

def CH₂ : 𝔹 := (⨆ x, Ord x ⊓ (larger_than bSet.omega x)ᶜ ⊓
    (larger_than x (bv_powerset bSet.omega))ᶜ)ᶜ

lemma CH_iff_CH₂ {Γ : 𝔹} : Γ ≤ CH ↔ Γ ≤ CH₂ := by
  dsimp [CH, CH₂]
  -- Equivalence of two CH formulations; port TBD
  exact sorry

end bSet

end Flypitch
