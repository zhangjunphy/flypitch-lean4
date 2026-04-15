import Mathlib.SetTheory.Cardinal.Aleph
import Mathlib.SetTheory.ZFC.Ordinal

universe u

namespace Flypitch

/-!
`Flypitch.PSetOrdinal` starts the forcing-side port by reinstating the ordinal/cardinal encoding
layer used by the original development. Mathlib already supplies the underlying `PSet` and
von Neumann ordinal machinery, so this file mainly provides compatibility names and the first
group of bridge lemmas that later forcing files expect.
-/

/-- Compatibility alias for Mathlib's pre-set model of ZFC. -/
abbrev pSet := PSet

/-- Compatibility alias for Mathlib ordinals. -/
abbrev ordinal := Ordinal

/-- Compatibility alias for Mathlib cardinals. -/
abbrev cardinal := Cardinal

attribute [nolint docBlame] pSet ordinal cardinal

namespace cardinal

/-- The countable cardinal, matching the upstream `cardinal.omega` name. -/
abbrev omega : cardinal := Cardinal.aleph0

attribute [nolint docBlame] omega

end cardinal

namespace ordinal

/-- Interpret an ordinal as its von Neumann pre-set. -/
noncomputable abbrev mk : ordinal → pSet := Ordinal.toPSet

attribute [nolint docBlame] mk

theorem lt_zero_false {x : ordinal} : x < 0 → False := by
  intro hx
  exact not_lt_of_ge (bot_le : 0 ≤ x) hx

theorem mk_rank (o : ordinal) : PSet.rank (mk o) = o := by
  simp [mk]

theorem mk_type_card (o : ordinal) : Cardinal.mk (mk o).Type = o.card := by
  simp [mk]

attribute [nolint simpNF] mk_rank mk_type_card

theorem mk_mem_mk_of_lt {a b : ordinal} (h : a < b) : mk a ∈ mk b := by
  rw [mk, Ordinal.mem_toPSet_iff]
  exact ⟨a, h, PSet.Equiv.rfl⟩

theorem lt_of_mk_mem {a b : ordinal} (h : mk a ∈ mk b) : a < b := by
  simpa [mk] using PSet.rank_lt_of_mem h

theorem mk_inj {a b : ordinal} (h : PSet.Equiv (mk a) (mk b)) : a = b := by
  simpa [mk] using PSet.rank_congr h

theorem mk_subset_mk_iff {a b : ordinal} : mk a ⊆ mk b ↔ a ≤ b := by
  constructor
  · intro h
    simpa [mk] using PSet.rank_mono h
  · intro h
    rw [PSet.subset_iff]
    intro z hz
    rw [mk, Ordinal.mem_toPSet_iff] at hz ⊢
    rcases hz with ⟨c, hc, hzc⟩
    exact ⟨c, hc.trans_le h, hzc⟩

end ordinal

namespace pSet

/-- The successor of a pre-set, implemented as `insert x x`. -/
abbrev succ (x : pSet) : pSet := insert x x

/-- Pick a canonical pre-set representative of a cardinal via its initial ordinal. -/
noncomputable abbrev card_ex (κ : cardinal) : pSet := ordinal.mk (Cardinal.ord κ)

attribute [nolint docBlame] succ card_ex

theorem powerset_type {x : pSet} : (PSet.powerset x).Type = Set x.Type := by
  cases x
  rfl

@[simp] theorem mem_mk' {x : pSet} {i : x.Type} : x.Func i ∈ x :=
  PSet.func_mem _ _

theorem mem_unfold {x y : pSet} : x ∈ y ↔ ∃ j : y.Type, PSet.Equiv x (y.Func j) :=
  PSet.mem_def

theorem ext_iff {x y : pSet} : PSet.Equiv x y ↔ ∀ z, z ∈ x ↔ z ∈ y := by
  simpa using (PSet.equiv_iff_mem (x := x) (y := y))

theorem mem_mem_false {x y : pSet} (hxy : x ∈ y) (hyx : y ∈ x) : False :=
  PSet.mem_asymm hxy hyx

theorem mem_self {x : pSet} : x ∈ x → False :=
  PSet.mem_irrefl x

theorem subset_of_all_mem {x y : pSet} (h : ∀ z, z ∈ y → z ∈ x) : y ⊆ x :=
  (PSet.subset_iff).2 h

theorem all_mem_of_subset {x y : pSet} (h : y ⊆ x) : ∀ z, z ∈ y → z ∈ x :=
  (PSet.subset_iff).1 h

theorem subset_iff_all_mem {x y : pSet} : y ⊆ x ↔ ∀ z, z ∈ y → z ∈ x :=
  PSet.subset_iff

theorem mem_trans_of_transitive {x y z : pSet} (hxy : x ∈ y) (hyz : y ∈ z)
    (htrans : ∀ w, w ∈ z → w ⊆ z) : x ∈ z :=
  all_mem_of_subset (htrans y hyz) x hxy

theorem exists_mem_of_nonempty {x : pSet} (h : x.Nonempty) : ∃ y, y ∈ x := by
  classical
  cases x with
  | mk α A =>
      simpa [PSet.nonempty_def] using h

/-- The trichotomy-and-minimal-element property used for ordinal-shaped pre-sets. -/
def epsilon_well_orders (x : pSet) : Prop :=
  (∀ y, y ∈ x → ∀ z, z ∈ x → PSet.Equiv y z ∨ y ∈ z ∨ z ∈ y) ∧
    ∀ s, s ⊆ x → s.Nonempty → ∃ y, y ∈ s ∧ ∀ z', z' ∈ s → z' ∉ y

/-- A pre-set is transitive when every member is again a subset of it. -/
def is_transitive (x : pSet) : Prop :=
  ∀ y, y ∈ x → y ⊆ x

/-- Ordinal-shaped pre-sets are the transitive epsilon-well-ordered ones. -/
def Ord (x : pSet) : Prop :=
  epsilon_well_orders x ∧ is_transitive x

@[simp] theorem is_transitive_of_Ord {x : pSet} (h : Ord x) : is_transitive x :=
  h.2

@[simp] theorem is_ewo_of_Ord {x : pSet} (h : Ord x) : epsilon_well_orders x :=
  h.1

theorem mem_succ (x : pSet) : x ∈ succ x := by
  simpa [succ] using (PSet.mem_insert x x)

attribute [nolint simpNF] mem_self mem_succ

theorem well_founded (s : pSet) (h : s.Nonempty) :
    ∃ y : pSet, y ∈ s ∧ ∀ z' : pSet, z' ∈ s → z' ∉ y := by
  classical
  have hu : {y : pSet | y ∈ s}.Nonempty := by
    rcases exists_mem_of_nonempty h with ⟨y, hy⟩
    exact ⟨y, hy⟩
  refine ⟨PSet.mem_wf.min {y : pSet | y ∈ s} hu, ?_, ?_⟩
  · exact PSet.mem_wf.min_mem {y : pSet | y ∈ s} hu
  · intro z' hz'
    exact PSet.mem_wf.not_lt_min {y : pSet | y ∈ s} hz'

@[simp] theorem Ord_empty : Ord (∅ : pSet) := by
  refine ⟨?_, ?_⟩
  · constructor
    · intro y hy
      exact False.elim (PSet.notMem_empty _ hy)
    · intro u _ hu
      exact well_founded u hu
  · intro y hy
    exact False.elim (PSet.notMem_empty _ hy)

theorem transitive_succ (x : pSet) (h : is_transitive x) : is_transitive (succ x) := by
  intro y hy
  rcases PSet.mem_insert_iff.mp hy with hyEq | hyx
  · have hxsubset : x ⊆ succ x := by
      intro a
      exact PSet.mem_insert_of_mem x (PSet.func_mem x a)
    exact (PSet.Subset.congr_left hyEq).2 hxsubset
  · exact subset_of_all_mem fun z hz =>
      PSet.mem_insert_of_mem x (all_mem_of_subset (h y hyx) z hz)

@[simp] theorem Ord_succ (x : pSet) (h : Ord x) : Ord (succ x) := by
  refine ⟨?_, transitive_succ x h.2⟩
  constructor
  · intro y hy z hz
    rcases PSet.mem_insert_iff.mp hy with hyEq | hyx
    · rcases PSet.mem_insert_iff.mp hz with hzEq | hzx
      · exact Or.inl (hyEq.trans hzEq.symm)
      · exact Or.inr <| Or.inr <| (PSet.Mem.congr_right hyEq).2 hzx
    · rcases PSet.mem_insert_iff.mp hz with hzEq | hzx
      · exact Or.inr <| Or.inl <| (PSet.Mem.congr_right hzEq).2 hyx
      · exact h.1.1 y hyx z hzx
  · intro u _ hu
    exact well_founded u hu

theorem transitive_Union (x : pSet) (h : ∀ y ∈ x, is_transitive y) :
    is_transitive (⋃₀ x) := by
  intro z hz
  apply subset_of_all_mem
  intro w hw
  rcases PSet.mem_sUnion.mp hz with ⟨y, hy, hzy⟩
  exact PSet.mem_sUnion.mpr ⟨y, hy, all_mem_of_subset (h y hy z hzy) w hw⟩

theorem equiv_mk_of_mem_mk {η : ordinal} {x : pSet} (hx : x ∈ ordinal.mk η) :
    ∃ ρ < η, PSet.Equiv x (ordinal.mk ρ) := by
  simpa [ordinal.mk] using (Ordinal.mem_toPSet_iff (o := η) (x := x)).mp hx

theorem Ord_mk (η : ordinal) : Ord (ordinal.mk η) := by
  refine ⟨?_, ?_⟩
  · constructor
    · intro y hy z hz
      rcases equiv_mk_of_mem_mk hy with ⟨ξ, hξη, hyξ⟩
      rcases equiv_mk_of_mem_mk hz with ⟨ζ, hζη, hzζ⟩
      rcases lt_trichotomy ξ ζ with hlt | rfl | hgt
      · exact Or.inr <| Or.inl <|
          (PSet.Mem.congr_right hzζ).2 <|
            (PSet.Mem.congr_left hyξ).2 <|
              ordinal.mk_mem_mk_of_lt hlt
      · exact Or.inl (hyξ.trans hzζ.symm)
      · exact Or.inr <| Or.inr <|
          (PSet.Mem.congr_right hyξ).2 <|
            (PSet.Mem.congr_left hzζ).2 <|
              ordinal.mk_mem_mk_of_lt hgt
    · intro s _ hs
      exact well_founded s hs
  · intro y hy
    rcases equiv_mk_of_mem_mk hy with ⟨ξ, hξη, hyξ⟩
    apply subset_of_all_mem
    intro z hz
    have hz' : z ∈ ordinal.mk ξ := (PSet.Mem.congr_right hyξ).1 hz
    rcases equiv_mk_of_mem_mk hz' with ⟨ρ, hρξ, hzρ⟩
    have hρη : ordinal.mk ρ ∈ ordinal.mk η := ordinal.mk_mem_mk_of_lt (lt_trans hρξ hξη)
    exact (PSet.Mem.congr_left hzρ).2 hρη

theorem mem_mem_mem_false {x y z : pSet} (hxy : x ∈ y) (hyz : y ∈ z) (hzx : z ∈ x) : False :=
  lt_irrefl _ (((PSet.rank_lt_of_mem hxy).trans (PSet.rank_lt_of_mem hyz)).trans
    (PSet.rank_lt_of_mem hzx))

theorem transitive_of_mem_Ord {y x : pSet} (h : Ord x) (hmem : y ∈ x) : is_transitive y := by
  intro w hw
  apply subset_of_all_mem
  intro z hz
  have hwy : w ∈ x := all_mem_of_subset (h.2 y hmem) w hw
  have hzx : z ∈ x := all_mem_of_subset (h.2 w hwy) z hz
  rcases h.1.1 y hmem z hzx with hyEq | hyInz | hzIny
  · have hwz : w ∈ z := (PSet.Mem.congr_right hyEq).1 hw
    exact False.elim (mem_mem_false hz hwz)
  · exact False.elim (mem_mem_mem_false hz hw hyInz)
  · exact hzIny

theorem mk_mem_succ {η : ordinal} : ordinal.mk η ∈ ordinal.mk (Order.succ η) := by
  simpa using ordinal.mk_mem_mk_of_lt (Order.lt_succ η)

theorem subset_Union {x y : pSet} (h : y ∈ x) : y ⊆ ⋃₀ x := by
  exact subset_of_all_mem fun z hz => PSet.mem_sUnion.mpr ⟨y, h, hz⟩

theorem rank_ofNat : ∀ n : Nat, PSet.rank (PSet.ofNat n) = n
  | 0 => by simp [PSet.ofNat]
  | n + 1 => by simp [PSet.ofNat, rank_ofNat n]

theorem subset_refl {x : pSet} : x ⊆ x := by
  exact subset_of_all_mem fun _ hz => hz

theorem subset_self {x : pSet} : x ⊆ x := subset_refl

attribute [nolint simpNF] subset_self

theorem subset_trans {x y z : pSet} : x ⊆ y → y ⊆ z → x ⊆ z := by
  intro hxy hyz
  exact subset_of_all_mem fun w hw => all_mem_of_subset hyz w (all_mem_of_subset hxy w hw)

theorem of_nat_succ {k : Nat} : PSet.ofNat (k + 1) = pSet.succ (PSet.ofNat k) := by
  simp [PSet.ofNat, pSet.succ]

theorem subset_of_le {k₁ k₂ : Nat} (h : k₁ ≤ k₂) : PSet.ofNat k₁ ⊆ PSet.ofNat k₂ := by
  induction h with
  | refl =>
      exact subset_refl
  | @step n h ih =>
      refine subset_trans ih ?_
      exact subset_of_all_mem fun z hz => PSet.mem_insert_of_mem (PSet.ofNat n) hz

theorem of_nat_mem_of_lt {k₁ k₂ : Nat} (h : k₁ < k₂) : PSet.ofNat k₁ ∈ PSet.ofNat k₂ := by
  induction k₂ with
  | zero =>
      cases h
  | succ n ih =>
      rw [of_nat_succ]
      rcases lt_or_eq_of_le (Nat.le_of_lt_succ h) with hlt | rfl
      · exact PSet.mem_insert_of_mem (PSet.ofNat n) (ih hlt)
      · simpa [pSet.succ] using (PSet.mem_insert (PSet.ofNat k₁) (PSet.ofNat k₁))

theorem false_of_subset_of_nat_ge {k₁ k₂ : Nat} (h : k₁ < k₂) : ¬ PSet.ofNat k₂ ⊆ PSet.ofNat k₁ := by
  intro hsub
  have hk : PSet.ofNat k₁ ∈ PSet.ofNat k₂ := of_nat_mem_of_lt h
  exact mem_self (all_mem_of_subset hsub _ hk)

theorem le_of_subset {k₁ k₂ : Nat} (h : PSet.ofNat k₁ ⊆ PSet.ofNat k₂) : k₁ ≤ k₂ := by
  by_contra h'
  exact false_of_subset_of_nat_ge (Nat.lt_of_not_ge h') h

theorem of_nat_is_transitive {k : Nat} : is_transitive (PSet.ofNat k) := by
  induction k with
  | zero =>
      intro y hy
      exact False.elim (PSet.notMem_empty _ hy)
  | succ n ih =>
      rw [of_nat_succ]
      exact transitive_succ _ ih

theorem of_nat_of_mem_of_nat {y : PSet.{u}} {k : Nat} (h : y ∈ PSet.ofNat.{u} k) :
    ∃ j : Nat, PSet.Equiv y (PSet.ofNat.{u} j) := by
  induction k with
  | zero =>
      exact False.elim (PSet.notMem_empty _ h)
  | succ n ih =>
      rw [of_nat_succ] at h
      rcases PSet.mem_insert_iff.mp h with hy | hy
      · exact ⟨n, hy⟩
      · exact ih hy

theorem of_nat_inj {n k : Nat} (hneq : n ≠ k) : ¬ PSet.Equiv (PSet.ofNat.{u} n) (PSet.ofNat.{u} k) := by
  intro h
  apply hneq
  simpa [rank_ofNat] using PSet.rank_congr h

theorem is_transitive_omega : is_transitive (PSet.omega : pSet) := by
  intro z hz
  apply subset_of_all_mem
  intro w hw
  rcases mem_unfold.mp hz with ⟨i, hi⟩
  have hw' : w ∈ PSet.ofNat i.down := (PSet.Mem.congr_right hi).1 hw
  rcases of_nat_of_mem_of_nat hw' with ⟨j, hj⟩
  exact (PSet.Mem.congr_left hj).2 ⟨ULift.up j, PSet.Equiv.rfl⟩

theorem is_ewo_omega : epsilon_well_orders (PSet.omega : pSet) := by
  constructor
  · intro y hy z hz
    rcases mem_unfold.mp hy with ⟨i, hi⟩
    rcases mem_unfold.mp hz with ⟨j, hj⟩
    rcases lt_trichotomy i.down j.down with hlt | heq | hgt
    · exact Or.inr <| Or.inl <|
        (PSet.Mem.congr_right hj).2 <| (PSet.Mem.congr_left hi).2 <| of_nat_mem_of_lt hlt
    · have hij : i = j := by
        cases i
        cases j
        cases heq
        rfl
      subst hij
      exact Or.inl (hi.trans hj.symm)
    · exact Or.inr <| Or.inr <|
        (PSet.Mem.congr_right hi).2 <| (PSet.Mem.congr_left hj).2 <| of_nat_mem_of_lt hgt
  · intro s _ hs
    exact well_founded s hs

theorem Ord_omega : Ord (PSet.omega : pSet) :=
  ⟨is_ewo_omega, is_transitive_omega⟩

theorem lt_of_of_nat_mem {k₁ k₂ : Nat} (h : PSet.ofNat k₁ ∈ PSet.ofNat k₂) : k₁ < k₂ := by
  have hlt := PSet.rank_lt_of_mem h
  simpa [rank_ofNat] using hlt

theorem omega_inj {i j : PSet.omega.Type} (h : PSet.Equiv (PSet.omega.Func i) (PSet.omega.Func j)) :
    i = j := by
  cases i with
  | up i =>
      cases j with
      | up j =>
          change PSet.Equiv (PSet.ofNat i) (PSet.ofNat j) at h
          have hijNat : i = j := by
            simpa [rank_ofNat] using PSet.rank_congr h
          cases hijNat
          rfl

theorem mk_type_mk_eq''' (o : ordinal) : Cardinal.mk (ordinal.mk o).Type = o.card := by
  simp

theorem card_ex_type (κ : cardinal) : Cardinal.mk (card_ex κ).Type = κ := by
  simp [card_ex]

theorem card_ex_rank (κ : cardinal) : PSet.rank (card_ex κ) = Cardinal.ord κ := by
  simp [card_ex]

attribute [nolint simpNF] mk_type_mk_eq''' card_ex_type card_ex_rank

theorem mk_equiv_of_eq {β₁ β₂ : ordinal} (h : β₁ = β₂) :
    PSet.Equiv (ordinal.mk β₁) (ordinal.mk β₂) := by
  subst h
  exact PSet.Equiv.rfl

theorem zero_aleph : cardinal.omega = Cardinal.aleph 0 := by
  simpa [cardinal.omega] using (Cardinal.aleph_zero : Cardinal.aleph 0 = Cardinal.aleph0)

@[simp] theorem omega_lt_aleph_one : cardinal.omega < Cardinal.aleph 1 := by
  simpa [cardinal.omega] using Cardinal.aleph0_lt_aleph_one

theorem aleph_one_eq_succ_aleph_zero : Cardinal.aleph 1 = Order.succ cardinal.omega := by
  simpa [cardinal.omega] using (Cardinal.succ_aleph0).symm

/-- The Kuratowski ordered pair of two pre-sets. -/
def pair (x y : pSet.{u}) : pSet.{u} := {{x}, {x, y}}

theorem unordered_pair_congr_right {a b c : pSet.{u}} (h : PSet.Equiv b c) :
    PSet.Equiv ({a, b} : pSet.{u}) ({a, c} : pSet.{u}) := by
  apply PSet.Mem.ext
  intro z
  constructor
  · intro hz
    rcases (PSet.mem_pair.mp hz) with hza | hzb
    · exact PSet.mem_pair.mpr (Or.inl hza)
    · exact PSet.mem_pair.mpr (Or.inr (hzb.trans h))
  · intro hz
    rcases (PSet.mem_pair.mp hz) with hza | hzc
    · exact PSet.mem_pair.mpr (Or.inl hza)
    · exact PSet.mem_pair.mpr (Or.inr (hzc.trans h.symm))

theorem unordered_pair_congr_left {a b c : pSet.{u}} (h : PSet.Equiv b c) :
    PSet.Equiv ({b, a} : pSet.{u}) ({c, a} : pSet.{u}) := by
  apply PSet.Mem.ext
  intro z
  constructor
  · intro hz
    rcases (PSet.mem_pair.mp hz) with hzb | hza
    · exact PSet.mem_pair.mpr (Or.inl (hzb.trans h))
    · exact PSet.mem_pair.mpr (Or.inr hza)
  · intro hz
    rcases (PSet.mem_pair.mp hz) with hzc | hza
    · exact PSet.mem_pair.mpr (Or.inl (hzc.trans h.symm))
    · exact PSet.mem_pair.mpr (Or.inr hza)

theorem singleton_congr {a b : pSet.{u}} (h : PSet.Equiv a b) :
    PSet.Equiv ({a} : pSet.{u}) ({b} : pSet.{u}) := by
  apply PSet.Mem.ext
  intro z
  rw [PSet.mem_singleton, PSet.mem_singleton]
  constructor
  · intro hz
    exact hz.trans h
  · intro hz
    exact hz.trans h.symm

theorem pair_congr_right {a b c : pSet.{u}} (h : PSet.Equiv b c) :
    PSet.Equiv (pair a b) (pair a c) := by
  apply PSet.Mem.ext
  intro z
  constructor
  · intro hz
    rcases (PSet.mem_pair.mp hz) with hza | hzab
    · exact PSet.mem_pair.mpr (Or.inl hza)
    · exact PSet.mem_pair.mpr (Or.inr (hzab.trans (unordered_pair_congr_right h)))
  · intro hz
    rcases (PSet.mem_pair.mp hz) with hza | hzac
    · exact PSet.mem_pair.mpr (Or.inl hza)
    · exact PSet.mem_pair.mpr (Or.inr (hzac.trans (unordered_pair_congr_right h.symm)))

theorem pair_congr_left {a b c : pSet.{u}} (h : PSet.Equiv b c) :
    PSet.Equiv (pair b a) (pair c a) := by
  apply PSet.Mem.ext
  intro z
  constructor
  · intro hz
    rcases (PSet.mem_pair.mp hz) with hzb | hzba
    · exact PSet.mem_pair.mpr (Or.inl (hzb.trans (singleton_congr h)))
    · exact PSet.mem_pair.mpr (Or.inr (hzba.trans (unordered_pair_congr_left h)))
  · intro hz
    rcases (PSet.mem_pair.mp hz) with hzc | hzca
    · exact PSet.mem_pair.mpr (Or.inl (hzc.trans (singleton_congr h.symm)))
    · exact PSet.mem_pair.mpr (Or.inr (hzca.trans (unordered_pair_congr_left h.symm)))

theorem pair_mem_congr_right {a b c x : pSet.{u}} (h : PSet.Equiv b c) :
    pair a b ∈ x ↔ pair a c ∈ x := by
  exact PSet.Mem.congr_left (pair_congr_right h)

theorem pair_mem_congr_left {a b c x : pSet.{u}} (h : PSet.Equiv b c) :
    pair b a ∈ x ↔ pair c a ∈ x := by
  exact PSet.Mem.congr_left (pair_congr_left h)

/-- The Cartesian product of two pre-sets, encoded using Kuratowski pairs. -/
def prod (x y : pSet.{u}) : pSet.{u} :=
  ⟨x.Type × y.Type, fun ij => pair (x.Func ij.1) (y.Func ij.2)⟩

theorem mem_prod_of_mem {x y a b : pSet.{u}} (ha : a ∈ x) (hb : b ∈ y) :
    pair a b ∈ prod x y := by
  rcases mem_unfold.mp ha with ⟨i, hi⟩
  rcases mem_unfold.mp hb with ⟨j, hj⟩
  refine ⟨(i, j), ?_⟩
  exact (pair_congr_left hi).trans (pair_congr_right hj)

/-- A weak function is a single-valued total relation from `x` to `y`. -/
def is_weak_func (x y f : pSet.{u}) : Prop :=
  ∀ z, z ∈ x → ∃ w, w ∈ y ∧ pair z w ∈ f ∧ ∀ v, v ∈ y → pair z v ∈ f → PSet.Equiv v w

/-- A function is a weak function whose graph is contained in the Cartesian product. -/
def is_func (x y f : pSet.{u}) : Prop :=
  f ⊆ prod x y ∧ is_weak_func x y f

/-- A relation on `x × y` is total when every element of `x` appears in its graph. -/
def is_total (x y f : pSet.{u}) : Prop :=
  ∀ z, z ∈ x → ∃ w, w ∈ y ∧ pair z w ∈ f

/-- An extensional relation respects equivalence of both coordinates. -/
def is_extensional (f : pSet.{u}) : Prop :=
  ∀ w₁ w₂ v₁ v₂, pair w₁ v₁ ∈ f → pair w₂ v₂ ∈ f →
    PSet.Equiv w₁ w₂ → PSet.Equiv v₁ v₂

/-- A relation is surjective onto `y` when every target element has a preimage in `x`. -/
def is_surj (x y f : pSet.{u}) : Prop :=
  ∀ b, b ∈ y → ∃ a, a ∈ x ∧ pair a b ∈ f

/-- An injective relation never sends equivalent outputs to inequivalent inputs. -/
def is_inj (f : pSet.{u}) : Prop :=
  ∀ w₁ w₂ v₁ v₂, pair w₁ v₁ ∈ f → pair w₂ v₂ ∈ f →
    PSet.Equiv v₁ v₂ → PSet.Equiv w₁ w₂

/-- An injective function from `x` to `y`. -/
def is_injective_function (x y f : pSet.{u}) : Prop :=
  is_func x y f ∧ is_inj f

/-- There exists an injective function from `x` into `y`. -/
def injects_into (x y : pSet.{u}) : Prop :=
  ∃ f, is_injective_function x y f

theorem is_weak_func_congr {x y f g : pSet.{u}} (hfg : PSet.Equiv f g) :
    is_weak_func x y f ↔ is_weak_func x y g := by
  constructor <;> intro h z hz
  · rcases h z hz with ⟨w, hwy, hwf, huniq⟩
    refine ⟨w, hwy, (PSet.Mem.congr_right hfg).1 hwf, ?_⟩
    intro v hvy hvg
    exact huniq v hvy ((PSet.Mem.congr_right hfg).2 hvg)
  · rcases h z hz with ⟨w, hwy, hwg, huniq⟩
    refine ⟨w, hwy, (PSet.Mem.congr_right hfg).2 hwg, ?_⟩
    intro v hvy hvf
    exact huniq v hvy ((PSet.Mem.congr_right hfg).1 hvf)

theorem is_func_congr {x y f g : pSet.{u}} (hfg : PSet.Equiv f g) :
    is_func x y f ↔ is_func x y g := by
  constructor <;> intro h
  · refine ⟨(PSet.Subset.congr_left hfg).1 h.1, (is_weak_func_congr hfg).1 h.2⟩
  · refine ⟨(PSet.Subset.congr_left hfg).2 h.1, (is_weak_func_congr hfg).2 h.2⟩

theorem subset_prod_of_is_func {x y f : pSet.{u}} (h : is_func x y f) : f ⊆ prod x y :=
  h.1

theorem is_total_of_is_func {x y f : pSet.{u}} (h : is_func x y f) : is_total x y f := by
  intro z hz
  rcases h.2 z hz with ⟨w, hwy, hwf, _⟩
  exact ⟨w, hwy, hwf⟩

/-- The pre-set of graphs of functions from `x` to `y`. -/
def functions (x y : pSet.{u}) : pSet.{u} :=
  PSet.sep (fun z => is_func x y z) (PSet.powerset (prod x y))

theorem mem_functions_iff {x y z : pSet.{u}} : z ∈ functions x y ↔ is_func x y z := by
  let hcongr : ∀ a b : pSet.{u}, PSet.Equiv a b → is_func x y a → is_func x y b := by
    intro a b hab
    exact (is_func_congr hab).1
  constructor
  · intro hz
    exact (PSet.mem_sep hcongr).1 hz |>.2
  · intro hz
    refine (PSet.mem_sep hcongr).2 ?_
    exact ⟨(PSet.mem_powerset).2 hz.1, hz⟩

/-- Lift a weak `pSet`-function to an actual Lean function landing in the subtype of members of
`y`. This avoids choosing an index of `y`; later refinements can recover index-level lifts when the
target indexing is rigid enough. -/
noncomputable def function_lift {x y f : pSet.{u}} (h : is_weak_func x y f) :
    x.Type → {w : pSet.{u} // w ∈ y} :=
  fun i =>
    let hw := h (x.Func i) (mem_mk' (x := x) (i := i))
    ⟨Classical.choose hw, (Classical.choose_spec hw).1⟩

/-- The chosen value of `function_lift` stays in the graph of the weak function. -/
theorem function_lift_graph {x y f : pSet.{u}} (h : is_weak_func x y f) (i : x.Type) :
    pair (x.Func i) (function_lift h i).1 ∈ f := by
  dsimp [function_lift]
  exact (Classical.choose_spec (h (x.Func i) (mem_mk' (x := x) (i := i)))).2.1

/-- Any two graph values over the same input are equivalent by weak functionality. -/
theorem function_lift_graph_unique {x y f : pSet.{u}} (h : is_weak_func x y f) (i : x.Type)
    {v : pSet.{u}} (hv : v ∈ y) (hgraph : pair (x.Func i) v ∈ f) :
    PSet.Equiv v (function_lift h i).1 := by
  dsimp [function_lift]
  exact (Classical.choose_spec (h (x.Func i) (mem_mk' (x := x) (i := i)))).2.2 v hv hgraph

/-- If membership in `y` has unique representatives at the index level, a weak `pSet`-function
can be lifted to an honest Lean function into `y.Type`. -/
theorem function_lift_indexed_aux {x y f : pSet.{u}} (h : is_weak_func x y f) (i : x.Type) :
    ∃ j : y.Type, pair (x.Func i) (y.Func j) ∈ f := by
  rcases h (x.Func i) (mem_mk' (x := x) (i := i)) with ⟨w, hwy, hwf, _⟩
  rcases mem_unfold.mp hwy with ⟨j, hj⟩
  exact ⟨j, (pair_mem_congr_right hj).1 hwf⟩

/-- Indexed form of `function_lift` when the target indexing is extensional enough to choose
canonical representatives. -/
noncomputable def function_lift_indexed {x y f : pSet.{u}} (h : is_weak_func x y f) :
    x.Type → y.Type :=
  fun i => Classical.choose (function_lift_indexed_aux h i)

/-- The graph of the indexed lift lies in `f`. -/
theorem function_lift_indexed_spec {x y f : pSet.{u}} (h : is_weak_func x y f) (i : x.Type) :
    pair (x.Func i) (y.Func (function_lift_indexed h i)) ∈ f :=
  Classical.choose_spec (function_lift_indexed_aux h i)

theorem mem_fun_of_function_lift_graph {x y f : pSet.{u}} (h : is_weak_func x y f) (i : x.Type)
    {w : {v : pSet.{u} // v ∈ y}} (hw : function_lift h i = w) :
    pair (x.Func i) w.1 ∈ f := by
  simpa [hw] using function_lift_graph h i

theorem mem_fun_of_function_lift_indexed_graph {x y f : pSet.{u}} (h : is_weak_func x y f)
    (i : x.Type) {j : y.Type} (hij : function_lift_indexed h i = j) :
    pair (x.Func i) (y.Func j) ∈ f := by
  simpa [hij] using function_lift_indexed_spec h i

/-- If the indexing of `y` is injective up to `PSet.Equiv`, then a graph edge determines the value
of `function_lift_indexed`. -/
theorem function_lift_indexed_eq_of_graph {x y f : pSet.{u}} (h : is_weak_func x y f)
    (hinj : ∀ j₁ j₂ : y.Type, PSet.Equiv (y.Func j₁) (y.Func j₂) → j₁ = j₂)
    (i : x.Type) (j : y.Type) (hgraph : pair (x.Func i) (y.Func j) ∈ f) :
    function_lift_indexed h i = j := by
  apply hinj
  refine (function_lift_graph_unique h i (mem_mk' (x := y) (i := function_lift_indexed h i))
    (function_lift_indexed_spec h i)).trans ?_
  exact (function_lift_graph_unique h i (mem_mk' (x := y) (i := j)) hgraph).symm

theorem surj_lift {x y f : pSet.{u}} (hweak : is_weak_func x y f) (hsurj : is_surj x y f) :
    ∀ b, b ∈ y → ∃ i : x.Type, PSet.Equiv b (function_lift hweak i).1 := by
  intro b hb
  rcases hsurj b hb with ⟨a, ha, hab⟩
  rcases mem_unfold.mp ha with ⟨i, hai⟩
  have hgraph : pair (x.Func i) b ∈ f := by
    exact (pair_mem_congr_left hai).1 hab
  exact ⟨i, function_lift_graph_unique hweak i hb hgraph⟩

/-- If the target indexing is injective up to equivalence, surjectivity of the graph yields
surjectivity of the indexed lift. -/
theorem surj_lift_indexed {x y f : pSet.{u}} (hweak : is_weak_func x y f)
    (hinj : ∀ j₁ j₂ : y.Type, PSet.Equiv (y.Func j₁) (y.Func j₂) → j₁ = j₂)
    (hsurj : is_surj x y f) : Function.Surjective (function_lift_indexed hweak) := by
  intro j
  rcases hsurj (y.Func j) (mem_mk' (x := y) (i := j)) with ⟨a, ha, hab⟩
  rcases mem_unfold.mp ha with ⟨i, hai⟩
  have hgraph : pair (x.Func i) (y.Func j) ∈ f := by
    exact (pair_mem_congr_left hai).1 hab
  exact ⟨i, function_lift_indexed_eq_of_graph hweak hinj i j hgraph⟩

end pSet

end Flypitch
