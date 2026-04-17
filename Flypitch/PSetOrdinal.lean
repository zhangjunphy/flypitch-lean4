import Mathlib.SetTheory.Cardinal.Aleph
import Mathlib.SetTheory.Cardinal.Regular
import Mathlib.SetTheory.ZFC.Ordinal

universe u

namespace Flypitch

/-!
`Flypitch.PSetOrdinal` starts the forcing-side port by reinstating the ordinal/cardinal encoding
layer used by the original development. Mathlib already supplies the underlying `PSet` and
von Neumann ordinal machinery, so this file mainly provides compatibility names and the first
group of bridge lemmas that later forcing files expect.
-/

set_option linter.missingDocs false
set_option linter.style.longLine false

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

@[simp] theorem mk_zero_type : (ordinal.mk 0).Type = (0 : ordinal).ToType := by
  simp [ordinal.mk]

def mk_zero_cast : (0 : ordinal).ToType → (ordinal.mk 0).Type :=
  cast mk_zero_type.symm

def mk_zero_cast' : (ordinal.mk 0).Type → (0 : ordinal).ToType :=
  cast mk_zero_type

theorem mk_zero_forall {P : (ordinal.mk 0).Type → (ordinal.mk 0).Type → Prop} :
    (∀ i j : (ordinal.mk 0).Type, P i j) ↔
      ∀ i' j' : (0 : ordinal).ToType, P (mk_zero_cast i') (mk_zero_cast j') := by
  constructor
  · intro h i' j'
    exact h (mk_zero_cast i') (mk_zero_cast j')
  · intro h i j
    exact isEmptyElim (mk_zero_cast' i)

end ordinal

namespace pSet

/-- The successor of a pre-set, implemented as `insert x x`. -/
abbrev succ (x : pSet) : pSet := insert x x

@[simp] theorem ordinal.mk_succ {η : ordinal} :
    PSet.Equiv (ordinal.mk (Order.succ η)) (pSet.succ (ordinal.mk η)) := by
  apply ZFSet.exact
  change Ordinal.toZFSet (Order.succ η) = ZFSet.mk (pSet.succ (ordinal.mk η))
  change Ordinal.toZFSet (η + 1) = ZFSet.mk (pSet.succ (ordinal.mk η))
  rw [Ordinal.toZFSet_add_one]
  rfl

/-- Pick a canonical pre-set representative of a cardinal via its initial ordinal. -/
noncomputable abbrev card_ex (κ : cardinal) : pSet := ordinal.mk (Cardinal.ord κ)

attribute [nolint docBlame] succ card_ex

theorem mk_eq {x : pSet} : x = ⟨x.Type, x.Func⟩ := by
  cases x
  rfl

@[simp] theorem eta {x : pSet} : PSet.mk x.Type x.Func = x :=
  mk_eq.symm

theorem powerset_type {x : pSet} : (PSet.powerset x).Type = Set x.Type := by
  cases x
  rfl

@[simp] theorem mem_mk' {x : pSet} {i : x.Type} : x.Func i ∈ x :=
  PSet.func_mem _ _

theorem mem_unfold {x y : pSet} : x ∈ y ↔ ∃ j : y.Type, PSet.Equiv x (y.Func j) :=
  PSet.mem_def

theorem ext_iff {x y : pSet} : PSet.Equiv x y ↔ ∀ z, z ∈ x ↔ z ∈ y := by
  simpa using (PSet.equiv_iff_mem (x := x) (y := y))

theorem equiv_of_eq {x y : pSet} : ZFSet.mk x = ZFSet.mk y → PSet.Equiv x y :=
  ZFSet.exact

theorem equiv_iff_eq {x y : pSet} : PSet.Equiv x y ↔ ZFSet.mk x = ZFSet.mk y := by
  constructor
  · exact ZFSet.sound
  · exact ZFSet.exact

theorem mem_iff {x y : pSet} : x ∈ y ↔ ZFSet.mk x ∈ ZFSet.mk y := by
  exact ZFSet.mk_mem_iff

theorem not_mem_iff {x y : pSet} : x ∉ y ↔ ¬ ZFSet.mk x ∈ ZFSet.mk y := by
  rw [mem_iff]

theorem mem_sound {x y : pSet} : x ∈ y ↔ ZFSet.mk x ∈ ZFSet.mk y :=
  mem_iff

theorem mem_insert {x y z : pSet} (h : x ∈ insert y z) : PSet.Equiv x y ∨ x ∈ z := by
  simpa using (PSet.mem_insert_iff.mp h)

theorem mem_insert' {x y z : pSet} (h : PSet.Equiv x y ∨ x ∈ z) : x ∈ insert y z := by
  simpa using (PSet.mem_insert_iff.mpr h)

theorem Set.subset_iff_all_mem {x y : ZFSet.{u}} : x ⊆ y ↔ ∀ z, z ∈ x → z ∈ y := by
  rfl

theorem empty_empty : (∅ : ZFSet.{u}) = ZFSet.mk (∅ : pSet.{u}) := by
  rfl

theorem Set.mk_unfold {x : pSet.{u}} : ZFSet.mk x = ⟦x⟧ := by
  rfl

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

@[simp] theorem succ_type {x : pSet} : (succ x).Type = Option x.Type := by
  cases x
  rfl

@[simp] theorem option_succ_type {x : pSet} : Option (succ x).Type = Option (Option x.Type) := by
  simp

def succ_type_cast {x : pSet} : (succ x).Type → Option x.Type :=
  cast succ_type

def succ_type_cast' {x : pSet} : Option x.Type → (succ x).Type :=
  cast succ_type.symm

def option_cast' {x : pSet} : Option (Option x.Type) → Option (succ x).Type :=
  cast option_succ_type.symm

@[simp] theorem succ_func_none {x : pSet} : (succ x).Func (succ_type_cast' none) = x := by
  cases x
  rfl

@[simp] theorem succ_func_some {x : pSet} {i : x.Type} :
    (succ x).Func (succ_type_cast' (some i)) = x.Func i := by
  cases x
  rfl

theorem succ_type_forall {x : pSet} {P : (succ x).Type → Prop} :
    (∀ i : (succ x).Type, P i) ↔ ∀ i : Option x.Type, P (succ_type_cast' i) := by
  cases x
  rfl

theorem succ_type_exists {x : pSet} {P : (succ x).Type → Prop} :
    (∃ i : (succ x).Type, P i) ↔ ∃ i : Option x.Type, P (succ_type_cast' i) := by
  cases x
  rfl

theorem option_succ_type_forall {x : pSet} {P : Option (succ x).Type → Prop} :
    (∀ i : Option (succ x).Type, P i) ↔ ∀ i : Option (Option x.Type), P (option_cast' i) := by
  cases x
  rfl

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

theorem subset_sound {x y : pSet} : x ⊆ y ↔ (x : Set pSet) ⊆ (y : Set pSet) := by
  constructor
  · intro h z hz
    exact all_mem_of_subset h z hz
  · intro h
    exact subset_of_all_mem h

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

theorem mk_type_mk_eq (κ : cardinal) : Cardinal.mk (ordinal.mk (Cardinal.ord κ)).Type = κ := by
  simp

namespace ordinal

theorem mk_card {η : ordinal} : Cardinal.mk (ordinal.mk η).Type = η.card :=
  mk_type_mk_eq''' η

end ordinal

theorem mk_type_mk_eq' (κ : cardinal) (_hInf : cardinal.omega < κ) :
    Cardinal.mk (ordinal.mk (Cardinal.ord κ)).Type = κ :=
  mk_type_mk_eq κ

@[simp] theorem mk_type_mk_eq'' (κ : cardinal) :
    Cardinal.mk (card_ex κ).Type = κ :=
  by simp [card_ex]

@[simp] theorem mk_type_mk_eq'''' {k : ordinal} :
    Cardinal.mk (ordinal.mk (Cardinal.ord (Cardinal.aleph k))).Type = Cardinal.aleph k :=
  mk_type_mk_eq (Cardinal.aleph k)

@[simp] theorem mk_type_mk_eq''''' {k : ordinal} :
    Cardinal.mk (card_ex (Cardinal.aleph k)).Type = Cardinal.aleph k :=
  by simp [card_ex]

theorem card_ex_type (κ : cardinal) : Cardinal.mk (card_ex κ).Type = κ := by
  simp [card_ex]

theorem card_ex_rank (κ : cardinal) : PSet.rank (card_ex κ) = Cardinal.ord κ := by
  simp [card_ex]

attribute [nolint simpNF] mk_type_mk_eq''' card_ex_type card_ex_rank

theorem mk_equiv_of_eq {β₁ β₂ : ordinal} (h : β₁ = β₂) :
    PSet.Equiv (ordinal.mk β₁) (ordinal.mk β₂) := by
  subst h
  exact PSet.Equiv.rfl

theorem eq_of_mk_equiv {β₁ β₂ : ordinal}
    (h : PSet.Equiv (ordinal.mk β₁) (ordinal.mk β₂)) : β₁ = β₂ := by
  apply le_antisymm
  · by_contra hβ
    have hlt : β₂ < β₁ := lt_of_not_ge hβ
    have hself : ordinal.mk β₁ ∈ ordinal.mk β₁ :=
      (PSet.Mem.congr_left h).2 (ordinal.mk_mem_mk_of_lt hlt)
    exact mem_self hself
  · by_contra hβ
    have hlt : β₁ < β₂ := lt_of_not_ge hβ
    have hself : ordinal.mk β₂ ∈ ordinal.mk β₂ :=
      (PSet.Mem.congr_left h.symm).2 (ordinal.mk_mem_mk_of_lt hlt)
    exact mem_self hself

theorem eq_iff_mk_eq {β₁ β₂ : ordinal} :
    β₁ = β₂ ↔ PSet.Equiv (ordinal.mk β₁) (ordinal.mk β₂) := by
  constructor
  · exact mk_equiv_of_eq
  · exact eq_of_mk_equiv

theorem zero_aleph : cardinal.omega = Cardinal.aleph 0 := by
  simp [cardinal.omega]

@[simp] theorem omega_lt_aleph_one : cardinal.omega < Cardinal.aleph 1 := by
  change Cardinal.aleph0 < Cardinal.aleph 1
  exact Cardinal.aleph0_lt_aleph_one

theorem aleph_one_eq_succ_aleph_zero : Cardinal.aleph 1 = Order.succ cardinal.omega := by
  simp [cardinal.omega]

theorem aleph_two_eq_succ_aleph_one : Cardinal.aleph 2 = Order.succ (Cardinal.aleph 1) := by
  simp [one_add_one_eq_two]

theorem mk_omega_eq : Cardinal.mk PSet.omega.Type = cardinal.omega := by
  simp [cardinal.omega, PSet.omega]

theorem is_regular_aleph_one : Cardinal.IsRegular (Cardinal.aleph 1) := by
  simpa using Cardinal.isRegular_aleph_one

theorem is_regular_aleph_two : Cardinal.IsRegular (Cardinal.aleph 2) := by
  simpa [one_add_one_eq_two] using Cardinal.isRegular_aleph_add_one 1

theorem aleph_one_lt_aleph_two : Cardinal.aleph 1 < Cardinal.aleph 2 := by
  exact (Cardinal.aleph_lt_aleph (o₁ := (1 : Ordinal)) (o₂ := (2 : Ordinal))).2 (by simp)

theorem omega_lt_aleph_two : cardinal.omega < Cardinal.aleph 2 := by
  exact lt_trans omega_lt_aleph_one aleph_one_lt_aleph_two

theorem two_eq_succ_one : (2 : ordinal) = Order.succ 1 := by
  symm
  change (1 : ordinal) + 1 = 2
  simpa using (one_add_one_eq_two : (1 : ordinal) + 1 = 2)

theorem add_one_lt_add_one {a b : ordinal} : a < b ↔ a + 1 < b + 1 := by
  exact (Order.succ_lt_succ_iff : Order.succ a < Order.succ b ↔ a < b).symm

theorem one_lt_two : (1 : ordinal) < 2 := by
  rw [two_eq_succ_one]
  exact Order.lt_succ 1

theorem exists_mem_of_nonzero {η : ordinal} (hη : 0 < η) : ∃ z : pSet, z ∈ ordinal.mk η := by
  exact ⟨ordinal.mk 0, ordinal.mk_mem_mk_of_lt hη⟩

theorem exists_mem_of_regular {κ : cardinal} (hκ : Cardinal.IsRegular κ) : ∃ z : pSet, z ∈ card_ex κ := by
  simpa [pSet.card_ex] using exists_mem_of_nonzero (Cardinal.IsRegular.ord_pos hκ)

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

namespace pair_mem

theorem congr_right {a b c x : pSet.{u}} (h : PSet.Equiv b c) :
    pair a b ∈ x ↔ pair a c ∈ x :=
  pair_mem_congr_right h

theorem congr_left {a b c x : pSet.{u}} (h : PSet.Equiv b c) :
    pair b a ∈ x ↔ pair c a ∈ x :=
  pair_mem_congr_left h

end pair_mem

theorem pair_sound {x y : pSet.{u}} : ZFSet.mk (pair x y) = ZFSet.pair (ZFSet.mk x) (ZFSet.mk y) := by
  rfl

theorem eq_iff_eq_pair {x y x' y' : pSet.{u}} :
    PSet.Equiv x x' ∧ PSet.Equiv y y' ↔ PSet.Equiv (pair x y) (pair x' y') := by
  constructor
  · rintro ⟨hx, hy⟩
    apply ZFSet.exact
    rw [pair_sound, pair_sound, ZFSet.pair_inj]
    exact ⟨ZFSet.sound hx, ZFSet.sound hy⟩
  · intro h
    have h' : ZFSet.pair (ZFSet.mk x) (ZFSet.mk y) = ZFSet.pair (ZFSet.mk x') (ZFSet.mk y') := by
      simpa [pair_sound] using ZFSet.sound h
    rcases (ZFSet.pair_inj).mp h' with ⟨hx, hy⟩
    exact ⟨ZFSet.exact hx, ZFSet.exact hy⟩

/-- The Cartesian product of two pre-sets, encoded using Kuratowski pairs. -/
def prod (x y : pSet.{u}) : pSet.{u} :=
  ⟨x.Type × y.Type, fun ij => pair (x.Func ij.1) (y.Func ij.2)⟩

theorem prod_congr_left {x₁ x₂ y : pSet.{u}} (h : PSet.Equiv x₁ x₂) :
    PSet.Equiv (prod x₁ y) (prod x₂ y) := by
  apply PSet.Mem.ext
  intro z
  constructor
  · intro hz
    rcases mem_unfold.mp hz with ⟨⟨i, j⟩, hij⟩
    rcases h.exists_left i with ⟨i', hii'⟩
    exact ⟨(i', j), hij.trans (pair_congr_left hii')⟩
  · intro hz
    rcases mem_unfold.mp hz with ⟨⟨i, j⟩, hij⟩
    rcases h.exists_right i with ⟨i', hi'i⟩
    exact ⟨(i', j), hij.trans (pair_congr_left hi'i.symm)⟩

theorem prod_congr_right {x y₁ y₂ : pSet.{u}} (h : PSet.Equiv y₁ y₂) :
    PSet.Equiv (prod x y₁) (prod x y₂) := by
  apply PSet.Mem.ext
  intro z
  constructor
  · intro hz
    rcases mem_unfold.mp hz with ⟨⟨i, j⟩, hij⟩
    rcases h.exists_left j with ⟨j', hjj'⟩
    exact ⟨(i, j'), hij.trans (pair_congr_right hjj')⟩
  · intro hz
    rcases mem_unfold.mp hz with ⟨⟨i, j⟩, hij⟩
    rcases h.exists_right j with ⟨j', hj'j⟩
    exact ⟨(i, j'), hij.trans (pair_congr_right hj'j.symm)⟩

theorem mem_prod_of_mem {x y a b : pSet.{u}} (ha : a ∈ x) (hb : b ∈ y) :
    pair a b ∈ prod x y := by
  rcases mem_unfold.mp ha with ⟨i, hi⟩
  rcases mem_unfold.mp hb with ⟨j, hj⟩
  refine ⟨(i, j), ?_⟩
  exact (pair_congr_left hi).trans (pair_congr_right hj)

theorem mem_prod_iff {x y a b : pSet.{u}} : pair a b ∈ prod x y ↔ a ∈ x ∧ b ∈ y := by
  constructor
  · intro h
    rcases mem_unfold.mp h with ⟨ij, hij⟩
    rcases (Flypitch.pSet.eq_iff_eq_pair).mpr hij with ⟨ha, hb⟩
    exact ⟨(PSet.Mem.congr_left ha).2 (mem_mk' (x := x) (i := ij.1)),
      (PSet.Mem.congr_left hb).2 (mem_mk' (x := y) (i := ij.2))⟩
  · rintro ⟨ha, hb⟩
    exact mem_prod_of_mem ha hb

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

theorem is_func_congr_left {x₁ x₂ y f : pSet.{u}} (h : PSet.Equiv x₁ x₂) :
    is_func x₁ y f ↔ is_func x₂ y f := by
  constructor
  · intro hf
    refine ⟨(PSet.Subset.congr_right (prod_congr_left h)).1 hf.1, ?_⟩
    intro z hz
    rcases hf.2 z ((PSet.Mem.congr_right h).2 hz) with ⟨w, hwy, hwf, huniq⟩
    exact ⟨w, hwy, hwf, huniq⟩
  · intro hf
    refine ⟨(PSet.Subset.congr_right (prod_congr_left h)).2 hf.1, ?_⟩
    intro z hz
    rcases hf.2 z ((PSet.Mem.congr_right h).1 hz) with ⟨w, hwy, hwf, huniq⟩
    exact ⟨w, hwy, hwf, huniq⟩

theorem is_func_congr_right {x y₁ y₂ f : pSet.{u}} (h : PSet.Equiv y₁ y₂) :
    is_func x y₁ f ↔ is_func x y₂ f := by
  constructor
  · intro hf
    refine ⟨(PSet.Subset.congr_right (prod_congr_right h)).1 hf.1, ?_⟩
    intro z hz
    rcases hf.2 z hz with ⟨w, hwy, hwf, huniq⟩
    refine ⟨w, (PSet.Mem.congr_right h).1 hwy, hwf, ?_⟩
    intro v hvy hvf
    exact huniq v ((PSet.Mem.congr_right h).2 hvy) hvf
  · intro hf
    refine ⟨(PSet.Subset.congr_right (prod_congr_right h)).2 hf.1, ?_⟩
    intro z hz
    rcases hf.2 z hz with ⟨w, hwy, hwf, huniq⟩
    refine ⟨w, (PSet.Mem.congr_right h).2 hwy, hwf, ?_⟩
    intro v hvy hvf
    exact huniq v ((PSet.Mem.congr_right h).1 hvy) hvf

theorem subset_prod_of_is_func {x y f : pSet.{u}} (h : is_func x y f) : f ⊆ prod x y :=
  h.1

theorem is_total_of_is_func {x y f : pSet.{u}} (h : is_func x y f) : is_total x y f := by
  intro z hz
  rcases h.2 z hz with ⟨w, hwy, hwf, _⟩
  exact ⟨w, hwy, hwf⟩

theorem is_func_iff {x y f : pSet.{u}} :
    is_func x y f ↔
      f ⊆ prod x y ∧ ∀ z, z ∈ x → ∃ w, w ∈ y ∧ pair z w ∈ f ∧
        ∀ v, pair z v ∈ f → PSet.Equiv v w := by
  constructor
  · intro h
    refine ⟨h.1, ?_⟩
    intro z hz
    rcases h.2 z hz with ⟨w, hwy, hwf, huniq⟩
    refine ⟨w, hwy, hwf, ?_⟩
    intro v hvf
    rcases mem_prod_iff.mp (PSet.mem_of_subset h.1 hvf) with ⟨_, hvy⟩
    exact huniq v hvy hvf
  · rintro ⟨hsub, hfun⟩
    refine ⟨hsub, ?_⟩
    intro z hz
    rcases hfun z hz with ⟨w, hwy, hwf, huniq⟩
    exact ⟨w, hwy, hwf, fun v hvy hvf => huniq v hvf⟩

/-- Build a subset of `x` from an indicator predicate on its indices. -/
def set_of_indicator {x : pSet.{u}} (χ : x.Type → Prop) : pSet.{u} :=
  ⟨{i : x.Type // χ i}, fun i => x.Func i.1⟩

/-- The pre-set powerset agrees with the ZFC powerset after quotienting. -/
theorem powerset_sound {x : pSet.{u}} : ZFSet.mk (PSet.powerset x) = ZFSet.powerset (ZFSet.mk x) := by
  apply ZFSet.ext
  intro z
  induction z using Quotient.inductionOn with
  | h z =>
      simp [ZFSet.mem_powerset, ZFSet.subset_iff, PSet.mem_powerset]

/-- The pre-set product agrees with the ZFC product after quotienting. -/
theorem prod_sound {x y : pSet.{u}} : ZFSet.mk (prod x y) = ZFSet.prod (ZFSet.mk x) (ZFSet.mk y) := by
  apply ZFSet.ext
  intro z
  induction z using Quotient.inductionOn with
  | h w =>
      constructor
      · intro hw
        have hw' : w ∈ prod x y := by
          simpa using hw
        rcases mem_unfold.mp hw' with ⟨⟨i, j⟩, hij⟩
        refine (ZFSet.mem_prod).2 ?_
        refine ⟨ZFSet.mk (x.Func i), ?_, ZFSet.mk (y.Func j), ?_, ?_⟩
        · simp [mem_mk' (x := x) (i := i)]
        · simp [mem_mk' (x := y) (i := j)]
        · have : ZFSet.mk w = ZFSet.mk (pair (x.Func i) (y.Func j)) := ZFSet.sound hij
          simpa [pair_sound] using this
      · intro hw
        rcases (ZFSet.mem_prod).1 hw with ⟨a, ha, b, hb, hab⟩
        rw [← ZFSet.mk_out a, ZFSet.mk_mem_iff] at ha
        rw [← ZFSet.mk_out b, ZFSet.mk_mem_iff] at hb
        have hwEq : ZFSet.mk w = ZFSet.mk (pair a.out b.out) := by
          rw [← ZFSet.mk_out a, ← ZFSet.mk_out b] at hab
          simpa [pair_sound] using hab
        have hpeq : PSet.Equiv w (pair a.out b.out) := ZFSet.exact hwEq
        exact (PSet.Mem.congr_left hpeq).2 (mem_prod_of_mem ha hb)

theorem is_func_sound {x y f : pSet.{u}} :
    is_func x y f ↔ ZFSet.IsFunc (ZFSet.mk x) (ZFSet.mk y) (ZFSet.mk f) := by
  constructor
  · intro hf
    refine ⟨?_, ?_⟩
    · simpa [prod_sound] using (ZFSet.subset_iff).2 hf.1
    · intro z hz
      rw [← ZFSet.mk_out z, ZFSet.mk_mem_iff] at hz
      rcases hf.2 z.out hz with ⟨w, hwy, hwf, huniq⟩
      refine ⟨ZFSet.mk w, ?_, ?_⟩
      · rw [← ZFSet.mk_out z]
        change ZFSet.mk (pair z.out w) ∈ ZFSet.mk f
        rwa [ZFSet.mk_mem_iff]
      · intro v hv
        have hv' : pair z.out v.out ∈ f := by
          rw [← ZFSet.mk_out z, ← ZFSet.mk_out v] at hv
          change ZFSet.mk (pair z.out v.out) ∈ ZFSet.mk f at hv
          rwa [ZFSet.mk_mem_iff] at hv
        have hvy : v.out ∈ y := by
          exact (mem_prod_iff.mp (PSet.mem_of_subset hf.1 hv')).2
        have hEq : PSet.Equiv v.out w := huniq v.out hvy hv'
        simpa using ZFSet.sound hEq
  · intro hf
    refine ⟨?_, ?_⟩
    · exact (ZFSet.subset_iff).1 (by simpa [prod_sound] using hf.1)
    · intro z hz
      rcases hf.2 (ZFSet.mk z) (by simpa [ZFSet.mk_mem_iff] using hz) with ⟨w, hwf, huniq⟩
      refine ⟨w.out, ?_, ?_, ?_⟩
      · have hwymk : w ∈ ZFSet.mk y := (ZFSet.pair_mem_prod.1 (hf.1 hwf)).2
        rw [← ZFSet.mk_out w, ZFSet.mk_mem_iff] at hwymk
        exact hwymk
      · rw [← ZFSet.mk_out w] at hwf
        change ZFSet.mk (pair z w.out) ∈ ZFSet.mk f at hwf
        rwa [ZFSet.mk_mem_iff] at hwf
      · intro v hvy hvf
        have hvEq : ZFSet.mk v = w := by
          apply huniq
          simpa [pair_sound] using hvf
        rw [← ZFSet.mk_out w] at hvEq
        exact ZFSet.exact hvEq

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

theorem subset_prod_of_mem_functions {x y z : pSet.{u}} (hz : z ∈ functions x y) : z ⊆ prod x y :=
  subset_prod_of_is_func ((mem_functions_iff).1 hz)

theorem is_func_of_mem_functions {x y f : pSet.{u}} (hf : f ∈ functions x y) : is_func x y f :=
  (mem_functions_iff).1 hf

theorem is_weak_func_of_mem_functions {x y f : pSet.{u}} (hf : f ∈ functions x y) :
    is_weak_func x y f :=
  (is_func_of_mem_functions hf).2

/-- Lift a weak `pSet`-function to an actual Lean function landing in the subtype of members of
`y`. This avoids choosing an index of `y`; later refinements can recover index-level lifts when the
target indexing is rigid enough. -/
noncomputable def function_lift {x y f : pSet.{u}} (h : is_weak_func x y f) :
    x.Type → {w : pSet.{u} // w ∈ y} :=
  fun i =>
    let hw := h (x.Func i) (mem_mk' (x := x) (i := i))
    ⟨Classical.choose hw, (Classical.choose_spec hw).1⟩

/-- The value chosen by `function_lift` really lands in the target pre-set. -/
theorem function_lift_mem {x y f : pSet.{u}} (h : is_weak_func x y f) (i : x.Type) :
    (function_lift h i).1 ∈ y :=
  (function_lift h i).2

/-- The chosen value of `function_lift` stays in the graph of the weak function. -/
theorem function_lift_graph {x y f : pSet.{u}} (h : is_weak_func x y f) (i : x.Type) :
    pair (x.Func i) (function_lift h i).1 ∈ f := by
  dsimp [function_lift]
  exact (Classical.choose_spec (h (x.Func i) (mem_mk' (x := x) (i := i)))).2.1

theorem function_lift_spec {x y f : pSet.{u}} (h : is_weak_func x y f) (i : x.Type) :
    pair (x.Func i) (function_lift h i).1 ∈ f :=
  function_lift_graph h i

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

/-- The indexed lift lands on a genuine member of `y`. -/
theorem function_lift_indexed_mem {x y f : pSet.{u}} (h : is_weak_func x y f) (i : x.Type) :
    y.Func (function_lift_indexed h i) ∈ y :=
  mem_mk' (x := y) (i := function_lift_indexed h i)

/-- The graph of the indexed lift lies in `f`. -/
theorem function_lift_indexed_spec {x y f : pSet.{u}} (h : is_weak_func x y f) (i : x.Type) :
    pair (x.Func i) (y.Func (function_lift_indexed h i)) ∈ f :=
  Classical.choose_spec (function_lift_indexed_aux h i)

theorem function_lift'_spec {x y f : pSet.{u}} (h : is_weak_func x y f) (i : x.Type) :
    pair (x.Func i) (y.Func (function_lift_indexed h i)) ∈ f :=
  function_lift_indexed_spec h i

theorem mem_fun_of_function_lift_graph {x y f : pSet.{u}} (h : is_weak_func x y f) (i : x.Type)
    {w : {v : pSet.{u} // v ∈ y}} (hw : function_lift h i = w) :
    pair (x.Func i) w.1 ∈ f := by
  simpa [hw] using function_lift_graph h i

theorem mem_fun_of_function_lift_indexed_graph {x y f : pSet.{u}} (h : is_weak_func x y f)
    (i : x.Type) {j : y.Type} (hij : function_lift_indexed h i = j) :
    pair (x.Func i) (y.Func j) ∈ f := by
  simpa [hij] using function_lift_indexed_spec h i

theorem mem_fun_of_function_lift'_graph {x y f : pSet.{u}} (h : is_weak_func x y f)
    (i : x.Type) {j : y.Type} (hij : function_lift_indexed h i = j) :
    pair (x.Func i) (y.Func j) ∈ f :=
  mem_fun_of_function_lift_indexed_graph h i hij

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

theorem function_lift_graph_of_mem_fun_inj {x y f : pSet.{u}} (h : is_weak_func x y f)
    (hinj : ∀ j₁ j₂ : y.Type, PSet.Equiv (y.Func j₁) (y.Func j₂) → j₁ = j₂)
    (i : x.Type) (j : y.Type) (hgraph : pair (x.Func i) (y.Func j) ∈ f) :
    function_lift_indexed h i = j :=
  function_lift_indexed_eq_of_graph h hinj i j hgraph

theorem function_lift'_graph_of_mem_fun_inj {x y f : pSet.{u}} (h : is_weak_func x y f)
    (hinj : ∀ j₁ j₂ : y.Type, PSet.Equiv (y.Func j₁) (y.Func j₂) → j₁ = j₂)
    (i : x.Type) (j : y.Type) (hgraph : pair (x.Func i) (y.Func j) ∈ f) :
    function_lift_indexed h i = j :=
  function_lift_graph_of_mem_fun_inj h hinj i j hgraph

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

theorem surj_lift' {x y f : pSet.{u}} (hweak : is_weak_func x y f)
    (hinj : ∀ j₁ j₂ : y.Type, PSet.Equiv (y.Func j₁) (y.Func j₂) → j₁ = j₂)
    (hsurj : is_surj x y f) : Function.Surjective (function_lift_indexed hweak) :=
  surj_lift_indexed hweak hinj hsurj

/-- A graph chosen from `functions x y` is automatically total over `x`. -/
theorem is_total_of_mem_functions {x y f : pSet.{u}} (hf : f ∈ functions x y) : is_total x y f :=
  is_total_of_is_func ((mem_functions_iff).1 hf)

theorem surj_lift_indexed_of_mem_functions {x y f : pSet.{u}} (hf : f ∈ functions x y)
    (hinj : ∀ j₁ j₂ : y.Type, PSet.Equiv (y.Func j₁) (y.Func j₂) → j₁ = j₂)
    (hsurj : is_surj x y f) : Function.Surjective (function_lift_indexed (is_weak_func_of_mem_functions hf)) := by
  exact surj_lift_indexed (is_weak_func_of_mem_functions hf) hinj hsurj

theorem surj_lift_of_mem_functions {x y f : pSet.{u}} (hf : f ∈ functions x y)
    (hsurj : is_surj x y f) :
    ∀ b, b ∈ y → ∃ i : x.Type, PSet.Equiv b (function_lift (is_weak_func_of_mem_functions hf) i).1 :=
  surj_lift (is_weak_func_of_mem_functions hf) hsurj


theorem function_lift_mem_of_mem_functions {x y f : pSet.{u}} (hf : f ∈ functions x y) (i : x.Type) :
    (function_lift (is_weak_func_of_mem_functions hf) i).1 ∈ y :=
  function_lift_mem (is_weak_func_of_mem_functions hf) i

theorem function_lift_graph_of_mem_functions {x y f : pSet.{u}} (hf : f ∈ functions x y) (i : x.Type) :
    pair (x.Func i) (function_lift (is_weak_func_of_mem_functions hf) i).1 ∈ f :=
  function_lift_graph (is_weak_func_of_mem_functions hf) i

theorem function_lift_indexed_spec_of_mem_functions {x y f : pSet.{u}} (hf : f ∈ functions x y)
    (i : x.Type) :
    pair (x.Func i) (y.Func (function_lift_indexed (is_weak_func_of_mem_functions hf) i)) ∈ f :=
  function_lift_indexed_spec (is_weak_func_of_mem_functions hf) i

theorem function_lift_graph_unique_of_mem_functions {x y f : pSet.{u}} (hf : f ∈ functions x y)
    (i : x.Type) {v : pSet.{u}} (hv : v ∈ y) (hgraph : pair (x.Func i) v ∈ f) :
    PSet.Equiv v (function_lift (is_weak_func_of_mem_functions hf) i).1 :=
  function_lift_graph_unique (is_weak_func_of_mem_functions hf) i hv hgraph

theorem function_lift_indexed_eq_of_graph_of_mem_functions {x y f : pSet.{u}} (hf : f ∈ functions x y)
    (hinj : ∀ j₁ j₂ : y.Type, PSet.Equiv (y.Func j₁) (y.Func j₂) → j₁ = j₂)
    (i : x.Type) (j : y.Type) (hgraph : pair (x.Func i) (y.Func j) ∈ f) :
    function_lift_indexed (is_weak_func_of_mem_functions hf) i = j :=
  function_lift_indexed_eq_of_graph (is_weak_func_of_mem_functions hf) hinj i j hgraph

theorem eq_of_is_func_of_eq {a b c d x y f : pSet.{u}} (hf : is_func x y f)
    (h₁ : pair a c ∈ f) (h₂ : pair b d ∈ f) (hab : PSet.Equiv a b) : PSet.Equiv c d := by
  rcases mem_prod_iff.mp (PSet.mem_of_subset (subset_prod_of_is_func hf) h₁) with ⟨ha, hc⟩
  rcases mem_prod_iff.mp (PSet.mem_of_subset (subset_prod_of_is_func hf) h₂) with ⟨hb, hd⟩
  rcases hf.2 a ha with ⟨w, hw, haw, huniq⟩
  have hbw : pair a d ∈ f := (pair_mem_congr_left hab.symm).1 h₂
  have hcw : PSet.Equiv c w := huniq c hc h₁
  have hdw : PSet.Equiv d w := huniq d hd hbw
  exact hcw.trans hdw.symm

theorem eq_of_mem_functions_of_eq {a b c d x y f : pSet.{u}} (hf : f ∈ functions x y)
    (h₁ : pair a c ∈ f) (h₂ : pair b d ∈ f) (hab : PSet.Equiv a b) : PSet.Equiv c d :=
  eq_of_is_func_of_eq (is_func_of_mem_functions hf) h₁ h₂ hab

theorem is_extensional_of_is_func {x y f : pSet.{u}} (hf : is_func x y f) : is_extensional f := by
  intro w₁ w₂ v₁ v₂ hw₁ hw₂ hv
  exact eq_of_is_func_of_eq hf hw₁ hw₂ hv

theorem is_extensional_of_mem_functions {x y f : pSet.{u}} (hf : f ∈ functions x y) :
    is_extensional f :=
  is_extensional_of_is_func (is_func_of_mem_functions hf)

namespace function

/-- Build the graph of a Lean function on the underlying index type of a pre-set. -/
def mk {x : pSet.{u}} (ψ : x.Type → pSet.{u}) : pSet.{u} :=
  ⟨x.Type, fun i => pair (x.Func i) (ψ i)⟩

/-- Every graph edge produced by `function.mk` is a member of that graph. -/
theorem mk_mem {x : pSet.{u}} {ψ : x.Type → pSet.{u}} {i : x.Type} :
    pair (x.Func i) (ψ i) ∈ mk ψ :=
  mem_mk' (x := mk ψ) (i := i)

/-- A graph built from a Lean function is a `pSet`-function whenever equivalent inputs produce
equivalent outputs and all outputs land in the target. -/
theorem mk_is_func {x y : pSet.{u}} (ψ : x.Type → pSet.{u})
    (himg : ∀ i, ψ i ∈ y)
    (hcompat : ∀ i j, PSet.Equiv (x.Func i) (x.Func j) → PSet.Equiv (ψ i) (ψ j)) :
    is_func x y (mk ψ) := by
  refine ⟨?_, ?_⟩
  · apply subset_of_all_mem
    intro z hz
    rcases mem_unfold.mp hz with ⟨i, hi⟩
    exact (PSet.Mem.congr_left hi).2 (mem_prod_of_mem (mem_mk' (x := x) (i := i)) (himg i))
  · intro z hz
    rcases mem_unfold.mp hz with ⟨i, hzi⟩
    refine ⟨ψ i, himg i, ?_, ?_⟩
    · exact (pair_mem_congr_left hzi).2 (mk_mem (ψ := ψ) (i := i))
    · intro v hvy hv
      rcases mem_unfold.mp hv with ⟨j, hp⟩
      rcases (eq_iff_eq_pair).mpr hp with ⟨hzj, hvj⟩
      exact hvj.trans (hcompat j i (hzj.symm.trans hzi))

/-- If equal outputs force equal inputs for the generating Lean function, then the induced graph is
injective as a `pSet`-function. -/
theorem mk_inj_of_inj {x : pSet.{u}} (ψ : x.Type → pSet.{u})
    (hinj : ∀ i₁ i₂, PSet.Equiv (ψ i₁) (ψ i₂) → PSet.Equiv (x.Func i₁) (x.Func i₂)) :
    is_inj (mk ψ) := by
  intro w₁ w₂ v₁ v₂ hw₁ hw₂ hv
  rcases mem_unfold.mp hw₁ with ⟨i, hi⟩
  rcases mem_unfold.mp hw₂ with ⟨j, hj⟩
  rcases (eq_iff_eq_pair).mpr hi with ⟨hwi, hvi⟩
  rcases (eq_iff_eq_pair).mpr hj with ⟨hwj, hvj⟩
  have hψ : PSet.Equiv (ψ i) (ψ j) := hvi.symm.trans (hv.trans hvj)
  have hx : PSet.Equiv (x.Func i) (x.Func j) := hinj i j hψ
  exact hwi.trans (hx.trans hwj.symm)

theorem mk_is_injective_function {x y : pSet.{u}} (ψ : x.Type → pSet.{u})
    (himg : ∀ i, ψ i ∈ y)
    (hcompat : ∀ i j, PSet.Equiv (x.Func i) (x.Func j) → PSet.Equiv (ψ i) (ψ j))
    (hinj : ∀ i₁ i₂, PSet.Equiv (ψ i₁) (ψ i₂) → PSet.Equiv (x.Func i₁) (x.Func i₂)) :
    is_injective_function x y (mk ψ) := by
  exact ⟨mk_is_func ψ himg hcompat, mk_inj_of_inj ψ hinj⟩

end function

/-- Separation is always a subset of the original pre-set. -/
@[simp] theorem sep_subset {p : pSet.{u} → Prop} {x : pSet.{u}} : PSet.sep p x ⊆ x := by
  cases x with
  | mk α A =>
      intro w
      exact ⟨w.1, PSet.Equiv.rfl⟩

/-- Predicates on pre-sets that respect extensional equivalence. -/
def P_ext (χ : Set pSet.{u}) : Prop :=
  ∀ x y, PSet.Equiv x y → χ x → χ y

@[simp] theorem P_ext_mem_left {y : pSet.{u}} : P_ext (fun x => x ∈ y) := by
  intro z₁ z₂ hEq hz
  exact (PSet.Mem.congr_left hEq).1 hz

@[simp] theorem P_ext_mem_right {x : pSet.{u}} : P_ext (fun y => x ∈ y) := by
  intro z₁ z₂ hEq hz
  exact (PSet.Mem.congr_right hEq).1 hz

@[simp] theorem P_ext_neg {χ : Set pSet.{u}} (hχ : P_ext χ) : P_ext (fun z => ¬ χ z) := by
  intro x y hEq hNot hy
  exact hNot (hχ y x hEq.symm hy)

@[simp] theorem P_ext_injects_into_left {y : pSet.{u}} : P_ext (fun x => injects_into x y) := by
  intro x₁ x₂ hEq hx
  rcases hx with ⟨f, hfFunc, hfInj⟩
  exact ⟨f, (is_func_congr_left hEq).1 hfFunc, hfInj⟩

@[simp] theorem P_ext_is_func {x y : pSet.{u}} : P_ext (fun f => is_func x y f) := by
  intro f g hfg hf
  exact (is_func_congr hfg).1 hf

theorem injects_into_refl (x : pSet.{u}) : injects_into x x := by
  refine ⟨pSet.function.mk x.Func, ?_⟩
  exact pSet.function.mk_is_injective_function x.Func (fun i => mem_mk' (x := x) (i := i))
    (fun _ _ h => h) (fun _ _ h => h)

theorem injects_into_congr_left {x₁ x₂ y : pSet.{u}} (h : PSet.Equiv x₁ x₂) :
    injects_into x₁ y ↔ injects_into x₂ y := by
  constructor
  · exact P_ext_injects_into_left (y := y) _ _ h
  · exact P_ext_injects_into_left (y := y) _ _ h.symm

theorem injects_into_congr_right {x y₁ y₂ : pSet.{u}} (h : PSet.Equiv y₁ y₂) :
    injects_into x y₁ ↔ injects_into x y₂ := by
  constructor
  · rintro ⟨f, hfFunc, hfInj⟩
    exact ⟨f, (is_func_congr_right h).1 hfFunc, hfInj⟩
  · rintro ⟨f, hfFunc, hfInj⟩
    exact ⟨f, (is_func_congr_right h).2 hfFunc, hfInj⟩

/-- Membership in a separated pre-set is equivalent to membership in the base set together with
the predicate, provided the predicate is extensional. -/
theorem mem_sep_iff {p : Set pSet.{u}} {x : pSet.{u}} {w : pSet.{u}} (hcongr : P_ext p) :
    w ∈ PSet.sep p x ↔ w ∈ x ∧ p w := by
  constructor
  · intro hw
    refine ⟨PSet.mem_of_subset (sep_subset (p := p) (x := x)) hw, ?_⟩
    cases x with
    | mk α A =>
        rcases hw with ⟨⟨i, hi⟩, hwi⟩
        exact hcongr _ _ hwi.symm hi
  · intro hw
    cases x with
    | mk α A =>
        rcases hw with ⟨hx, hp⟩
        rcases hx with ⟨i, hwi⟩
        refine ⟨⟨i, hcongr _ _ hwi hp⟩, hwi⟩

theorem sep_equiv_iff {p₁ p₂ : Set pSet.{u}} {x : pSet.{u}} (h₁ : P_ext p₁) (h₂ : P_ext p₂) :
    PSet.Equiv (PSet.sep p₁ x) (PSet.sep p₂ x) ↔ ∀ z, (z ∈ x ∧ p₁ z) ↔ (z ∈ x ∧ p₂ z) := by
  constructor
  · intro h z
    simpa [mem_sep_iff h₁, mem_sep_iff h₂] using (PSet.equiv_iff_mem.mp h)
  · intro h
    apply PSet.Mem.ext
    intro z
    simpa [mem_sep_iff h₁, mem_sep_iff h₂] using h z

theorem mem_two {x : pSet.{u}} (h : x ∈ (PSet.ofNat 2 : pSet.{u})) :
    PSet.Equiv x (PSet.ofNat 0 : pSet.{u}) ∨ PSet.Equiv x (PSet.ofNat 1 : pSet.{u}) := by
  change x ∈ PSet.ofNat (1 + 1) at h
  simp [PSet.ofNat] at h
  rcases h with hx | hx
  · right
    exact hx
  · left
    exact hx

@[simp] theorem P_ext_pair_mem_right {b c : pSet.{u}} : P_ext (fun w => pair b w ∈ c) := by
  intro x y hEq hx
  exact (pair_mem_congr_right hEq).1 hx

@[simp] theorem P_ext_pair_mem_left {b c : pSet.{u}} : P_ext (fun w => pair w b ∈ c) := by
  intro x y hEq hx
  exact (pair_mem_congr_left hEq).1 hx

section injects_powerset

variable {x : pSet.{u}}

local notation "fx2" => (functions x (PSet.ofNat 2))

/-- A function into `2` determines the subset of inputs sent to `0`. -/
def f2ipF : PSet.Type (functions x (PSet.ofNat 2)) → pSet.{u} :=
  fun χ => PSet.sep (fun z => pair z (PSet.ofNat 0) ∈ PSet.Func (functions x (PSet.ofNat 2)) χ) x

@[simp] theorem f2ip_P_ext {χ : PSet.Type (functions x (PSet.ofNat 2))} {b : pSet.{u}} :
    P_ext (fun z => pair z b ∈ PSet.Func (functions x (PSet.ofNat 2)) χ) := by
  exact P_ext_pair_mem_left

theorem mem_f2ipF_iff {χ : PSet.Type (functions x (PSet.ofNat 2))} {w : pSet.{u}} :
    w ∈ f2ipF (x := x) χ ↔
      w ∈ x ∧ pair w (PSet.ofNat 0) ∈ PSet.Func (functions x (PSet.ofNat 2)) χ := by
  simpa [f2ipF] using
    (mem_sep_iff (x := x)
      (w := w)
      (p := fun z => pair z (PSet.ofNat 0) ∈ PSet.Func (functions x (PSet.ofNat 2)) χ)
      (hcongr := f2ip_P_ext (x := x) (χ := χ)))

theorem f2ipF_ext {i j : PSet.Type (functions x (PSet.ofNat 2))}
    (hEq :
      PSet.Equiv (PSet.Func (functions x (PSet.ofNat 2)) i)
        (PSet.Func (functions x (PSet.ofNat 2)) j)) :
    PSet.Equiv (f2ipF (x := x) i) (f2ipF (x := x) j) := by
  apply (sep_equiv_iff
    (x := x)
    (p₁ := fun z => pair z (PSet.ofNat 0) ∈ PSet.Func (functions x (PSet.ofNat 2)) i)
    (p₂ := fun z => pair z (PSet.ofNat 0) ∈ PSet.Func (functions x (PSet.ofNat 2)) j)
    (h₁ := f2ip_P_ext (x := x) (χ := i))
    (h₂ := f2ip_P_ext (x := x) (χ := j))).2
  intro z
  constructor
  · rintro ⟨hzx, hz⟩
    exact ⟨hzx, (PSet.Mem.congr_right hEq).1 hz⟩
  · rintro ⟨hzx, hz⟩
    exact ⟨hzx, (PSet.Mem.congr_right hEq).2 hz⟩

/-- The graph sending a `2`-valued function to its zero-fiber subset. -/
def f2ip (x : pSet.{u}) : pSet.{u} :=
  pSet.function.mk (@f2ipF x)

theorem mem_f2ip_iff {a b : pSet.{u}} :
    pair a b ∈ f2ip x ↔
      a ∈ fx2 ∧ b ∈ PSet.powerset x ∧
        PSet.Equiv b (PSet.sep (fun z => pair z (PSet.ofNat 0) ∈ a) x) := by
  constructor
  · intro h
    rcases mem_unfold.mp h with ⟨χ, hχ⟩
    have hχ' :
        PSet.Equiv (pair a b)
          (pair (PSet.Func (functions x (PSet.ofNat 2)) χ) (f2ipF (x := x) χ)) := by
      simpa using hχ
    have hpairparts :
        PSet.Equiv a (PSet.Func (functions x (PSet.ofNat 2)) χ) ∧
          PSet.Equiv b (f2ipF (x := x) χ) := by
      have hsound :
          ZFSet.pair (ZFSet.mk a) (ZFSet.mk b) =
            ZFSet.pair (ZFSet.mk (PSet.Func (functions x (PSet.ofNat 2)) χ))
              (ZFSet.mk (f2ipF (x := x) χ)) := by
        simpa [pair_sound] using ZFSet.sound hχ'
      rcases ZFSet.pair_inj.mp hsound with ⟨ha, hb⟩
      exact ⟨ZFSet.exact ha, ZFSet.exact hb⟩
    rcases hpairparts with ⟨ha, hb⟩
    refine ⟨?_, ?_, ?_⟩
    · exact (PSet.Mem.congr_left ha).2 (mem_mk' (x := functions x (PSet.ofNat 2)) (i := χ))
    · refine (PSet.Mem.congr_left hb).2 ?_
      refine (PSet.mem_powerset).2 ?_
      simp [f2ipF]
    · apply hb.trans
      apply (sep_equiv_iff
        (x := x)
        (p₁ := fun z => pair z (PSet.ofNat 0) ∈ PSet.Func (functions x (PSet.ofNat 2)) χ)
        (p₂ := fun z => pair z (PSet.ofNat 0) ∈ a)
        (h₁ := f2ip_P_ext (x := x) (χ := χ))
        (h₂ := P_ext_pair_mem_left (b := PSet.ofNat 0) (c := a))).2
      intro z
      constructor <;> rintro ⟨hzx, hz⟩
      · exact ⟨hzx, (PSet.Mem.congr_right ha).2 hz⟩
      · exact ⟨hzx, (PSet.Mem.congr_right ha).1 hz⟩
  · rintro ⟨ha, hb, hEq⟩
    rcases mem_unfold.mp ha with ⟨χ, hχ⟩
    change PSet.Equiv a (PSet.Func (functions x (PSet.ofNat 2)) χ) at hχ
    have hSep :
        PSet.Equiv (f2ipF (x := x) χ)
          (PSet.sep (fun z => pair z (PSet.ofNat 0) ∈ a) x) := by
      apply (sep_equiv_iff
        (x := x)
        (p₁ := fun z => pair z (PSet.ofNat 0) ∈ PSet.Func (functions x (PSet.ofNat 2)) χ)
        (p₂ := fun z => pair z (PSet.ofNat 0) ∈ a)
        (h₁ := f2ip_P_ext (x := x) (χ := χ))
        (h₂ := P_ext_pair_mem_left (b := PSet.ofNat 0) (c := a))).2
      intro z
      constructor <;> rintro ⟨hzx, hz⟩
      · exact ⟨hzx, (PSet.Mem.congr_right hχ).2 hz⟩
      · exact ⟨hzx, (PSet.Mem.congr_right hχ).1 hz⟩
    have hpair :
        PSet.Equiv (pair a b)
          (pair (PSet.Func (functions x (PSet.ofNat 2)) χ) (f2ipF (x := x) χ)) := by
      apply ZFSet.exact
      rw [pair_sound, pair_sound, ZFSet.pair_inj]
      exact ⟨ZFSet.sound hχ, ZFSet.sound (hEq.trans hSep.symm)⟩
    exact (PSet.Mem.congr_left hpair).2 (mem_mk' (x := f2ip x) (i := χ))

theorem rel_eq_iff {x y f g : pSet.{u}} (hf : f ⊆ prod x y) (hg : g ⊆ prod x y) :
    PSet.Equiv f g ↔ ∀ a ∈ x, ∀ b ∈ y, pair a b ∈ f ↔ pair a b ∈ g := by
  constructor
  · intro h a ha b hb
    exact PSet.Mem.congr_right h
  · intro h
    apply PSet.Mem.ext
    intro p
    constructor
    · intro hp
      rcases mem_unfold.mp (PSet.mem_of_subset hf hp) with ⟨⟨i, j⟩, hpij⟩
      have hp' : pair (x.Func i) (y.Func j) ∈ f := by
        exact (PSet.Mem.congr_left hpij).1 hp
      have hg' : pair (x.Func i) (y.Func j) ∈ g :=
        (h _ (mem_mk' (x := x) (i := i)) _ (mem_mk' (x := y) (i := j))).1 hp'
      exact (PSet.Mem.congr_left hpij).2 hg'
    · intro hp
      rcases mem_unfold.mp (PSet.mem_of_subset hg hp) with ⟨⟨i, j⟩, hpij⟩
      have hp' : pair (x.Func i) (y.Func j) ∈ g := by
        exact (PSet.Mem.congr_left hpij).1 hp
      have hf' : pair (x.Func i) (y.Func j) ∈ f :=
        (h _ (mem_mk' (x := x) (i := i)) _ (mem_mk' (x := y) (i := j))).2 hp'
      exact (PSet.Mem.congr_left hpij).2 hf'

theorem false_of_zero_eq_one
    (h : PSet.Equiv (PSet.ofNat 0 : pSet.{u}) (PSet.ofNat 1 : pSet.{u})) :
    False :=
  of_nat_inj (n := 0) (k := 1) (by decide) h

theorem function_to_2_eq_aux₂ {x w : pSet.{u}} (hfunc : is_func x (PSet.ofNat 2) w) {a : pSet.{u}} :
    pair a (PSet.ofNat 0) ∈ w → pair a (PSet.ofNat 1) ∈ w → False := by
  intro h0 h1
  rcases mem_prod_iff.mp (PSet.mem_of_subset hfunc.1 h0) with ⟨ha, _⟩
  rcases hfunc.2 a ha with ⟨v, hv2, hav, huniq⟩
  have hEq0 : PSet.Equiv (PSet.ofNat 0 : pSet.{u}) v :=
    huniq _ (of_nat_mem_of_lt (k₁ := 0) (k₂ := 2) (by decide)) h0
  have hEq1 : PSet.Equiv (PSet.ofNat 1 : pSet.{u}) v :=
    huniq _ (of_nat_mem_of_lt (k₁ := 1) (k₂ := 2) (by decide)) h1
  exact false_of_zero_eq_one (hEq0.trans hEq1.symm)

theorem function_to_2_eq_aux {x w₁ w₂ : pSet.{u}}
    (hfunc₁ : is_func x (PSet.ofNat 2) w₁)
    (hfunc₂ : is_func x (PSet.ofNat 2) w₂)
    (hEq : PSet.Equiv
      (PSet.sep (fun z => pair z (PSet.ofNat 0 : pSet.{u}) ∈ w₁) x)
      (PSet.sep (fun z => pair z (PSet.ofNat 0 : pSet.{u}) ∈ w₂) x)) :
    PSet.Equiv
      (PSet.sep (fun z => pair z (PSet.ofNat 1 : pSet.{u}) ∈ w₁) x)
      (PSet.sep (fun z => pair z (PSet.ofNat 1 : pSet.{u}) ∈ w₂) x) := by
  apply PSet.Mem.ext
  intro w
  constructor
  · intro hw
    rw [mem_sep_iff
      (hcongr := P_ext_pair_mem_left (b := (PSet.ofNat 1 : pSet.{u})) (c := w₁))] at hw
    refine (mem_sep_iff
      (hcongr := P_ext_pair_mem_left (b := (PSet.ofNat 1 : pSet.{u})) (c := w₂))).2 ?_
    rcases hw with ⟨hwx, hw1⟩
    refine ⟨hwx, ?_⟩
    by_contra hw0
    rcases is_total_of_is_func hfunc₂ _ hwx with ⟨k, hk2, hwk⟩
    rcases mem_two hk2 with hk0 | hk1
    · have hwZero : w ∈ PSet.sep (fun z => pair z (PSet.ofNat 0 : pSet.{u}) ∈ w₂) x := by
        refine (mem_sep_iff
          (hcongr := P_ext_pair_mem_left (b := (PSet.ofNat 0 : pSet.{u})) (c := w₂))).2 ?_
        exact ⟨hwx, (pair_mem_congr_right hk0).1 hwk⟩
      have hwZero' : w ∈ PSet.sep (fun z => pair z (PSet.ofNat 0 : pSet.{u}) ∈ w₁) x :=
        (PSet.Mem.congr_right hEq).2 hwZero
      rw [mem_sep_iff
        (hcongr := P_ext_pair_mem_left (b := (PSet.ofNat 0 : pSet.{u})) (c := w₁))] at hwZero'
      exact function_to_2_eq_aux₂ hfunc₁ hwZero'.2 hw1
    · exact hw0 ((pair_mem_congr_right hk1).1 hwk)
  · intro hw
    rw [mem_sep_iff
      (hcongr := P_ext_pair_mem_left (b := (PSet.ofNat 1 : pSet.{u})) (c := w₂))] at hw
    refine (mem_sep_iff
      (hcongr := P_ext_pair_mem_left (b := (PSet.ofNat 1 : pSet.{u})) (c := w₁))).2 ?_
    rcases hw with ⟨hwx, hw1⟩
    refine ⟨hwx, ?_⟩
    by_contra hw0
    rcases is_total_of_is_func hfunc₁ _ hwx with ⟨k, hk2, hwk⟩
    rcases mem_two hk2 with hk0 | hk1
    · have hwZero : w ∈ PSet.sep (fun z => pair z (PSet.ofNat 0 : pSet.{u}) ∈ w₁) x := by
        refine (mem_sep_iff
          (hcongr := P_ext_pair_mem_left (b := (PSet.ofNat 0 : pSet.{u})) (c := w₁))).2 ?_
        exact ⟨hwx, (pair_mem_congr_right hk0).1 hwk⟩
      have hwZero' : w ∈ PSet.sep (fun z => pair z (PSet.ofNat 0 : pSet.{u}) ∈ w₂) x :=
        (PSet.Mem.congr_right hEq).1 hwZero
      rw [mem_sep_iff
        (hcongr := P_ext_pair_mem_left (b := (PSet.ofNat 0 : pSet.{u})) (c := w₂))] at hwZero'
      exact function_to_2_eq_aux₂ hfunc₂ hwZero'.2 hw1
    · exact hw0 ((pair_mem_congr_right hk1).1 hwk)

theorem functions_to_2_eq {x w₁ w₂ : pSet.{u}}
    (hEq :
      PSet.Equiv
        (PSet.sep (fun z => pair z (PSet.ofNat 0 : pSet.{u}) ∈ w₁) x)
        (PSet.sep (fun z => pair z (PSet.ofNat 0 : pSet.{u}) ∈ w₂) x))
    (hw₁ : w₁ ∈ functions x (PSet.ofNat 2))
    (hw₂ : w₂ ∈ functions x (PSet.ofNat 2)) :
    PSet.Equiv w₁ w₂ := by
  have hf₁ : is_func x (PSet.ofNat 2) w₁ := (mem_functions_iff).1 hw₁
  have hf₂ : is_func x (PSet.ofNat 2) w₂ := (mem_functions_iff).1 hw₂
  rw [rel_eq_iff (subset_prod_of_mem_functions hw₁) (subset_prod_of_mem_functions hw₂)]
  intro a ha b hb
  constructor <;> intro hab
  · rcases mem_two hb with hb0 | hb1
    · have ha0 : a ∈ PSet.sep (fun z => pair z (PSet.ofNat 0 : pSet.{u}) ∈ w₁) x := by
        refine (mem_sep_iff
          (hcongr := P_ext_pair_mem_left (b := (PSet.ofNat 0 : pSet.{u})) (c := w₁))).2 ?_
        exact ⟨ha, (pair_mem_congr_right hb0).1 hab⟩
      have ha0' : a ∈ PSet.sep (fun z => pair z (PSet.ofNat 0 : pSet.{u}) ∈ w₂) x :=
        (PSet.Mem.congr_right hEq).1 ha0
      rw [mem_sep_iff
        (hcongr := P_ext_pair_mem_left (b := (PSet.ofNat 0 : pSet.{u})) (c := w₂))] at ha0'
      exact (pair_mem_congr_right hb0).2 ha0'.2
    · have hEq1 := function_to_2_eq_aux hf₁ hf₂ hEq
      have ha1 : a ∈ PSet.sep (fun z => pair z (PSet.ofNat 1 : pSet.{u}) ∈ w₁) x := by
        refine (mem_sep_iff
          (hcongr := P_ext_pair_mem_left (b := (PSet.ofNat 1 : pSet.{u})) (c := w₁))).2 ?_
        exact ⟨ha, (pair_mem_congr_right hb1).1 hab⟩
      have ha1' : a ∈ PSet.sep (fun z => pair z (PSet.ofNat 1 : pSet.{u}) ∈ w₂) x :=
        (PSet.Mem.congr_right hEq1).1 ha1
      rw [mem_sep_iff
        (hcongr := P_ext_pair_mem_left (b := (PSet.ofNat 1 : pSet.{u})) (c := w₂))] at ha1'
      exact (pair_mem_congr_right hb1).2 ha1'.2
  · rcases mem_two hb with hb0 | hb1
    · have ha0 : a ∈ PSet.sep (fun z => pair z (PSet.ofNat 0 : pSet.{u}) ∈ w₂) x := by
        refine (mem_sep_iff
          (hcongr := P_ext_pair_mem_left (b := (PSet.ofNat 0 : pSet.{u})) (c := w₂))).2 ?_
        exact ⟨ha, (pair_mem_congr_right hb0).1 hab⟩
      have ha0' : a ∈ PSet.sep (fun z => pair z (PSet.ofNat 0 : pSet.{u}) ∈ w₁) x :=
        (PSet.Mem.congr_right hEq).2 ha0
      rw [mem_sep_iff
        (hcongr := P_ext_pair_mem_left (b := (PSet.ofNat 0 : pSet.{u})) (c := w₁))] at ha0'
      exact (pair_mem_congr_right hb0).2 ha0'.2
    · have hEq1 := function_to_2_eq_aux hf₁ hf₂ hEq
      have ha1 : a ∈ PSet.sep (fun z => pair z (PSet.ofNat 1 : pSet.{u}) ∈ w₂) x := by
        refine (mem_sep_iff
          (hcongr := P_ext_pair_mem_left (b := (PSet.ofNat 1 : pSet.{u})) (c := w₂))).2 ?_
        exact ⟨ha, (pair_mem_congr_right hb1).1 hab⟩
      have ha1' : a ∈ PSet.sep (fun z => pair z (PSet.ofNat 1 : pSet.{u}) ∈ w₁) x :=
        (PSet.Mem.congr_right hEq1).2 ha1
      rw [mem_sep_iff
        (hcongr := P_ext_pair_mem_left (b := (PSet.ofNat 1 : pSet.{u})) (c := w₁))] at ha1'
      exact (pair_mem_congr_right hb1).2 ha1'.2

theorem functions_2_injects_into_powerset (x : pSet.{u}) :
    ∃ f : pSet.{u}, is_injective_function (pSet.functions x (PSet.ofNat 2) : pSet.{u})
      (PSet.powerset x : pSet.{u}) f := by
  refine ⟨f2ip x, ?_⟩
  refine ⟨?_, ?_⟩
  · simpa [f2ip] using
      (pSet.function.mk_is_func (@f2ipF x)
        (fun χ => (PSet.mem_powerset).2 <|
          sep_subset (p := fun z => pair z (PSet.ofNat 0) ∈ (functions x (PSet.ofNat 2)).Func χ))
        (fun i j hEq => f2ipF_ext (x := x) hEq))
  · intro w₁ w₂ v₁ v₂ hw₁ hw₂ hv
    rw [mem_f2ip_iff (x := x)] at hw₁ hw₂
    rcases hw₁ with ⟨hw₁f, _, hw₁v⟩
    rcases hw₂ with ⟨hw₂f, _, hw₂v⟩
    exact functions_to_2_eq (x := x) (hw₁v.symm.trans (hv.trans hw₂v)) hw₁f hw₂f

end injects_powerset

end pSet

end Flypitch

attribute [nolint docBlame]
  Flypitch.ordinal.mk_zero_cast Flypitch.ordinal.mk_zero_cast' Flypitch.pSet.succ_type_cast
  Flypitch.pSet.succ_type_cast' Flypitch.pSet.option_cast'

attribute [nolint simpNF]
  Flypitch.ordinal.mk_zero_type Flypitch.pSet.ordinal.mk_succ Flypitch.pSet.eta
  Flypitch.pSet.option_succ_type Flypitch.pSet.mk_type_mk_eq' Flypitch.pSet.mk_type_mk_eq''
  Flypitch.pSet.mk_type_mk_eq'''' Flypitch.pSet.mk_type_mk_eq''''' Flypitch.pSet.f2ip_P_ext

attribute [nolint unusedArguments]
  Flypitch.pSet.mk_type_mk_eq'
