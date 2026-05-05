import Flypitch.RegularOpenAlgebra
import Flypitch.PSetOrdinal

universe u v

namespace Flypitch

open Set TopologicalSpace Cardinal Function PFun Part

set_option linter.missingDocs false
set_option linter.style.longLine false

/-!
Port of upstream `src/collapse.lean`.
-/

/-! ### Collapse poset -/

/-- A collapse poset: partial function `X ⇀ Y` with domain cardinality below `κ`. -/
structure collapse_poset (X Y : Type u) (κ : Cardinal.{u}) where
  f : X →. Y
  Hc : Cardinal.mk (PFun.Dom f) < κ

namespace collapse_poset

variable {X Y : Type u} {κ : Cardinal.{u}}

/-- Empty collapse poset. -/
def empty (h : 0 < κ) : collapse_poset X Y κ :=
  { f := fun _ => Part.none
    Hc := by simp [PFun.Dom, h] }

/-- Principal open: all total functions extending the partial function. -/
def principal_open (p : collapse_poset X Y κ) : Set (X → Y) :=
  {g | ∀ a b, b ∈ p.f a → g a = b}

theorem mem_principal_open_iff {p : collapse_poset X Y κ} {g : X → Y} :
    g ∈ principal_open p ↔ ∀ a b, b ∈ p.f a → g a = b := by rfl

theorem mem_principal_open_iff' {p : collapse_poset X Y κ} {g : X → Y} :
    g ∈ principal_open p ↔ ∀ (a : X) (ha : a ∈ PFun.Dom p.f), g a = fn p.f a ha := by
  rw [mem_principal_open_iff]
  constructor
  · intro H a ha
    exact H a (fn p.f a ha) (get_mem ha)
  · intro H a b hb
    have ha : a ∈ PFun.Dom p.f := (mem_dom _ _).mpr ⟨b, hb⟩
    have h_eq : fn p.f a ha = b := mem_unique (get_mem ha) hb
    rw [H a ha, h_eq]

theorem mem_compl_principal_open {p : collapse_poset X Y κ} {g : X → Y} :
    g ∈ (principal_open p)ᶜ ↔ ∃ (a : X) (ha : a ∈ PFun.Dom p.f), g a ≠ fn p.f a ha := by
  rw [Set.mem_compl_iff, mem_principal_open_iff']
  constructor
  · intro h
    rcases not_forall.mp h with ⟨a, ha⟩
    rcases not_forall.mp ha with ⟨ha_dom, hneq⟩
    exact ⟨a, ha_dom, hneq⟩
  · intro ⟨a, ha, hneq⟩ h
    apply hneq
    apply h a ha

theorem trivial_extension_mem_principal_open {p : collapse_poset X Y κ} {y : Y} :
    (open Classical in fun (x : X) => if h : (p.f x).Dom then (p.f x).get h else y) ∈
      principal_open p := by
  rw [mem_principal_open_iff]
  intro a b hb
  rcases hb with ⟨h_dom, h_eq⟩
  rw [dif_pos h_dom]
  exact h_eq

/-! ### PFun singleton -/

/-- A partial function defined only at `x` with value `y`. -/
def pfun_singleton (x : X) (y : Y) : X →. Y := fun a =>
  { Dom := a = x, get := fun _ => y }

theorem mem_pfun_singleton_iff {x a : X} {y b : Y} :
    b ∈ pfun_singleton x y a ↔ a = x ∧ b = y := by
  dsimp [pfun_singleton]
  simp [eq_comm]

theorem pfun_singleton_dom {x : X} {y : Y} : PFun.Dom (pfun_singleton x y) = {x} := by
  ext a; simp [pfun_singleton, PFun.mem_dom]

/-- A singleton collapse poset (requires 1 < κ). -/
def singleton_collapse_poset (x : X) (y : Y) (hκ : 1 < κ) : collapse_poset X Y κ :=
  { f := pfun_singleton x y
    Hc := by
      rw [pfun_singleton_dom]
      simp [hκ] }

theorem singleton_collapse_poset_principal_open {x : X} {y : Y} {hκ : 1 < κ} :
    principal_open (singleton_collapse_poset x y hκ) = {g : X → Y | g x = y} := by
  ext g; constructor
  · intro hg
    rw [mem_principal_open_iff] at hg
    have : y ∈ pfun_singleton x y x := by
      apply mem_pfun_singleton_iff.mpr ⟨rfl, rfl⟩
    exact hg x y this
  · intro hg
    rw [mem_principal_open_iff]
    intro a b hb
    rcases mem_pfun_singleton_iff.mp hb with ⟨rfl, rfl⟩
    exact hg

/-! ### Complement of principal open is union of singletons -/

theorem one_lt_succ_aleph0 : 1 < Order.succ Cardinal.aleph0 := by
  refine lt_of_lt_of_le Cardinal.one_lt_aleph0 ?_
  exact Order.le_succ _

theorem compl_principal_open_is_union_of_singletons
    (p : collapse_poset X Y (Order.succ Cardinal.aleph0)) :
    ∃ (ι : Type u) (s : ι → collapse_poset X Y (Order.succ Cardinal.aleph0)),
      Set.iUnion (fun (i : ι) => principal_open (s i)) = (principal_open p)ᶜ := by
  -- Index: pairs (x, y) where x ∈ Dom p.f and y ≠ fn p.f x
  let ι : Type u := { pr : X × Y // ∃ (h_mem : pr.1 ∈ PFun.Dom p.f), pr.2 ≠ fn p.f pr.1 h_mem }
  let s : ι → collapse_poset X Y (Order.succ Cardinal.aleph0) := fun pr =>
    singleton_collapse_poset pr.val.1 pr.val.2 one_lt_succ_aleph0
  refine ⟨ι, s, ?_⟩
  ext f; constructor
  · intro h
    rw [Set.mem_compl_iff, mem_principal_open_iff]
    rcases Set.mem_iUnion.mp h with ⟨i, hi⟩
    rcases i with ⟨⟨x, y⟩, ⟨h_mem, h_neq⟩⟩
    rw [singleton_collapse_poset_principal_open] at hi
    have hy_eq : f x = y := by simpa using hi
    -- In the principal open of the singleton, f x = y
    -- We need to show that f is NOT in the principal open of p
    -- Specifically, at x, fn p.f x h_mem ≠ f x (= y) by h_neq
    -- So there's a witness x where fn differs from f
    intro hmain
    apply h_neq
    -- hmain : ∀ a b, b ∈ p.f a → f a = b
    -- In particular, fn p.f x h_mem ∈ p.f x
    have h_fn_mem : fn p.f x h_mem ∈ p.f x := get_mem h_mem
    have h_eq2 : f x = fn p.f x h_mem := hmain x (fn p.f x h_mem) h_fn_mem
    rw [h_eq2] at hy_eq
    exact hy_eq.symm
  · intro h
    rw [mem_compl_principal_open] at h
    rcases h with ⟨x, hx, hneq⟩
    -- f x ≠ fn p.f x hx, so (x, f x) is in the index set
    apply Set.mem_iUnion.mpr
    refine ⟨⟨(x, f x), ⟨hx, hneq⟩⟩, ?_⟩
    rw [singleton_collapse_poset_principal_open]
    simp

/-! ### Collapse space topology -/

/-- Topology on `X → Y` generated by principal opens at level ω₁. -/
@[reducible] def collapse_space (X Y : Type u) : TopologicalSpace (X → Y) :=
  generateFrom (principal_open '' (Set.univ : Set (collapse_poset X Y (Order.succ Cardinal.aleph0))))

theorem collapse_space_principal_open_isOpen
    (p : collapse_poset X Y (Order.succ Cardinal.aleph0)) :
    @IsOpen (X → Y) (collapse_space X Y) (principal_open p) := by
  apply isOpen_generateFrom_of_mem
  exact Set.mem_image_of_mem _ (Set.mem_univ _)

theorem collapse_space_regular_principal_open
    (p : collapse_poset X Y (Order.succ Cardinal.aleph0)) :
    @is_regular (X → Y) (collapse_space X Y) (principal_open p) := by
  apply @is_regular_of_clopen (X → Y) (collapse_space X Y)
  have ho : @IsOpen (X → Y) (collapse_space X Y) (principal_open p) :=
    collapse_space_principal_open_isOpen p
  have hc : @IsClosed (X → Y) (collapse_space X Y) (principal_open p) := by
    letI := collapse_space X Y
    rcases compl_principal_open_is_union_of_singletons p with ⟨ι, s, h_union⟩
    have h_open : IsOpen ((principal_open p)ᶜ) := by
      rw [← h_union]
      apply isOpen_iUnion
      intro i
      simpa using collapse_space_principal_open_isOpen (s i)
    exact isOpen_compl_iff.mp h_open
  exact ⟨hc, ho⟩

/-! ### Collapse algebra -/

/-- The regular-open algebra of the collapse space. -/
def collapse_algebra (X Y : Type u) : Type u :=
  @regular_opens (X → Y) (collapse_space X Y)

/-- Embedding of a collapse poset into the collapse algebra. -/
def collapse_inclusion {X Y : Type u}
    (p : collapse_poset X Y (Order.succ Cardinal.aleph0)) : collapse_algebra X Y :=
  ⟨principal_open p, collapse_space_regular_principal_open p⟩

end collapse_poset

end Flypitch
