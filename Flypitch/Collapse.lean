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

theorem poset_yoneda_iff {β : Type u} [PartialOrder β] {a b : β} :
    (∀ Γ : β, Γ ≤ a → Γ ≤ b) ↔ a ≤ b := by
  constructor
  · intro h
    exact h a le_rfl
  · intro hab Γ hΓ
    exact le_trans hΓ hab

theorem poset_coyoneda_iff {β : Type u} [PartialOrder β] {a b : β} :
    (∀ Γ : β, a ≤ Γ → b ≤ Γ) ↔ b ≤ a := by
  constructor
  · intro h
    exact h a le_rfl
  · intro hba Γ haΓ
    exact le_trans hba haΓ

namespace Set

theorem subset_iInter_iff {α : Sort v} {β : Type u} {t : Set β} {s : α → Set β} :
    t ⊆ Set.iInter s ↔ ∀ i, t ⊆ s i := by
  constructor
  · intro h i x hx
    exact Set.mem_iInter.mp (h (a := x) hx) i
  · intro h x hx
    exact Set.mem_iInter.mpr fun i => h i hx

end Set

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

@[simp] theorem principal_open_empty (h : 0 < κ) :
    principal_open (empty (X := X) (Y := Y) h) = Set.univ := by
  ext g
  simp [principal_open, empty]

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

theorem mem_compl_principal_open_iff {p : collapse_poset X Y κ} {g : X → Y} :
    g ∈ (principal_open p)ᶜ ↔ ∃ (a : X) (ha : a ∈ PFun.Dom p.f), g a ≠ fn p.f a ha :=
  mem_compl_principal_open

def compatible (p q : collapse_poset X Y κ) : Prop :=
  ∀ a (hp : a ∈ PFun.Dom p.f) (hq : a ∈ PFun.Dom q.f), fn p.f a hp = fn q.f a hq

noncomputable def union_f (p q : collapse_poset X Y κ) : X →. Y := fun a => by
  classical
  exact if h : a ∈ PFun.Dom p.f then Part.some (fn p.f a h) else q.f a

theorem union_f_dom (p q : collapse_poset X Y κ) :
    PFun.Dom (union_f p q) = PFun.Dom p.f ∪ PFun.Dom q.f := by
  classical
  ext a
  by_cases hp : a ∈ PFun.Dom p.f
  · rw [PFun.mem_dom]
    simp [union_f, hp]
    exact ⟨fn p.f a hp, get_mem hp⟩
  · simp [union_f, hp, PFun.mem_dom]

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

theorem zero_lt_succ_aleph0 : 0 < Order.succ Cardinal.aleph0 := by
  exact lt_trans (by norm_num : (0 : Cardinal) < 1) one_lt_succ_aleph0

noncomputable def union (p q : collapse_poset X Y (Order.succ Cardinal.aleph0)) :
    collapse_poset X Y (Order.succ Cardinal.aleph0) :=
  { f := union_f p q
    Hc := by
      rw [union_f_dom]
      exact lt_of_le_of_lt (Cardinal.mk_union_le _ _)
        (Cardinal.add_lt_of_lt (Order.le_succ Cardinal.aleph0) p.Hc q.Hc) }

theorem inter_principal_open {p q : collapse_poset X Y (Order.succ Cardinal.aleph0)}
    (hcomp : compatible p q) : principal_open p ∩ principal_open q = principal_open (union p q) := by
  classical
  ext g
  constructor
  · intro hg
    rw [mem_principal_open_iff]
    intro a b hb
    by_cases hp : a ∈ PFun.Dom p.f
    · have hmem : fn p.f a hp ∈ (union p q).f a := by
        simp [union, union_f, hp]
        exact get_mem hp
      have hb_eq : b = fn p.f a hp := mem_unique hb hmem
      rw [hb_eq]
      exact hg.1 a (fn p.f a hp) (get_mem hp)
    · have hbq : b ∈ q.f a := by
        simpa [union, union_f, hp] using hb
      exact hg.2 a b hbq
  · intro hg
    constructor
    · rw [mem_principal_open_iff]
      intro a b hb
      apply hg
      have hp : a ∈ PFun.Dom p.f := (mem_dom _ _).mpr ⟨b, hb⟩
      have hEq : fn p.f a hp = b := mem_unique (get_mem hp) hb
      simpa [union, union_f, hp, hEq]
    · rw [mem_principal_open_iff]
      intro a b hb
      apply hg
      by_cases hp : a ∈ PFun.Dom p.f
      · have hq : a ∈ PFun.Dom q.f := (mem_dom _ _).mpr ⟨b, hb⟩
        have hEq : fn p.f a hp = b := (hcomp a hp hq).trans (mem_unique (get_mem hq) hb)
        simpa [union, union_f, hp, hEq]
      · simpa [union, union_f, hp] using hb

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

@[simp] theorem principal_open_is_open
    (p : collapse_poset X Y (Order.succ Cardinal.aleph0)) :
    @IsOpen (X → Y) (collapse_space X Y) (principal_open p) :=
  collapse_space_principal_open_isOpen p

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

@[simp] theorem principal_open_is_closed
    (p : collapse_poset X Y (Order.succ Cardinal.aleph0)) :
    @IsClosed (X → Y) (collapse_space X Y) (principal_open p) := by
  letI := collapse_space X Y
  rcases compl_principal_open_is_union_of_singletons p with ⟨ι, s, h_union⟩
  have h_open : IsOpen ((principal_open p)ᶜ) := by
    rw [← h_union]
    exact isOpen_iUnion fun i => collapse_space_principal_open_isOpen (s i)
  exact isOpen_compl_iff.mp h_open

@[simp] theorem is_regular_principal_open
    (p : collapse_poset X Y (Order.succ Cardinal.aleph0)) :
    @is_regular (X → Y) (collapse_space X Y) (principal_open p) :=
  collapse_space_regular_principal_open p

def collapse_space_basis (X Y : Type u) : Set (Set (X → Y)) :=
  insert (∅ : Set (X → Y))
    (principal_open '' (Set.univ : Set (collapse_poset X Y (Order.succ Cardinal.aleph0))))

theorem empty_mem_collapse_space_basis :
    (∅ : Set (X → Y)) ∈ collapse_space_basis X Y := by
  simp [collapse_space_basis]

theorem principal_open_mem_collapse_space_basis
    (p : collapse_poset X Y (Order.succ Cardinal.aleph0)) :
    principal_open p ∈ collapse_space_basis X Y := by
  rw [collapse_space_basis]
  right
  exact Set.mem_image_of_mem principal_open (Set.mem_univ p)

theorem isOpen_of_mem_collapse_space_basis {T : Set (X → Y)}
    (hT : T ∈ collapse_space_basis X Y) : @IsOpen (X → Y) (collapse_space X Y) T := by
  rw [collapse_space_basis] at hT
  rcases hT with rfl | hT
  · exact @isOpen_empty (X → Y) (collapse_space X Y)
  · rcases hT with ⟨p, _, rfl⟩
    exact collapse_space_principal_open_isOpen p

theorem sUnion_collapse_space_basis_eq_univ :
    ⋃₀ (collapse_space_basis X Y) = Set.univ := by
  ext f
  constructor
  · intro _
    trivial
  · intro _
    refine ⟨principal_open (empty (X := X) (Y := Y) zero_lt_succ_aleph0), ?_, ?_⟩
    · exact principal_open_mem_collapse_space_basis (empty (X := X) (Y := Y) zero_lt_succ_aleph0)
    · simp

/-! ### Collapse algebra -/

/-- The regular-open algebra of the collapse space. -/
def collapse_algebra (X Y : Type u) : Type u :=
  @regular_opens (X → Y) (collapse_space X Y)

/-- Embedding of a collapse poset into the collapse algebra. -/
def collapse_inclusion {X Y : Type u}
    (p : collapse_poset X Y (Order.succ Cardinal.aleph0)) : collapse_algebra X Y :=
  ⟨principal_open p, collapse_space_regular_principal_open p⟩

def inclusion {X Y : Type u}
    (p : collapse_poset X Y (Order.succ Cardinal.aleph0)) : collapse_algebra X Y :=
  collapse_inclusion p

end collapse_poset

end Flypitch
