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

/-! ### Dense omega-closed subsets -/

/-- A subset is omega-closed if every nonzero decreasing omega-chain in it has infimum in it. -/
def omega_closed {α : Type u} [CompleteLattice α] (D : Set α) : Prop :=
  ∀ (s : ℕ → α), (∀ n, s n ∈ D) → (∀ n, ⊥ < s n) → (∀ n, s (n + 1) ≤ s n) →
    (⨅ n, s n) ∈ D

/-- A dense subset of an ordered type with bottom. -/
def dense_subset {α : Type u} [PartialOrder α] [OrderBot α] (D : Set α) : Prop :=
  ⊥ ∉ D ∧ ∀ x, ⊥ < x → ∃ y ∈ D, y ≤ x

/-- A subset that is both dense and omega-closed. -/
def dense_omega_closed_subset {α : Type u} [CompleteLattice α] (D : Set α) : Prop :=
  dense_subset D ∧ omega_closed D

/-- The type has a dense omega-closed subset. -/
def has_dense_omega_closed_subset (α : Type u) [CompleteLattice α] : Prop :=
  ∃ D : Set α, dense_omega_closed_subset D

theorem nonzero_of_mem_dense_omega_closed_subset {α : Type u} [CompleteLattice α]
    {x : α} {D : Set α} (hD : dense_omega_closed_subset D) (hx : x ∈ D) : ⊥ < x := by
  exact bot_lt_iff_ne_bot.mpr fun hxbot => hD.1.1 (hxbot ▸ hx)

theorem nonzero_infi_of_mem_dense_omega_closed_subset {α : Type u} [CompleteLattice α]
    {s : ℕ → α} {D : Set α} (hD : dense_omega_closed_subset D)
    (h_chain : ∀ n, s (n + 1) ≤ s n) (h_mem : ∀ n, s n ∈ D) :
    ⊥ < ⨅ n, s n := by
  apply nonzero_of_mem_dense_omega_closed_subset hD
  exact hD.2 s h_mem (fun n => nonzero_of_mem_dense_omega_closed_subset hD (h_mem n)) h_chain

/-! ### Collapse poset -/

/-- A collapse poset: partial function `X ⇀ Y` with domain cardinality below `κ`. -/
structure collapse_poset (X Y : Type u) (κ : Cardinal.{u}) where
  /-- The underlying partial function. -/
  f : X →. Y
  /-- The domain of the partial function has cardinality below `κ`. -/
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

theorem trivial_extension_mem_principal_open {p : collapse_poset X Y κ} {y : Y} :
    (open Classical in fun (x : X) => if h : (p.f x).Dom then (p.f x).get h else y) ∈
      principal_open p := by
  rw [mem_principal_open_iff]
  intro a b hb
  rcases hb with ⟨h_dom, h_eq⟩
  rw [dif_pos h_dom]
  exact h_eq

theorem principal_open_nonempty [Nonempty Y] (p : collapse_poset X Y κ) :
    (principal_open p).Nonempty := by
  obtain ⟨y⟩ := ‹Nonempty Y›
  exact ⟨open Classical in fun x => if h : (p.f x).Dom then (p.f x).get h else y,
    trivial_extension_mem_principal_open (p := p) (y := y)⟩

/-- Two collapse-poset conditions are compatible when they agree on common domain points. -/
def compatible (p q : collapse_poset X Y κ) : Prop :=
  ∀ a (hp : a ∈ PFun.Dom p.f) (hq : a ∈ PFun.Dom q.f), fn p.f a hp = fn q.f a hq

theorem compatible.symm {p q : collapse_poset X Y κ} (h : compatible p q) : compatible q p := by
  intro a hq hp
  exact (h a hp hq).symm

theorem compatible_of_principal_open_subset [Nonempty Y] {p q : collapse_poset X Y κ}
    (hsubset : principal_open q ⊆ principal_open p) : compatible p q := by
  intro a hp hq
  rcases principal_open_nonempty q with ⟨g, hgq⟩
  have hgp : g ∈ principal_open p := hsubset hgq
  have hp_eq := (mem_principal_open_iff'.mp hgp) a hp
  have hq_eq := (mem_principal_open_iff'.mp hgq) a hq
  exact hp_eq.symm.trans hq_eq

/-- The partial-function union used to combine compatible collapse-poset conditions. -/
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

/-- Countable union of a family of partial functions, as a partial function. -/
noncomputable def omegaUnion_f (p : ℕ → collapse_poset X Y κ) : X →. Y := fun x =>
  ⟨∃ n, x ∈ PFun.Dom (p n).f,
    fun h => fn (p (Classical.choose h)).f x (Classical.choose_spec h)⟩

theorem omegaUnion_f_dom (p : ℕ → collapse_poset X Y κ) :
    PFun.Dom (omegaUnion_f p) = ⋃ n, PFun.Dom (p n).f := by
  ext x
  simp [omegaUnion_f, PFun.Dom]

theorem omegaUnion_f_fn_eq_of_mem {p : ℕ → collapse_poset X Y κ}
    (hcomp : ∀ m n, compatible (p m) (p n)) {x : X}
    (h : x ∈ PFun.Dom (omegaUnion_f p)) {n : ℕ} (hx : x ∈ PFun.Dom (p n).f) :
    fn (omegaUnion_f p) x h = fn (p n).f x hx := by
  exact hcomp (Classical.choose h) n x (Classical.choose_spec h) hx

theorem mem_omegaUnion_f_iff_of_compatible {p : ℕ → collapse_poset X Y κ}
    (hcomp : ∀ m n, compatible (p m) (p n)) {x : X} {y : Y} :
    y ∈ omegaUnion_f p x ↔ ∃ n, y ∈ (p n).f x := by
  constructor
  · intro hy
    rcases hy with ⟨hdom, hval⟩
    refine ⟨Classical.choose hdom, ?_⟩
    rw [← hval]
    exact get_mem (Classical.choose_spec hdom)
  · rintro ⟨n, hyn⟩
    have hx : x ∈ PFun.Dom (p n).f := (PFun.mem_dom _ _).mpr ⟨y, hyn⟩
    have hdom : x ∈ PFun.Dom (omegaUnion_f p) := by
      rw [omegaUnion_f_dom]
      exact Set.mem_iUnion.mpr ⟨n, hx⟩
    refine ⟨hdom, ?_⟩
    change fn (omegaUnion_f p) x hdom = y
    rw [omegaUnion_f_fn_eq_of_mem hcomp hdom hx]
    exact mem_unique (get_mem hx) hyn

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

/-- Countable union of collapse-poset conditions at level `ω₁`. -/
noncomputable def omegaUnion (p : ℕ → collapse_poset X Y (Order.succ Cardinal.aleph0)) :
    collapse_poset X Y (Order.succ Cardinal.aleph0) :=
  { f := omegaUnion_f p
    Hc := by
      rw [omegaUnion_f_dom]
      rw [← (ULift.down_surjective :
        Function.Surjective (ULift.down : ULift.{u} ℕ → ℕ)).iUnion_comp
          (fun n => PFun.Dom (p n).f)]
      exact (Cardinal.card_iUnion_lt_iff_forall_of_isRegular
        (c := Order.succ Cardinal.aleph0)
        (t := fun n : ULift.{u} ℕ => PFun.Dom (p n.down).f)
        (Cardinal.isRegular_succ (le_rfl : Cardinal.aleph0 ≤ Cardinal.aleph0))
        (by simp)).mpr
        (fun n => (p n.down).Hc) }

/-- Compatible omega-unions represent membership as membership in some stage. -/
theorem mem_omegaUnion_iff_of_compatible
    {p : ℕ → collapse_poset X Y (Order.succ Cardinal.aleph0)}
    (hcomp : ∀ m n, compatible (p m) (p n)) {x : X} {y : Y} :
    y ∈ (omegaUnion p).f x ↔ ∃ n, y ∈ (p n).f x :=
  mem_omegaUnion_f_iff_of_compatible hcomp

/-- A total function extends a compatible omega-union iff it extends every stage. -/
theorem mem_principal_open_omegaUnion_iff_of_compatible
    {p : ℕ → collapse_poset X Y (Order.succ Cardinal.aleph0)}
    (hcomp : ∀ m n, compatible (p m) (p n)) {g : X → Y} :
    g ∈ principal_open (omegaUnion p) ↔ ∀ n, g ∈ principal_open (p n) := by
  rw [mem_principal_open_iff]
  constructor
  · intro hg n
    rw [mem_principal_open_iff]
    intro x y hy
    exact hg x y ((mem_omegaUnion_iff_of_compatible hcomp).mpr ⟨n, hy⟩)
  · intro hg x y hy
    rcases (mem_omegaUnion_iff_of_compatible hcomp).mp hy with ⟨n, hyn⟩
    exact (mem_principal_open_iff.mp (hg n)) x y hyn

/-- Union of two collapse-poset conditions at level `ω₁`. -/
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

theorem principal_open_is_open
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

/-- The collapse-space basis consisting of the empty set and all principal opens. -/
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

theorem collapse_space_basis_inter_refinement {T₁ T₂ : Set (X → Y)}
    (hT₁ : T₁ ∈ collapse_space_basis X Y) (hT₂ : T₂ ∈ collapse_space_basis X Y)
    {f : X → Y} (hf : f ∈ T₁ ∩ T₂) :
    ∃ T₃ ∈ collapse_space_basis X Y, f ∈ T₃ ∧ T₃ ⊆ T₁ ∩ T₂ := by
  rw [collapse_space_basis] at hT₁ hT₂
  rcases hT₁ with rfl | hT₁
  · exact False.elim hf.1
  rcases hT₂ with rfl | hT₂
  · exact False.elim hf.2
  rcases hT₁ with ⟨p₁, _, rfl⟩
  rcases hT₂ with ⟨p₂, _, rfl⟩
  by_cases hcomp : compatible p₁ p₂
  · refine ⟨principal_open (union p₁ p₂), ?_, ?_, ?_⟩
    · exact principal_open_mem_collapse_space_basis (union p₁ p₂)
    · rw [← inter_principal_open hcomp]
      exact hf
    · rw [← inter_principal_open hcomp]
  · have hEmpty : principal_open p₁ ∩ principal_open p₂ = (∅ : Set (X → Y)) := by
      ext g
      constructor
      · intro hg
        exfalso
        rw [compatible] at hcomp
        push Not at hcomp
        rcases hcomp with ⟨x, hp, hq, hneq⟩
        have hg₁ := (mem_principal_open_iff'.mp hg.1) x hp
        have hg₂ := (mem_principal_open_iff'.mp hg.2) x hq
        exact hneq (hg₁.symm.trans hg₂)
      · intro h
        exact False.elim h
    rw [hEmpty] at hf
    exact False.elim hf

theorem collapse_space_basis_spec :
    @IsTopologicalBasis (X → Y) (collapse_space X Y) (collapse_space_basis X Y) := by
  letI : TopologicalSpace (X → Y) := collapse_space X Y
  refine ⟨?_, sUnion_collapse_space_basis_eq_univ (X := X) (Y := Y), ?_⟩
  · intro T₁ hT₁ T₂ hT₂ f hf
    exact collapse_space_basis_inter_refinement hT₁ hT₂ hf
  · apply le_antisymm
    · apply le_generateFrom
      intro T hT
      exact isOpen_of_mem_collapse_space_basis hT
    · unfold collapse_space collapse_space_basis
      apply generateFrom_anti
      intro T hT
      rcases hT with ⟨p, _, rfl⟩
      exact Or.inr (Set.mem_image_of_mem _ (Set.mem_univ p))

theorem is_regular_singleton_regular_open {x : X} {y : Y} :
    @is_regular (X → Y) (collapse_space X Y)
      (principal_open (singleton_collapse_poset x y one_lt_succ_aleph0)) :=
  is_regular_principal_open _

theorem is_regular_singleton_regular_open' {x : X} {y : Y} :
    @is_regular (X → Y) (collapse_space X Y) {g : X → Y | g x = y} := by
  rw [← singleton_collapse_poset_principal_open]
  exact is_regular_singleton_regular_open

/-! ### Collapse algebra -/

/-- The regular-open algebra of the collapse space. -/
abbrev collapse_algebra (X Y : Type u) : Type u :=
  @regular_opens (X → Y) (collapse_space X Y)

/-- Collapse algebras inherit coercion to their underlying regular-open sets. -/
instance collapseAlgebraCoe (X Y : Type u) : Coe (collapse_algebra X Y) (Set (X → Y)) :=
  @regularOpenCoe (X → Y) (collapse_space X Y)

/-- Collapse algebras inherit the regular-open order. -/
instance collapseAlgebraPartialOrder (X Y : Type u) : PartialOrder (collapse_algebra X Y) :=
  @regularOpenPartialOrder (X → Y) (collapse_space X Y)

/-- Collapse algebras inherit the regular-open complete lattice. -/
instance collapseAlgebraCompleteLattice (X Y : Type u) : CompleteLattice (collapse_algebra X Y) :=
  @regularOpenCompleteLattice (X → Y) (collapse_space X Y)

/-- Collapse algebras inherit the regular-open Boolean algebra. -/
instance collapseAlgebraBooleanAlgebra (X Y : Type u) : BooleanAlgebra (collapse_algebra X Y) :=
  @regularOpenBooleanAlgebra (X → Y) (collapse_space X Y)

/-- Collapse algebras inherit the regular-open complete Boolean algebra. -/
instance collapseAlgebraCompleteBooleanAlgebra (X Y : Type u) :
    CompleteBooleanAlgebra (collapse_algebra X Y) :=
  @regularOpenCompleteBooleanAlgebra (X → Y) (collapse_space X Y)

/-- Nonempty collapse spaces produce nontrivial collapse algebras. -/
instance collapseAlgebraNontrivial (X Y : Type u) [Nonempty (X → Y)] :
    Nontrivial (collapse_algebra X Y) :=
  @regularOpenNontrivial (X → Y) (collapse_space X Y) ‹Nonempty (X → Y)›

/-- Embedding of a collapse poset into the collapse algebra. -/
def collapse_inclusion {X Y : Type u}
    (p : collapse_poset X Y (Order.succ Cardinal.aleph0)) : collapse_algebra X Y :=
  ⟨principal_open p, collapse_space_regular_principal_open p⟩

/-- Upstream-compatible name for the collapse-poset embedding into the regular-open algebra. -/
def inclusion {X Y : Type u}
    (p : collapse_poset X Y (Order.succ Cardinal.aleph0)) : collapse_algebra X Y :=
  collapse_inclusion p

theorem compatible_of_inclusion_le [Nonempty Y]
    {p q : collapse_poset X Y (Order.succ Cardinal.aleph0)}
    (hsubset : inclusion q ≤ inclusion p) : compatible p q :=
  compatible_of_principal_open_subset hsubset

theorem inclusion_le_of_chain {p : ℕ → collapse_poset X Y (Order.succ Cardinal.aleph0)}
    (hchain : ∀ n, inclusion (p (n + 1)) ≤ inclusion (p n)) :
    ∀ {m n : ℕ}, m ≤ n → inclusion (p n) ≤ inclusion (p m) := by
  intro m n hmn
  induction hmn with
  | refl => exact le_rfl
  | @step k hmk ih =>
      exact le_trans (hchain k) ih

theorem compatible_of_inclusion_chain [Nonempty Y]
    {p : ℕ → collapse_poset X Y (Order.succ Cardinal.aleph0)}
    (hchain : ∀ n, inclusion (p (n + 1)) ≤ inclusion (p n)) (m n : ℕ) :
    compatible (p m) (p n) := by
  by_cases hmn : m ≤ n
  · exact compatible_of_inclusion_le (inclusion_le_of_chain hchain hmn)
  · have hnm : n ≤ m := Nat.le_of_not_ge hmn
    exact (compatible_of_inclusion_le (inclusion_le_of_chain hchain hnm)).symm

theorem inclusion_omegaUnion_eq_iInf_of_compatible
    {p : ℕ → collapse_poset X Y (Order.succ Cardinal.aleph0)}
    (hcomp : ∀ m n, compatible (p m) (p n)) :
    inclusion (omegaUnion p) = ⨅ n, inclusion (p n) := by
  apply le_antisymm
  · apply le_iInf
    intro n
    change principal_open (omegaUnion p) ⊆ principal_open (p n)
    intro g hg
    exact (mem_principal_open_omegaUnion_iff_of_compatible hcomp).mp hg n
  · change ((⨅ n, inclusion (p n) : collapse_algebra X Y) : Set (X → Y)) ⊆
      principal_open (omegaUnion p)
    intro g hg
    rw [mem_principal_open_omegaUnion_iff_of_compatible hcomp]
    intro n
    exact (iInf_le (fun n => inclusion (p n)) n) hg

/-- The set of principal regular opens inside the collapse algebra. -/
def collapse_principal_opens (X Y : Type u) : Set (collapse_algebra X Y) :=
  Set.range inclusion

theorem inclusion_ne_bot [Nonempty Y]
    (p : collapse_poset X Y (Order.succ Cardinal.aleph0)) : inclusion p ≠ ⊥ := by
  intro hbot
  obtain ⟨y⟩ := ‹Nonempty Y›
  letI : TopologicalSpace (X → Y) := collapse_space X Y
  have h_nonempty : ((inclusion p : collapse_algebra X Y) : Set (X → Y)).Nonempty := by
    exact ⟨open Classical in fun x => if h : (p.f x).Dom then (p.f x).get h else y,
      trivial_extension_mem_principal_open (p := p) (y := y)⟩
  have hlt : (⊥ : collapse_algebra X Y) < inclusion p :=
    (regularOpen_bot_lt (S := inclusion p)).mpr h_nonempty
  exact (ne_of_lt hlt) hbot.symm

/-- Every nonempty collapse-basis open contains a principal open. -/
theorem collapse_poset_dense_basis {T : Set (X → Y)}
    (hT : T ∈ collapse_space_basis X Y) (h_nonempty : T ≠ ∅) :
    ∃ p : collapse_poset X Y (Order.succ Cardinal.aleph0), (inclusion p).1 ⊆ T := by
  rw [collapse_space_basis] at hT
  rcases hT with rfl | hT
  · exact False.elim (h_nonempty rfl)
  · rcases hT with ⟨p, _, rfl⟩
    exact ⟨p, subset_rfl⟩

/-- Principal opens are dense in the collapse regular-open algebra. -/
theorem collapse_poset_dense {b : collapse_algebra X Y}
    (hb : ⊥ < b) :
    ∃ p : collapse_poset X Y (Order.succ Cardinal.aleph0), inclusion p ≤ b := by
  letI : TopologicalSpace (X → Y) := collapse_space X Y
  rcases (regularOpen_bot_lt (S := b)).mp hb with ⟨f, hf⟩
  rcases collapse_space_basis_spec.exists_subset_of_mem_open hf (isOpen_of_is_regular b.2) with
    ⟨T, hT_basis, hfT, hT_subset⟩
  have hT_nonempty : T ≠ ∅ := by
    intro hT_empty
    rw [hT_empty] at hfT
    exact hfT
  rcases collapse_poset_dense_basis hT_basis hT_nonempty with ⟨p, hp⟩
  exact ⟨p, subset_trans hp hT_subset⟩

theorem collapse_principal_opens_dense [Nonempty Y] :
    dense_subset (collapse_principal_opens X Y) := by
  constructor
  · rintro ⟨p, hp⟩
    exact inclusion_ne_bot p hp
  · intro b hb
    rcases collapse_poset_dense (X := X) (Y := Y) hb with ⟨p, hp⟩
    exact ⟨inclusion p, ⟨p, rfl⟩, hp⟩

theorem collapse_principal_opens_omega_closed [Nonempty Y] :
    omega_closed (collapse_principal_opens X Y) := by
  intro s hmem _hnonzero hchain
  choose p hp using hmem
  have hchain_p : ∀ n, inclusion (p (n + 1)) ≤ inclusion (p n) := by
    intro n
    rw [hp (n + 1), hp n]
    exact hchain n
  have hcomp : ∀ m n, compatible (p m) (p n) :=
    compatible_of_inclusion_chain hchain_p
  refine ⟨omegaUnion p, ?_⟩
  rw [inclusion_omegaUnion_eq_iInf_of_compatible hcomp]
  congr
  ext n
  exact hp n

theorem collapse_principal_opens_dense_omega_closed [Nonempty Y] :
    dense_omega_closed_subset (collapse_principal_opens X Y) :=
  ⟨collapse_principal_opens_dense, collapse_principal_opens_omega_closed⟩

theorem collapse_algebra_has_dense_omega_closed_subset [Nonempty Y] :
    has_dense_omega_closed_subset (collapse_algebra X Y) :=
  ⟨collapse_principal_opens X Y, collapse_principal_opens_dense_omega_closed⟩

/-- The empty subset of `omega`, viewed as a member of the pre-set powerset of `omega`. -/
def empty_powerset_omega : (PSet.powerset (PSet.omega : pSet.{u})).Type :=
  cast (pSet.powerset_type (x := (PSet.omega : pSet.{u}))).symm
    (∅ : Set (PSet.omega : pSet.{u}).Type)

instance nonempty_powerset_omega :
    Nonempty (PSet.powerset (PSet.omega : pSet.{u})).Type :=
  ⟨empty_powerset_omega⟩

instance nonempty_aleph_one_to_powerset_omega :
    Nonempty ((pSet.card_ex (Cardinal.aleph 1) : pSet.{u}).Type →
      (PSet.powerset (PSet.omega : pSet.{u})).Type) :=
  ⟨fun _ => empty_powerset_omega⟩

/-- The collapse Boolean algebra used for the CH forcing construction. -/
abbrev collapse_boolean_algebra : Type u :=
  collapse_algebra ((pSet.card_ex (Cardinal.aleph 1) : pSet.{u}).Type)
    (PSet.powerset (PSet.omega : pSet.{u})).Type

instance collapseBooleanAlgebraCompleteBooleanAlgebra :
    CompleteBooleanAlgebra (collapse_boolean_algebra.{u}) :=
  inferInstance

instance collapseBooleanAlgebraNontrivial : Nontrivial (collapse_boolean_algebra.{u}) :=
  inferInstance

theorem collapse_boolean_algebra_has_dense_omega_closed_subset :
    has_dense_omega_closed_subset (collapse_boolean_algebra.{u}) :=
  collapse_algebra_has_dense_omega_closed_subset

end collapse_poset

end Flypitch
