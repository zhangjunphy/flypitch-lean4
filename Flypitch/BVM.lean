import Flypitch.BVTauto
import Flypitch.PSetOrdinal

universe u v

namespace Flypitch

/-!
Front slice of upstream `src/bvm.lean`: Boolean-valued set names and the first Boolean-valued
connectives used by the later forcing development.
-/

set_option linter.missingDocs false
set_option linter.style.longLine false

namespace lattice

/-- Boolean bi-implication, matching the upstream `lattice.biimp` connective. -/
def biimp {α : Type u} [BooleanAlgebra α] (a b : α) : α :=
  imp a b ⊓ imp b a

theorem supr_imp_eq {𝔹 : Type u} [CompleteBooleanAlgebra 𝔹] {ι : Sort v}
    {s : ι → 𝔹} {b : 𝔹} :
    imp (⨆ i, s i) b = ⨅ i, imp (s i) b := by
  simp [imp, compl_iSup, iInf_sup_eq]

theorem imp_infi_eq {𝔹 : Type u} [CompleteBooleanAlgebra 𝔹] {ι : Sort v}
    {s : ι → 𝔹} {b : 𝔹} :
    imp b (⨅ i, s i) = ⨅ i, imp b (s i) := by
  simp [imp, sup_iInf_eq]

theorem le_imp_iff {𝔹 : Type u} [CompleteBooleanAlgebra 𝔹] {a b c : 𝔹} :
    a ≤ imp b c ↔ a ⊓ b ≤ c := by
  constructor
  · intro h
    calc
      a ⊓ b ≤ (bᶜ ⊔ c) ⊓ b := inf_le_inf_right b h
      _ = c ⊓ b := by
        rw [inf_sup_right]
        simp [inf_comm]
      _ ≤ c := inf_le_left
  · intro h
    calc
      a = a ⊓ (b ⊔ bᶜ) := by rw [sup_compl_eq_top, inf_top_eq]
      _ = a ⊓ b ⊔ a ⊓ bᶜ := by rw [inf_sup_left]
      _ ≤ c ⊔ bᶜ := sup_le_sup h inf_le_right
      _ = imp b c := by
        dsimp [imp]
        ac_rfl

theorem imp_eq_top_iff {𝔹 : Type u} [CompleteBooleanAlgebra 𝔹] {a b : 𝔹} :
    imp a b = ⊤ ↔ a ≤ b := by
  rw [← top_le_iff, le_imp_iff, top_inf_eq]

/-- Curried Boolean implication reassociates into implication from a conjunction. -/
theorem imp_imp_eq_imp_inf {𝔹 : Type u} [CompleteBooleanAlgebra 𝔹] {a b c : 𝔹} :
    imp a (imp b c) = imp (a ⊓ b) c := by
  dsimp [imp]
  rw [compl_inf]
  ac_rfl

theorem bv_Or_elim {𝔹 : Type u} [CompleteBooleanAlgebra 𝔹] {ι : Sort v}
    {s : ι → 𝔹} {c : 𝔹} (h : ∀ i, s i ≤ c) : (⨆ i, s i) ≤ c := by
  exact iSup_le h

theorem bv_And_intro {𝔹 : Type u} [CompleteBooleanAlgebra 𝔹] {ι : Sort v}
    {s : ι → 𝔹} {c : 𝔹} (h : ∀ i, c ≤ s i) : c ≤ ⨅ i, s i := by
  exact le_iInf h

theorem bv_or_elim {𝔹 : Type u} [CompleteBooleanAlgebra 𝔹] {b₁ b₂ c : 𝔹}
    (h₁ : b₁ ≤ c) (h₂ : b₂ ≤ c) : b₁ ⊔ b₂ ≤ c :=
  sup_le h₁ h₂

theorem bv_or_elim_left {𝔹 : Type u} [CompleteBooleanAlgebra 𝔹] {b₁ b₂ c d : 𝔹}
    (h₁ : b₁ ⊓ d ≤ c) (h₂ : b₂ ⊓ d ≤ c) : (b₁ ⊔ b₂) ⊓ d ≤ c := by
  rw [inf_comm, inf_sup_left]
  exact sup_le (by simpa [inf_comm] using h₁) (by simpa [inf_comm] using h₂)

theorem bv_or_elim_right {𝔹 : Type u} [CompleteBooleanAlgebra 𝔹] {b₁ b₂ c d : 𝔹}
    (h₁ : d ⊓ b₁ ≤ c) (h₂ : d ⊓ b₂ ≤ c) : d ⊓ (b₁ ⊔ b₂) ≤ c := by
  rw [inf_sup_left]
  exact sup_le h₁ h₂

theorem bv_exfalso {𝔹 : Type u} [CompleteBooleanAlgebra 𝔹] {a b : 𝔹}
    (h : a ≤ ⊥) : a ≤ b :=
  le_trans h bot_le

theorem bv_cases_left {𝔹 : Type u} [CompleteBooleanAlgebra 𝔹] {ι : Sort v}
    {s : ι → 𝔹} {c b : 𝔹} (h : ∀ i : ι, s i ⊓ c ≤ b) :
    (⨆ i, s i) ⊓ c ≤ b := by
  apply lattice.le_imp_iff.mp
  apply iSup_le
  intro i
  exact lattice.le_imp_iff.mpr (h i)

theorem bv_cases_right {𝔹 : Type u} [CompleteBooleanAlgebra 𝔹] {ι : Sort v}
    {s : ι → 𝔹} {c b : 𝔹} (h : ∀ i : ι, c ⊓ s i ≤ b) :
    c ⊓ (⨆ i, s i) ≤ b := by
  rw [inf_comm]
  apply bv_cases_left
  intro i
  simpa [inf_comm] using h i

theorem bv_specialize {𝔹 : Type u} [CompleteBooleanAlgebra 𝔹] {ι : Sort v}
    (i : ι) {s : ι → 𝔹} {b : 𝔹} (h : s i ≤ b) : (⨅ i, s i) ≤ b :=
  (iInf_le s i).trans h

theorem bv_specialize_twice {𝔹 : Type u} [CompleteBooleanAlgebra 𝔹] {ι : Sort v}
    (i j : ι) {s : ι → 𝔹} {b : 𝔹} (h : s i ⊓ s j ≤ b) : (⨅ i, s i) ≤ b :=
  (le_inf (iInf_le s i) (iInf_le s j)).trans h

theorem bv_specialize_left {𝔹 : Type u} [CompleteBooleanAlgebra 𝔹] {ι : Sort v}
    (i : ι) {s : ι → 𝔹} {c b : 𝔹} (h : s i ⊓ c ≤ b) :
    (⨅ i, s i) ⊓ c ≤ b :=
  (inf_le_inf_right c (iInf_le s i)).trans h

theorem bv_specialize_left_twice {𝔹 : Type u} [CompleteBooleanAlgebra 𝔹] {ι : Sort v}
    (i j : ι) {s : ι → 𝔹} {c b : 𝔹} (h : s i ⊓ s j ⊓ c ≤ b) :
    (⨅ i, s i) ⊓ c ≤ b :=
  (inf_le_inf_right c (le_inf (iInf_le s i) (iInf_le s j))).trans h

theorem bv_specialize_right {𝔹 : Type u} [CompleteBooleanAlgebra 𝔹] {ι : Sort v}
    (i : ι) {s : ι → 𝔹} {c b : 𝔹} (h : c ⊓ s i ≤ b) :
    c ⊓ (⨅ i, s i) ≤ b := by
  rw [inf_comm]
  exact bv_specialize_left i (by simpa [inf_comm] using h)

theorem bv_specialize_right_twice {𝔹 : Type u} [CompleteBooleanAlgebra 𝔹] {ι : Sort v}
    (i j : ι) {s : ι → 𝔹} {c b : 𝔹} (h : c ⊓ (s i ⊓ s j) ≤ b) :
    c ⊓ (⨅ i, s i) ≤ b := by
  rw [inf_comm]
  exact bv_specialize_left_twice i j (by simpa [inf_assoc, inf_comm, inf_left_comm] using h)

theorem bv_imp_elim {𝔹 : Type u} [CompleteBooleanAlgebra 𝔹] {a b : 𝔹} :
    imp a b ⊓ a ≤ b := by
  simp [imp, inf_sup_right]

theorem bv_imp_elim' {𝔹 : Type u} [CompleteBooleanAlgebra 𝔹] {a b : 𝔹} :
    imp a b ⊓ a ≤ a ⊓ b :=
  le_inf inf_le_right bv_imp_elim

theorem bv_imp_intro {𝔹 : Type u} [CompleteBooleanAlgebra 𝔹] {a b c : 𝔹}
    (h : a ⊓ b ≤ c) : a ≤ imp b c :=
  le_imp_iff.mpr h

theorem bv_cancel_antecedent {𝔹 : Type u} [CompleteBooleanAlgebra 𝔹] {a b c : 𝔹}
    (h : b ≤ c) : imp a b ≤ imp a c := by
  apply le_imp_iff.mpr
  exact (bv_imp_elim.trans h)

theorem bv_and_intro {𝔹 : Type u} [CompleteBooleanAlgebra 𝔹] {a b₁ b₂ : 𝔹}
    (h₁ : a ≤ b₁) (h₂ : a ≤ b₂) : a ≤ b₁ ⊓ b₂ :=
  le_inf h₁ h₂

theorem bv_or_left {𝔹 : Type u} [CompleteBooleanAlgebra 𝔹] {a b₁ b₂ : 𝔹}
    (h : a ≤ b₁) : a ≤ b₁ ⊔ b₂ :=
  h.trans le_sup_left

theorem bv_or_right {𝔹 : Type u} [CompleteBooleanAlgebra 𝔹] {a b₁ b₂ : 𝔹}
    (h : a ≤ b₂) : a ≤ b₁ ⊔ b₂ :=
  h.trans le_sup_right

theorem bv_and.left {𝔹 : Type u} [CompleteBooleanAlgebra 𝔹] {a b Γ : 𝔹}
    (h : Γ ≤ a ⊓ b) : Γ ≤ a :=
  le_trans h inf_le_left

theorem bv_and.right {𝔹 : Type u} [CompleteBooleanAlgebra 𝔹] {a b Γ : 𝔹}
    (h : Γ ≤ a ⊓ b) : Γ ≤ b :=
  le_trans h inf_le_right

theorem from_empty_context {𝔹 : Type u} [CompleteBooleanAlgebra 𝔹] {a b : 𝔹}
    (h : ⊤ ≤ b) : a ≤ b :=
  le_top.trans h

theorem bv_use {𝔹 : Type u} [CompleteBooleanAlgebra 𝔹] {ι : Sort v}
    (i : ι) {s : ι → 𝔹} {b : 𝔹} (h : b ≤ s i) : b ≤ ⨆ j, s j :=
  h.trans (le_iSup s i)

theorem bv_context_apply {𝔹 : Type u} [CompleteBooleanAlgebra 𝔹] {Γ a₁ a₂ : 𝔹}
    (h₁ : Γ ≤ imp a₁ a₂) (h₂ : Γ ≤ a₁) : Γ ≤ a₂ :=
  (le_inf le_rfl h₂).trans (le_imp_iff.mp h₁)

theorem bv_have {𝔹 : Type u} [CompleteBooleanAlgebra 𝔹] {a b c : 𝔹}
    (h : a ≤ b) (h' : a ⊓ b ≤ c) : a ≤ c :=
  (le_inf le_rfl h).trans h'

theorem bv_have_true {𝔹 : Type u} [CompleteBooleanAlgebra 𝔹] {a b c : 𝔹}
    (h₁ : ⊤ ≤ b) (h₂ : a ⊓ b ≤ c) : a ≤ c := by
  have hb : b = ⊤ := top_le_iff.mp h₁
  simpa [hb] using h₂

theorem bv_imp_iff {𝔹 : Type u} [CompleteBooleanAlgebra 𝔹] {Γ b₁ b₂ : 𝔹} :
    Γ ≤ imp b₁ b₂ ↔ ∀ {Γ' : 𝔹}, Γ' ≤ Γ → Γ' ≤ b₁ → Γ' ≤ b₂ := by
  constructor
  · intro h Γ' hΓ hb₁
    exact bv_context_apply (hΓ.trans h) hb₁
  · intro h
    apply bv_imp_intro
    exact h inf_le_left inf_le_right

theorem bv_biimp_iff {𝔹 : Type u} [CompleteBooleanAlgebra 𝔹] {b₁ b₂ Γ : 𝔹} :
    Γ ≤ biimp b₁ b₂ ↔ ∀ {Γ' : 𝔹}, Γ' ≤ Γ → (Γ' ≤ b₁ ↔ Γ' ≤ b₂) := by
  constructor
  · intro h Γ' hΓ
    have h₁ : Γ ≤ imp b₁ b₂ := h.trans inf_le_left
    have h₂ : Γ ≤ imp b₂ b₁ := h.trans inf_le_right
    exact ⟨
      fun hb₁ => (bv_imp_iff.mp h₁) hΓ hb₁,
      fun hb₂ => (bv_imp_iff.mp h₂) hΓ hb₂⟩
  · intro h
    dsimp [biimp]
    apply le_inf
    · rw [bv_imp_iff]
      intro Γ' hΓ hb₁
      exact (h hΓ).mp hb₁
    · rw [bv_imp_iff]
      intro Γ' hΓ hb₂
      exact (h hΓ).mpr hb₂

theorem bv_Or_imp {𝔹 : Type u} [CompleteBooleanAlgebra 𝔹] {ι : Sort v}
    {Γ : 𝔹} {φ₁ φ₂ : ι → 𝔹}
    (hSub : Γ ≤ ⨅ i, imp (φ₁ i) (φ₂ i)) (h : Γ ≤ ⨆ i, φ₁ i) :
    Γ ≤ ⨆ i, φ₂ i := by
  apply (le_inf le_rfl h).trans
  apply bv_cases_right
  intro i
  apply bv_use i
  exact bv_context_apply (inf_le_left.trans (hSub.trans (iInf_le _ i))) inf_le_right

end lattice

open lattice

namespace pSet

theorem not_equiv {x y : pSet.{u}} (hneq : ¬ PSet.Equiv x y) :
    (∃ a : x.Type, ∀ a' : y.Type, ¬ PSet.Equiv (x.Func a) (y.Func a')) ∨
      (∃ a' : y.Type, ∀ a : x.Type, ¬ PSet.Equiv (x.Func a) (y.Func a')) := by
  by_contra h
  push Not at h
  apply hneq
  rw [pSet.ext_iff]
  intro z
  constructor
  · intro hz
    rcases pSet.mem_unfold.mp hz with ⟨a, ha⟩
    rcases h.1 a with ⟨a', ha'⟩
    exact pSet.mem_unfold.mpr ⟨a', ha.trans ha'⟩
  · intro hz
    rcases pSet.mem_unfold.mp hz with ⟨a', ha'⟩
    rcases h.2 a' with ⟨a, ha⟩
    exact pSet.mem_unfold.mpr ⟨a, ha'.trans ha.symm⟩

end pSet

/-- Boolean-valued pre-sets, or `𝔹`-names. -/
inductive bSet (𝔹 : Type u) [CompleteBooleanAlgebra 𝔹] : Type (u + 1) where
  | mk : (α : Type u) → (α → bSet 𝔹) → (α → 𝔹) → bSet 𝔹

namespace bSet

variable {𝔹 : Type u} [CompleteBooleanAlgebra 𝔹]

/-- The underlying index type of a Boolean-valued pre-set. -/
def type : bSet 𝔹 → Type u
  | mk α _ _ => α

/-- The indexing function of a Boolean-valued pre-set. -/
def func : (x : bSet 𝔹) → x.type → bSet 𝔹
  | mk _ A _, i => A i

/-- The Boolean truth-value attached to each indexed member. -/
def bval : (x : bSet 𝔹) → x.type → 𝔹
  | mk _ _ B, i => B i

@[simp] theorem mk_type_func_bval (x : bSet 𝔹) : mk x.type x.func x.bval = x := by
  cases x
  rfl

/-- The empty Boolean-valued pre-set. -/
def empty : bSet 𝔹 :=
  mk PEmpty PEmpty.elim PEmpty.elim

instance instEmptyCollection : EmptyCollection (bSet 𝔹) :=
  ⟨empty⟩

instance instInhabited : Inhabited (bSet 𝔹) :=
  ⟨empty⟩

theorem forall_over_empty (φ : (∅ : bSet 𝔹).type → 𝔹) : (⨅ a, φ a) = ⊤ := by
  apply le_antisymm le_top
  apply le_iInf
  intro a
  cases a

theorem exists_over_empty (φ : (∅ : bSet 𝔹).type → 𝔹) : (⨆ a, φ a) = ⊥ := by
  apply le_antisymm
  · apply iSup_le
    intro a
    cases a
  · exact bot_le

/-- Extensional Boolean equality for Boolean-valued pre-sets. -/
def bv_eq : bSet 𝔹 → bSet 𝔹 → 𝔹
  | mk α A B, mk α' A' B' =>
      (⨅ a : α, lattice.imp (B a) (⨆ a' : α', B' a' ⊓ bv_eq (A a) (A' a'))) ⊓
        (⨅ a' : α', lattice.imp (B' a') (⨆ a : α, B a ⊓ bv_eq (A a) (A' a')))

/-- Boolean-valued equality of Boolean-valued sets. -/
scoped infix:79 " =ᴮ " => bv_eq

/-- The relation induced by Boolean-valued equality below a context `Γ`. -/
def bv_eq' (Γ : 𝔹) : bSet 𝔹 → bSet 𝔹 → Prop :=
  fun x y => Γ ≤ x =ᴮ y

/-- Boolean membership: `x` is equivalent to a member of `y`. -/
def mem (x : bSet 𝔹) : bSet 𝔹 → 𝔹
  | mk α A B => ⨆ a : α, B a ⊓ x =ᴮ A a

/-- Boolean-valued membership. -/
scoped infix:80 " ∈ᴮ " => mem

theorem mem_unfold {x y : bSet 𝔹} : x ∈ᴮ y = ⨆ i : y.type, y.bval i ⊓ x =ᴮ y.func i := by
  cases y
  rfl

@[simp] theorem mem_empty (x : bSet 𝔹) : x ∈ᴮ (∅ : bSet 𝔹) = ⊥ := by
  exact exists_over_empty _

/-- Boolean subset. -/
def subset : bSet 𝔹 → bSet 𝔹 → 𝔹
  | mk α A B, y => ⨅ a : α, lattice.imp (B a) (A a ∈ᴮ y)

/-- Boolean-valued subset relation. -/
scoped infix:80 " ⊆ᴮ " => subset

theorem subset_unfold {x y : bSet 𝔹} :
    x ⊆ᴮ y = ⨅ i : x.type, lattice.imp (x.bval i) (x.func i ∈ᴮ y) := by
  cases x
  rfl

theorem empty_subset {x : bSet 𝔹} {Γ : 𝔹} : Γ ≤ (∅ : bSet 𝔹) ⊆ᴮ x := by
  rw [subset_unfold, forall_over_empty]
  exact le_top

@[simp] theorem empty_subset_eq_top (x : bSet 𝔹) : (∅ : bSet 𝔹) ⊆ᴮ x = ⊤ := by
  apply le_antisymm le_top
  exact empty_subset

/-- A singleton-indexed empty set whose only candidate member has Boolean value `⊥`. -/
def empty' : bSet 𝔹 :=
  mk PUnit (fun _ => ∅) (fun _ => ⊥)

/-- A two-indexed empty-set name with both zero and one Boolean weights. -/
def empty'' : bSet 𝔹 :=
  mk (Option PUnit.{u + 1}) (fun _ => ∅) (fun o => match o with | none => ⊥ | some _ => ⊤)

/-- Adjoin a Boolean-weighted candidate member to a Boolean-valued set. -/
protected def insert (u : bSet 𝔹) (b : 𝔹) : bSet 𝔹 → bSet 𝔹
  | mk α A B =>
      mk (Option α)
        (fun o => match o with | none => u | some a => A a)
        (fun o => match o with | none => b | some a => B a)

/-- Sum-indexed variant of `bSet.insert`, useful for compatibility with upstream statements. -/
protected def insert' (u : bSet 𝔹) (b : 𝔹) : bSet 𝔹 → bSet 𝔹
  | mk α A B => mk (PUnit ⊕ α) (Sum.elim (fun _ => u) A) (Sum.elim (fun _ => b) B)

/-- Adjoin a candidate member with Boolean value `⊤`. -/
protected def insert1 (u v : bSet 𝔹) : bSet 𝔹 :=
  bSet.insert u ⊤ v

theorem insert1_unfold {u v : bSet 𝔹} :
    bSet.insert1 u v =
      mk (Option v.type)
        (fun o => match o with | none => u | some a => v.func a)
        (fun o => match o with | none => ⊤ | some a => v.bval a) := by
  cases v
  dsimp [bSet.insert1, bSet.insert, type, func, bval]
  congr <;> funext o <;> cases o <;> rfl

instance instInsert : Insert (bSet 𝔹) (bSet 𝔹) :=
  ⟨fun u v => bSet.insert1 u v⟩

@[simp] theorem insert_unfold {y z : bSet 𝔹} : insert y z = bSet.insert y ⊤ z := rfl

theorem bv_eq_symm {x y : bSet 𝔹} : x =ᴮ y = y =ᴮ x := by
  induction x generalizing y with
  | mk α A B ih =>
      cases y with
      | mk α' A' B' =>
          simp [bv_eq, ih, inf_comm]

theorem bv_symm {x y : bSet 𝔹} {Γ : 𝔹} (h : Γ ≤ x =ᴮ y) : Γ ≤ y =ᴮ x := by
  rw [← bv_eq_symm]
  exact h

theorem bv_eq_unfold (x y : bSet 𝔹) :
    x =ᴮ y =
      (⨅ i : x.type, lattice.imp (x.bval i) (x.func i ∈ᴮ y)) ⊓
        (⨅ j : y.type, lattice.imp (y.bval j) (y.func j ∈ᴮ x)) := by
  cases x with
  | mk α A B =>
      cases y with
      | mk β C D =>
          dsimp [bv_eq, mem]
          congr 1
          apply iInf_congr
          intro j
          apply congrArg (lattice.imp (D j))
          apply iSup_congr
          intro i
          rw [bv_eq_symm]
          rfl

theorem eq_iff_subset_subset {x y : bSet 𝔹} : x =ᴮ y = x ⊆ᴮ y ⊓ y ⊆ᴮ x := by
  rw [bv_eq_unfold, subset_unfold, subset_unfold]

@[simp] theorem bv_eq_refl : ∀ x : bSet 𝔹, x =ᴮ x = ⊤
  | mk α A B => by
      apply le_antisymm le_top
      dsimp [bv_eq]
      apply le_inf
      · apply le_iInf
        intro i
        rw [top_le_iff]
        rw [lattice.imp_eq_top_iff]
        calc
          B i = B i ⊓ (A i =ᴮ A i) := by rw [bv_eq_refl (A i), inf_top_eq]
          _ ≤ ⨆ j, B j ⊓ A i =ᴮ A j := le_iSup (fun j => B j ⊓ A i =ᴮ A j) i
      · apply le_iInf
        intro i
        rw [top_le_iff]
        rw [lattice.imp_eq_top_iff]
        calc
          B i = B i ⊓ (A i =ᴮ A i) := by rw [bv_eq_refl (A i), inf_top_eq]
          _ ≤ ⨆ j, B j ⊓ A j =ᴮ A i := by
            simpa [bv_eq_symm] using le_iSup (fun j => B j ⊓ A j =ᴮ A i) i

theorem bv_refl {Γ : 𝔹} {x : bSet 𝔹} : Γ ≤ x =ᴮ x := by
  rw [bv_eq_refl]
  exact le_top

theorem bv_eq_top_of_eq {x y : bSet 𝔹} (h : x = y) : x =ᴮ y = ⊤ := by
  subst h
  simp

theorem bv_of_eq {x y : bSet 𝔹} {Γ : 𝔹} (h : x = y) : Γ ≤ x =ᴮ y := by
  rw [h, bv_eq_refl]
  exact le_top

theorem mem.mk {α : Type u} (A : α → bSet 𝔹) (B : α → 𝔹) (a : α) :
    B a ≤ A a ∈ᴮ mk α A B := by
  dsimp [mem]
  calc
    B a = B a ⊓ (A a =ᴮ A a) := by rw [bv_eq_refl, inf_top_eq]
    _ ≤ ⨆ a', B a' ⊓ A a =ᴮ A a' :=
      le_iSup (fun a' => B a' ⊓ A a =ᴮ A a') a

theorem mem.mk' (x : bSet 𝔹) (a : x.type) : x.bval a ≤ x.func a ∈ᴮ x := by
  cases x
  exact mem.mk _ _ _

theorem mem.mk'' {x : bSet 𝔹} {a : x.type} {Γ : 𝔹}
    (h : Γ ≤ x.bval a) : Γ ≤ x.func a ∈ᴮ x :=
  h.trans (mem.mk' x a)

@[simp] theorem mem_insert {x y z : bSet 𝔹} {b : 𝔹} :
    x ∈ᴮ bSet.insert y b z = (b ⊓ x =ᴮ y) ⊔ x ∈ᴮ z := by
  cases z
  dsimp [bSet.insert, mem]
  rw [iSup_option]

theorem mem_insert1 {x y z : bSet 𝔹} :
    x ∈ᴮ insert y z = x =ᴮ y ⊔ x ∈ᴮ z := by
  rw [insert_unfold, mem_insert, top_inf_eq]

theorem mem_insert1' {x y z : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ x ∈ᴮ insert y z ↔ Γ ≤ x =ᴮ y ⊔ x ∈ᴮ z := by
  rw [mem_insert1]

theorem mem_insert_of_eq {x y z : bSet 𝔹} {Γ : 𝔹}
    (h : Γ ≤ x =ᴮ y) : Γ ≤ x ∈ᴮ insert y z := by
  rw [mem_insert1]
  exact lattice.bv_or_left h

theorem mem_insert_of_mem {x y z : bSet 𝔹} {Γ : 𝔹}
    (h : Γ ≤ x ∈ᴮ z) : Γ ≤ x ∈ᴮ insert y z := by
  rw [mem_insert1]
  exact lattice.bv_or_right h

theorem mem_insert_self {x y : bSet 𝔹} {Γ : 𝔹} : Γ ≤ x ∈ᴮ insert x y :=
  mem_insert_of_eq bv_refl

theorem mem_insert_empty {x y : bSet 𝔹} :
    x ∈ᴮ insert y (∅ : bSet 𝔹) = x =ᴮ y := by
  rw [mem_insert1, mem_empty, sup_bot_eq]

theorem eq_of_subset_subset (x y : bSet 𝔹) : x ⊆ᴮ y ⊓ y ⊆ᴮ x ≤ x =ᴮ y := by
  rw [eq_iff_subset_subset]

theorem subset_subset_of_eq (x y : bSet 𝔹) : x =ᴮ y ≤ x ⊆ᴮ y ⊓ y ⊆ᴮ x := by
  rw [eq_iff_subset_subset]

theorem subset_subset_of_eq' {x y : bSet 𝔹} {Γ : 𝔹}
    (h : Γ ≤ x =ᴮ y) : Γ ≤ x ⊆ᴮ y ∧ Γ ≤ y ⊆ᴮ x := by
  have h' : Γ ≤ x ⊆ᴮ y ⊓ y ⊆ᴮ x := h.trans (subset_subset_of_eq x y)
  exact ⟨h'.trans inf_le_left, h'.trans inf_le_right⟩

theorem subset_of_eq {x y : bSet 𝔹} {Γ : 𝔹} (h : Γ ≤ x =ᴮ y) : Γ ≤ x ⊆ᴮ y :=
  (subset_subset_of_eq' h).1

theorem subset_of_eq_right {x y : bSet 𝔹} {Γ : 𝔹} (h : Γ ≤ x =ᴮ y) : Γ ≤ y ⊆ᴮ x :=
  (subset_subset_of_eq' h).2

@[simp] theorem subset_self {x : bSet 𝔹} {Γ : 𝔹} : Γ ≤ x ⊆ᴮ x :=
  subset_of_eq bv_refl

theorem subset_ext {x y : bSet 𝔹} {Γ : 𝔹}
    (h₁ : Γ ≤ x ⊆ᴮ y) (h₂ : Γ ≤ y ⊆ᴮ x) : Γ ≤ x =ᴮ y :=
  (le_inf h₁ h₂).trans (eq_of_subset_subset x y)

theorem subset_intro {x y : bSet 𝔹} {Γ : 𝔹}
    (h : ∀ i : x.type, Γ ⊓ x.bval i ≤ x.func i ∈ᴮ y) : Γ ≤ x ⊆ᴮ y := by
  rw [subset_unfold]
  apply le_iInf
  intro i
  exact lattice.le_imp_iff.mpr (h i)

theorem subset_empty_intro {x : bSet 𝔹} {Γ : 𝔹}
    (h : ∀ i : x.type, Γ ⊓ x.bval i ≤ ⊥) : Γ ≤ x ⊆ᴮ (∅ : bSet 𝔹) := by
  apply subset_intro
  intro i
  simpa using h i

theorem subset_elim {x y : bSet 𝔹} {Γ : 𝔹}
    (h : Γ ≤ x ⊆ᴮ y) (i : x.type) : Γ ⊓ x.bval i ≤ x.func i ∈ᴮ y := by
  rw [subset_unfold] at h
  exact lattice.le_imp_iff.mp (h.trans (iInf_le _ i))

theorem subset_elim_context {x y : bSet 𝔹} {Γ Γ' : 𝔹}
    (h : Γ ≤ x ⊆ᴮ y) (hΓ : Γ' ≤ Γ) {i : x.type} (hi : Γ' ≤ x.bval i) :
    Γ' ≤ x.func i ∈ᴮ y :=
  (le_inf hΓ hi).trans (subset_elim h i)

/-- Boolean-valued equality is transitive. -/
theorem bv_eq_trans {x y z : bSet 𝔹} : x =ᴮ y ⊓ y =ᴮ z ≤ x =ᴮ z := by
  induction x generalizing y z with
  | mk α A B ih =>
      cases y with
      | mk β C D =>
          cases z with
          | mk γ E F =>
              apply subset_ext
              · apply subset_intro
                intro i
                let Γ : 𝔹 := (mk α A B =ᴮ mk β C D) ⊓ (mk β C D =ᴮ mk γ E F)
                change Γ ⊓ B i ≤ A i ∈ᴮ mk γ E F
                have hsubXY : Γ ≤ mk α A B ⊆ᴮ mk β C D := by
                  dsimp [Γ]
                  exact subset_of_eq inf_le_left
                have hmemY : Γ ⊓ B i ≤ A i ∈ᴮ mk β C D :=
                  subset_elim hsubXY i
                rw [mem_unfold] at hmemY ⊢
                apply (le_inf le_rfl hmemY).trans
                apply lattice.bv_cases_right
                intro j
                let Δ : 𝔹 := Γ ⊓ B i ⊓ (D j ⊓ A i =ᴮ C j)
                change Δ ≤ ⨆ k : γ, F k ⊓ A i =ᴮ E k
                have hYZ : Δ ≤ mk β C D =ᴮ mk γ E F := by
                  dsimp [Δ, Γ]
                  exact (inf_le_left.trans inf_le_left).trans inf_le_right
                have hD : Δ ≤ D j := by
                  dsimp [Δ]
                  exact inf_le_right.trans inf_le_left
                have hmemC : Δ ≤ C j ∈ᴮ mk γ E F :=
                  subset_elim_context (subset_of_eq hYZ) le_rfl hD
                rw [mem_unfold] at hmemC
                apply (le_inf le_rfl hmemC).trans
                apply lattice.bv_cases_right
                intro k
                apply lattice.bv_use k
                apply le_inf
                · dsimp [Δ]
                  exact inf_le_right.trans inf_le_left
                · have hAiC : Δ ⊓ (F k ⊓ C j =ᴮ E k) ≤ A i =ᴮ C j := by
                    dsimp [Δ]
                    exact (inf_le_left.trans inf_le_right).trans inf_le_right
                  have hCE : Δ ⊓ (F k ⊓ C j =ᴮ E k) ≤ C j =ᴮ E k :=
                    inf_le_right.trans inf_le_right
                  exact (le_inf hAiC hCE).trans (ih i)
              · apply subset_intro
                intro k
                let Γ : 𝔹 := (mk α A B =ᴮ mk β C D) ⊓ (mk β C D =ᴮ mk γ E F)
                change Γ ⊓ F k ≤ E k ∈ᴮ mk α A B
                have hZY : Γ ≤ mk γ E F ⊆ᴮ mk β C D := by
                  dsimp [Γ]
                  exact subset_of_eq_right inf_le_right
                have hmemY : Γ ⊓ F k ≤ E k ∈ᴮ mk β C D :=
                  subset_elim hZY k
                rw [mem_unfold] at hmemY ⊢
                apply (le_inf le_rfl hmemY).trans
                apply lattice.bv_cases_right
                intro j
                let Δ : 𝔹 := Γ ⊓ F k ⊓ (D j ⊓ E k =ᴮ C j)
                change Δ ≤ ⨆ i : α, B i ⊓ E k =ᴮ A i
                have hYX : Γ ≤ mk β C D ⊆ᴮ mk α A B := by
                  dsimp [Γ]
                  exact subset_of_eq_right inf_le_left
                have hΓ : Δ ≤ Γ := by
                  dsimp [Δ]
                  exact inf_le_left.trans inf_le_left
                have hD : Δ ≤ D j := by
                  dsimp [Δ]
                  exact inf_le_right.trans inf_le_left
                have hmemC : Δ ≤ C j ∈ᴮ mk α A B :=
                  subset_elim_context hYX hΓ hD
                rw [mem_unfold] at hmemC
                apply (le_inf le_rfl hmemC).trans
                apply lattice.bv_cases_right
                intro i
                apply lattice.bv_use i
                apply le_inf
                · exact inf_le_right.trans inf_le_left
                · have hEC : Δ ⊓ (B i ⊓ C j =ᴮ A i) ≤ E k =ᴮ C j := by
                    dsimp [Δ]
                    exact (inf_le_left.trans inf_le_right).trans inf_le_right
                  have hCA : Δ ⊓ (B i ⊓ C j =ᴮ A i) ≤ C j =ᴮ A i :=
                    inf_le_right.trans inf_le_right
                  have hAC : Δ ⊓ (B i ⊓ C j =ᴮ A i) ≤ A i =ᴮ C j :=
                    bv_symm hCA
                  have hCE : Δ ⊓ (B i ⊓ C j =ᴮ A i) ≤ C j =ᴮ E k :=
                    bv_symm hEC
                  exact bv_symm ((le_inf hAC hCE).trans (ih i))

/-- Contextual form of transitivity for Boolean-valued equality. -/
theorem bv_trans {Γ : 𝔹} {x y z : bSet 𝔹}
    (hxy : Γ ≤ x =ᴮ y) (hyz : Γ ≤ y =ᴮ z) : Γ ≤ x =ᴮ z :=
  (le_inf hxy hyz).trans bv_eq_trans

/-- Substitute Boolean-valued equals on the left side of membership. -/
theorem subst_congr_mem_left {u v w : bSet 𝔹} : u =ᴮ v ⊓ u ∈ᴮ w ≤ v ∈ᴮ w := by
  rw [mem_unfold (x := u) (y := w), mem_unfold (x := v) (y := w)]
  apply lattice.bv_cases_right
  intro i
  apply lattice.bv_use i
  apply le_inf
  · exact inf_le_right.trans inf_le_left
  · have huv : u =ᴮ v ⊓ (w.bval i ⊓ u =ᴮ w.func i) ≤ u =ᴮ v :=
      inf_le_left
    have huw : u =ᴮ v ⊓ (w.bval i ⊓ u =ᴮ w.func i) ≤ u =ᴮ w.func i :=
      inf_le_right.trans inf_le_right
    exact bv_trans (bv_symm huv) huw

/-- Contextual form of left membership substitution. -/
theorem subst_congr_mem_left' {Γ : 𝔹} {u v w : bSet 𝔹}
    (huv : Γ ≤ u =ᴮ v) (hmem : Γ ≤ u ∈ᴮ w) : Γ ≤ v ∈ᴮ w :=
  (le_inf huv hmem).trans subst_congr_mem_left

/-- Substitute Boolean-valued equals on the right side of membership. -/
theorem subst_congr_mem_right {u v w : bSet 𝔹} : v =ᴮ w ⊓ u ∈ᴮ v ≤ u ∈ᴮ w := by
  rw [mem_unfold (x := u) (y := v)]
  apply lattice.bv_cases_right
  intro i
  let Γ : 𝔹 := v =ᴮ w ⊓ (v.bval i ⊓ u =ᴮ v.func i)
  change Γ ≤ u ∈ᴮ w
  have hvw : Γ ≤ v =ᴮ w := by
    dsimp [Γ]
    exact inf_le_left
  have hval : Γ ≤ v.bval i := by
    dsimp [Γ]
    exact inf_le_right.trans inf_le_left
  have hui : Γ ≤ u =ᴮ v.func i := by
    dsimp [Γ]
    exact inf_le_right.trans inf_le_right
  have hmem : Γ ≤ v.func i ∈ᴮ w :=
    subset_elim_context (subset_of_eq hvw) le_rfl hval
  exact (le_inf (bv_symm hui) hmem).trans subst_congr_mem_left

/-- Contextual form of right membership substitution. -/
theorem subst_congr_mem_right' {Γ : 𝔹} {u v w : bSet 𝔹}
    (hvw : Γ ≤ v =ᴮ w) (hmem : Γ ≤ u ∈ᴮ v) : Γ ≤ u ∈ᴮ w :=
  (le_inf hvw hmem).trans subst_congr_mem_right

/-- Membership is monotone along Boolean-valued subset. -/
theorem mem_of_mem_subset {x y z : bSet 𝔹} : x ⊆ᴮ y ⊓ z ∈ᴮ x ≤ z ∈ᴮ y := by
  rw [mem_unfold (x := z) (y := x)]
  apply lattice.bv_cases_right
  intro i
  let Γ : 𝔹 := x ⊆ᴮ y ⊓ (x.bval i ⊓ z =ᴮ x.func i)
  change Γ ≤ z ∈ᴮ y
  have hsub : Γ ≤ x ⊆ᴮ y := by
    dsimp [Γ]
    exact inf_le_left
  have hval : Γ ≤ x.bval i := by
    dsimp [Γ]
    exact inf_le_right.trans inf_le_left
  have hzx : Γ ≤ z =ᴮ x.func i := by
    dsimp [Γ]
    exact inf_le_right.trans inf_le_right
  have hmem : Γ ≤ x.func i ∈ᴮ y :=
    subset_elim_context hsub le_rfl hval
  exact (le_inf (bv_symm hzx) hmem).trans subst_congr_mem_left

/-- Contextual form of membership monotonicity along Boolean-valued subset. -/
theorem mem_of_mem_subset' {Γ : 𝔹} {x y z : bSet 𝔹}
    (hsub : Γ ≤ x ⊆ᴮ y) (hmem : Γ ≤ z ∈ᴮ x) : Γ ≤ z ∈ᴮ y :=
  (le_inf hsub hmem).trans mem_of_mem_subset

/-- Substitute Boolean-valued equals on the left side of subset. -/
theorem subst_congr_subset_left {x y z : bSet 𝔹} :
    x =ᴮ y ⊓ x ⊆ᴮ z ≤ y ⊆ᴮ z := by
  apply subset_intro
  intro i
  let Γ : 𝔹 := x =ᴮ y ⊓ x ⊆ᴮ z
  change Γ ⊓ y.bval i ≤ y.func i ∈ᴮ z
  have hxy : Γ ⊓ y.bval i ≤ x =ᴮ y := by
    dsimp [Γ]
    exact inf_le_left.trans inf_le_left
  have hyxSub : Γ ⊓ y.bval i ≤ y ⊆ᴮ x :=
    subset_of_eq_right hxy
  have hyMemX : Γ ⊓ y.bval i ≤ y.func i ∈ᴮ x :=
    subset_elim_context hyxSub le_rfl inf_le_right
  have hxz : Γ ⊓ y.bval i ≤ x ⊆ᴮ z := by
    dsimp [Γ]
    exact inf_le_left.trans inf_le_right
  exact mem_of_mem_subset' hxz hyMemX

/-- Contextual form of left subset substitution. -/
theorem subst_congr_subset_left' {Γ : 𝔹} {x y z : bSet 𝔹}
    (hxy : Γ ≤ x =ᴮ y) (hsub : Γ ≤ x ⊆ᴮ z) : Γ ≤ y ⊆ᴮ z :=
  (le_inf hxy hsub).trans subst_congr_subset_left

/-- Substitute Boolean-valued equals on the right side of subset. -/
theorem subst_congr_subset_right {x y z : bSet 𝔹} :
    y =ᴮ z ⊓ x ⊆ᴮ y ≤ x ⊆ᴮ z := by
  apply subset_intro
  intro i
  let Γ : 𝔹 := y =ᴮ z ⊓ x ⊆ᴮ y
  change Γ ⊓ x.bval i ≤ x.func i ∈ᴮ z
  have hxy : Γ ⊓ x.bval i ≤ x ⊆ᴮ y := by
    dsimp [Γ]
    exact inf_le_left.trans inf_le_right
  have hxMemY : Γ ⊓ x.bval i ≤ x.func i ∈ᴮ y :=
    subset_elim_context hxy le_rfl inf_le_right
  have hyz : Γ ⊓ x.bval i ≤ y =ᴮ z := by
    dsimp [Γ]
    exact inf_le_left.trans inf_le_left
  have hyzSub : Γ ⊓ x.bval i ≤ y ⊆ᴮ z :=
    subset_of_eq hyz
  exact mem_of_mem_subset' hyzSub hxMemY

/-- Contextual form of right subset substitution. -/
theorem subst_congr_subset_right' {Γ : 𝔹} {x y z : bSet 𝔹}
    (hyz : Γ ≤ y =ᴮ z) (hsub : Γ ≤ x ⊆ᴮ y) : Γ ≤ x ⊆ᴮ z :=
  (le_inf hyz hsub).trans subst_congr_subset_right

theorem bSet_axiom_of_extensionality (x y : bSet 𝔹) :
    (⨅ z : bSet 𝔹,
        (lattice.imp (z ∈ᴮ x) (z ∈ᴮ y)) ⊓
          (lattice.imp (z ∈ᴮ y) (z ∈ᴮ x))) ≤ x =ᴮ y := by
  set Γ : 𝔹 :=
    ⨅ z : bSet 𝔹,
      (lattice.imp (z ∈ᴮ x) (z ∈ᴮ y)) ⊓
        (lattice.imp (z ∈ᴮ y) (z ∈ᴮ x))
  apply subset_ext
  · apply subset_intro
    intro i
    have hΓ : Γ ≤ lattice.imp (x.func i ∈ᴮ x) (x.func i ∈ᴮ y) :=
      (iInf_le
        (fun z : bSet 𝔹 =>
          (lattice.imp (z ∈ᴮ x) (z ∈ᴮ y)) ⊓
            (lattice.imp (z ∈ᴮ y) (z ∈ᴮ x)))
        (x.func i)).trans inf_le_left
    exact lattice.bv_context_apply (inf_le_left.trans hΓ) (mem.mk'' inf_le_right)
  · apply subset_intro
    intro i
    have hΓ : Γ ≤ lattice.imp (y.func i ∈ᴮ y) (y.func i ∈ᴮ x) :=
      (iInf_le
        (fun z : bSet 𝔹 =>
          (lattice.imp (z ∈ᴮ x) (z ∈ᴮ y)) ⊓
            (lattice.imp (z ∈ᴮ y) (z ∈ᴮ x)))
        (y.func i)).trans inf_le_right
    exact lattice.bv_context_apply (inf_le_left.trans hΓ) (mem.mk'' inf_le_right)

theorem mem_ext {x y : bSet 𝔹} {Γ : 𝔹}
    (hxy : Γ ≤ ⨅ z : bSet 𝔹, lattice.imp (z ∈ᴮ x) (z ∈ᴮ y))
    (hyx : Γ ≤ ⨅ z : bSet 𝔹, lattice.imp (z ∈ᴮ y) (z ∈ᴮ x)) : Γ ≤ x =ᴮ y := by
  apply le_trans ?_ (bSet_axiom_of_extensionality x y)
  apply le_iInf
  intro z
  exact le_inf (hxy.trans (iInf_le _ z)) (hyx.trans (iInf_le _ z))

theorem mem_ext_of_biimp {x y : bSet 𝔹} {Γ : 𝔹}
    (h : Γ ≤ ⨅ z : bSet 𝔹, lattice.biimp (z ∈ᴮ x) (z ∈ᴮ y)) : Γ ≤ x =ᴮ y := by
  apply mem_ext
  · apply le_iInf
    intro z
    exact (h.trans (iInf_le _ z)).trans inf_le_left
  · apply le_iInf
    intro z
    exact (h.trans (iInf_le _ z)).trans inf_le_right

/-- A Boolean-valued predicate respects Boolean equality in its argument. -/
def B_ext (φ : bSet 𝔹 → 𝔹) : Prop :=
  ∀ x y, x =ᴮ y ⊓ φ x ≤ φ y

/-- A Boolean-valued set operation respects Boolean equality in its argument. -/
def B_congr (F : bSet 𝔹 → bSet 𝔹) : Prop :=
  ∀ x y, x =ᴮ y ≤ F x =ᴮ F y

/-- Rewrite a Boolean-valued extensional predicate across top-valued equality. -/
theorem bv_rw {x y : bSet 𝔹} (hxy : x =ᴮ y = ⊤)
    (φ : bSet 𝔹 → 𝔹) (hφ : B_ext φ) : φ y = φ x := by
  apply le_antisymm
  · have hyx : y =ᴮ x = ⊤ := by
      simpa [bv_eq_symm] using hxy
    calc
      φ y = y =ᴮ x ⊓ φ y := by rw [hyx, top_inf_eq]
      _ ≤ φ x := hφ y x
  · calc
      φ x = x =ᴮ y ⊓ φ x := by rw [hxy, top_inf_eq]
      _ ≤ φ y := hφ x y

/-- Membership is extensional in its left argument. -/
theorem B_ext_mem_left (w : bSet 𝔹) : B_ext (fun u => u ∈ᴮ w) :=
  fun _ _ => subst_congr_mem_left

/-- Membership is extensional in its right argument. -/
theorem B_ext_mem_right (u : bSet 𝔹) : B_ext (fun w => u ∈ᴮ w) :=
  fun _ _ => subst_congr_mem_right

/-- Subset is extensional in its left argument. -/
theorem B_ext_subset_left (z : bSet 𝔹) : B_ext (fun x => x ⊆ᴮ z) :=
  fun _ _ => subst_congr_subset_left

/-- Subset is extensional in its right argument. -/
theorem B_ext_subset_right (x : bSet 𝔹) : B_ext (fun y => x ⊆ᴮ y) :=
  fun _ _ => subst_congr_subset_right

/-- Boolean-valued equality is extensional in its left argument. -/
theorem B_ext_eq_left (z : bSet 𝔹) : B_ext (fun x => x =ᴮ z) := by
  intro x y
  have hyx : x =ᴮ y ⊓ x =ᴮ z ≤ y =ᴮ x :=
    inf_le_left.trans (le_of_eq bv_eq_symm)
  have hxz : x =ᴮ y ⊓ x =ᴮ z ≤ x =ᴮ z :=
    inf_le_right
  exact bv_trans hyx hxz

/-- Boolean-valued equality is extensional in its right argument. -/
theorem B_ext_eq_right (x : bSet 𝔹) : B_ext (fun y => x =ᴮ y) := by
  intro y z
  have hxy : y =ᴮ z ⊓ x =ᴮ y ≤ x =ᴮ y :=
    inf_le_right
  have hyz : y =ᴮ z ⊓ x =ᴮ y ≤ y =ᴮ z :=
    inf_le_left
  exact bv_trans hxy hyz

/-- The identity operation on Boolean-valued sets is congruent. -/
theorem B_congr_id : B_congr (𝔹 := 𝔹) (fun x : bSet 𝔹 => x) :=
  fun _ _ => le_rfl

/-- Constant Boolean-valued predicates are extensional. -/
theorem B_ext_const (b : 𝔹) : B_ext (𝔹 := 𝔹) (fun _ : bSet 𝔹 => b) := by
  intro _ _
  exact inf_le_right

theorem B_ext_top : B_ext (𝔹 := 𝔹) (fun _ : bSet 𝔹 => ⊤) := by
  intro x y
  exact le_top

theorem B_ext_bot : B_ext (𝔹 := 𝔹) (fun _ : bSet 𝔹 => ⊥) := by
  intro x y
  exact inf_le_right

theorem B_ext_inf {φ ψ : bSet 𝔹 → 𝔹} (hφ : B_ext φ) (hψ : B_ext ψ) :
    B_ext (fun x => φ x ⊓ ψ x) := by
  intro x y
  apply le_inf
  · exact (le_inf inf_le_left (inf_le_right.trans inf_le_left)).trans (hφ x y)
  · exact (le_inf inf_le_left (inf_le_right.trans inf_le_right)).trans (hψ x y)

theorem B_ext_sup {φ ψ : bSet 𝔹 → 𝔹} (hφ : B_ext φ) (hψ : B_ext ψ) :
    B_ext (fun x => φ x ⊔ ψ x) := by
  intro x y
  apply lattice.bv_or_elim_right
  · exact (hφ x y).trans le_sup_left
  · exact (hψ x y).trans le_sup_right

theorem B_ext_imp {φ ψ : bSet 𝔹 → 𝔹} (hφ : B_ext φ) (hψ : B_ext ψ) :
    B_ext (fun x => lattice.imp (φ x) (ψ x)) := by
  intro x y
  apply lattice.bv_imp_intro
  have hEq : (x =ᴮ y ⊓ lattice.imp (φ x) (ψ x)) ⊓ φ y ≤ x =ᴮ y :=
    inf_le_left.trans inf_le_left
  have hSym : (x =ᴮ y ⊓ lattice.imp (φ x) (ψ x)) ⊓ φ y ≤ y =ᴮ x := by
    exact hEq.trans (le_of_eq bv_eq_symm)
  have hφx : (x =ᴮ y ⊓ lattice.imp (φ x) (ψ x)) ⊓ φ y ≤ φ x :=
    (le_inf hSym inf_le_right).trans (hφ y x)
  have hImp : (x =ᴮ y ⊓ lattice.imp (φ x) (ψ x)) ⊓ φ y ≤ lattice.imp (φ x) (ψ x) :=
    inf_le_left.trans inf_le_right
  have hψx : (x =ᴮ y ⊓ lattice.imp (φ x) (ψ x)) ⊓ φ y ≤ ψ x :=
    lattice.bv_context_apply hImp hφx
  exact (le_inf hEq hψx).trans (hψ x y)

theorem B_ext_biimp {φ ψ : bSet 𝔹 → 𝔹} (hφ : B_ext φ) (hψ : B_ext ψ) :
    B_ext (fun x => lattice.biimp (φ x) (ψ x)) :=
  B_ext_inf (B_ext_imp hφ hψ) (B_ext_imp hψ hφ)

/-- Boolean complementation preserves extensional predicates. -/
theorem B_ext_compl {φ : bSet 𝔹 → 𝔹} (hφ : B_ext φ) : B_ext (fun x => (φ x)ᶜ) := by
  intro x y
  have hImp : x =ᴮ y ⊓ (φ x)ᶜ ≤ lattice.imp (φ y) ⊥ := by
    apply lattice.bv_imp_intro
    have hEq : (x =ᴮ y ⊓ (φ x)ᶜ) ⊓ φ y ≤ y =ᴮ x :=
      (inf_le_left.trans inf_le_left).trans (le_of_eq bv_eq_symm)
    have hφx : (x =ᴮ y ⊓ (φ x)ᶜ) ⊓ φ y ≤ φ x :=
      (le_inf hEq inf_le_right).trans (hφ y x)
    have hNot : (x =ᴮ y ⊓ (φ x)ᶜ) ⊓ φ y ≤ (φ x)ᶜ :=
      inf_le_left.trans inf_le_right
    calc
      (x =ᴮ y ⊓ (φ x)ᶜ) ⊓ φ y ≤ (φ x)ᶜ ⊓ φ x := le_inf hNot hφx
      _ = ⊥ := compl_inf_eq_bot
  simpa [lattice.imp] using hImp

/-- The predicate `x ⊆ᴮ y or y ⊆ᴮ x` is extensional in its left argument. -/
theorem B_ext_subset_or_subset_left (y : bSet 𝔹) :
    B_ext (fun x : bSet 𝔹 => x ⊆ᴮ y ⊔ y ⊆ᴮ x) :=
  B_ext_sup (B_ext_subset_left y) (B_ext_subset_right y)

/-- The predicate `x ⊆ᴮ y or y ⊆ᴮ x` is extensional in its right argument. -/
theorem B_ext_subset_or_subset_right (x : bSet 𝔹) :
    B_ext (fun y : bSet 𝔹 => x ⊆ᴮ y ⊔ y ⊆ᴮ x) :=
  B_ext_sup (B_ext_subset_right x) (B_ext_subset_left x)

theorem B_ext_iInf {ι : Sort v} {φ : ι → bSet 𝔹 → 𝔹}
    (hφ : ∀ i, B_ext (φ i)) : B_ext (fun x => ⨅ i, φ i x) := by
  intro x y
  apply le_iInf
  intro i
  exact (le_inf inf_le_left (inf_le_right.trans (iInf_le _ i))).trans (hφ i x y)

theorem B_ext_iSup {ι : Sort v} {φ : ι → bSet 𝔹 → 𝔹}
    (hφ : ∀ i, B_ext (φ i)) : B_ext (fun x => ⨆ i, φ i x) := by
  intro x y
  apply lattice.bv_cases_right
  intro i
  exact (hφ i x y).trans (le_iSup (fun i => φ i y) i)

theorem bounded_forall (x : bSet 𝔹) (φ : bSet 𝔹 → 𝔹) (hφ : B_ext φ) :
    (⨅ i : x.type, lattice.imp (x.bval i) (φ (x.func i))) =
      ⨅ y : bSet 𝔹, lattice.imp (y ∈ᴮ x) (φ y) := by
  apply le_antisymm
  · apply le_iInf
    intro y
    apply lattice.bv_imp_intro
    rw [mem_unfold]
    apply lattice.bv_cases_right
    intro i
    have hImp :
        (⨅ j : x.type, lattice.imp (x.bval j) (φ (x.func j))) ⊓
            (x.bval i ⊓ y =ᴮ x.func i) ≤
          lattice.imp (x.bval i) (φ (x.func i)) :=
      inf_le_left.trans (iInf_le _ i)
    have hVal :
        (⨅ j : x.type, lattice.imp (x.bval j) (φ (x.func j))) ⊓
            (x.bval i ⊓ y =ᴮ x.func i) ≤ x.bval i :=
      inf_le_right.trans inf_le_left
    have hφi :
        (⨅ j : x.type, lattice.imp (x.bval j) (φ (x.func j))) ⊓
            (x.bval i ⊓ y =ᴮ x.func i) ≤ φ (x.func i) :=
      lattice.bv_context_apply hImp hVal
    have hEq :
        (⨅ j : x.type, lattice.imp (x.bval j) (φ (x.func j))) ⊓
            (x.bval i ⊓ y =ᴮ x.func i) ≤ x.func i =ᴮ y :=
      (inf_le_right.trans inf_le_right).trans (le_of_eq bv_eq_symm)
    exact (le_inf hEq hφi).trans (hφ (x.func i) y)
  · apply le_iInf
    intro i
    apply lattice.bv_imp_intro
    have hImp :
        (⨅ y : bSet 𝔹, lattice.imp (y ∈ᴮ x) (φ y)) ⊓ x.bval i ≤
          lattice.imp (x.func i ∈ᴮ x) (φ (x.func i)) :=
      inf_le_left.trans (iInf_le _ (x.func i))
    have hMem :
        (⨅ y : bSet 𝔹, lattice.imp (y ∈ᴮ x) (φ y)) ⊓ x.bval i ≤
          x.func i ∈ᴮ x :=
      inf_le_right.trans (mem.mk' x i)
    exact lattice.bv_context_apply hImp hMem

theorem bounded_exists (x : bSet 𝔹) (φ : bSet 𝔹 → 𝔹) (hφ : B_ext φ) :
    (⨆ i : x.type, x.bval i ⊓ φ (x.func i)) =
      ⨆ y : bSet 𝔹, y ∈ᴮ x ⊓ φ y := by
  apply le_antisymm
  · apply iSup_le
    intro i
    apply le_trans ?_ (le_iSup (fun y : bSet 𝔹 => y ∈ᴮ x ⊓ φ y) (x.func i))
    exact le_inf (inf_le_left.trans (mem.mk' x i)) inf_le_right
  · apply iSup_le
    intro y
    rw [mem_unfold]
    apply lattice.bv_cases_left
    intro i
    apply lattice.bv_use i
    apply le_inf
    · exact inf_le_left.trans inf_le_left
    · have hEq : x.bval i ⊓ y =ᴮ x.func i ⊓ φ y ≤ y =ᴮ x.func i :=
        inf_le_left.trans inf_le_right
      have hφy : x.bval i ⊓ y =ᴮ x.func i ⊓ φ y ≤ φ y :=
        inf_le_right
      exact (le_inf hEq hφy).trans (hφ y (x.func i))

theorem subset_unfold' {x y : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ x ⊆ᴮ y ↔
      Γ ≤ ⨅ z : bSet 𝔹, lattice.imp (z ∈ᴮ x) (z ∈ᴮ y) := by
  rw [subset_unfold]
  rw [bounded_forall x (fun z : bSet 𝔹 => z ∈ᴮ y) (B_ext_mem_left y)]

/-- Structural recursion over a Boolean-valued set, exposing recursive data for each indexed member. -/
protected noncomputable def rec_on' {C : bSet 𝔹 → Sort v} (y : bSet 𝔹)
    (h : ∀ x : bSet 𝔹, (∀ a : x.type, C (x.func a)) → C x) : C y := by
  induction y with
  | mk α A B ih =>
      exact h (mk α A B) ih

/-- Curried structural recursion over Boolean-valued sets. -/
protected noncomputable def rec' {C : bSet 𝔹 → Sort v}
    (h : ∀ x : bSet 𝔹, (∀ a : x.type, C (x.func a)) → C x) :
    ∀ y : bSet 𝔹, C y := by
  intro y
  exact bSet.rec_on' y h

/-- Boolean-valued epsilon induction as a top-valued implication. -/
theorem bSet_epsilon_induction (φ : bSet 𝔹 → 𝔹) (hφ : B_ext φ) :
    lattice.imp
      (⨅ x : bSet 𝔹, lattice.imp (⨅ y : bSet 𝔹, lattice.imp (y ∈ᴮ x) (φ y)) (φ x))
      (⨅ z : bSet 𝔹, φ z) = ⊤ := by
  apply lattice.imp_eq_top_iff.mpr
  apply le_iInf
  intro z
  induction z with
  | mk α A B ih =>
      let H : 𝔹 :=
        ⨅ x : bSet 𝔹, lattice.imp (⨅ y : bSet 𝔹, lattice.imp (y ∈ᴮ x) (φ y)) (φ x)
      change H ≤ φ (mk α A B)
      have hMembers : H ≤ ⨅ i : α, lattice.imp (B i) (φ (A i)) := by
        apply le_iInf
        intro i
        apply lattice.bv_imp_intro
        exact inf_le_left.trans (ih i)
      have hBounded :
          (⨅ i : α, lattice.imp (B i) (φ (A i))) =
            ⨅ y : bSet 𝔹, lattice.imp (y ∈ᴮ mk α A B) (φ y) := by
        simpa only [type, func, bval] using bounded_forall (mk α A B) φ hφ
      have hPremise : H ≤ ⨅ y : bSet 𝔹, lattice.imp (y ∈ᴮ mk α A B) (φ y) := by
        simpa [hBounded] using hMembers
      have hStep :
          H ≤ lattice.imp (⨅ y : bSet 𝔹, lattice.imp (y ∈ᴮ mk α A B) (φ y))
              (φ (mk α A B)) :=
        iInf_le _ (mk α A B)
      exact lattice.bv_context_apply hStep hPremise

/-- Contextual Boolean-valued epsilon induction. -/
theorem epsilon_induction {Γ : 𝔹} (φ : bSet 𝔹 → 𝔹) (hφ : B_ext φ)
    (hstep : ∀ x : bSet 𝔹,
      Γ ≤ lattice.imp (⨅ y : bSet 𝔹, lattice.imp (y ∈ᴮ x) (φ y)) (φ x)) :
    ∀ z : bSet 𝔹, Γ ≤ φ z := by
  let H : 𝔹 :=
    ⨅ x : bSet 𝔹, lattice.imp (⨅ y : bSet 𝔹, lattice.imp (y ∈ᴮ x) (φ y)) (φ x)
  have hH : Γ ≤ H := by
    apply le_iInf
    intro x
    exact hstep x
  have hAll : H ≤ ⨅ z : bSet 𝔹, φ z := by
    exact lattice.imp_eq_top_iff.mp (bSet_epsilon_induction φ hφ)
  intro z
  exact (hH.trans hAll).trans (iInf_le _ z)

/-- Boolean-valued unique existence: some witness is equal to every satisfying object. -/
def bv_exists_unique (φ : bSet 𝔹 → 𝔹) : 𝔹 :=
  ⨆ x : bSet 𝔹, ⨅ y : bSet 𝔹, lattice.imp (φ y) (y =ᴮ x)

/-- Reindex two bounded universal quantifiers over members of the same Boolean-valued set. -/
theorem forall_forall_reindex (φ : bSet 𝔹 → bSet 𝔹 → 𝔹)
    (h₁ : ∀ x, B_ext (fun y => φ x y)) (h₂ : ∀ y, B_ext (fun x => φ x y))
    (C : bSet 𝔹) :
    (⨅ i₁ : C.type,
        lattice.imp (C.bval i₁)
          (⨅ i₂ : C.type, lattice.imp (C.bval i₂) (φ (C.func i₁) (C.func i₂)))) =
      ⨅ w₁ : bSet 𝔹, ⨅ w₂ : bSet 𝔹,
        lattice.imp (w₁ ∈ᴮ C ⊓ w₂ ∈ᴮ C) (φ w₁ w₂) := by
  have hOuterExt :
      B_ext (fun x => ⨅ i₂ : C.type,
        lattice.imp (C.bval i₂) (φ x (C.func i₂))) := by
    apply B_ext_iInf
    intro i₂
    exact B_ext_imp (B_ext_const _) (h₂ (C.func i₂))
  rw [bounded_forall C
    (fun x => ⨅ i₂ : C.type, lattice.imp (C.bval i₂) (φ x (C.func i₂))) hOuterExt]
  apply le_antisymm
  · apply le_iInf
    intro w₁
    apply le_iInf
    intro w₂
    rw [← lattice.imp_imp_eq_imp_inf]
    apply le_trans (iInf_le _ w₁)
    apply lattice.bv_cancel_antecedent
    rw [bounded_forall C (fun y => φ w₁ y) (h₁ w₁)]
    exact iInf_le _ w₂
  · apply le_iInf
    intro w₁
    apply lattice.bv_imp_intro
    apply le_iInf
    intro i₂
    apply lattice.bv_imp_intro
    have hImp :
        ((⨅ w₁ : bSet 𝔹, ⨅ w₂ : bSet 𝔹,
            lattice.imp (w₁ ∈ᴮ C ⊓ w₂ ∈ᴮ C) (φ w₁ w₂)) ⊓ w₁ ∈ᴮ C) ⊓ C.bval i₂ ≤
          lattice.imp (w₁ ∈ᴮ C ⊓ C.func i₂ ∈ᴮ C) (φ w₁ (C.func i₂)) :=
      ((inf_le_left.trans inf_le_left).trans (iInf_le _ w₁)).trans (iInf_le _ (C.func i₂))
    have hArg :
        ((⨅ w₁ : bSet 𝔹, ⨅ w₂ : bSet 𝔹,
            lattice.imp (w₁ ∈ᴮ C ⊓ w₂ ∈ᴮ C) (φ w₁ w₂)) ⊓ w₁ ∈ᴮ C) ⊓ C.bval i₂ ≤
          w₁ ∈ᴮ C ⊓ C.func i₂ ∈ᴮ C :=
      le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans (mem.mk' C i₂))
    exact lattice.bv_context_apply hImp hArg

namespace subset

/-- Restrict a Boolean-valued set by assigning each indexed member a smaller Boolean value. -/
def mk {x : bSet 𝔹} (χ : x.type → 𝔹) : bSet 𝔹 :=
  bSet.mk x.type x.func (fun i => χ i ⊓ x.bval i)

@[simp] theorem mk_type {x : bSet 𝔹} {χ : x.type → 𝔹} : (mk χ).type = x.type := rfl

@[simp] theorem mk_func {x : bSet 𝔹} {χ : x.type → 𝔹} (i : (mk χ).type) :
    (mk χ).func i = x.func i := rfl

@[simp] theorem mk_bval {x : bSet 𝔹} {χ : x.type → 𝔹} (i : (mk χ).type) :
    (mk χ).bval i = χ i ⊓ x.bval i := rfl

theorem mk_subset {x : bSet 𝔹} {χ : x.type → 𝔹} {Γ : 𝔹} :
    Γ ≤ mk χ ⊆ᴮ x := by
  apply subset_intro
  intro i
  exact mem.mk'' (x := x) (a := i) (inf_le_right.trans inf_le_right)

theorem mem_mk_iff {x z : bSet 𝔹} {χ : x.type → 𝔹} {Γ : 𝔹} :
    Γ ≤ z ∈ᴮ mk χ ↔ Γ ≤ ⨆ i : x.type, (χ i ⊓ x.bval i) ⊓ z =ᴮ x.func i := by
  rfl

theorem mem_mk_iff' {x z : bSet 𝔹} {χ : x.type → 𝔹} {Γ : 𝔹} :
    Γ ≤ z ∈ᴮ mk χ ↔ Γ ≤ ⨆ i : x.type, z =ᴮ x.func i ⊓ (χ i ⊓ x.bval i) := by
  rw [mem_mk_iff]
  have hEq :
      (⨆ i : x.type, (χ i ⊓ x.bval i) ⊓ z =ᴮ x.func i) =
        ⨆ i : x.type, z =ᴮ x.func i ⊓ (χ i ⊓ x.bval i) := by
    apply iSup_congr
    intro i
    ac_rfl
  rw [hEq]

theorem mem_mk_iff₂ {x z : bSet 𝔹} {χ : x.type → 𝔹} {Γ : 𝔹} :
    Γ ≤ z ∈ᴮ mk χ ↔ Γ ≤ ⨆ i : x.type, x.bval i ⊓ (z =ᴮ x.func i ⊓ χ i) := by
  rw [mem_mk_iff]
  have hEq :
      (⨆ i : x.type, (χ i ⊓ x.bval i) ⊓ z =ᴮ x.func i) =
        ⨆ i : x.type, x.bval i ⊓ (z =ᴮ x.func i ⊓ χ i) := by
    apply iSup_congr
    intro i
    ac_rfl
  rw [hEq]

theorem mem_of_mem_mk {x z : bSet 𝔹} {χ : x.type → 𝔹} {Γ : 𝔹}
    (hz : Γ ≤ z ∈ᴮ mk χ) : Γ ≤ z ∈ᴮ x :=
  mem_of_mem_subset' mk_subset hz

end subset

/-- A subset name determined by a Boolean-valued indicator over an existing name. -/
def set_of_indicator {x : bSet 𝔹} (χ : x.type → 𝔹) : bSet 𝔹 :=
  subset.mk χ

theorem mem_set_of_indicator_iff {x z : bSet 𝔹} {χ : x.type → 𝔹} {Γ : 𝔹} :
    Γ ≤ z ∈ᴮ set_of_indicator χ ↔
      Γ ≤ ⨆ i : x.type, (χ i ⊓ x.bval i) ⊓ z =ᴮ x.func i := by
  exact subset.mem_mk_iff

namespace mem_subset

theorem mk_iff {x z : bSet 𝔹} {χ : x.type → 𝔹} {Γ : 𝔹} :
    Γ ≤ z ∈ᴮ subset.mk χ ↔
      Γ ≤ ⨆ i : x.type, z =ᴮ x.func i ⊓ (χ i ⊓ x.bval i) :=
  subset.mem_mk_iff'

theorem mk_iff₂ {x z : bSet 𝔹} {χ : x.type → 𝔹} {Γ : 𝔹} :
    Γ ≤ z ∈ᴮ subset.mk χ ↔
      Γ ≤ ⨆ i : x.type, x.bval i ⊓ (z =ᴮ x.func i ⊓ χ i) :=
  subset.mem_mk_iff₂

end mem_subset

namespace mem_of_mem_subset

theorem mk {x z : bSet 𝔹} {χ : x.type → 𝔹} {Γ : 𝔹}
    (hz : Γ ≤ z ∈ᴮ subset.mk χ) : Γ ≤ z ∈ᴮ x :=
  subset.mem_of_mem_mk hz

end mem_of_mem_subset

/-- Boolean-valued separation of a name by an extensional predicate. -/
def comprehend (φ : bSet 𝔹 → 𝔹) (x : bSet 𝔹) : bSet 𝔹 :=
  subset.mk (x := x) (fun i : x.type => φ (x.func i))

theorem mem_comprehend_iff {φ : bSet 𝔹 → 𝔹} {x z : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ z ∈ᴮ comprehend φ x ↔
      Γ ≤ ⨆ i : x.type, x.bval i ⊓ (z =ᴮ x.func i ⊓ φ (x.func i)) :=
  subset.mem_mk_iff₂

theorem mem_comprehend_iff₂ {φ : bSet 𝔹 → 𝔹} (hφ : B_ext φ) {x z : bSet 𝔹}
    {Γ : 𝔹} :
    Γ ≤ z ∈ᴮ comprehend φ x ↔
      Γ ≤ ⨆ w : bSet 𝔹, w ∈ᴮ x ⊓ (z =ᴮ w ⊓ φ w) := by
  rw [mem_comprehend_iff]
  rw [bounded_exists x (fun w => z =ᴮ w ⊓ φ w) (B_ext_inf (B_ext_eq_right z) hφ)]

theorem B_congr_comprehend {φ : bSet 𝔹 → 𝔹} (hφ : B_ext φ) :
    B_congr (fun x : bSet 𝔹 => comprehend φ x) := by
  intro x y
  apply mem_ext
  · apply le_iInf
    intro z
    apply lattice.bv_imp_intro
    let Δ : 𝔹 := x =ᴮ y ⊓ z ∈ᴮ comprehend φ x
    change Δ ≤ z ∈ᴮ comprehend φ y
    have hCases :
        Δ ≤ ⨆ w : bSet 𝔹, w ∈ᴮ x ⊓ (z =ᴮ w ⊓ φ w) :=
      (mem_comprehend_iff₂ hφ).mp inf_le_right
    rw [mem_comprehend_iff₂ hφ]
    apply (le_inf le_rfl hCases).trans
    apply lattice.bv_cases_right
    intro w
    apply lattice.bv_use w
    apply le_inf
    · have hxy : Δ ⊓ (w ∈ᴮ x ⊓ (z =ᴮ w ⊓ φ w)) ≤ x =ᴮ y := by
        dsimp [Δ]
        exact inf_le_left.trans inf_le_left
      have hmem : Δ ⊓ (w ∈ᴮ x ⊓ (z =ᴮ w ⊓ φ w)) ≤ w ∈ᴮ x :=
        inf_le_right.trans inf_le_left
      exact subst_congr_mem_right' hxy hmem
    · exact inf_le_right.trans inf_le_right
  · apply le_iInf
    intro z
    apply lattice.bv_imp_intro
    let Δ : 𝔹 := x =ᴮ y ⊓ z ∈ᴮ comprehend φ y
    change Δ ≤ z ∈ᴮ comprehend φ x
    have hCases :
        Δ ≤ ⨆ w : bSet 𝔹, w ∈ᴮ y ⊓ (z =ᴮ w ⊓ φ w) :=
      (mem_comprehend_iff₂ hφ).mp inf_le_right
    rw [mem_comprehend_iff₂ hφ]
    apply (le_inf le_rfl hCases).trans
    apply lattice.bv_cases_right
    intro w
    apply lattice.bv_use w
    apply le_inf
    · have hxy : Δ ⊓ (w ∈ᴮ y ⊓ (z =ᴮ w ⊓ φ w)) ≤ x =ᴮ y := by
        dsimp [Δ]
        exact inf_le_left.trans inf_le_left
      have hmem : Δ ⊓ (w ∈ᴮ y ⊓ (z =ᴮ w ⊓ φ w)) ≤ w ∈ᴮ y :=
        inf_le_right.trans inf_le_left
      exact subst_congr_mem_right' (bv_symm hxy) hmem
    · exact inf_le_right.trans inf_le_right

theorem comprehend_subset {φ : bSet 𝔹 → 𝔹} {x : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ comprehend φ x ⊆ᴮ x :=
  subset.mk_subset

/-- Boolean-valued separation: every extensional predicate cuts out a subset of a name. -/
theorem bSet_axiom_of_comprehension (φ : bSet 𝔹 → 𝔹) (x : bSet 𝔹) (hφ : B_ext φ)
    {Γ : 𝔹} :
    Γ ≤ ⨆ y : bSet 𝔹,
      y ⊆ᴮ x ⊓ ⨅ z : bSet 𝔹,
        lattice.biimp (z ∈ᴮ y) (z ∈ᴮ x ⊓ φ z) := by
  apply lattice.bv_use (comprehend φ x)
  apply le_inf
  · exact comprehend_subset
  · apply le_iInf
    intro z
    apply le_inf
    · apply lattice.bv_imp_intro
      let Δ : 𝔹 := Γ ⊓ z ∈ᴮ comprehend φ x
      change Δ ≤ z ∈ᴮ x ⊓ φ z
      have hCases :
          Δ ≤ ⨆ i : x.type, x.bval i ⊓ (z =ᴮ x.func i ⊓ φ (x.func i)) :=
        (mem_comprehend_iff (φ := φ) (x := x) (z := z)).mp inf_le_right
      apply (le_inf le_rfl hCases).trans
      apply lattice.bv_cases_right
      intro i
      apply le_inf
      · have hVal :
            Δ ⊓ (x.bval i ⊓ (z =ᴮ x.func i ⊓ φ (x.func i))) ≤ x.bval i :=
          inf_le_right.trans inf_le_left
        have hMem : Δ ⊓ (x.bval i ⊓ (z =ᴮ x.func i ⊓ φ (x.func i))) ≤
            x.func i ∈ᴮ x :=
          mem.mk'' hVal
        have hEq : Δ ⊓ (x.bval i ⊓ (z =ᴮ x.func i ⊓ φ (x.func i))) ≤
            z =ᴮ x.func i :=
          inf_le_right.trans inf_le_right |>.trans inf_le_left
        exact subst_congr_mem_left' (bv_symm hEq) hMem
      · have hEq : Δ ⊓ (x.bval i ⊓ (z =ᴮ x.func i ⊓ φ (x.func i))) ≤
            x.func i =ᴮ z :=
          bv_symm (inf_le_right.trans inf_le_right |>.trans inf_le_left)
        have hφi : Δ ⊓ (x.bval i ⊓ (z =ᴮ x.func i ⊓ φ (x.func i))) ≤
            φ (x.func i) :=
          inf_le_right.trans inf_le_right |>.trans inf_le_right
        exact (le_inf hEq hφi).trans (hφ (x.func i) z)
    · apply lattice.bv_imp_intro
      let Δ : 𝔹 := Γ ⊓ (z ∈ᴮ x ⊓ φ z)
      change Δ ≤ z ∈ᴮ comprehend φ x
      rw [mem_comprehend_iff₂ hφ]
      apply lattice.bv_use z
      exact le_inf (inf_le_right.trans inf_le_left)
        (le_inf bv_refl (inf_le_right.trans inf_le_right))

theorem subset_of_pointwise_bounded {Γ : 𝔹} {x : bSet 𝔹} {p p' : x.type → 𝔹}
    (hbd : ∀ i : x.type, p i ≤ p' i) :
    Γ ≤ set_of_indicator p ⊆ᴮ set_of_indicator p' := by
  apply subset_intro
  intro i
  change Γ ⊓ (p i ⊓ x.bval i) ≤ x.func i ∈ᴮ subset.mk p'
  rw [mem_subset.mk_iff₂ (x := x) (χ := p') (z := x.func i)]
  apply lattice.bv_use i
  apply le_inf
  · exact inf_le_right.trans inf_le_right
  · apply le_inf
    · exact bv_refl
    · exact (inf_le_right.trans inf_le_left).trans (hbd i)

theorem set_of_indicator_eq_of_pointwise_eq {x : bSet 𝔹} {p p' : x.type → 𝔹}
    (hp : ∀ i : x.type, p i = p' i) {Γ : 𝔹} :
    Γ ≤ set_of_indicator p =ᴮ set_of_indicator p' := by
  apply subset_ext
  · exact subset_of_pointwise_bounded (fun i => (hp i).le)
  · exact subset_of_pointwise_bounded (fun i => (hp i).ge)

theorem subset_insert {x y : bSet 𝔹} {Γ : 𝔹} : Γ ≤ y ⊆ᴮ insert x y := by
  apply subset_intro
  intro i
  apply mem_insert_of_mem
  exact mem.mk'' (x := y) (a := i) inf_le_right

theorem insert_subset {x y z : bSet 𝔹} {Γ : 𝔹}
    (hx : Γ ≤ x ∈ᴮ z) (hy : Γ ≤ y ⊆ᴮ z) : Γ ≤ insert x y ⊆ᴮ z := by
  rw [insert_unfold]
  apply subset_intro
  intro i
  cases y with
  | mk α A B =>
      cases i with
      | none =>
          dsimp [bSet.insert, type, func, bval]
          rwa [inf_top_eq]
      | some a =>
          dsimp [bSet.insert, type, func, bval]
          exact subset_elim hy a

theorem insert_subset_iff {x y z : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ insert x y ⊆ᴮ z ↔ Γ ≤ x ∈ᴮ z ∧ Γ ≤ y ⊆ᴮ z := by
  cases y with
  | mk α A B =>
      constructor
      · intro h
        rw [insert_unfold] at h
        constructor
        · have hnone := subset_elim h (none : (bSet.insert x ⊤ (mk α A B)).type)
          dsimp [bSet.insert, type, func, bval] at hnone
          simpa [top_inf_eq] using hnone
        · apply subset_intro
          intro a
          have hsome := subset_elim h (some a : (bSet.insert x ⊤ (mk α A B)).type)
          dsimp [bSet.insert, type, func, bval] at hsome
          exact hsome
      · intro h
        exact insert_subset h.1 h.2

theorem insert_empty_subset_iff {x z : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ insert x (∅ : bSet 𝔹) ⊆ᴮ z ↔ Γ ≤ x ∈ᴮ z := by
  rw [insert_subset_iff]
  constructor
  · intro h
    exact h.1
  · intro h
    exact ⟨h, empty_subset⟩

/-- The canonical Boolean-valued check-name of a pre-set. -/
def check : pSet.{u} → bSet 𝔹
  | PSet.mk α A => mk α (fun i => check (A i)) (fun _ => ⊤)

/-- Check-name notation for pre-sets as Boolean-valued names. -/
scoped postfix:90 "̌" => check

@[simp] theorem check_type {x : pSet.{u}} : (check x : bSet 𝔹).type = x.Type := by
  cases x
  rfl

@[simp] theorem check_func {x : pSet.{u}} (i : (check x : bSet 𝔹).type) :
    (check x : bSet 𝔹).func i =
      check (x.Func (cast (check_type (𝔹 := 𝔹) (x := x)) i)) := by
  cases x
  rfl

@[simp] theorem check_bval {x : pSet.{u}} (i : (check x : bSet 𝔹).type) :
    (check x : bSet 𝔹).bval i = ⊤ := by
  cases x
  rfl

/-- Forget Boolean truth values from a Boolean-valued name, retaining its recursive domain. -/
def dom : bSet 𝔹 → pSet.{u}
  | mk α A _ => PSet.mk α (fun i => dom (A i))

@[simp] theorem dom_check : ∀ x : pSet.{u}, dom (check x : bSet 𝔹) = x
  | PSet.mk α A => by
      dsimp [check, dom]
      congr
      funext i
      exact dom_check (A i)

theorem dom_left_inv_check : Function.LeftInverse (dom (𝔹 := 𝔹)) check :=
  fun x => dom_check x

theorem check_injective : Function.Injective (check : pSet.{u} → bSet 𝔹) :=
  dom_left_inv_check.injective

@[simp] theorem check_bv_eq_of_equiv :
    ∀ {x y : pSet.{u}}, PSet.Equiv x y → (check x : bSet 𝔹) =ᴮ check y = ⊤
  | PSet.mk α A, PSet.mk β B, h => by
      apply le_antisymm le_top
      dsimp [check, bv_eq]
      apply le_inf
      · apply le_iInf
        intro a
        rw [top_le_iff, lattice.imp_eq_top_iff]
        rcases PSet.Equiv.exists_left h a with ⟨b, hb⟩
        have htop : ((check (A a) : bSet 𝔹) =ᴮ check (B b)) = ⊤ := by
          simpa using (check_bv_eq_of_equiv (x := A a) (y := B b) hb :
            ((check (A a) : bSet 𝔹) =ᴮ check (B b)) = ⊤)
        calc
          (⊤ : 𝔹) = ⊤ ⊓ ((check (A a) : bSet 𝔹) =ᴮ check (B b)) := by
            rw [htop, inf_top_eq]
          _ ≤ ⨆ b', ⊤ ⊓ ((check (A a) : bSet 𝔹) =ᴮ check (B b')) :=
            le_iSup (fun b' => ⊤ ⊓ ((check (A a) : bSet 𝔹) =ᴮ check (B b'))) b
      · apply le_iInf
        intro b
        rw [top_le_iff, lattice.imp_eq_top_iff]
        rcases PSet.Equiv.exists_right h b with ⟨a, ha⟩
        have htop : ((check (A a) : bSet 𝔹) =ᴮ check (B b)) = ⊤ := by
          simpa using (check_bv_eq_of_equiv (x := A a) (y := B b) ha :
            ((check (A a) : bSet 𝔹) =ᴮ check (B b)) = ⊤)
        calc
          (⊤ : 𝔹) = ⊤ ⊓ ((check (A a) : bSet 𝔹) =ᴮ check (B b)) := by
            rw [htop, inf_top_eq]
          _ ≤ ⨆ a', ⊤ ⊓ ((check (A a') : bSet 𝔹) =ᴮ check (B b)) :=
            le_iSup (fun a' => ⊤ ⊓ ((check (A a') : bSet 𝔹) =ᴮ check (B b))) a

theorem check_eq {x y : pSet.{u}} (h : PSet.Equiv x y) {Γ : 𝔹} :
    Γ ≤ (check x : bSet 𝔹) =ᴮ check y := by
  rw [check_bv_eq_of_equiv h]
  exact le_top

@[simp] theorem check_bv_eq_bot_of_not_equiv :
    ∀ {x y : pSet.{u}}, ¬ PSet.Equiv x y → (check x : bSet 𝔹) =ᴮ check y = ⊥
  | PSet.mk α A, PSet.mk β B, hneq => by
      apply le_antisymm ?_ bot_le
      dsimp [check, bv_eq]
      rcases pSet.not_equiv hneq with h | h
      · rcases h with ⟨a, ha⟩
        apply le_trans inf_le_left
        apply le_trans (iInf_le (fun a => lattice.imp (⊤ : 𝔹)
          (⨆ b, ⊤ ⊓ ((check (A a) : bSet 𝔹) =ᴮ check (B b)))) a)
        have hsup : (⨆ b, ⊤ ⊓ ((check (A a) : bSet 𝔹) =ᴮ check (B b))) = ⊥ := by
          apply le_antisymm
          · apply iSup_le
            intro b
            have hbot : ((check (A a) : bSet 𝔹) =ᴮ check (B b)) = ⊥ := by
              simpa using (check_bv_eq_bot_of_not_equiv (x := A a) (y := B b) (ha b) :
                ((check (A a) : bSet 𝔹) =ᴮ check (B b)) = ⊥)
            rw [hbot, inf_bot_eq]
          · exact bot_le
        rw [hsup]
        simp [lattice.imp]
      · rcases h with ⟨b, hb⟩
        apply le_trans inf_le_right
        apply le_trans (iInf_le (fun b => lattice.imp (⊤ : 𝔹)
          (⨆ a, ⊤ ⊓ ((check (A a) : bSet 𝔹) =ᴮ check (B b)))) b)
        have hsup : (⨆ a, ⊤ ⊓ ((check (A a) : bSet 𝔹) =ᴮ check (B b))) = ⊥ := by
          apply le_antisymm
          · apply iSup_le
            intro a
            have hbot : ((check (A a) : bSet 𝔹) =ᴮ check (B b)) = ⊥ := by
              simpa using (check_bv_eq_bot_of_not_equiv (x := A a) (y := B b) (hb a) :
                ((check (A a) : bSet 𝔹) =ᴮ check (B b)) = ⊥)
            rw [hbot, inf_bot_eq]
          · exact bot_le
        rw [hsup]
        simp [lattice.imp]

theorem equiv_of_check_bv_eq_top [Nontrivial 𝔹] {x y : pSet.{u}}
    (h : (check x : bSet 𝔹) =ᴮ check y = ⊤) : PSet.Equiv x y := by
  by_contra hneq
  have hbot : (check x : bSet 𝔹) =ᴮ check y = ⊥ :=
    check_bv_eq_bot_of_not_equiv hneq
  exact top_ne_bot (h.symm.trans hbot)

theorem check_bv_eq_top_iff [Nontrivial 𝔹] {x y : pSet.{u}} :
    (check x : bSet 𝔹) =ᴮ check y = ⊤ ↔ PSet.Equiv x y :=
  ⟨equiv_of_check_bv_eq_top, check_bv_eq_of_equiv⟩

theorem check_bv_eq_congr_left_of_equiv {x y z : pSet.{u}} (hxy : PSet.Equiv x y) :
    (check x : bSet 𝔹) =ᴮ check z = (check y : bSet 𝔹) =ᴮ check z := by
  classical
  by_cases hxz : PSet.Equiv x z
  · have hyz : PSet.Equiv y z := hxy.symm.trans hxz
    rw [check_bv_eq_of_equiv hxz, check_bv_eq_of_equiv hyz]
  · have hyz : ¬ PSet.Equiv y z := by
      intro hyz
      exact hxz (hxy.trans hyz)
    rw [check_bv_eq_bot_of_not_equiv hxz, check_bv_eq_bot_of_not_equiv hyz]

theorem check_bv_eq_congr_right_of_equiv {x y z : pSet.{u}} (hyz : PSet.Equiv y z) :
    (check x : bSet 𝔹) =ᴮ check y = (check x : bSet 𝔹) =ᴮ check z := by
  classical
  by_cases hxy : PSet.Equiv x y
  · have hxz : PSet.Equiv x z := hxy.trans hyz
    rw [check_bv_eq_of_equiv hxy, check_bv_eq_of_equiv hxz]
  · have hxz : ¬ PSet.Equiv x z := by
      intro hxz
      exact hxy (hxz.trans hyz.symm)
    rw [check_bv_eq_bot_of_not_equiv hxy, check_bv_eq_bot_of_not_equiv hxz]

theorem check_bv_eq_congr_of_equiv {x₁ x₂ y₁ y₂ : pSet.{u}}
    (hx : PSet.Equiv x₁ x₂) (hy : PSet.Equiv y₁ y₂) :
    (check x₁ : bSet 𝔹) =ᴮ check y₁ = (check x₂ : bSet 𝔹) =ᴮ check y₂ := by
  rw [check_bv_eq_congr_left_of_equiv hx, check_bv_eq_congr_right_of_equiv hy]

theorem check_mem {x y : pSet.{u}} (h : x ∈ y) {Γ : 𝔹} :
    Γ ≤ (check x : bSet 𝔹) ∈ᴮ check y := by
  cases y with
  | mk α A =>
      rcases pSet.mem_unfold.mp h with ⟨i, hi⟩
      dsimp [check, mem]
      apply lattice.bv_use i
      exact le_inf le_top (check_eq hi)

@[simp] theorem check_bv_mem_bot_of_not_mem {x y : pSet.{u}} (h : x ∉ y) :
    (check x : bSet 𝔹) ∈ᴮ check y = ⊥ := by
  cases y with
  | mk α A =>
      apply le_antisymm ?_ bot_le
      dsimp [check, mem]
      apply iSup_le
      intro i
      have hbot : ((check x : bSet 𝔹) =ᴮ check (A i)) = ⊥ := by
        apply check_bv_eq_bot_of_not_equiv
        intro heq
        exact h (pSet.mem_unfold.mpr ⟨i, heq⟩)
      rw [hbot, inf_bot_eq]

theorem check_not_mem {x y : pSet.{u}} (h : x ∉ y) {Γ : 𝔹}
    (hmem : Γ ≤ (check x : bSet 𝔹) ∈ᴮ check y) : Γ ≤ ⊥ := by
  rw [check_bv_mem_bot_of_not_mem h] at hmem
  exact hmem

theorem mem_of_check_bv_mem_top [Nontrivial 𝔹] {x y : pSet.{u}}
    (h : (check x : bSet 𝔹) ∈ᴮ check y = ⊤) : x ∈ y := by
  by_contra hmem
  have hbot : (check x : bSet 𝔹) ∈ᴮ check y = ⊥ :=
    check_bv_mem_bot_of_not_mem hmem
  exact top_ne_bot (h.symm.trans hbot)

theorem check_bv_mem_top_iff [Nontrivial 𝔹] {x y : pSet.{u}} :
    (check x : bSet 𝔹) ∈ᴮ check y = ⊤ ↔ x ∈ y := by
  constructor
  · exact mem_of_check_bv_mem_top
  · intro h
    apply le_antisymm le_top
    exact check_mem h

theorem check_bv_mem_top_of_mem {x y : pSet.{u}} (h : x ∈ y) :
    (check x : bSet 𝔹) ∈ᴮ check y = ⊤ := by
  apply le_antisymm le_top
  exact check_mem h

theorem check_bv_mem_congr_left_of_equiv {x y z : pSet.{u}} (hxy : PSet.Equiv x y) :
    (check x : bSet 𝔹) ∈ᴮ check z = (check y : bSet 𝔹) ∈ᴮ check z := by
  classical
  by_cases hx : x ∈ z
  · have hy : y ∈ z := by
      rcases pSet.mem_unfold.mp hx with ⟨i, hi⟩
      exact pSet.mem_unfold.mpr ⟨i, hxy.symm.trans hi⟩
    rw [check_bv_mem_top_of_mem hx, check_bv_mem_top_of_mem hy]
  · have hy : y ∉ z := by
      intro hy
      apply hx
      rcases pSet.mem_unfold.mp hy with ⟨i, hi⟩
      exact pSet.mem_unfold.mpr ⟨i, hxy.trans hi⟩
    rw [check_bv_mem_bot_of_not_mem hx, check_bv_mem_bot_of_not_mem hy]

theorem check_bv_mem_congr_right_of_equiv {x y z : pSet.{u}} (hyz : PSet.Equiv y z) :
    (check x : bSet 𝔹) ∈ᴮ check y = (check x : bSet 𝔹) ∈ᴮ check z := by
  classical
  by_cases hy : x ∈ y
  · have hz : x ∈ z := ((pSet.ext_iff.mp hyz) x).1 hy
    rw [check_bv_mem_top_of_mem hy, check_bv_mem_top_of_mem hz]
  · have hz : x ∉ z := by
      intro hz
      exact hy (((pSet.ext_iff.mp hyz) x).2 hz)
    rw [check_bv_mem_bot_of_not_mem hy, check_bv_mem_bot_of_not_mem hz]

theorem check_bv_mem_congr_of_equiv {x₁ x₂ y₁ y₂ : pSet.{u}}
    (hx : PSet.Equiv x₁ x₂) (hy : PSet.Equiv y₁ y₂) :
    (check x₁ : bSet 𝔹) ∈ᴮ check y₁ = (check x₂ : bSet 𝔹) ∈ᴮ check y₂ := by
  rw [check_bv_mem_congr_left_of_equiv hx, check_bv_mem_congr_right_of_equiv hy]

theorem check_subset {x y : pSet.{u}} (h : x ⊆ y) {Γ : 𝔹} :
    Γ ≤ (check x : bSet 𝔹) ⊆ᴮ check y := by
  cases x with
  | mk α A =>
      apply subset_intro
      intro i
      dsimp [check, bval, func]
      rw [inf_top_eq]
      apply check_mem
      exact pSet.all_mem_of_subset h (A i) pSet.mem_mk'

theorem check_bv_subset_top_of_subset {x y : pSet.{u}} (h : x ⊆ y) :
    (check x : bSet 𝔹) ⊆ᴮ check y = ⊤ := by
  apply le_antisymm le_top
  exact check_subset h

@[simp] theorem check_bv_subset_bot_of_not_subset {x y : pSet.{u}} (h : ¬ x ⊆ y) :
    (check x : bSet 𝔹) ⊆ᴮ check y = ⊥ := by
  cases x with
  | mk α A =>
      apply le_antisymm ?_ bot_le
      dsimp [check, subset]
      have hmem : ∃ i : α, A i ∉ y := by
        by_contra hall
        push Not at hall
        apply h
        apply pSet.subset_of_all_mem
        intro z hz
        rcases pSet.mem_unfold.mp hz with ⟨i, hzi⟩
        rcases pSet.mem_unfold.mp (hall i) with ⟨j, hij⟩
        exact pSet.mem_unfold.mpr ⟨j, hzi.trans hij⟩
      rcases hmem with ⟨i, hi⟩
      apply le_trans (iInf_le (fun i => lattice.imp (⊤ : 𝔹)
        ((check (A i) : bSet 𝔹) ∈ᴮ check y)) i)
      have hbot : ((check (A i) : bSet 𝔹) ∈ᴮ check y) = ⊥ :=
        check_bv_mem_bot_of_not_mem hi
      rw [hbot]
      simp [lattice.imp]

theorem subset_of_check_bv_subset_top [Nontrivial 𝔹] {x y : pSet.{u}}
    (h : (check x : bSet 𝔹) ⊆ᴮ check y = ⊤) : x ⊆ y := by
  by_contra hsub
  have hbot : (check x : bSet 𝔹) ⊆ᴮ check y = ⊥ :=
    check_bv_subset_bot_of_not_subset hsub
  exact top_ne_bot (h.symm.trans hbot)

theorem check_bv_subset_top_iff [Nontrivial 𝔹] {x y : pSet.{u}} :
    (check x : bSet 𝔹) ⊆ᴮ check y = ⊤ ↔ x ⊆ y :=
  ⟨subset_of_check_bv_subset_top, check_bv_subset_top_of_subset⟩

theorem check_bv_subset_congr_left_of_equiv {x y z : pSet.{u}} (hxy : PSet.Equiv x y) :
    (check x : bSet 𝔹) ⊆ᴮ check z = (check y : bSet 𝔹) ⊆ᴮ check z := by
  classical
  by_cases hx : x ⊆ z
  · have hy : y ⊆ z := by
      apply pSet.subset_of_all_mem
      intro w hw
      exact pSet.all_mem_of_subset hx w (((pSet.ext_iff.mp hxy) w).2 hw)
    rw [check_bv_subset_top_of_subset hx, check_bv_subset_top_of_subset hy]
  · have hy : ¬ y ⊆ z := by
      intro hy
      apply hx
      apply pSet.subset_of_all_mem
      intro w hw
      exact pSet.all_mem_of_subset hy w (((pSet.ext_iff.mp hxy) w).1 hw)
    rw [check_bv_subset_bot_of_not_subset hx, check_bv_subset_bot_of_not_subset hy]

theorem check_bv_subset_congr_right_of_equiv {x y z : pSet.{u}} (hyz : PSet.Equiv y z) :
    (check x : bSet 𝔹) ⊆ᴮ check y = (check x : bSet 𝔹) ⊆ᴮ check z := by
  classical
  by_cases hy : x ⊆ y
  · have hz : x ⊆ z := by
      apply pSet.subset_of_all_mem
      intro w hw
      exact ((pSet.ext_iff.mp hyz) w).1 (pSet.all_mem_of_subset hy w hw)
    rw [check_bv_subset_top_of_subset hy, check_bv_subset_top_of_subset hz]
  · have hz : ¬ x ⊆ z := by
      intro hz
      apply hy
      apply pSet.subset_of_all_mem
      intro w hw
      exact ((pSet.ext_iff.mp hyz) w).2 (pSet.all_mem_of_subset hz w hw)
    rw [check_bv_subset_bot_of_not_subset hy, check_bv_subset_bot_of_not_subset hz]

theorem check_bv_subset_congr_of_equiv {x₁ x₂ y₁ y₂ : pSet.{u}}
    (hx : PSet.Equiv x₁ x₂) (hy : PSet.Equiv y₁ y₂) :
    (check x₁ : bSet 𝔹) ⊆ᴮ check y₁ = (check x₂ : bSet 𝔹) ⊆ᴮ check y₂ := by
  rw [check_bv_subset_congr_left_of_equiv hx, check_bv_subset_congr_right_of_equiv hy]

/-- Boolean-valued union of all members indexed by a Boolean-valued set. -/
def bv_union (x : bSet 𝔹) : bSet 𝔹 :=
  mk (Σ i : x.type, (x.func i).type)
    (fun p => (x.func p.1).func p.2)
    (fun p => x.bval p.1 ⊓ (x.func p.1).bval p.2)

theorem mem_bv_union_unfold {x z : bSet 𝔹} :
    z ∈ᴮ bv_union x =
      ⨆ p : Σ i : x.type, (x.func i).type,
        (x.bval p.1 ⊓ (x.func p.1).bval p.2) ⊓
          z =ᴮ (x.func p.1).func p.2 := by
  rfl

theorem mem_bv_union_iff {x z : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ z ∈ᴮ bv_union x ↔ Γ ≤ ⨆ y : bSet 𝔹, y ∈ᴮ x ⊓ z ∈ᴮ y := by
  constructor
  · intro hz
    rw [mem_bv_union_unfold] at hz
    apply (le_inf le_rfl hz).trans
    apply lattice.bv_cases_right
    intro p
    rcases p with ⟨i, j⟩
    apply lattice.bv_use (x.func i)
    apply le_inf
    · apply mem.mk''
      exact (inf_le_right.trans inf_le_left).trans inf_le_left
    · have hVal :
          Γ ⊓ ((x.bval i ⊓ (x.func i).bval j) ⊓ z =ᴮ (x.func i).func j) ≤
            (x.func i).bval j :=
        (inf_le_right.trans inf_le_left).trans inf_le_right
      have hMem :
          Γ ⊓ ((x.bval i ⊓ (x.func i).bval j) ⊓ z =ᴮ (x.func i).func j) ≤
            (x.func i).func j ∈ᴮ x.func i :=
        mem.mk'' hVal
      have hEq :
          Γ ⊓ ((x.bval i ⊓ (x.func i).bval j) ⊓ z =ᴮ (x.func i).func j) ≤
            z =ᴮ (x.func i).func j :=
        inf_le_right.trans inf_le_right
      exact subst_congr_mem_left' (bv_symm hEq) hMem
  · intro hz
    apply (le_inf le_rfl hz).trans
    apply lattice.bv_cases_right
    intro y
    let Δ : 𝔹 := Γ ⊓ (y ∈ᴮ x ⊓ z ∈ᴮ y)
    change Δ ≤ z ∈ᴮ bv_union x
    have hMemY : Δ ≤ y ∈ᴮ x := by
      dsimp [Δ]
      exact inf_le_right.trans inf_le_left
    rw [mem_unfold] at hMemY
    apply (le_inf le_rfl hMemY).trans
    apply lattice.bv_cases_right
    intro i
    let Δi : 𝔹 := Δ ⊓ (x.bval i ⊓ y =ᴮ x.func i)
    change Δi ≤ z ∈ᴮ bv_union x
    have hEqY : Δi ≤ y =ᴮ x.func i := by
      dsimp [Δi]
      exact inf_le_right.trans inf_le_right
    have hMemZY : Δi ≤ z ∈ᴮ y := by
      dsimp [Δi, Δ]
      exact inf_le_left.trans (inf_le_right.trans inf_le_right)
    have hMemZX : Δi ≤ z ∈ᴮ x.func i :=
      subst_congr_mem_right' hEqY hMemZY
    rw [mem_unfold] at hMemZX
    apply (le_inf le_rfl hMemZX).trans
    apply lattice.bv_cases_right
    intro j
    apply lattice.bv_use ⟨i, j⟩
    apply le_inf
    · apply le_inf
      · dsimp [Δi]
        exact (inf_le_left.trans inf_le_right).trans inf_le_left
      · exact inf_le_right.trans inf_le_left
    · exact inf_le_right.trans inf_le_right

/-- Upstream-compatible form of the Boolean-valued union specification. -/
theorem bv_union_spec' (x : bSet 𝔹) (Γ : 𝔹) :
    ∀ z : bSet 𝔹,
      (Γ ≤ z ∈ᴮ bv_union x ↔ Γ ≤ ⨆ y : bSet 𝔹, y ∈ᴮ x ⊓ z ∈ᴮ y) :=
  fun _ => mem_bv_union_iff

theorem bv_union_congr : B_congr (fun x : bSet 𝔹 => bv_union x) := by
  intro x y
  apply mem_ext
  · apply le_iInf
    intro z
    apply lattice.bv_imp_intro
    let Δ : 𝔹 := x =ᴮ y ⊓ z ∈ᴮ bv_union x
    change Δ ≤ z ∈ᴮ bv_union y
    have hCases :
        Δ ≤ ⨆ w : bSet 𝔹, w ∈ᴮ x ⊓ z ∈ᴮ w :=
      (mem_bv_union_iff (x := x) (z := z)).mp inf_le_right
    rw [mem_bv_union_iff (x := y) (z := z)]
    apply (le_inf le_rfl hCases).trans
    apply lattice.bv_cases_right
    intro w
    apply lattice.bv_use w
    apply le_inf
    · have hxy : Δ ⊓ (w ∈ᴮ x ⊓ z ∈ᴮ w) ≤ x =ᴮ y := by
        dsimp [Δ]
        exact inf_le_left.trans inf_le_left
      have hmem : Δ ⊓ (w ∈ᴮ x ⊓ z ∈ᴮ w) ≤ w ∈ᴮ x :=
        inf_le_right.trans inf_le_left
      exact subst_congr_mem_right' hxy hmem
    · exact inf_le_right.trans inf_le_right
  · apply le_iInf
    intro z
    apply lattice.bv_imp_intro
    let Δ : 𝔹 := x =ᴮ y ⊓ z ∈ᴮ bv_union y
    change Δ ≤ z ∈ᴮ bv_union x
    have hCases :
        Δ ≤ ⨆ w : bSet 𝔹, w ∈ᴮ y ⊓ z ∈ᴮ w :=
      (mem_bv_union_iff (x := y) (z := z)).mp inf_le_right
    rw [mem_bv_union_iff (x := x) (z := z)]
    apply (le_inf le_rfl hCases).trans
    apply lattice.bv_cases_right
    intro w
    apply lattice.bv_use w
    apply le_inf
    · have hxy : Δ ⊓ (w ∈ᴮ y ⊓ z ∈ᴮ w) ≤ x =ᴮ y := by
        dsimp [Δ]
        exact inf_le_left.trans inf_le_left
      have hmem : Δ ⊓ (w ∈ᴮ y ⊓ z ∈ᴮ w) ≤ w ∈ᴮ y :=
        inf_le_right.trans inf_le_left
      exact subst_congr_mem_right' (bv_symm hxy) hmem
    · exact inf_le_right.trans inf_le_right

theorem B_congr_bv_union : B_congr (fun x : bSet 𝔹 => bv_union x) :=
  bv_union_congr

theorem bv_union_spec_indexed {x : bSet 𝔹} {Γ : 𝔹} (i : x.type) :
    Γ ⊓ x.bval i ≤ x.func i ⊆ᴮ bv_union x := by
  apply subset_intro
  intro j
  apply mem.mk'' (x := bv_union x) (a := ⟨i, j⟩)
  dsimp [bv_union, type, bval]
  exact le_inf (inf_le_left.trans inf_le_right) inf_le_right

theorem bv_union_spec'' (x : bSet 𝔹) :
    (⊤ : 𝔹) ≤ ⨅ w : bSet 𝔹, lattice.imp (w ∈ᴮ x) (w ⊆ᴮ bv_union x) := by
  rw [← bounded_forall x (fun w => w ⊆ᴮ bv_union x) (B_ext_subset_left (bv_union x))]
  apply le_iInf
  intro i
  apply lattice.bv_imp_intro
  exact bv_union_spec_indexed (Γ := ⊤) i

theorem bv_union_spec (x : bSet 𝔹) :
    (⊤ : 𝔹) ≤ ⨅ i : x.type, lattice.imp (x.bval i) (x.func i ⊆ᴮ bv_union x) := by
  apply le_iInf
  intro i
  apply lattice.bv_imp_intro
  exact bv_union_spec_indexed (Γ := ⊤) i

theorem bSet_axiom_of_union (x : bSet 𝔹) {Γ : 𝔹} :
    Γ ≤ ⨆ y : bSet 𝔹,
      ⨅ z : bSet 𝔹,
        lattice.biimp (z ∈ᴮ y)
          (⨆ w : bSet 𝔹, w ∈ᴮ x ⊓ z ∈ᴮ w) := by
  apply lattice.bv_use (bv_union x)
  apply le_iInf
  intro z
  apply le_inf
  · apply lattice.bv_imp_intro
    exact (mem_bv_union_iff (x := x) (z := z)).mp inf_le_right
  · apply lattice.bv_imp_intro
    exact (mem_bv_union_iff (x := x) (z := z)).mpr inf_le_right

theorem bSet_axiom_of_union_all :
    (⊤ : 𝔹) ≤ ⨅ x : bSet 𝔹,
      ⨆ y : bSet 𝔹,
        ⨅ z : bSet 𝔹,
          lattice.biimp (z ∈ᴮ y)
            (⨆ w : bSet 𝔹, w ∈ᴮ x ⊓ z ∈ᴮ w) := by
  apply le_iInf
  intro x
  exact bSet_axiom_of_union x

theorem bSet_axiom_of_union_all_eq :
    (⨅ x : bSet 𝔹,
      ⨆ y : bSet 𝔹,
        ⨅ z : bSet 𝔹,
          lattice.biimp (z ∈ᴮ y)
            (⨆ w : bSet 𝔹, w ∈ᴮ x ⊓ z ∈ᴮ w)) = ⊤ := by
  apply le_antisymm le_top
  exact bSet_axiom_of_union_all

/-- Boolean-valued powerset: all bounded Boolean-valued subnames of `u`. -/
def bv_powerset (u : bSet 𝔹) : bSet 𝔹 :=
  mk (u.type → 𝔹) (fun χ => subset.mk (x := u) χ) (fun _ => ⊤)

theorem mem_bv_powerset_iff_eq_subset_mk {u x : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ x ∈ᴮ bv_powerset u ↔
      Γ ≤ ⨆ χ : u.type → 𝔹, x =ᴮ subset.mk (x := u) χ := by
  rw [mem_unfold]
  change
    Γ ≤ (⨆ χ : u.type → 𝔹, (⊤ : 𝔹) ⊓ x =ᴮ subset.mk (x := u) χ) ↔
      Γ ≤ ⨆ χ : u.type → 𝔹, x =ᴮ subset.mk (x := u) χ
  simp

theorem subset_eq_subset_mk_of_subset {u x : bSet 𝔹} {Γ : 𝔹}
    (hxu : Γ ≤ x ⊆ᴮ u) :
    Γ ≤ x =ᴮ subset.mk (x := u) (fun i : u.type => u.func i ∈ᴮ x) := by
  apply subset_ext
  · apply subset_intro
    intro j
    let Δ : 𝔹 := Γ ⊓ x.bval j
    change Δ ≤ x.func j ∈ᴮ subset.mk (x := u) (fun i : u.type => u.func i ∈ᴮ x)
    have hxjU : Δ ≤ x.func j ∈ᴮ u := by
      dsimp [Δ]
      exact subset_elim hxu j
    rw [mem_unfold] at hxjU
    apply (le_inf le_rfl hxjU).trans
    apply lattice.bv_cases_right
    intro i
    let Δi : 𝔹 := Δ ⊓ (u.bval i ⊓ x.func j =ᴮ u.func i)
    change Δi ≤ x.func j ∈ᴮ subset.mk (x := u) (fun i : u.type => u.func i ∈ᴮ x)
    have huiMem :
        Δi ≤ u.func i ∈ᴮ subset.mk (x := u) (fun i : u.type => u.func i ∈ᴮ x) := by
      change
        Δi ≤
          (subset.mk (x := u) (fun i : u.type => u.func i ∈ᴮ x)).func i ∈ᴮ
            subset.mk (x := u) (fun i : u.type => u.func i ∈ᴮ x)
      apply mem.mk''
      dsimp [subset.mk, Δi, Δ]
      apply le_inf
      · have hxMem : Δi ≤ x.func j ∈ᴮ x := by
          apply mem.mk''
          exact (inf_le_left.trans inf_le_right)
        have hEq : Δi ≤ x.func j =ᴮ u.func i := by
          exact inf_le_right.trans inf_le_right
        exact subst_congr_mem_left' hEq hxMem
      · exact inf_le_right.trans inf_le_left
    have hEq : Δi ≤ x.func j =ᴮ u.func i := by
      exact inf_le_right.trans inf_le_right
    exact subst_congr_mem_left' (bv_symm hEq) huiMem
  · apply subset_intro
    intro i
    let Δ : 𝔹 := Γ ⊓ (subset.mk (x := u) (fun i : u.type => u.func i ∈ᴮ x)).bval i
    change Δ ≤ (subset.mk (x := u) (fun i : u.type => u.func i ∈ᴮ x)).func i ∈ᴮ x
    dsimp [subset.mk, Δ]
    exact inf_le_right.trans inf_le_left

theorem bv_powerset_spec {u x : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ x ⊆ᴮ u ↔ Γ ≤ x ∈ᴮ bv_powerset u := by
  constructor
  · intro hxu
    rw [mem_bv_powerset_iff_eq_subset_mk]
    apply lattice.bv_use (fun i : u.type => u.func i ∈ᴮ x)
    exact subset_eq_subset_mk_of_subset hxu
  · intro hxPow
    rw [mem_bv_powerset_iff_eq_subset_mk] at hxPow
    apply (le_inf le_rfl hxPow).trans
    apply lattice.bv_cases_right
    intro χ
    let Δ : 𝔹 := Γ ⊓ x =ᴮ subset.mk (x := u) χ
    change Δ ≤ x ⊆ᴮ u
    have hEq : Δ ≤ x =ᴮ subset.mk (x := u) χ := by
      dsimp [Δ]
      exact inf_le_right
    exact subst_congr_subset_left' (bv_symm hEq) subset.mk_subset

theorem mem_powerset_iff {u x : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ x ∈ᴮ bv_powerset u ↔ Γ ≤ x ⊆ᴮ u :=
  bv_powerset_spec.symm

theorem bv_powerset_congr {Γ : 𝔹} {x y : bSet 𝔹}
    (hxy : Γ ≤ x =ᴮ y) : Γ ≤ bv_powerset x =ᴮ bv_powerset y := by
  apply mem_ext
  · apply le_iInf
    intro z
    apply lattice.bv_imp_intro
    let Δ : 𝔹 := Γ ⊓ z ∈ᴮ bv_powerset x
    change Δ ≤ z ∈ᴮ bv_powerset y
    rw [← bv_powerset_spec]
    have hzSubX : Δ ≤ z ⊆ᴮ x := by
      rw [bv_powerset_spec]
      exact inf_le_right
    have hxyΔ : Δ ≤ x =ᴮ y := by
      dsimp [Δ]
      exact inf_le_left.trans hxy
    exact subst_congr_subset_right' hxyΔ hzSubX
  · apply le_iInf
    intro z
    apply lattice.bv_imp_intro
    let Δ : 𝔹 := Γ ⊓ z ∈ᴮ bv_powerset y
    change Δ ≤ z ∈ᴮ bv_powerset x
    rw [← bv_powerset_spec]
    have hzSubY : Δ ≤ z ⊆ᴮ y := by
      rw [bv_powerset_spec]
      exact inf_le_right
    have hxyΔ : Δ ≤ x =ᴮ y := by
      dsimp [Δ]
      exact inf_le_left.trans hxy
    exact subst_congr_subset_right' (bv_symm hxyΔ) hzSubY

theorem B_congr_bv_powerset : B_congr (fun x : bSet 𝔹 => bv_powerset x) := by
  intro x y
  exact bv_powerset_congr (Γ := x =ᴮ y) (x := x) (y := y) le_rfl

theorem bSet_axiom_of_powerset' (u : bSet 𝔹) {Γ : 𝔹} :
    Γ ≤ ⨅ x : bSet 𝔹, lattice.biimp (x ∈ᴮ bv_powerset u) (x ⊆ᴮ u) := by
  apply le_iInf
  intro x
  apply le_inf
  · apply lattice.bv_imp_intro
    exact (mem_powerset_iff (u := u) (x := x)).mp inf_le_right
  · apply lattice.bv_imp_intro
    exact (mem_powerset_iff (u := u) (x := x)).mpr inf_le_right

theorem bSet_axiom_of_powerset :
    (⊤ : 𝔹) ≤ ⨅ u : bSet 𝔹,
      ⨆ v : bSet 𝔹,
        ⨅ x : bSet 𝔹, lattice.biimp (x ∈ᴮ v) (x ⊆ᴮ u) := by
  apply le_iInf
  intro u
  apply lattice.bv_use (bv_powerset u)
  exact bSet_axiom_of_powerset' u

@[simp] theorem check_empty_eq_empty :
    (check (∅ : pSet.{u}) : bSet 𝔹) =ᴮ (∅ : bSet 𝔹) = ⊤ := by
  apply le_antisymm le_top
  dsimp [check, empty, bv_eq]
  apply le_inf <;>
    apply le_iInf <;>
    intro i <;>
    cases i

theorem check_empty {Γ : 𝔹} :
    Γ ≤ (check (∅ : pSet.{u}) : bSet 𝔹) =ᴮ (∅ : bSet 𝔹) := by
  rw [check_empty_eq_empty]
  exact le_top

/-- The check-name of the ordinary pre-set omega. -/
def omega : bSet 𝔹 :=
  check (PSet.omega : pSet.{u})

/-- The `n`th von Neumann natural number as a Boolean-valued name. -/
def ofNat (n : Nat) : bSet 𝔹 :=
  check (PSet.ofNat.{u} n)

@[simp] theorem check_omega_type : (omega : bSet 𝔹).type = ULift Nat := rfl

@[simp] theorem omega_type : (omega : bSet 𝔹).type = ULift Nat := rfl

@[simp] theorem omega_func (k : (omega : bSet 𝔹).type) :
    (omega : bSet 𝔹).func k = ofNat k.down := rfl

@[simp] theorem omega_bval (k : (omega : bSet 𝔹).type) :
    (omega : bSet 𝔹).bval k = ⊤ := rfl

theorem ofNat_zero_eq_empty {Γ : 𝔹} :
    Γ ≤ ofNat 0 =ᴮ (∅ : bSet 𝔹) := by
  rw [ofNat, PSet.ofNat, check_empty_eq_empty]
  exact le_top

theorem omega_definite {n : Nat} {Γ : 𝔹} : Γ ≤ ofNat n ∈ᴮ omega := by
  apply check_mem
  exact pSet.mem_unfold.mpr ⟨ULift.up n, PSet.Equiv.rfl⟩

theorem ofNat_mem_omega {n : Nat} {Γ : 𝔹} : Γ ≤ ofNat n ∈ᴮ omega :=
  omega_definite

instance instOfNat (n : Nat) : OfNat (bSet 𝔹) n where
  ofNat := ofNat n

/-- Boolean-valued infinity says a name contains empty and is closed under successors. -/
def axiom_of_infinity_spec (u : bSet 𝔹) : 𝔹 :=
  ((∅ : bSet 𝔹) ∈ᴮ u) ⊓
    (⨅ i : u.type, ⨆ j : u.type, u.func i ∈ᴮ u.func j)

/-- The Boolean truth value that `u` contains the empty Boolean-valued name. -/
def contains_empty (u : bSet 𝔹) : 𝔹 :=
  (∅ : bSet 𝔹) ∈ᴮ u

/-- The Boolean truth value that every indexed member of `u` has a successor member in `u`. -/
def contains_succ (u : bSet 𝔹) : 𝔹 :=
  ⨅ i : u.type, ⨆ j : u.type, u.func i ∈ᴮ u.func j

theorem infinity_of_empty_succ {u : bSet 𝔹} {Γ : 𝔹}
    (hEmpty : Γ ≤ contains_empty u) (hSucc : Γ ≤ contains_succ u) :
    Γ ≤ axiom_of_infinity_spec u :=
  le_inf hEmpty hSucc

theorem contains_empty_check_omega : (⊤ : 𝔹) ≤ contains_empty (omega : bSet 𝔹) := by
  exact subst_congr_mem_left' ofNat_zero_eq_empty omega_definite

theorem contains_succ_check_omega : (⊤ : 𝔹) ≤ contains_succ (omega : bSet 𝔹) := by
  apply le_iInf
  intro n
  apply lattice.bv_use (ULift.up (n.down + 1))
  simpa [omega, ofNat] using
    (check_mem (pSet.of_nat_mem_of_lt (k₁ := n.down) (k₂ := n.down + 1)
      (Nat.lt_succ_self n.down)) :
      (⊤ : 𝔹) ≤
        (check (PSet.ofNat.{u} n.down) : bSet 𝔹) ∈ᴮ
          check (PSet.ofNat.{u} (n.down + 1)))

theorem bSet_axiom_of_infinity :
    (⨆ u : bSet 𝔹, axiom_of_infinity_spec u) = ⊤ := by
  apply le_antisymm le_top
  apply lattice.bv_use (omega : bSet 𝔹)
  exact infinity_of_empty_succ contains_empty_check_omega contains_succ_check_omega

theorem bSet_axiom_of_infinity' :
    (⊤ : 𝔹) ≤
      ((∅ : bSet 𝔹) ∈ᴮ omega) ⊓
        (⨅ x : bSet 𝔹,
          lattice.imp (x ∈ᴮ omega)
            (⨆ y : bSet 𝔹, y ∈ᴮ omega ⊓ x ∈ᴮ y)) := by
  apply le_inf
  · exact contains_empty_check_omega
  · have hExt :
        B_ext (fun x : bSet 𝔹 =>
          ⨆ y : bSet 𝔹, y ∈ᴮ omega ⊓ x ∈ᴮ y) := by
      apply B_ext_iSup
      intro y
      exact B_ext_inf (B_ext_const _) (B_ext_mem_left y)
    rw [← bounded_forall (omega : bSet 𝔹)
      (fun x : bSet 𝔹 => ⨆ y : bSet 𝔹, y ∈ᴮ omega ⊓ x ∈ᴮ y) hExt]
    apply le_iInf
    intro n
    apply lattice.bv_imp_intro
    apply lattice.bv_use (ofNat (n.down + 1))
    apply le_inf
    · exact ofNat_mem_omega
    · simpa [omega, ofNat] using
        (check_mem (pSet.of_nat_mem_of_lt (k₁ := n.down) (k₂ := n.down + 1)
          (Nat.lt_succ_self n.down)) :
          (⊤ : 𝔹) ≤
            (check (PSet.ofNat.{u} n.down) : bSet 𝔹) ∈ᴮ
              check (PSet.ofNat.{u} (n.down + 1)))

end bSet

end Flypitch
