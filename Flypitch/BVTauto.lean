import Mathlib.Order.CompleteBooleanAlgebra
import Mathlib.Tactic

universe u

namespace Flypitch

/-!
`Flypitch.BVTauto` ports the small Boolean-valued tautology helper file from upstream.

The original Lean 3 file mixed one lattice lemma with a custom interactive tactic
implementation. For the Lean 4 port we keep the same compatibility surface, but use a
smaller Lean 4-native tactic shim for now:

- `lattice.imp` reintroduces the Boolean implication connective used throughout the forcing
  development;
- `lattice.context_or_elim'` supplies the context-splitting lemma that the old tactic used;
- `tidy_context` and `bv_tauto` provide a lightweight first-pass tactic interface that is
  sufficient for the current ported surface and can be strengthened as later forcing files
  demand more automation.
-/

namespace lattice

/-- Boolean implication in a Boolean algebra, matching the upstream `lattice.imp` notation. -/
def imp {α : Type u} [BooleanAlgebra α] (a b : α) : α :=
  aᶜ ⊔ b

/-- Split a context bounded by `a ⊔ b` and discharge the two branches separately. -/
theorem context_or_elim' {β : Type u} [CompleteBooleanAlgebra β] {Γ a b c : β}
    (h : Γ ≤ a ⊔ b)
    (hLeft : ∀ {Γ'} (_ : Γ' ≤ Γ) (_ : Γ' ≤ a), Γ' ≤ c)
    (hRight : ∀ {Γ'} (_ : Γ' ≤ Γ) (_ : Γ' ≤ b), Γ' ≤ c) :
    Γ ≤ c := by
  have hsplit : Γ = (Γ ⊓ a) ⊔ (Γ ⊓ b) := by
    calc
      Γ = Γ ⊓ (a ⊔ b) := by exact (inf_eq_left.mpr h).symm
      _ = (Γ ⊓ a) ⊔ (Γ ⊓ b) := by rw [inf_sup_left]
  rw [hsplit]
  refine sup_le ?_ ?_
  · exact hLeft inf_le_left inf_le_right
  · exact hRight inf_le_left inf_le_right

/-- The transitivity tautology for Boolean implication. -/
theorem imp_trans {β : Type u} [CompleteBooleanAlgebra β] {a b c : β} :
    (imp a b) ⊓ (imp b c) ≤ imp a c := by
  let x : β := (imp a b) ⊓ (imp b c)
  have hx1 : x ⊓ a ≤ b := by
    dsimp [x, imp]
    calc
      ((aᶜ ⊔ b) ⊓ (bᶜ ⊔ c)) ⊓ a ≤ (aᶜ ⊔ b) ⊓ a := by
        exact inf_le_inf_right _ inf_le_left
      _ = b ⊓ a := by
        rw [inf_sup_right]
        simp [inf_comm]
      _ ≤ b := inf_le_left
  have hx2 : x ⊓ a ≤ imp b c := by
    dsimp [x]
    exact le_trans inf_le_left inf_le_right
  have hxa : x ⊓ a ≤ c := by
    calc
      x ⊓ a ≤ b ⊓ imp b c := by exact le_inf hx1 hx2
      _ = b ⊓ c := by
        dsimp [imp]
        rw [inf_sup_left]
        simp
      _ ≤ c := inf_le_right
  calc
    x = x ⊓ (a ⊔ aᶜ) := by rw [sup_compl_eq_top, inf_top_eq]
    _ = (x ⊓ a) ⊔ (x ⊓ aᶜ) := by rw [inf_sup_left]
    _ ≤ c ⊔ aᶜ := by exact sup_le_sup hxa inf_le_right
    _ = imp a c := by
      dsimp [imp]
      ac_rfl

end lattice

local infix:65 " ⟹ " => lattice.imp

/-- A lightweight Lean 4 replacement for the old `tidy_context` helper. -/
syntax "tidy_context" : tactic

macro_rules
  | `(tactic| tidy_context) =>
      `(tactic| try simp [lattice.imp, le_inf_iff, sup_le_iff] at *)

/-- A first-pass Boolean-valued tautology tactic for the early forcing port. -/
syntax "bv_tauto" : tactic

macro_rules
  | `(tactic| bv_tauto) =>
      `(tactic|
        first
          | exact lattice.imp_trans
          | simp [lattice.imp]
          | aesop)

example {𝔹 : Type u} [CompleteBooleanAlgebra 𝔹] {a b c : 𝔹} :
    (a ⟹ b) ⊓ (b ⟹ c) ≤ a ⟹ c := by
  tidy_context
  bv_tauto

end Flypitch
