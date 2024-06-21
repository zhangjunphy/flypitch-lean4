/-
Copyright (c) 2019 The Flypitch Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Jesse Han, Floris van Doorn
-/
/- theorems which we should (maybe) backport to mathlib -/

import Mathlib

universe variables u v w w'

namespace function
lemma injective.ne_iff {α β} {f : α → β} (hf : function.injective f) {a₁ a₂ : α} :
  f a₁ ≠ f a₂ ↔ a₁ ≠ a₂ :=
not_congr hf.eq_iff
end function

inductive dvector (α : Type u) : ℕ → Type u
| nil {} : dvector 0
| cons : ∀{n} (x : α) (xs : dvector n), dvector (n+1)

inductive dfin : ℕ → Type
| fz {n} : dfin (n+1)
| fs {n} : dfin n → dfin (n+1)
