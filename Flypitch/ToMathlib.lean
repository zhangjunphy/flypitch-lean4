/-
Copyright (c) 2019 The Flypitch Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Jesse Han, Floris van Doorn
-/
/- theorems which we should (maybe) backport to mathlib -/

-- import Mathlib

universe u v w w'

inductive DVector (α : Type u) : ℕ → Type u where
| nil : DVector α 0
| cons : α → {n : ℕ} → DVector α n → DVector α (n+1)

inductive DFin : ℕ → Type
| fz {n} : DFin (n+1)
| fs {n} : DFin n → DFin (n+1)
