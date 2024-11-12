/-
Copyright (c) 2019 The Flypitch Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Jesse Han, Floris van Doorn
-/
/- theorems which we should (maybe) backport to mathlib -/

import Mathlib.Algebra.Free

variable (u v w w' : Prop)

inductive DVector (α : Type u) : ℕ → Type u
| nil : DVector α 0
| cons : ∀{n} (x : α) (xs : DVector α n), DVector α (n+1)

inductive DFin : ℕ → Type
| fz {n} : DFin (n+1)
| fs {n} : DFin n → DFin (n+1)

class HasZero (α : Type u) := (zero : α)

instance hasZeroDFin {n} : HasZero $ DFin (n+1) := ⟨DFin.fz⟩

-- note from Mario --- use dfin to synergize with dvector
namespace DVector
section DVectors
local notation h "::" t  => DVector.cons h t
syntax (priority := high) "[" term,* "]" : term
macro_rules
  | `([]) => `(DVector.nil)
  | `([$x]) => `(DVector.cons $x [])
  | `([$x, $xs:term,*]) => `(DVector.cons $x [$xs,*])
variable {α : Type u} {β : Type v} {γ : Type w} {n : ℕ}

@[simp] protected lemma zero_eq : ∀(xs : DVector α 0), xs = []
| [] => rfl

@[simp] protected def concat {n : ℕ} (xs : DVector α n) (x : α) : DVector α (n+1) :=
match xs with
  | [] => [x]
  | x::xs => x::(DVector.concat xs x)

@[simp] protected def nth : ∀{n : ℕ} (xs : DVector α n) (m : ℕ) (h : m < n), α
| _ []      m     h => by { exfalso, exact nat.not_lt_zero m h }
| _ (x::xs) 0     h => x
| _ (x::xs) (m+1) h => nth xs m (lt_of_add_lt_add_right h)

end DVectors

end DVector
