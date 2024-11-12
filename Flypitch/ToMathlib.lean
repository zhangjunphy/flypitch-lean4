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

@[simp] protected def concat : ∀{n : ℕ} (xs : DVector α n) (x : α), DVector α (n+1)
| _, [], x'  => [x']
| _, (x::xs), x' => x::DVector.concat xs x'

@[simp] protected def nth : ∀{n : ℕ} (xs : DVector α n) (m : ℕ) (h : m < n), α
| _, [], m, h => by { exfalso; exact Nat.not_lt_zero m h }
| _, (x::_), 0, _ => x
| _, (_::xs), (m+1), h => DVector.nth xs m (Nat.lt_of_add_lt_add_right h)

protected lemma nth_cons {n : ℕ} (x : α) (xs : DVector α n) (m : ℕ) (h : m < n) :
  DVector.nth (x::xs) (m+1) (Nat.succ_lt_succ h) = DVector.nth xs m h := by rfl

@[reducible, simp] protected def last {n : ℕ} (xs : DVector α (n+1)) : α :=
  xs.nth n (by {repeat{constructor}})

protected def nth' {n : ℕ} (xs : DVector α n) (m : Fin n) : α :=
xs.nth m.1 m.2

protected def nth'' : ∀ {n : ℕ} (xs : DVector α n) (m : DFin n), α
| _, (x::xs), DFin.fz => x
| _, (x::xs), (DFin.fs (m)) => DVector.nth'' xs m

protected def mem : ∀{n : ℕ} (x : α) (xs : DVector α n), Prop
| _, x, [] => false
| _, x, (x'::xs) => x = x' ∨ DVector.mem x xs
instance {n : ℕ} : Membership α (DVector α n) := ⟨DVector.mem⟩

protected def pmem : ∀{n : ℕ} (x : α) (xs : DVector α n), Type
| _, x, []       => Empty
| _, x, (x'::xs) => PSum (x = x') (DVector.pmem x xs)

protected lemma mem_of_pmem : ∀{n : ℕ} {x : α} {xs : DVector α n} (hx : xs.pmem x), x ∈ xs
| _, x, [],       hx => by cases hx
| _, x, (x'::xs), hx => by 
  cases hx with
  | inl _ => apply Or.inl; assumption
  | inr hx' => apply Or.inr; exact DVector.mem_of_pmem hx'

@[simp] protected def map (f : α → β) : ∀{n : ℕ}, DVector α n → DVector β n
| _, [] => []
| _, (x::xs) => f x :: DVector.map f xs

@[simp] protected def map2 (f : α → β → γ) : ∀{n : ℕ}, DVector α n → DVector β n → DVector γ n
| _, [], [] => []
| _, (x::xs), (y::ys) => f x y :: DVector.map2 f xs ys

@[simp] protected lemma map_id : ∀{n : ℕ} (xs : DVector α n), xs.map (λx => x) = xs
| _, [] => rfl
| _, (x::xs) => by
  apply DVector.map _
  _
  

end DVectors

end DVector
