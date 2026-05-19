import Mathlib.Data.Fin.Basic
import Mathlib.Logic.Function.Basic

universe u v w

namespace Flypitch

/-!
`Flypitch.Compat.Core` collects small compatibility definitions that emulate the dependent-vector
utilities used by the original development. They provide the lightweight data structures and
arity helpers that the first-order syntax layer builds on.
-/

theorem Function.Injective.ne_iff {α β : Sort _} {f : α → β} (hf : Function.Injective f)
    {a₁ a₂ : α} : f a₁ ≠ f a₂ ↔ a₁ ≠ a₂ :=
  not_congr hf.eq_iff

/-- A dependently typed vector carrying its length in the index. -/
inductive dvector (α : Type u) : Nat → Type u
  | nil : dvector α 0
  | cons : {n : Nat} → α → dvector α n → dvector α (n + 1)

/-- Finite indices for `dvector`, matching the shape of the original Flypitch development. -/
inductive dfin : Nat → Type
  | fz : {n : Nat} → dfin (n + 1)
  | fs : {n : Nat} → dfin n → dfin (n + 1)

instance {n : Nat} : OfNat (dfin (n + 1)) (nat_lit 0) where
  ofNat := dfin.fz

namespace dvector

variable {α : Type u} {β : Type v} {γ : Type w} {n : Nat}

local notation "[]" => dvector.nil
local infixr:67 " :: " => dvector.cons

theorem zero_eq : (xs : dvector α 0) → xs = []
  | [] => rfl

/-- Keep the leftmost `n` entries of a dependent vector. -/
@[simp] def take : (n : Nat) → {m : Nat} → dvector α m → n ≤ m → dvector α n
  | 0, _, _, _ => []
  | n + 1, 0, [], h => False.elim (Nat.not_succ_le_zero n h)
  | n + 1, _ + 1, x :: xs, h => x :: take n xs (Nat.le_of_succ_le_succ h)

/-- Append an element to the right end of a dependent vector. -/
@[simp] def concat : {n : Nat} → dvector α n → α → dvector α (n + 1)
  | _, [], x => x :: []
  | _, y :: ys, x => y :: concat ys x

/-- Insert an element at a bounded natural-number position. -/
@[simp] def insertAt : (m : Nat) → {n : Nat} → dvector α n → α → m ≤ n → dvector α (n + 1)
  | 0, _, xs, x, _ => x :: xs
  | m + 1, 0, [], _, h => False.elim (Nat.not_succ_le_zero m h)
  | m + 1, _ + 1, y :: ys, x, h => y :: insertAt m ys x (Nat.le_of_succ_le_succ h)

/-- Return the entry at a natural-number index with a proof that the index is in range. -/
@[simp] def nth : {n : Nat} → (xs : dvector α n) → (m : Nat) → m < n → α
  | _, [], m, h => False.elim (Nat.not_lt_zero m h)
  | _, x :: _, 0, _ => x
  | _, _ :: xs, m + 1, h => nth xs m (Nat.lt_of_succ_lt_succ h)

@[simp] theorem nth_cons (x : α) (xs : dvector α n) (m : Nat) (h : m < n) :
    nth (x :: xs) (m + 1) (Nat.succ_lt_succ h) = nth xs m h := by
  simp [nth]

theorem nth_irrel : {n : Nat} → (xs : dvector α n) → (m : Nat) →
    (h₁ h₂ : m < n) → xs.nth m h₁ = xs.nth m h₂
  | 0, [], m, h₁, _ => False.elim (Nat.not_lt_zero m h₁)
  | _ + 1, _ :: _, 0, _, _ => rfl
  | _ + 1, _ :: xs, m + 1, h₁, h₂ =>
      nth_irrel xs m (Nat.lt_of_succ_lt_succ h₁) (Nat.lt_of_succ_lt_succ h₂)

@[simp] theorem nth_take : {n m : Nat} → (xs : dvector α m) → (h : n ≤ m) →
    (k : Nat) → (hk : k < n) →
      (take n xs h).nth k hk = xs.nth k (lt_of_lt_of_le hk h)
  | 0, _, _, _, k, hk => False.elim (Nat.not_lt_zero k hk)
  | n + 1, 0, [], h, _, _ => False.elim (Nat.not_succ_le_zero n h)
  | n + 1, m + 1, x :: xs, h, 0, _ => rfl
  | n + 1, m + 1, x :: xs, h, k + 1, hk => by
      simpa [take, nth] using
        nth_take xs (Nat.le_of_succ_le_succ h) k (Nat.lt_of_succ_lt_succ hk)

/-- Return the last entry of a nonempty dependent vector. -/
@[reducible, simp] def last (xs : dvector α (n + 1)) : α :=
  nth xs n (Nat.lt_succ_self n)

/-- Return the entry at a bundled `Fin` index. -/
def nth' (xs : dvector α n) (m : Fin n) : α :=
  nth xs m.1 m.2

/-- Return the entry at a `dfin` index. -/
def nth'' : {n : Nat} → dvector α n → dfin n → α
  | _, x :: _, .fz => x
  | _, _ :: xs, .fs m => nth'' xs m

/-- Propositional membership for `dvector`. -/
def mem (x : α) : {n : Nat} → dvector α n → Prop
  | _, [] => False
  | _, y :: ys => x = y ∨ mem x ys

instance : Membership α (dvector α n) where
  mem xs x := mem x xs

/-- Proof-relevant membership for `dvector`. -/
def pmem (x : α) : {n : Nat} → dvector α n → Type _
  | _, [] => Empty
  | _, y :: ys => PSum (x = y) (pmem x ys)

theorem mem_of_pmem {x : α} : {n : Nat} → {xs : dvector α n} → xs.pmem x → x ∈ xs
  | _, [], h => nomatch h
  | _, _ :: _, h =>
      match h with
      | PSum.inl h' => Or.inl h'
      | PSum.inr h' => Or.inr (mem_of_pmem h')

/-- Map a function over every entry of a dependent vector. -/
@[simp] def map (f : α → β) : {n : Nat} → dvector α n → dvector β n
  | _, [] => []
  | _, x :: xs => f x :: map f xs

/-- Zip two dependent vectors with a binary function. -/
@[simp] def map2 (f : α → β → γ) : {n : Nat} → dvector α n → dvector β n → dvector γ n
  | _, [], [] => []
  | _, x :: xs, y :: ys => f x y :: map2 f xs ys

/-- Finite infimum over a dependent vector. -/
@[simp] def fInf [Top α] [SemilatticeInf α] : {n : Nat} → dvector α n → α
  | _, [] => ⊤
  | _, x :: xs => x ⊓ fInf xs

theorem map_congr_pmem {f g : α → β} :
    {n : Nat} → {xs : dvector α n} →
      (h : ∀ x, xs.pmem x → f x = g x) → xs.map f = xs.map g
  | _, [], _ => rfl
  | _, x :: xs, h => by
      have hs : xs.map f = xs.map g := map_congr_pmem (xs := xs) (fun y hy => h y (PSum.inr hy))
      simp [map, hs, h x (PSum.inl rfl)]

theorem map_congr_mem {f g : α → β} {n : Nat} {xs : dvector α n}
    (h : ∀ x, x ∈ xs → f x = g x) : xs.map f = xs.map g :=
  map_congr_pmem (xs := xs) (fun x hx => h x (mem_of_pmem hx))

@[simp] theorem map_id : {n : Nat} → (xs : dvector α n) → xs.map (fun x => x) = xs
  | _, [] => rfl
  | _, _ :: _ => by simp [map_id]

@[simp] theorem map_map (g : β → γ) (f : α → β) :
    {n : Nat} → (xs : dvector α n) → (xs.map f).map g = xs.map (fun x => g (f x))
  | _, [] => rfl
  | _, _ :: _ => by simp [map_map]

@[simp] theorem map_nth (f : α → β) :
    {n : Nat} → (xs : dvector α n) → (m : Nat) → (h : m < n) →
      (xs.map f).nth m h = f (xs.nth m h)
  | _, [], m, h => False.elim (Nat.not_lt_zero m h)
  | _, _ :: _, 0, _ => rfl
  | _, _ :: xs, m + 1, h => map_nth f xs m (Nat.lt_of_succ_lt_succ h)

end dvector

/-- The type `α → (α → ... (α → β)...)` with `n` copies of `α`. -/
def arity' (α β : Type u) : Nat → Type u
  | 0 => β
  | n + 1 => α → arity' α β n

namespace arity'

variable {α : Type u} {β : Type u} {γ : Type u}

local notation "[]" => dvector.nil
local infixr:67 " :: " => dvector.cons

/-- Lift a constant value to an `n`-ary function that ignores all arguments. -/
def constant : {n : Nat} → β → arity' α β n
  | 0, b => b
  | _ + 1, b => fun _ => constant b

/-- Convert a dependent-vector function into its curried `arity'` form. -/
@[simp] def ofDVectorMap : {l : Nat} → ((xs : dvector α l) → β) → arity' α β l
  | 0, f => f []
  | _ + 1, f => fun x => ofDVectorMap (fun xs => f (x :: xs))

/-- Apply a curried `arity'` function to all arguments from a dependent vector. -/
@[simp] def app : {l : Nat} → arity' α β l → dvector α l → β
  | 0, b, [] => b
  | _ + 1, f, x :: xs => app (f x) xs

@[simp] theorem app_zero (f : arity' α β 0) (xs : dvector α 0) : app f xs = f := by
  cases xs
  simp [app]

/-- Postcompose the result of an `arity'` function with a map on outputs. -/
def postcompose (g : β → γ) : {n : Nat} → arity' α β n → arity' α γ n
  | 0, b => g b
  | _ + 1, f => fun x => postcompose g (f x)

/-- Precompose every argument position of an `arity'` function with the same map. -/
def precompose : {n : Nat} → arity' β γ n → (α → β) → arity' α γ n
  | 0, g, _ => g
  | _ + 1, g, f => fun x => precompose (g (f x)) f

end arity'

end Flypitch
