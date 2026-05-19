import Flypitch.FOL
import Flypitch.BVM

universe u v w

namespace Flypitch
namespace fol

set_option linter.missingDocs false
set_option linter.style.longLine false

local notation "[]" => dvector.nil
local infixr:67 " :: " => dvector.cons

namespace bfol

variable (L : Language.{u}) (β : Type v) [CompleteBooleanAlgebra β]

/-- Boolean-valued first-order structures. -/
structure bStructure where
  carrier : Type w
  fun_map : ∀ {n}, L.functions n → dvector carrier n → carrier
  rel_map : ∀ {n}, L.relations n → dvector carrier n → β
  eq : carrier → carrier → β
  eq_refl : ∀ x, eq x x = ⊤
  eq_symm : ∀ x y, eq x y = eq y x
  eq_trans : ∀ {x} y {z}, eq x y ⊓ eq y z ≤ eq x z
  fun_congr : ∀ {n} (f : L.functions n) (x y : dvector carrier n),
    (x.map2 eq y).fInf ≤ eq (fun_map f x) (fun_map f y)
  rel_congr : ∀ {n} (R : L.relations n) (x y : dvector carrier n),
    (x.map2 eq y).fInf ⊓ rel_map R x ≤ rel_map R y

instance : CoeSort (bStructure L β) (Type w) where
  coe S := S.carrier

variable {L β}
variable {S : bStructure L β}

@[simp] theorem eq_drefl : {n : Nat} → (x : dvector S n) → (x.map2 S.eq x).fInf = ⊤
  | _, [] => rfl
  | _, x :: xs => by
      simp [dvector.map2, dvector.fInf, S.eq_refl x, eq_drefl xs]

theorem eq_dsymm : {n : Nat} → (x y : dvector S n) →
    (x.map2 S.eq y).fInf = (y.map2 S.eq x).fInf
  | _, [], [] => rfl
  | _, x :: xs, y :: ys => by
      simp [dvector.map2, dvector.fInf, S.eq_symm x y, eq_dsymm xs ys]

theorem eq_dtrans : {n : Nat} → {x : dvector S n} → (y : dvector S n) →
    {z : dvector S n} → (x.map2 S.eq y).fInf ⊓ (y.map2 S.eq z).fInf ≤
      (x.map2 S.eq z).fInf
  | _, [], [], [] => by
      simp [dvector.map2, dvector.fInf]
  | _, x :: xs, y :: ys, z :: zs => by
      simp only [dvector.map2, dvector.fInf]
      apply le_inf
      · exact (inf_le_inf inf_le_left inf_le_left).trans (S.eq_trans y)
      · exact (inf_le_inf inf_le_right inf_le_right).trans (eq_dtrans ys)

theorem subst_realize_congr1 (v v' : Nat → S) (x : S) (n : Nat) :
    (⨅ k : Nat, S.eq (v k) (v' k)) ≤
      ⨅ k : Nat, S.eq ((v[x // n]) k) ((v'[x // n]) k) := by
  apply le_iInf
  intro k
  by_cases hlt : k < n
  · simpa [subst_realize, hlt] using iInf_le (fun k : Nat => S.eq (v k) (v' k)) k
  · by_cases hgt : n < k
    · simpa [subst_realize, hlt, hgt] using
        iInf_le (fun k : Nat => S.eq (v k) (v' k)) (k - 1)
    · simp [subst_realize, hlt, hgt, S.eq_refl x]

theorem subst_realize_congr2 (v : Nat → S) (x y : S) (n : Nat) :
    S.eq x y ≤ ⨅ k : Nat, S.eq ((v[x // n]) k) ((v[y // n]) k) := by
  apply le_iInf
  intro k
  by_cases hlt : k < n
  · simp [subst_realize, hlt, S.eq_refl]
  · by_cases hgt : n < k
    · simp [subst_realize, hlt, hgt, S.eq_refl]
    · simp [subst_realize, hlt, hgt]

/-- Boolean-valued realization of terms from an unbounded valuation. -/
@[simp] def boolean_realize_term (v : Nat → S) :
    {l : Nat} → preterm L l → dvector S l → S
  | _, .var k, _ => v k
  | _, .func f, xs => S.fun_map f xs
  | _, .app t₁ t₂, xs =>
      boolean_realize_term v t₁ (boolean_realize_term v t₂ [] :: xs)
termination_by l t xs => sizeOf t
decreasing_by
  all_goals
    try simp_wf
    try omega

theorem boolean_realize_term_congr' {v v' : Nat → S} (h : ∀ n, v n = v' n) :
    {l : Nat} → (t : preterm L l) → (xs : dvector S l) →
      boolean_realize_term v t xs = boolean_realize_term v' t xs
  | _, .var k, xs => by
      cases xs
      simpa [boolean_realize_term] using h k
  | _, .func _, _ => by
      simp [boolean_realize_term]
  | _, .app t₁ t₂, xs => by
      have ht₂ :
          boolean_realize_term v t₂ [] = boolean_realize_term v' t₂ [] :=
        boolean_realize_term_congr' h t₂ []
      simpa [boolean_realize_term, ht₂] using
        (boolean_realize_term_congr' h t₁ (boolean_realize_term v' t₂ [] :: xs))
termination_by l t xs => sizeOf t
decreasing_by
  all_goals
    try simp_wf
    try omega

theorem boolean_realize_term_subst (v : Nat → S) :
    {l : Nat} → (n : Nat) → (t : preterm L l) → (s : term L) →
      (xs : dvector S l) →
      boolean_realize_term (v[boolean_realize_term v (s ↑ n) [] // n]) t xs =
        boolean_realize_term v (subst_term t s n) xs
  | _, n, .var k, s, xs => by
      cases xs
      by_cases hlt : k < n
      · simp [boolean_realize_term, subst_term, subst_realize, hlt]
      · by_cases hgt : n < k
        · simp [boolean_realize_term, subst_term, subst_realize, hlt, hgt]
        · have hk : k = n := Nat.le_antisymm (Nat.le_of_not_gt hgt) (Nat.le_of_not_gt hlt)
          subst hk
          simp [boolean_realize_term, subst_term, subst_realize, lift_term]
  | _, _, .func _, _, _ => by
      simp [boolean_realize_term, subst_term]
  | _, n, .app t₁ t₂, s, xs => by
      have ht₂ :
          boolean_realize_term (v[boolean_realize_term v (s ↑ n) [] // n]) t₂ [] =
            boolean_realize_term v (subst_term t₂ s n) [] :=
        boolean_realize_term_subst (v := v) (n := n) (t := t₂) (s := s) (xs := [])
      simpa [boolean_realize_term, subst_term, ht₂] using
        (boolean_realize_term_subst (v := v) (n := n) (t := t₁) (s := s)
          (xs := boolean_realize_term v (subst_term t₂ s n) [] :: xs))
termination_by l n t s xs => sizeOf t
decreasing_by
  all_goals
    try simp_wf
    try omega

theorem boolean_realize_term_subst_lift (v : Nat → S) (x : S) (m : Nat) :
    {l : Nat} → (t : preterm L l) → (xs : dvector S l) →
      boolean_realize_term (v[x // m]) (lift_term_at t 1 m) xs =
        boolean_realize_term v t xs
  | _, .var k, _ => by
      by_cases h : m ≤ k
      · have hk : m < k + 1 := Nat.lt_succ_of_le h
        simp [boolean_realize_term, lift_term_at, h, subst_realize_gt, hk]
      · have hk : k < m := Nat.lt_of_not_ge h
        simp [boolean_realize_term, lift_term_at, h, subst_realize_lt, hk]
  | _, .func _, _ => by
      simp [boolean_realize_term, lift_term_at]
  | _, .app t₁ t₂, xs => by
      have ht₂ :
          boolean_realize_term (v[x // m]) (lift_term_at t₂ 1 m) [] =
            boolean_realize_term v t₂ [] :=
        boolean_realize_term_subst_lift (v := v) (x := x) (m := m) (t := t₂) (xs := [])
      simpa [boolean_realize_term, lift_term_at, ht₂] using
        (boolean_realize_term_subst_lift (v := v) (x := x) (m := m) (t := t₁)
          (xs := boolean_realize_term v t₂ [] :: xs))
termination_by l t xs => sizeOf t
decreasing_by
  all_goals
    try simp_wf
    try omega

theorem boolean_realize_term_congr_gen (v v' : Nat → S) :
    {l : Nat} → (t : preterm L l) → (xs xs' : dvector S l) →
      (⨅ n : Nat, S.eq (v n) (v' n)) ⊓ (xs.map2 S.eq xs').fInf ≤
        S.eq (boolean_realize_term v t xs) (boolean_realize_term v' t xs')
  | _, .var k, xs, xs' => by
      cases xs
      cases xs'
      simpa [boolean_realize_term] using
        iInf_le (fun n : Nat => S.eq (v n) (v' n)) k
  | _, .func f, xs, xs' => by
      simpa [boolean_realize_term] using inf_le_right.trans (S.fun_congr f xs xs')
  | _, .app t₁ t₂, xs, xs' => by
      have ht₁ := boolean_realize_term_congr_gen v v' t₁
        (boolean_realize_term v t₂ [] :: xs)
        (boolean_realize_term v' t₂ [] :: xs')
      refine le_trans ?_ (by simpa [boolean_realize_term] using ht₁)
      change (⨅ n : Nat, S.eq (v n) (v' n)) ⊓ (xs.map2 S.eq xs').fInf ≤
        (⨅ n : Nat, S.eq (v n) (v' n)) ⊓
          (S.eq (boolean_realize_term v t₂ []) (boolean_realize_term v' t₂ []) ⊓
            (xs.map2 S.eq xs').fInf)
      apply le_inf
      · exact inf_le_left
      · apply le_inf
        · refine le_trans ?_ (boolean_realize_term_congr_gen v v' t₂ [] [])
          exact le_inf inf_le_left le_top
        · exact inf_le_right
termination_by l t xs xs' => sizeOf t
decreasing_by
  all_goals
    try simp_wf
    try omega

theorem boolean_realize_term_congr (v v' : Nat → S) {l : Nat}
    (t : preterm L l) (xs : dvector S l) :
    (⨅ n : Nat, S.eq (v n) (v' n)) ≤
      S.eq (boolean_realize_term v t xs) (boolean_realize_term v' t xs) := by
  refine le_trans ?_ (boolean_realize_term_congr_gen v v' t xs xs)
  simp [eq_drefl]

theorem boolean_realize_term_subst_congr (v : Nat → S) {n : Nat}
    (s s' : term L) :
    {l : Nat} → (t : preterm L l) → (xs : dvector S l) →
      S.eq (boolean_realize_term v (s ↑ n) [])
          (boolean_realize_term v (s' ↑ n) []) ≤
        S.eq (boolean_realize_term v (subst_term t s n) xs)
          (boolean_realize_term v (subst_term t s' n) xs)
  | _, t, xs => by
      rw [← boolean_realize_term_subst, ← boolean_realize_term_subst]
      refine le_trans ?_ (boolean_realize_term_congr _ _ _ _)
      exact subst_realize_congr2 v
        (boolean_realize_term v (s ↑ n) [])
        (boolean_realize_term v (s' ↑ n) []) n

/-- Boolean-valued realization of formulas from an unbounded valuation. -/
@[simp] def boolean_realize_formula :
    {l : Nat} → (Nat → S) → preformula L l → dvector S l → β
  | _, _, .falsum, _ => ⊥
  | _, v, .equal t₁ t₂, xs => S.eq (boolean_realize_term v t₁ xs) (boolean_realize_term v t₂ xs)
  | _, _, .rel R, xs => S.rel_map R xs
  | _, v, .apprel f t, xs =>
      boolean_realize_formula v f (boolean_realize_term v t [] :: xs)
  | _, v, .imp f₁ f₂, xs =>
      lattice.imp (boolean_realize_formula v f₁ xs) (boolean_realize_formula v f₂ xs)
  | _, v, .all f, xs => ⨅ x : S, boolean_realize_formula (v[x // 0]) f xs
termination_by l v f xs => sizeOf f
decreasing_by
  all_goals
    try simp_wf
    try omega

theorem boolean_realize_formula_congr' :
    {l : Nat} → {v v' : Nat → S} → (∀ n, v n = v' n) →
      (f : preformula L l) → (xs : dvector S l) →
      boolean_realize_formula v f xs = boolean_realize_formula v' f xs
  | _, _, _, _, .falsum, _ => by
      simp [boolean_realize_formula]
  | _, _, _, h, .equal t₁ t₂, xs => by
      simp [boolean_realize_formula, boolean_realize_term_congr' h]
  | _, _, _, _, .rel _, _ => by
      simp [boolean_realize_formula]
  | _, v, v', h, .apprel f t, xs => by
      have ht :
          boolean_realize_term v t [] = boolean_realize_term v' t [] :=
        boolean_realize_term_congr' h t []
      simpa [boolean_realize_formula, ht] using
        (boolean_realize_formula_congr' h f (boolean_realize_term v' t [] :: xs))
  | _, _, _, h, .imp f₁ f₂, xs => by
      simp [boolean_realize_formula, boolean_realize_formula_congr' h f₁ xs,
        boolean_realize_formula_congr' h f₂ xs]
  | _, _, _, h, .all f, xs => by
      simp only [boolean_realize_formula]
      apply congrArg iInf
      funext x
      apply boolean_realize_formula_congr'
      intro n
      exact subst_realize_congr h x 0 n
termination_by l v v' h f xs => sizeOf f
decreasing_by
  all_goals
    try simp_wf
    try omega

theorem boolean_realize_formula_subst :
    {l : Nat} → (v : Nat → S) → (n : Nat) → (f : preformula L l) →
      (s : term L) → (xs : dvector S l) →
      boolean_realize_formula (v[boolean_realize_term v (s ↑ n) [] // n]) f xs =
        boolean_realize_formula v (subst_formula f s n) xs
  | _, _, _, .falsum, _, _ => by
      simp [boolean_realize_formula, subst_formula]
  | _, v, n, .equal t₁ t₂, s, xs => by
      simp [boolean_realize_formula, boolean_realize_term_subst]
  | _, _, _, .rel _, _, _ => by
      simp [boolean_realize_formula, subst_formula]
  | _, v, n, .apprel f t, s, xs => by
      have ht :
          boolean_realize_term (v[boolean_realize_term v (s ↑ n) [] // n]) t [] =
            boolean_realize_term v (subst_term t s n) [] :=
        boolean_realize_term_subst (v := v) (n := n) (t := t) (s := s) (xs := [])
      simpa [boolean_realize_formula, subst_formula, ht] using
        (boolean_realize_formula_subst (v := v) (n := n) (f := f) (s := s)
          (xs := boolean_realize_term v (subst_term t s n) [] :: xs))
  | _, v, n, .imp f₁ f₂, s, xs => by
      simp [boolean_realize_formula, subst_formula,
        boolean_realize_formula_subst (v := v) (n := n) (f := f₁) (s := s) (xs := xs),
        boolean_realize_formula_subst (v := v) (n := n) (f := f₂) (s := s) (xs := xs)]
  | _, v, n, .all f, s, xs => by
      simp only [boolean_realize_formula, subst_formula]
      apply congrArg iInf
      funext x
      rw [← boolean_realize_formula_subst]
      apply boolean_realize_formula_congr'
      intro k
      rw [subst_realize2_0]
      rw [← boolean_realize_term_subst_lift v x 0]
      simp [lift_term_def, lift_term2, Nat.add_comm]
termination_by l v n f s xs => sizeOf f
decreasing_by
  all_goals
    try simp_wf
    try omega

theorem boolean_realize_formula_subst0 {l : Nat} (v : Nat → S) (f : preformula L l)
    (s : term L) (xs : dvector S l) :
    boolean_realize_formula (v[boolean_realize_term v s [] // 0]) f xs =
      boolean_realize_formula v (subst_formula f s 0) xs := by
  simpa [lift_term] using
    (boolean_realize_formula_subst (v := v) (n := 0) (f := f) (s := s) (xs := xs))

theorem boolean_realize_formula_subst_lift :
    {l : Nat} → (v : Nat → S) → (x : S) → (m : Nat) →
      (f : preformula L l) → (xs : dvector S l) →
      boolean_realize_formula (v[x // m]) (lift_formula_at f 1 m) xs =
        boolean_realize_formula v f xs
  | _, _, _, _, .falsum, _ => by
      simp [boolean_realize_formula, lift_formula_at]
  | _, v, x, m, .equal t₁ t₂, xs => by
      simp [boolean_realize_formula, lift_formula_at, boolean_realize_term_subst_lift]
  | _, _, _, _, .rel _, _ => by
      simp [boolean_realize_formula, lift_formula_at]
  | _, v, x, m, .apprel f t, xs => by
      have ht :
          boolean_realize_term (v[x // m]) (lift_term_at t 1 m) [] =
            boolean_realize_term v t [] :=
        boolean_realize_term_subst_lift (v := v) (x := x) (m := m) (t := t) (xs := [])
      simpa [boolean_realize_formula, lift_formula_at, ht] using
        (boolean_realize_formula_subst_lift (v := v) (x := x) (m := m) (f := f)
          (xs := boolean_realize_term v t [] :: xs))
  | _, v, x, m, .imp f₁ f₂, xs => by
      simp [boolean_realize_formula, lift_formula_at,
        boolean_realize_formula_subst_lift (v := v) (x := x) (m := m) (f := f₁) (xs := xs),
        boolean_realize_formula_subst_lift (v := v) (x := x) (m := m) (f := f₂) (xs := xs)]
  | _, v, x, m, .all f, xs => by
      simp only [boolean_realize_formula, lift_formula_at]
      apply congrArg iInf
      funext x'
      rw [boolean_realize_formula_congr' (subst_realize2_0 (v := v) (x := x') (x' := x) (n := m))]
      exact boolean_realize_formula_subst_lift
        (v := v[x' // 0]) (x := x) (m := m + 1) (f := f) (xs := xs)
termination_by l v x m f xs => sizeOf f
decreasing_by
  all_goals
    try simp_wf
    try omega

theorem boolean_imp_congr {E A A' B B' : β}
    (hA : E ⊓ A' ≤ A) (hB : E ⊓ B ≤ B') :
    E ⊓ lattice.imp A B ≤ lattice.imp A' B' := by
  rw [lattice.le_imp_iff]
  have hToB : (E ⊓ lattice.imp A B) ⊓ A' ≤ B := by
    have hEA : (E ⊓ lattice.imp A B) ⊓ A' ≤ A := by
      exact (le_inf (inf_le_left.trans inf_le_left) inf_le_right).trans hA
    have hImp : (E ⊓ lattice.imp A B) ⊓ A' ≤ lattice.imp A B :=
      inf_le_left.trans inf_le_right
    have hAB : A ⊓ lattice.imp A B ≤ B := by
      simpa [inf_comm] using (lattice.le_imp_iff.mp (le_rfl : lattice.imp A B ≤ lattice.imp A B))
    exact (le_inf hEA hImp).trans hAB
  have hE : (E ⊓ lattice.imp A B) ⊓ A' ≤ E :=
    inf_le_left.trans inf_le_left
  exact (le_inf hE hToB).trans hB

theorem boolean_realize_formula_congr_gen (v v' : Nat → S) :
    {l : Nat} → (f : preformula L l) → (xs xs' : dvector S l) →
      (⨅ n : Nat, S.eq (v n) (v' n)) ⊓ (xs.map2 S.eq xs').fInf ⊓
          boolean_realize_formula v f xs ≤
        boolean_realize_formula v' f xs'
  | _, .falsum, _, _ => by
      simp [boolean_realize_formula]
  | _, .equal t₁ t₂, xs, xs' => by
      simp only [boolean_realize_formula]
      let E : β := ⨅ n : Nat, S.eq (v n) (v' n)
      let X : β := (xs.map2 S.eq xs').fInf
      let a : S := boolean_realize_term v t₁ xs
      let b : S := boolean_realize_term v t₂ xs
      let a' : S := boolean_realize_term v' t₁ xs'
      let b' : S := boolean_realize_term v' t₂ xs'
      change E ⊓ X ⊓ S.eq a b ≤ S.eq a' b'
      have ha : E ⊓ X ≤ S.eq a a' := by
        simpa [E, X, a, a'] using boolean_realize_term_congr_gen v v' t₁ xs xs'
      have hb : E ⊓ X ≤ S.eq b b' := by
        simpa [E, X, b, b'] using boolean_realize_term_congr_gen v v' t₂ xs xs'
      have haSym : E ⊓ X ≤ S.eq a' a := by
        simpa [S.eq_symm a' a] using ha
      have hLeft : E ⊓ X ⊓ S.eq a b ≤ S.eq a' b := by
        exact (le_inf (inf_le_left.trans haSym) inf_le_right).trans (S.eq_trans a)
      have hRight : E ⊓ X ⊓ S.eq a' b ≤ S.eq a' b' := by
        have hb' : E ⊓ X ⊓ S.eq a' b ≤ S.eq b b' := inf_le_left.trans hb
        exact (le_inf inf_le_right hb').trans (S.eq_trans b)
      exact (le_inf inf_le_left hLeft).trans hRight
  | _, .rel R, xs, xs' => by
      simpa [boolean_realize_formula] using
        (inf_le_inf inf_le_right le_rfl).trans (S.rel_congr R xs xs')
  | _, .apprel f t, xs, xs' => by
      let E : β := ⨅ n : Nat, S.eq (v n) (v' n)
      have ht :
          E ⊓ (xs.map2 S.eq xs').fInf ≤
            S.eq (boolean_realize_term v t []) (boolean_realize_term v' t []) := by
        exact inf_le_left.trans (by simpa [E] using boolean_realize_term_congr_gen v v' t [] [])
      have hf := boolean_realize_formula_congr_gen v v' f
        (boolean_realize_term v t [] :: xs)
        (boolean_realize_term v' t [] :: xs')
      refine le_trans ?_ (by simpa [boolean_realize_formula] using hf)
      change E ⊓ (xs.map2 S.eq xs').fInf ⊓
          boolean_realize_formula v (preformula.apprel f t) xs ≤
        E ⊓ (S.eq (boolean_realize_term v t []) (boolean_realize_term v' t []) ⊓
          (xs.map2 S.eq xs').fInf) ⊓
          boolean_realize_formula v f (boolean_realize_term v t [] :: xs)
      apply le_inf
      · apply le_inf
        · exact inf_le_left.trans inf_le_left
        · apply le_inf
          · exact inf_le_left.trans ht
          · exact inf_le_left.trans inf_le_right
      · simpa [boolean_realize_formula] using inf_le_right
  | _, .imp f₁ f₂, xs, xs' => by
      simp only [boolean_realize_formula]
      let E : β := ⨅ n : Nat, S.eq (v n) (v' n)
      let X : β := (xs.map2 S.eq xs').fInf
      let A : β := boolean_realize_formula v f₁ xs
      let B : β := boolean_realize_formula v f₂ xs
      let A' : β := boolean_realize_formula v' f₁ xs'
      let B' : β := boolean_realize_formula v' f₂ xs'
      change E ⊓ X ⊓ lattice.imp A B ≤ lattice.imp A' B'
      have hB : E ⊓ X ⊓ B ≤ B' := by
        simpa [E, X, B, B'] using boolean_realize_formula_congr_gen v v' f₂ xs xs'
      have hE : E = (⨅ n : Nat, S.eq (v' n) (v n)) := by
        apply congrArg iInf
        funext n
        exact S.eq_symm (v n) (v' n)
      have hA : E ⊓ X ⊓ A' ≤ A := by
        have hA' := boolean_realize_formula_congr_gen v' v f₁ xs' xs
        simpa [E, X, A, A', hE, eq_dsymm xs' xs, inf_assoc, inf_left_comm, inf_comm]
          using hA'
      exact boolean_imp_congr hA hB
  | _, .all f, xs, xs' => by
      simp only [boolean_realize_formula]
      apply le_iInf
      intro x
      refine le_trans ?_ (boolean_realize_formula_congr_gen (v[x // 0]) (v'[x // 0]) f xs xs')
      apply le_inf
      · apply le_inf
        · exact (inf_le_left.trans inf_le_left).trans (subst_realize_congr1 v v' x 0)
        · exact inf_le_left.trans inf_le_right
      · exact inf_le_right.trans (iInf_le _ x)
termination_by l f xs xs' => sizeOf f
decreasing_by
  all_goals
    try simp_wf
    try omega

theorem boolean_realize_formula_congr (v v' : Nat → S) {l : Nat}
    (f : preformula L l) (xs : dvector S l) :
    (⨅ n : Nat, S.eq (v n) (v' n)) ⊓ boolean_realize_formula v f xs ≤
      boolean_realize_formula v' f xs := by
  refine le_trans ?_ (boolean_realize_formula_congr_gen v v' f xs xs)
  simp [eq_drefl]

theorem boolean_realize_formula_subst_congr (v : Nat → S) (s s' : term L) :
    {n l : Nat} → (f : preformula L l) → (xs : dvector S l) →
      S.eq (boolean_realize_term v (s ↑ n) []) (boolean_realize_term v (s' ↑ n) []) ⊓
          boolean_realize_formula v (subst_formula f s n) xs ≤
        boolean_realize_formula v (subst_formula f s' n) xs
  | n, _, f, xs => by
      rw [← boolean_realize_formula_subst, ← boolean_realize_formula_subst]
      refine le_trans ?_ (boolean_realize_formula_congr
        (v[boolean_realize_term v (s ↑ n) [] // n])
        (v[boolean_realize_term v (s' ↑ n) [] // n]) f xs)
      apply le_inf
      · exact inf_le_left.trans (subst_realize_congr2 v
          (boolean_realize_term v (s ↑ n) [])
          (boolean_realize_term v (s' ↑ n) []) n)
      · exact inf_le_right

theorem boolean_realize_formula_subst_congr0 (v : Nat → S) (s s' : term L)
    {l : Nat} (f : preformula L l) (xs : dvector S l) :
    S.eq (boolean_realize_term v s []) (boolean_realize_term v s' []) ⊓
        boolean_realize_formula v (subst_formula f s 0) xs ≤
      boolean_realize_formula v (subst_formula f s' 0) xs := by
  simpa [lift_term] using
    (boolean_realize_formula_subst_congr (v := v) (s := s) (s' := s')
      (n := 0) (f := f) (xs := xs))

/-- Boolean-valued realization of bounded terms from a bounded valuation. -/
@[simp] def boolean_realize_bounded_term {n : Nat} (v : dvector S n) :
    {l : Nat} → bounded_preterm L n l → dvector S l → S
  | _, ⟨.var k, hk⟩, _ => v.nth k hk
  | _, ⟨.func f, _⟩, xs => S.fun_map f xs
  | _, ⟨.app t₁ t₂, h⟩, xs =>
      boolean_realize_bounded_term v ⟨t₁, h.1⟩
        (boolean_realize_bounded_term v ⟨t₂, h.2⟩ [] :: xs)
termination_by l t xs => sizeOf t.1
decreasing_by
  all_goals
    try simp_wf
    try omega

@[simp] theorem boolean_realize_bounded_term_mk_fst {n l : Nat} {v : dvector S n}
    (t : bounded_preterm L n l) (h : bounded_term_at t.fst n) (xs : dvector S l) :
    boolean_realize_bounded_term v (⟨t.fst, h⟩ : bounded_preterm L n l) xs =
      boolean_realize_bounded_term v t xs := by
  cases t with
  | mk t ht =>
      congr

theorem boolean_realize_bounded_term_mono {n m l : Nat} (h : n ≤ m)
    {v : dvector S m} :
    ∀ (t : preterm L l) (htn : bounded_term_at t n) (htm : bounded_term_at t m)
      (xs : dvector S l),
      boolean_realize_bounded_term v (⟨t, htm⟩ : bounded_preterm L m l) xs =
        boolean_realize_bounded_term (dvector.take n v h)
          (⟨t, htn⟩ : bounded_preterm L n l) xs
  | .var k, htn, htm, _ => by
      simp only [boolean_realize_bounded_term]
      rw [dvector.nth_take]
  | .func _, _, _, _ => by
      simp [boolean_realize_bounded_term]
  | .app t₁ t₂, htn, htm, xs => by
      simp only [boolean_realize_bounded_term]
      have h₂ :
          boolean_realize_bounded_term v (⟨t₂, htm.2⟩ : bounded_preterm L m 0) [] =
            boolean_realize_bounded_term (dvector.take n v h)
              (⟨t₂, htn.2⟩ : bounded_preterm L n 0) [] :=
        boolean_realize_bounded_term_mono h t₂ htn.2 htm.2 []
      rw [h₂]
      exact boolean_realize_bounded_term_mono h t₁ htn.1 htm.1 _

@[simp] theorem boolean_realize_bounded_term_cast {n m l : Nat} (h : n ≤ m)
    {v : dvector S m} (t : bounded_preterm L n l) (xs : dvector S l) :
    boolean_realize_bounded_term v (t.cast h) xs =
      boolean_realize_bounded_term (dvector.take n v h) t xs :=
  boolean_realize_bounded_term_mono h t.fst t.2 (bounded_term_at_mono t.fst t.2 h) xs

/-- Lifting a bounded term is semantically neutral after extending the valuation. -/
@[simp] theorem boolean_realize_bounded_term_lift1 {n l : Nat} {v : dvector S n}
    (x : S) (t : bounded_preterm L n l) (xs : dvector S l) :
    boolean_realize_bounded_term (x :: v) t.lift1 xs =
      boolean_realize_bounded_term v t xs := by
  induction t using Subtype.rec with
  | _ t ht =>
      induction t with
      | var k =>
          simp [bounded_preterm.lift1, bounded_preterm.liftAt, lift_term, lift_term_at]
      | func f =>
          simp [bounded_preterm.lift1, bounded_preterm.liftAt, lift_term, lift_term_at,
            boolean_realize_bounded_term]
      | app t₁ t₂ ih₁ ih₂ =>
          simp only [bounded_preterm.lift1, bounded_preterm.liftAt,
            bounded_preterm.fst, lift_term_at, boolean_realize_bounded_term]
          have h₂ :
              boolean_realize_bounded_term (x :: v) ⟨t₂ ↑' 1 # 0, by
                exact bounded_term_at_lift_at t₂ ht.2⟩ [] =
                boolean_realize_bounded_term v ⟨t₂, ht.2⟩ [] := by
            simpa [bounded_preterm.lift1, bounded_preterm.liftAt, bounded_preterm.fst]
              using ih₂ [] ht.2
          rw [h₂]
          exact ih₁ (boolean_realize_bounded_term v ⟨t₂, ht.2⟩ [] :: xs) ht.1

/-- Boolean-valued realization of closed terms. -/
@[reducible] def boolean_realize_closed_term (S : bStructure L β) (t : closed_term L) : S :=
  boolean_realize_bounded_term (S := S) [] t []

/-- Boolean-valued realization of bounded formulas from a bounded valuation. -/
@[simp] def boolean_realize_bounded_formula :
    {n l : Nat} → dvector S n → bounded_preformula L n l → dvector S l → β
  | _, _, _, ⟨.falsum, _⟩, _ => ⊥
  | _, _, v, ⟨.equal t₁ t₂, h⟩, xs =>
      S.eq (boolean_realize_bounded_term v ⟨t₁, h.1⟩ xs)
        (boolean_realize_bounded_term v ⟨t₂, h.2⟩ xs)
  | _, _, _, ⟨.rel R, _⟩, xs => S.rel_map R xs
  | _, _, v, ⟨.apprel f t, h⟩, xs =>
      boolean_realize_bounded_formula v ⟨f, h.1⟩
        (boolean_realize_bounded_term v ⟨t, h.2⟩ [] :: xs)
  | _, _, v, ⟨.imp f₁ f₂, h⟩, xs =>
      lattice.imp (boolean_realize_bounded_formula v ⟨f₁, h.1⟩ xs)
        (boolean_realize_bounded_formula v ⟨f₂, h.2⟩ xs)
  | _, _, v, ⟨.all f, h⟩, xs =>
      ⨅ x : S, boolean_realize_bounded_formula (x :: v) ⟨f, h⟩ xs
termination_by n l v f xs => sizeOf f.1
decreasing_by
  all_goals
    try simp_wf
    try omega

@[simp] theorem boolean_realize_bounded_formula_mk_fst {n l : Nat} {v : dvector S n}
    (f : bounded_preformula L n l) (h : bounded_formula_at f.fst n) (xs : dvector S l) :
    boolean_realize_bounded_formula v (⟨f.fst, h⟩ : bounded_preformula L n l) xs =
      boolean_realize_bounded_formula v f xs := by
  cases f with
  | mk f hf =>
      congr

theorem boolean_realize_bounded_formula_mono {n m l : Nat} (h : n ≤ m)
    {v : dvector S m} :
    ∀ (f : preformula L l) (hfn : bounded_formula_at f n) (hfm : bounded_formula_at f m)
      (xs : dvector S l),
      boolean_realize_bounded_formula v (⟨f, hfm⟩ : bounded_preformula L m l) xs =
        boolean_realize_bounded_formula (dvector.take n v h)
          (⟨f, hfn⟩ : bounded_preformula L n l) xs
  | .falsum, _, _, _ => by
      simp [boolean_realize_bounded_formula]
  | .equal t₁ t₂, hfn, hfm, xs => by
      simp only [boolean_realize_bounded_formula]
      rw [boolean_realize_bounded_term_mono h t₁ hfn.1 hfm.1,
        boolean_realize_bounded_term_mono h t₂ hfn.2 hfm.2]
  | .rel _, _, _, _ => by
      simp [boolean_realize_bounded_formula]
  | .apprel f t, hfn, hfm, xs => by
      simp only [boolean_realize_bounded_formula]
      have ht :
          boolean_realize_bounded_term v (⟨t, hfm.2⟩ : bounded_preterm L m 0) [] =
            boolean_realize_bounded_term (dvector.take n v h)
              (⟨t, hfn.2⟩ : bounded_preterm L n 0) [] :=
        boolean_realize_bounded_term_mono h t hfn.2 hfm.2 []
      rw [ht]
      exact boolean_realize_bounded_formula_mono h f hfn.1 hfm.1 _
  | .imp f₁ f₂, hfn, hfm, xs => by
      simp only [boolean_realize_bounded_formula]
      rw [boolean_realize_bounded_formula_mono h f₁ hfn.1 hfm.1,
        boolean_realize_bounded_formula_mono h f₂ hfn.2 hfm.2]
  | .all f, hfn, hfm, xs => by
      simp only [boolean_realize_bounded_formula]
      apply congrArg iInf
      funext x
      simpa [dvector.take] using
        boolean_realize_bounded_formula_mono (Nat.succ_le_succ h)
          (v := x :: v) f hfn hfm xs

@[simp] theorem boolean_realize_bounded_formula_cast {n m l : Nat} (h : n ≤ m)
    {v : dvector S m} (f : bounded_preformula L n l) (xs : dvector S l) :
    boolean_realize_bounded_formula v (f.cast h) xs =
      boolean_realize_bounded_formula (dvector.take n v h) f xs :=
  boolean_realize_bounded_formula_mono h f.fst f.2
    (bounded_formula_at_mono f.fst f.2 h) xs

theorem boolean_realize_bounded_term_eq {n : Nat} {v₁ : dvector S n}
    {v₂ : Nat → S} (hv : ∀ k (hk : k < n), v₁.nth k hk = v₂ k) :
    {l : Nat} → (t : bounded_preterm L n l) → (xs : dvector S l) →
      boolean_realize_bounded_term v₁ t xs = boolean_realize_term v₂ t.fst xs
  | _, ⟨.var k, hk⟩, _ => by
      simp [boolean_realize_bounded_term, boolean_realize_term, hv k hk]
  | _, ⟨.func _, _⟩, _ => by
      simp [boolean_realize_bounded_term, boolean_realize_term]
  | _, ⟨.app t₁ t₂, h⟩, xs => by
      have ht₂ :
          boolean_realize_bounded_term v₁ ⟨t₂, h.2⟩ [] =
            boolean_realize_term v₂ t₂ [] :=
        boolean_realize_bounded_term_eq hv ⟨t₂, h.2⟩ []
      simpa [boolean_realize_bounded_term, boolean_realize_term, ht₂] using
        (boolean_realize_bounded_term_eq hv ⟨t₁, h.1⟩
          (boolean_realize_term v₂ t₂ [] :: xs))
termination_by l t xs => sizeOf t.1
decreasing_by
  all_goals
    try simp_wf
    try omega

theorem boolean_realize_bounded_formula_eq {n : Nat} {v₁ : dvector S n}
    {v₂ : Nat → S} (hv : ∀ k (hk : k < n), v₁.nth k hk = v₂ k) :
    {l : Nat} → (f : bounded_preformula L n l) → (xs : dvector S l) →
      boolean_realize_bounded_formula v₁ f xs = boolean_realize_formula v₂ f.fst xs
  | _, ⟨.falsum, _⟩, _ => by
      simp [boolean_realize_bounded_formula, boolean_realize_formula]
  | _, ⟨.equal t₁ t₂, h⟩, xs => by
      simp [boolean_realize_bounded_formula, boolean_realize_formula,
        boolean_realize_bounded_term_eq (v₁ := v₁) (v₂ := v₂) (hv := hv)
          (t := ⟨t₁, h.1⟩) (xs := xs),
        boolean_realize_bounded_term_eq (v₁ := v₁) (v₂ := v₂) (hv := hv)
          (t := ⟨t₂, h.2⟩) (xs := xs)]
  | _, ⟨.rel _, _⟩, _ => by
      simp [boolean_realize_bounded_formula, boolean_realize_formula]
  | _, ⟨.apprel f t, h⟩, xs => by
      have ht :
          boolean_realize_bounded_term v₁ ⟨t, h.2⟩ [] =
            boolean_realize_term v₂ t [] :=
        boolean_realize_bounded_term_eq (v₁ := v₁) (v₂ := v₂) (hv := hv)
          (t := ⟨t, h.2⟩) (xs := [])
      simpa [boolean_realize_bounded_formula, boolean_realize_formula, ht] using
        (boolean_realize_bounded_formula_eq (v₁ := v₁) (v₂ := v₂) (hv := hv)
          (f := ⟨f, h.1⟩) (xs := boolean_realize_term v₂ t [] :: xs))
  | _, ⟨.imp f₁ f₂, h⟩, xs => by
      simp [boolean_realize_bounded_formula, boolean_realize_formula,
        boolean_realize_bounded_formula_eq (v₁ := v₁) (v₂ := v₂) (hv := hv)
          (f := ⟨f₁, h.1⟩) (xs := xs),
        boolean_realize_bounded_formula_eq (v₁ := v₁) (v₂ := v₂) (hv := hv)
          (f := ⟨f₂, h.2⟩) (xs := xs)]
  | _, ⟨.all f, h⟩, xs => by
      unfold boolean_realize_bounded_formula
      unfold boolean_realize_formula
      apply congrArg iInf
      funext x
      exact boolean_realize_bounded_formula_eq
        (v₁ := x :: v₁) (v₂ := v₂[x // 0])
        (hv := by
          intro k hk
          cases k with
          | zero => rfl
          | succ k =>
              simpa using hv k (Nat.lt_of_succ_lt_succ hk))
        (f := ⟨f, h⟩) (xs := xs)
termination_by l f xs => sizeOf f.1
decreasing_by
  all_goals
    try simp_wf
    try omega

theorem boolean_realize_bounded_formula_fst_eq {n l : Nat}
    {v : dvector S n} {f g : bounded_preformula L n l}
    (h : f.fst = g.fst) (xs : dvector S l) :
    boolean_realize_bounded_formula v f xs =
      boolean_realize_bounded_formula v g xs := by
  cases f with
  | mk f hf =>
      cases g with
      | mk g hg =>
          dsimp [bounded_preformula.fst] at h
          subst g
          simp

/-- Extend a bounded valuation to an unbounded one, using `default` outside the bounded range. -/
def boundedVal {n : Nat} (default : S) (v : dvector S n) : Nat → S :=
  fun k => if h : k < n then v.nth k h else default

@[simp] theorem boundedVal_of_lt {n : Nat} (default : S) (v : dvector S n)
    {k : Nat} (h : k < n) : boundedVal default v k = v.nth k h := by
  simp [boundedVal, h]

@[simp] theorem boundedVal_of_ge {n : Nat} (default : S) (v : dvector S n)
    {k : Nat} (h : ¬ k < n) : boundedVal default v k = default := by
  simp [boundedVal, h]

theorem boundedVal_insertAt {n m : Nat} (h : m ≤ n) (default x : S)
    (v : dvector S n) :
    ∀ k (hk : k < n + 1),
      (dvector.insertAt m v x h).nth k hk =
        ((boundedVal default v)[x // m]) k := by
  induction m generalizing n with
  | zero =>
      intro k hk
      cases k with
      | zero =>
          simp [boundedVal, subst_realize]
      | succ k =>
          have hk' : k < n := Nat.lt_of_succ_lt_succ hk
          simp [boundedVal, subst_realize, hk']
  | succ m ih =>
      cases n with
      | zero =>
          exact False.elim (Nat.not_succ_le_zero m h)
      | succ n =>
          cases v with
          | cons y ys =>
              intro k hk
              cases k with
              | zero =>
                  simp [boundedVal, subst_realize]
              | succ k =>
                  cases k with
                  | zero =>
                      have hmn : m ≤ n := Nat.le_of_succ_le_succ h
                      simpa [boundedVal, subst_realize] using
                        ih hmn ys 0 (Nat.zero_lt_succ n)
                  | succ k =>
                      have hmn : m ≤ n := Nat.le_of_succ_le_succ h
                      have hk' : k + 1 < n + 1 := Nat.lt_of_succ_lt_succ hk
                      simpa [boundedVal, subst_realize, Nat.succ_eq_add_one] using
                        ih hmn ys (k + 1) hk'

theorem boolean_realize_bounded_formula_liftAt_insert {n l m : Nat} [Nonempty S]
    (h : m ≤ n) (f : bounded_preformula L n l) (v : dvector S n)
    (x : S) (xs : dvector S l) :
    boolean_realize_bounded_formula (dvector.insertAt m v x h) (f.liftAt 1 m) xs =
      boolean_realize_bounded_formula v f xs := by
  let default : S := Classical.choice (inferInstance : Nonempty S)
  let v₀ : Nat → S := boundedVal default v
  have hInserted :
      boolean_realize_bounded_formula (dvector.insertAt m v x h) (f.liftAt 1 m) xs =
        boolean_realize_formula (v₀[x // m]) (lift_formula_at f.fst 1 m) xs := by
    exact boolean_realize_bounded_formula_eq
      (v₁ := dvector.insertAt m v x h) (v₂ := v₀[x // m])
      (hv := by
        intro k hk
        exact boundedVal_insertAt h default x v k hk)
      (f := f.liftAt 1 m) (xs := xs)
  have hBase :
      boolean_realize_bounded_formula v f xs =
        boolean_realize_formula v₀ f.fst xs := by
    exact boolean_realize_bounded_formula_eq
      (v₁ := v) (v₂ := v₀)
      (hv := by
        intro k hk
        simp [v₀, boundedVal, hk])
      (f := f) (xs := xs)
  rw [hInserted, hBase]
  exact boolean_realize_formula_subst_lift (v := v₀) (x := x) (m := m)
    (f := f.fst) (xs := xs)

theorem boolean_realize_bounded_formula_liftAt_insert₂ {n l m : Nat} [Nonempty S]
    (h : m ≤ n) (f : bounded_preformula L n l) (v : dvector S n)
    (x y : S) (xs : dvector S l) :
    boolean_realize_bounded_formula
        (dvector.insertAt m (dvector.insertAt m v y h) x (Nat.le_succ_of_le h))
        (f.liftAt 2 m) xs =
      boolean_realize_bounded_formula v f xs := by
  have hfst :
      (f.liftAt 2 m).fst = ((f.liftAt 1 m).liftAt 1 m).fst := by
    simpa using
      (lift_formula_at2_medium (f := f.fst) (n := 1) 1 (m := m) (m' := m)
        le_rfl (Nat.le_add_right m 1)).symm
  rw [boolean_realize_bounded_formula_fst_eq hfst xs]
  rw [boolean_realize_bounded_formula_liftAt_insert
    (h := Nat.le_succ_of_le h) (f := f.liftAt 1 m)]
  exact boolean_realize_bounded_formula_liftAt_insert (h := h) (f := f) v y xs

theorem boolean_realize_bounded_formula_liftAt_insert₃ {n l m : Nat} [Nonempty S]
    (h : m ≤ n) (f : bounded_preformula L n l) (v : dvector S n)
    (x y z : S) (xs : dvector S l) :
    boolean_realize_bounded_formula
        (dvector.insertAt m
          (dvector.insertAt m (dvector.insertAt m v z h) y (Nat.le_succ_of_le h))
          x (Nat.le_succ_of_le (Nat.le_succ_of_le h)))
        (f.liftAt 3 m) xs =
      boolean_realize_bounded_formula v f xs := by
  have hfst :
      (f.liftAt 3 m).fst = ((f.liftAt 2 m).liftAt 1 m).fst := by
    simpa [Nat.add_assoc] using
      (lift_formula_at2_medium (f := f.fst) (n := 2) 1 (m := m) (m' := m)
        le_rfl (Nat.le_add_right m 2)).symm
  rw [boolean_realize_bounded_formula_fst_eq hfst xs]
  rw [boolean_realize_bounded_formula_liftAt_insert
    (h := Nat.le_succ_of_le (Nat.le_succ_of_le h)) (f := f.liftAt 2 m)]
  exact boolean_realize_bounded_formula_liftAt_insert₂ (h := h) (f := f) v y z xs

theorem boolean_realize_bounded_formula_subst_open {n l : Nat} [Nonempty S]
    (f : bounded_preformula L (n + 1) l) (t : bounded_term L n)
    (v : dvector S n) (xs : dvector S l) :
    boolean_realize_bounded_formula v (subst_bounded_formula_open f t) xs =
      boolean_realize_bounded_formula
        (boolean_realize_bounded_term v t [] :: v) f xs := by
  let default : S := Classical.choice (inferInstance : Nonempty S)
  let v₀ : Nat → S := boundedVal default v
  let tv : S := boolean_realize_bounded_term v t []
  have ht :
      boolean_realize_term v₀ t.fst [] = tv := by
    symm
    exact boolean_realize_bounded_term_eq
      (v₁ := v) (v₂ := v₀)
      (hv := by
        intro k hk
        simp [v₀, boundedVal, hk])
      (t := t) (xs := [])
  have hLeft :
      boolean_realize_bounded_formula v (subst_bounded_formula_open f t) xs =
        boolean_realize_formula v₀ (subst_formula f.fst t.fst 0) xs := by
    exact boolean_realize_bounded_formula_eq
      (v₁ := v) (v₂ := v₀)
      (hv := by
        intro k hk
        simp [v₀, boundedVal, hk])
      (f := subst_bounded_formula_open f t) (xs := xs)
  have hRight :
      boolean_realize_bounded_formula (tv :: v) f xs =
        boolean_realize_formula (v₀[boolean_realize_term v₀ t.fst [] // 0]) f.fst xs := by
    exact boolean_realize_bounded_formula_eq
      (v₁ := tv :: v)
      (v₂ := v₀[boolean_realize_term v₀ t.fst [] // 0])
      (hv := by
        intro k hk
        cases k with
        | zero =>
            exact ht.symm
        | succ k =>
            have hk' : k < n := Nat.lt_of_succ_lt_succ hk
            simp [v₀, boundedVal, hk', subst_realize])
      (f := f) (xs := xs)
  rw [hLeft, hRight]
  exact (boolean_realize_formula_subst0 (v := v₀) (f := f.fst) (s := t.fst) (xs := xs)).symm

theorem boolean_realize_bounded_formula_congr_head {n : Nat}
    (x y : S) (xs : dvector S n) (f : bounded_formula L (n + 1)) :
    S.eq x y ⊓ boolean_realize_bounded_formula (x :: xs) f [] ≤
      boolean_realize_bounded_formula (y :: xs) f [] := by
  let v₁ : Nat → S := boundedVal x (x :: xs)
  let v₂ : Nat → S := boundedVal y (y :: xs)
  have hv₁ : ∀ k (hk : k < n + 1), (x :: xs).nth k hk = v₁ k := by
    intro k hk
    simp [v₁, boundedVal, hk]
  have hv₂ : ∀ k (hk : k < n + 1), (y :: xs).nth k hk = v₂ k := by
    intro k hk
    simp [v₂, boundedVal, hk]
  have hEqVals : S.eq x y ≤ ⨅ k : Nat, S.eq (v₁ k) (v₂ k) := by
    apply le_iInf
    intro k
    by_cases hk : k < n + 1
    · cases k with
      | zero =>
          simp [v₁, v₂, boundedVal]
      | succ k =>
          have hk' : k < n := Nat.lt_of_succ_lt_succ hk
          simp [v₁, v₂, boundedVal, hk, hk', S.eq_refl]
    · simp [v₁, v₂, boundedVal, hk]
  have hCongr :
      (⨅ k : Nat, S.eq (v₁ k) (v₂ k)) ⊓
          boolean_realize_formula v₁ f.fst [] ≤
        boolean_realize_formula v₂ f.fst [] :=
    boolean_realize_formula_congr v₁ v₂ f.fst []
  have hBounded :
      boolean_realize_formula v₁ f.fst [] =
        boolean_realize_bounded_formula (x :: xs) f [] := by
    simpa [v₁] using
      (boolean_realize_bounded_formula_eq (v₁ := x :: xs) (v₂ := v₁)
        (hv := hv₁) (f := f) (xs := [])).symm
  have hBounded' :
      boolean_realize_formula v₂ f.fst [] =
        boolean_realize_bounded_formula (y :: xs) f [] := by
    simpa [v₂] using
      (boolean_realize_bounded_formula_eq (v₁ := y :: xs) (v₂ := v₂)
        (hv := hv₂) (f := f) (xs := [])).symm
  rw [hBounded.symm, hBounded'.symm]
  refine le_trans ?_ hCongr
  exact inf_le_inf hEqVals le_rfl

theorem boolean_realize_bounded_formula_congr_second {n : Nat}
    (z x y : S) (xs : dvector S n) (f : bounded_formula L (n + 2)) :
    S.eq x y ⊓ boolean_realize_bounded_formula (z :: x :: xs) f [] ≤
      boolean_realize_bounded_formula (z :: y :: xs) f [] := by
  let v₁ : Nat → S := boundedVal z (z :: x :: xs)
  let v₂ : Nat → S := boundedVal z (z :: y :: xs)
  have hv₁ : ∀ k (hk : k < n + 2), (z :: x :: xs).nth k hk = v₁ k := by
    intro k hk
    simp [v₁, boundedVal, hk]
  have hv₂ : ∀ k (hk : k < n + 2), (z :: y :: xs).nth k hk = v₂ k := by
    intro k hk
    simp [v₂, boundedVal, hk]
  have hEqVals : S.eq x y ≤ ⨅ k : Nat, S.eq (v₁ k) (v₂ k) := by
    apply le_iInf
    intro k
    by_cases hk : k < n + 2
    · cases k with
      | zero =>
          simp [v₁, v₂, boundedVal, S.eq_refl]
      | succ k =>
          cases k with
          | zero =>
              simp [v₁, v₂, boundedVal]
          | succ k =>
              have hk' : k < n := by omega
              simp [v₁, v₂, boundedVal, hk, hk', S.eq_refl]
    · simp [v₁, v₂, boundedVal, hk, S.eq_refl]
  have hCongr :
      (⨅ k : Nat, S.eq (v₁ k) (v₂ k)) ⊓
          boolean_realize_formula v₁ f.fst [] ≤
        boolean_realize_formula v₂ f.fst [] :=
    boolean_realize_formula_congr v₁ v₂ f.fst []
  have hBounded :
      boolean_realize_formula v₁ f.fst [] =
        boolean_realize_bounded_formula (z :: x :: xs) f [] := by
    simpa [v₁] using
      (boolean_realize_bounded_formula_eq (v₁ := z :: x :: xs) (v₂ := v₁)
        (hv := hv₁) (f := f) (xs := [])).symm
  have hBounded' :
      boolean_realize_formula v₂ f.fst [] =
        boolean_realize_bounded_formula (z :: y :: xs) f [] := by
    simpa [v₂] using
      (boolean_realize_bounded_formula_eq (v₁ := z :: y :: xs) (v₂ := v₂)
        (hv := hv₂) (f := f) (xs := [])).symm
  rw [hBounded.symm, hBounded'.symm]
  refine le_trans ?_ hCongr
  exact inf_le_inf hEqVals le_rfl

/-- Boolean truth value of a sentence. -/
@[reducible] def boolean_realize_sentence (S : bStructure L β) (f : sentence L) : β :=
  boolean_realize_bounded_formula (S := S) [] f []

notation "⟦" f "⟧[" S "]" => boolean_realize_sentence S f

theorem boolean_realize_sentence_eq (v : Nat → S) (f : sentence L) :
    boolean_realize_formula v (f : formula L) [] = ⟦f⟧[S] := by
  simpa [boolean_realize_sentence] using
    (boolean_realize_bounded_formula_eq (v₁ := []) (v₂ := v)
    (hv := by
      intro k hk
      exact False.elim (Nat.not_lt_zero k hk))
    (f := f) (xs := [])).symm

/-- Boolean truth value of an unbounded formula, universally over valuations. -/
def boolean_realize_formula_glb (S : bStructure L β) (f : formula L) : β :=
  ⨅ v : Nat → S, boolean_realize_formula v f []

notation "⟦" f "⟧[" S "]ᵤ" => boolean_realize_formula_glb S f

variable (β)

/-- Formula-level Boolean-valued semantic consequence. -/
def bstatisfied (T : Set (formula L)) (f : formula L) : Prop :=
  ∀ (S : bStructure.{u, v, w} L β) (v : Nat → S),
    (⨅ f' : formula L, ⨅ _ : f' ∈ T, boolean_realize_formula v f' []) ≤
      boolean_realize_formula v f []

notation T " ⊨ᵤ[" β "] " f => bstatisfied (β := β) T f

variable {β}

theorem bstatisfied_of_mem {T : Set (formula L)} {f : formula L} (hf : f ∈ T) :
    @bstatisfied.{u, v, w} L β _ T f := by
  intro S v
  exact (iInf_le (fun f' : formula L => ⨅ _ : f' ∈ T,
    boolean_realize_formula v f' []) f).trans (iInf_le _ hf)

theorem bstatisfied_weakening {T T' : Set (formula L)} (h : T ⊆ T')
    {f : formula L} (hf : @bstatisfied.{u, v, w} L β _ T f) :
    @bstatisfied.{u, v, w} L β _ T' f := by
  intro S v
  refine le_trans ?_ (hf S v)
  apply le_iInf
  intro g
  apply le_iInf
  intro hg
  exact (iInf_le (fun f' : formula L => ⨅ _ : f' ∈ T',
    boolean_realize_formula v f' []) g).trans (iInf_le _ (h hg))

theorem le_of_inf_compl_le_bot {a c : β} (h : c ⊓ aᶜ ≤ ⊥) : c ≤ a := by
  calc
    c = c ⊓ (a ⊔ aᶜ) := by rw [sup_compl_eq_top, inf_top_eq]
    _ = c ⊓ a ⊔ c ⊓ aᶜ := by rw [inf_sup_left]
    _ ≤ a ⊔ ⊥ := sup_le_sup inf_le_right h
    _ = a := by rw [sup_bot_eq]

@[simp] theorem boolean_realize_formula_not (v : Nat → S) (f : formula L) :
    boolean_realize_formula v (∼f) [] = (boolean_realize_formula v f [])ᶜ := by
  rw [fol.not]
  rw [boolean_realize_formula.eq_def]
  have hBot : boolean_realize_formula v (⊥ : formula L) [] = (⊥ : β) := by
    rw [boolean_realize_formula.eq_def]
  simp [hBot, lattice.imp]

theorem boolean_formula_soundness {Γ : Set (formula L)} {A : formula L}
    (h : Γ ⊢ A) : @bstatisfied.{u, v, w} L β _ Γ A := by
  induction h with
  | axm hmem =>
      exact bstatisfied_of_mem hmem
  | impI h ih =>
      intro S v
      rw [boolean_realize_formula, lattice.le_imp_iff]
      refine le_trans ?_ (ih S v)
      apply le_iInf
      intro g
      apply le_iInf
      intro hg
      simp only [Set.mem_insert_iff] at hg
      rcases hg with rfl | hg
      · exact inf_le_right
      · exact inf_le_left.trans
          ((iInf_le (fun f' : formula L => ⨅ _ : f' ∈ _,
            boolean_realize_formula v f' []) g).trans (iInf_le _ hg))
  | impE B hImp hA ihImp ihA =>
      intro S v
      have hImpVal := ihImp S v
      rw [boolean_realize_formula.eq_def] at hImpVal
      exact (le_inf le_rfl (ihA S v)).trans (lattice.le_imp_iff.mp hImpVal)
  | falsumE h ih =>
      intro S v
      apply le_of_inf_compl_le_bot
      have hbot := ih S v
      rw [boolean_realize_formula.eq_def] at hbot
      refine le_trans ?_ hbot
      apply le_iInf
      intro g
      apply le_iInf
      intro hg
      simp only [Set.mem_insert_iff] at hg
      rcases hg with rfl | hg
      · simp [boolean_realize_formula_not]
      · exact inf_le_left.trans
          ((iInf_le (fun f' : formula L => ⨅ _ : f' ∈ _,
            boolean_realize_formula v f' []) g).trans (iInf_le _ hg))
  | allI h ih =>
      intro S v
      simp only [boolean_realize_formula]
      apply le_iInf
      intro x
      refine le_trans ?_ (ih S (v[x // 0]))
      apply le_iInf
      intro g
      apply le_iInf
      intro hg
      rcases hg with ⟨g', hg', rfl⟩
      have hLift :
          boolean_realize_formula (v[x // 0]) (lift_formula1 g') [] =
            boolean_realize_formula v g' [] := by
        simpa [lift_formula1, lift_formula] using
          (boolean_realize_formula_subst_lift (v := v) (x := x) (m := 0)
            (f := g') (xs := []))
      have hCtx :
          (⨅ f' : formula L, ⨅ _ : f' ∈ _, boolean_realize_formula v f' []) ≤
            boolean_realize_formula v g' [] :=
        (iInf_le (fun f' : formula L => ⨅ _ : f' ∈ _,
          boolean_realize_formula v f' []) g').trans (iInf_le _ hg')
      simpa [hLift] using hCtx
  | allE₂ A t h ih =>
      intro S v
      rw [← boolean_realize_formula_subst0]
      exact (ih S v).trans (by
        simpa [boolean_realize_formula] using
          (iInf_le (fun x : S => boolean_realize_formula (v[x // 0]) A [])
            (boolean_realize_term v t [])))
  | ref Γ t =>
      intro S v
      simp [boolean_realize_formula, S.eq_refl]
  | subst₂ s t f hEq hSub ihEq ihSub =>
      intro S v
      refine le_trans ?_ (boolean_realize_formula_subst_congr0 (v := v)
        (s := s) (s' := t) (f := f) (xs := []))
      exact le_inf (by simpa [boolean_realize_formula] using ihEq S v) (ihSub S v)

@[simp] theorem boolean_realize_bounded_formula_falsum {n : Nat} {v : dvector S n} :
    boolean_realize_bounded_formula v (bd_falsum : bounded_formula L n) [] = ⊥ := by
  change boolean_realize_bounded_formula v (⟨preformula.falsum, trivial⟩ : bounded_formula L n) [] = ⊥
  unfold boolean_realize_bounded_formula
  rfl

@[simp] theorem boolean_realize_bounded_formula_equal {n : Nat} {v : dvector S n}
    (t₁ t₂ : bounded_term L n) :
    boolean_realize_bounded_formula v (bd_equal t₁ t₂) [] =
      S.eq (boolean_realize_bounded_term v t₁ []) (boolean_realize_bounded_term v t₂ []) := by
  simp [bd_equal, boolean_realize_bounded_formula]

@[simp] theorem boolean_realize_bounded_formula_imp {n : Nat} {v : dvector S n}
    (f₁ f₂ : bounded_formula L n) :
    boolean_realize_bounded_formula v (bd_imp f₁ f₂) [] =
      lattice.imp (boolean_realize_bounded_formula v f₁ [])
        (boolean_realize_bounded_formula v f₂ []) := by
  simp [bd_imp, boolean_realize_bounded_formula]

@[simp] theorem boolean_realize_bounded_formula_all {n : Nat} {v : dvector S n}
    (f : bounded_formula L (n + 1)) :
    boolean_realize_bounded_formula v (bd_all f) [] =
      ⨅ x : S, boolean_realize_bounded_formula (x :: v) f [] := by
  simp [bd_all, boolean_realize_bounded_formula]

@[simp] theorem boolean_realize_bounded_formula_not {n : Nat} {v : dvector S n}
    (f : bounded_formula L n) :
    boolean_realize_bounded_formula v (bd_not f) [] =
      (boolean_realize_bounded_formula v f [])ᶜ := by
  simp [bd_not, lattice.imp]

@[simp] theorem boolean_realize_bounded_formula_and {n : Nat} {v : dvector S n}
    (f₁ f₂ : bounded_formula L n) :
    boolean_realize_bounded_formula v (bd_and f₁ f₂) [] =
      boolean_realize_bounded_formula v f₁ [] ⊓ boolean_realize_bounded_formula v f₂ [] := by
  simp [bd_and, lattice.imp, compl_sup]

@[simp] theorem boolean_realize_bounded_formula_or {n : Nat} {v : dvector S n}
    (f₁ f₂ : bounded_formula L n) :
    boolean_realize_bounded_formula v (bd_or f₁ f₂) [] =
      boolean_realize_bounded_formula v f₁ [] ⊔ boolean_realize_bounded_formula v f₂ [] := by
  simp [bd_or, lattice.imp]

@[simp] theorem boolean_realize_bounded_formula_biimp {n : Nat} {v : dvector S n}
    (f₁ f₂ : bounded_formula L n) :
    boolean_realize_bounded_formula v (bd_biimp f₁ f₂) [] =
      lattice.biimp (boolean_realize_bounded_formula v f₁ [])
        (boolean_realize_bounded_formula v f₂ []) := by
  simp [bd_biimp, lattice.biimp]

@[simp] theorem boolean_realize_bounded_formula_ex {n : Nat} {v : dvector S n}
    (f : bounded_formula L (n + 1)) :
    boolean_realize_bounded_formula v (bd_ex f) [] =
      ⨆ x : S, boolean_realize_bounded_formula (x :: v) f [] := by
  simp [bd_ex, compl_iInf]

/-- A condition forces a sentence in a Boolean-valued structure. -/
def forces (Γ : β) (S : bStructure L β) (f : sentence L) : Prop :=
  Γ ≤ ⟦f⟧[S]

notation Γ " ⊩[" S "] " f => forces Γ S f

/-- A condition forces every axiom of a theory. -/
def forces_theory (Γ : β) (S : bStructure L β) (T : Theory L) : Prop :=
  Γ ≤ ⨅ f : sentence L, ⨅ _ : f ∈ T, ⟦f⟧[S]

notation Γ " ⊩[" S "] " T => forces_theory Γ S T

/-- Semantic consequence by Boolean-valued forcing. -/
def forced (T : Theory L) (f : sentence L) : Prop :=
  ∀ {S : bStructure.{u, v, w} L β}, Nonempty S →
    forces (⨅ f : sentence L, ⨅ _ : f ∈ T, ⟦f⟧[S]) S f

notation T " ⊨[" β "] " f => forced (β := β) T f

theorem forced_of_bsatisfied {T : Theory L} {f : sentence L}
    (h : @bstatisfied.{u, v, w} L β _ T.fst (f : formula L)) :
    @forced.{u, v, w} L β _ T f := by
  intro S hS
  rcases hS with ⟨s⟩
  change (⨅ g : sentence L, ⨅ _ : g ∈ T, ⟦g⟧[S]) ≤ ⟦f⟧[S]
  rw [← boolean_realize_sentence_eq (S := S) (v := fun _ => s) f]
  refine le_trans ?_ (h S (fun _ => s))
  apply le_iInf
  intro g
  apply le_iInf
  intro hg
  rcases hg with ⟨g', hg', rfl⟩
  exact ((iInf_le (fun g : sentence L => ⨅ _ : g ∈ T, ⟦g⟧[S]) g').trans
    (iInf_le _ hg')).trans (by
      rw [← boolean_realize_sentence_eq (S := S) (v := fun _ => s) g'])

@[simp] theorem inf_axioms_top_of_models {S : bStructure L β} {T : Theory L}
    (h : forces_theory (⊤ : β) S T) :
    (⨅ f : sentence L, ⨅ _ : f ∈ T, ⟦f⟧[S]) = ⊤ := by
  exact top_unique h

theorem forced_absurd {S : bStructure L β} {f : sentence L} {Γ : β}
    (hf : forces Γ S f) (hnf : forces Γ S (∼f)) :
    forces Γ S (⊥ : sentence L) := by
  have hbot : boolean_realize_bounded_formula (S := S) [] (⊥ : sentence L) [] = ⊥ := by
    change boolean_realize_bounded_formula (S := S) []
      (⟨preformula.falsum, trivial⟩ : sentence L) [] = ⊥
    unfold boolean_realize_bounded_formula
    rfl
  change Γ ≤ boolean_realize_bounded_formula (S := S) [] (⊥ : sentence L) []
  rw [hbot]
  have hnf' : Γ ≤ lattice.imp (⟦f⟧[S]) ⊥ := by
    simpa [forces, boolean_realize_sentence, sentence.not, sentence.imp, hbot]
      using hnf
  exact (le_inf le_rfl hf).trans (lattice.le_imp_iff.mp hnf')

theorem forced_not_not_of_forced {S : bStructure L β} {f : sentence L} {Γ : β}
    (hf : forces Γ S f) : forces Γ S (∼∼f) := by
  have hbot : boolean_realize_bounded_formula (S := S) [] (⊥ : sentence L) [] = ⊥ := by
    change boolean_realize_bounded_formula (S := S) []
      (⟨preformula.falsum, trivial⟩ : sentence L) [] = ⊥
    unfold boolean_realize_bounded_formula
    rfl
  simpa [forces, boolean_realize_sentence, sentence.not, sentence.imp, hbot, lattice.imp]
    using hf

variable (β)

/-- Boolean-valued models of a theory. -/
def bModel (T : Theory L) :=
  Σ' S : bStructure.{u, v, w} L β, forces_theory (⊤ : β) S T

variable {β}

theorem boolean_soundness {T : Theory L} {A : sentence L} (h : T ⊢ A) :
    @forced.{u, v, w} L β _ T A :=
  forced_of_bsatisfied (boolean_formula_soundness h)

lemma unprovable_of_model_neg {T : Theory L} {f : sentence L}
    (S : bStructure.{u, v, w} L β) (hModel : forces_theory (⊤ : β) S T)
    [Nonempty S] {Γ : β} (hNonzero : (⊥ : β) < Γ) (hNeg : forces Γ S (∼f)) :
    ¬ (T ⊢' f) := by
  intro hProv
  rcases hProv with ⟨hProv⟩
  have hfTop : forces (⊤ : β) S f := by
    simpa [inf_axioms_top_of_models hModel] using
      (boolean_soundness (β := β) hProv (S := S) (inferInstance : Nonempty S))
  have hfΓ : forces Γ S f :=
    le_top.trans hfTop
  have hBot : forces Γ S (⊥ : sentence L) :=
    forced_absurd hfΓ hNeg
  have hBotVal : Γ ≤ (⊥ : β) := by
    have hFalseVal :
        boolean_realize_bounded_formula (S := S) [] (⊥ : sentence L) [] = (⊥ : β) := by
      change boolean_realize_bounded_formula (S := S) []
        (⟨preformula.falsum, trivial⟩ : sentence L) [] = ⊥
      unfold boolean_realize_bounded_formula
      rfl
    simpa [forces, boolean_realize_sentence, hFalseVal] using hBot
  exact (not_lt_of_ge hBotVal) hNonzero

end bfol

export bfol (bStructure boolean_realize_term boolean_realize_formula
  boolean_realize_bounded_term boolean_realize_closed_term boolean_realize_bounded_formula
  boolean_realize_sentence boolean_realize_sentence_eq boolean_realize_formula_glb
  bstatisfied bstatisfied_of_mem bstatisfied_weakening forces forces_theory forced bModel
  forced_of_bsatisfied inf_axioms_top_of_models forced_absurd boolean_formula_soundness
  boolean_realize_bounded_formula_subst_open boolean_soundness forced_not_not_of_forced
  unprovable_of_model_neg)

end fol
end Flypitch
