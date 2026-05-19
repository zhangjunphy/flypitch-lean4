import Flypitch.BFOL
import Flypitch.Forcing
import Flypitch.ForcingCH

universe u

namespace Flypitch

set_option linter.missingDocs false
set_option linter.style.longLine false
set_option linter.dupNamespace false

open fol
open fol.bfol
open bSet
open scoped bSet

local notation "[]" => dvector.nil
local infixr:67 " :: " => dvector.cons

namespace ZFC

inductive ZFCRel : Nat → Type 1
  | epsilon : ZFCRel 2

inductive ZFCFunc : Nat → Type 1
  | emptyset : ZFCFunc 0
  | pair : ZFCFunc 2
  | omega : ZFCFunc 0
  | powerset : ZFCFunc 1
  | union : ZFCFunc 1

def L_ZFC : Language.{1} where
  functions := ZFCFunc
  relations := ZFCRel

variable {β : Type u} [CompleteBooleanAlgebra β]

def bSetModelFunMap : ∀ {n : Nat}, L_ZFC.functions n → dvector (bSet β) n → bSet β
  | _, ZFCFunc.emptyset, [] => ∅
  | _, ZFCFunc.pair, x :: y :: [] => bSet.pair x y
  | _, ZFCFunc.omega, [] => bSet.omega
  | _, ZFCFunc.powerset, x :: [] => bv_powerset x
  | _, ZFCFunc.union, x :: [] => bv_union x

def bSetModelRelMap : ∀ {n : Nat}, L_ZFC.relations n → dvector (bSet β) n → β
  | _, ZFCRel.epsilon, x :: y :: [] => x ∈ᴮ y

/-- The Boolean-valued universe as a first-order Boolean-valued ZFC structure. -/
def V (β : Type u) [CompleteBooleanAlgebra β] : bStructure L_ZFC β where
  carrier := bSet β
  fun_map := bSetModelFunMap
  rel_map := bSetModelRelMap
  eq := fun x y => x =ᴮ y
  eq_refl := bv_eq_refl
  eq_symm := by
    intro x y
    exact bv_eq_symm
  eq_trans := by
    intro x y z
    exact bv_eq_trans
  fun_congr := by
    intro n f x y
    cases f with
    | emptyset =>
        cases x
        cases y
        simp [bSetModelFunMap]
    | pair =>
        cases x with
        | cons x₀ xs =>
            cases xs with
            | cons x₁ xs =>
                cases xs
                cases y with
                | cons y₀ ys =>
                    cases ys with
                    | cons y₁ ys =>
                        cases ys
                        simp [bSetModelFunMap]
                        exact pair_congr inf_le_left inf_le_right
    | omega =>
        cases x
        cases y
        simp [bSetModelFunMap]
    | powerset =>
        cases x with
        | cons x₀ xs =>
            cases xs
            cases y with
            | cons y₀ ys =>
                cases ys
                simp [bSetModelFunMap]
                exact bv_powerset_congr le_rfl
    | union =>
        cases x with
        | cons x₀ xs =>
            cases xs
            cases y with
            | cons y₀ ys =>
                cases ys
                simp [bSetModelFunMap]
                exact bv_union_congr x₀ y₀
  rel_congr := by
    intro n R x y
    cases R
    cases x with
    | cons x₀ xs =>
        cases xs with
        | cons x₁ xs =>
            cases xs
            cases y with
            | cons y₀ ys =>
                cases ys with
                | cons y₁ ys =>
                    cases ys
                    simp [bSetModelRelMap]
                    let Γ : β := (x₀ =ᴮ y₀ ⊓ x₁ =ᴮ y₁) ⊓ x₀ ∈ᴮ x₁
                    change Γ ≤ y₀ ∈ᴮ y₁
                    have hxy : Γ ≤ x₀ =ᴮ y₀ := by
                      dsimp [Γ]
                      exact inf_le_left.trans inf_le_left
                    have hx₁y₁ : Γ ≤ x₁ =ᴮ y₁ := by
                      dsimp [Γ]
                      exact inf_le_left.trans inf_le_right
                    have hmem : Γ ≤ x₀ ∈ᴮ x₁ := by
                      dsimp [Γ]
                      exact inf_le_right
                    have hmem' : Γ ≤ y₀ ∈ᴮ x₁ :=
                      subst_congr_mem_left' hxy hmem
                    exact subst_congr_mem_right' hx₁y₁ hmem'

@[simp] theorem V_eq (a b : V β) : (V β).eq a b = (a : bSet β) =ᴮ (b : bSet β) := rfl

@[simp] theorem V_forall {C : V β → β} : (⨅ x : V β, C x) = ⨅ x : bSet β, C x := rfl

@[simp] theorem V_exists {C : V β → β} : (⨆ x : V β, C x) = ⨆ x : bSet β, C x := rfl

instance V_nonempty : Nonempty (V β) := ⟨(∅ : bSet β)⟩

def emptyset {n : Nat} : bounded_term L_ZFC n :=
  bd_const ZFCFunc.emptyset

def omega {n : Nat} : bounded_term L_ZFC n :=
  bd_const ZFCFunc.omega

def powerset {n : Nat} (t : bounded_term L_ZFC n) : bounded_term L_ZFC n :=
  bd_app (bd_func ZFCFunc.powerset) t

def union {n : Nat} (t : bounded_term L_ZFC n) : bounded_term L_ZFC n :=
  bd_app (bd_func ZFCFunc.union) t

def pair {n : Nat} (t₁ t₂ : bounded_term L_ZFC n) : bounded_term L_ZFC n :=
  bd_apps (bd_func ZFCFunc.pair) (t₁ :: t₂ :: [])

def mem {n : Nat} (t₁ t₂ : bounded_term L_ZFC n) : bounded_formula L_ZFC n :=
  bd_apps_rel (bd_rel ZFCRel.epsilon) (t₁ :: t₂ :: [])

/-- Close all currently free bounded variables by iterated universal quantification. -/
def bdAllsFrom : (n : Nat) → bounded_formula L_ZFC n → sentence L_ZFC
  | 0, f => f
  | n + 1, f => bdAllsFrom n (bd_all f)

@[simp] theorem boolean_realize_bdAllsFrom {n : Nat} (f : bounded_formula L_ZFC n) :
    ⟦bdAllsFrom n f⟧[V β] =
      ⨅ xs : dvector (V β) n, boolean_realize_bounded_formula (S := V β) xs f [] := by
  induction n with
  | zero =>
      simp [bdAllsFrom, boolean_realize_sentence]
      apply le_antisymm
      · apply le_iInf
        intro xs
        cases xs
        exact le_rfl
      · exact iInf_le _ []
  | succ n ih =>
      rw [bdAllsFrom, ih]
      simp [boolean_realize_bounded_formula_all]
      apply le_antisymm
      · apply le_iInf
        intro ys
        cases ys with
        | cons x xs =>
            exact (iInf_le _ xs).trans (iInf_le _ x)
      · apply le_iInf
        intro xs
        apply le_iInf
        intro x
        exact iInf_le _ (x :: xs)

def var {n : Nat} (k : Fin n) : bounded_term L_ZFC n :=
  bd_var k

def var0 {n : Nat} : bounded_term L_ZFC (n + 1) :=
  var ⟨0, by omega⟩

def var1 {n : Nat} : bounded_term L_ZFC (n + 2) :=
  var ⟨1, by omega⟩

def var2 {n : Nat} : bounded_term L_ZFC (n + 3) :=
  var ⟨2, by omega⟩

def var3 {n : Nat} : bounded_term L_ZFC (n + 4) :=
  var ⟨3, by omega⟩

def var4 {n : Nat} : bounded_term L_ZFC (n + 5) :=
  var ⟨4, by omega⟩

def subsetF {n : Nat} (t₁ t₂ : bounded_term L_ZFC n) : bounded_formula L_ZFC n :=
  bd_all (bd_imp (mem var0 t₁.lift1) (mem var0 t₂.lift1))

def axiomOfEmptyset : sentence L_ZFC :=
  bd_all (bd_not (mem var0 emptyset))

def axiomOfOrderedPairs : sentence L_ZFC :=
  bd_all (bd_all (bd_all (bd_all
    (bd_biimp (bd_equal (pair var3 var2) (pair var1 var0))
      (bd_and (bd_equal var3 var1) (bd_equal var2 var0))))))

def axiomOfExtensionality : sentence L_ZFC :=
  bd_all (bd_all
    (bd_imp (bd_all (bd_biimp (mem var0 var2) (mem var0 var1)))
      (bd_equal var1 var0)))

def axiomOfUnion : sentence L_ZFC :=
  bd_all (bd_all
    (bd_biimp (mem var0 (union var1))
      (bd_ex (bd_and (mem var0 var2) (mem var1 var0)))))

def axiomOfPowerset : sentence L_ZFC :=
  bd_all (bd_all
    (bd_biimp (mem var0 (powerset var1))
      (bd_all (bd_imp (mem var0 var1) (mem var0 var2)))))

def axiomOfCollection {n : Nat} (φ : bounded_formula L_ZFC (n + 2)) : sentence L_ZFC :=
  let premise : bounded_formula L_ZFC (n + 1) :=
    bd_all (bd_imp (mem var0 var1) (bd_ex (φ.liftAt 1 2)))
  let boundedImage : bounded_formula L_ZFC (n + 2) :=
    bd_and
      (bd_all (bd_imp (mem var0 var2)
        (bd_ex (bd_and (mem var0 var2) (φ.liftAt 2 2)))))
      (bd_all (bd_imp (mem var0 var1)
        (bd_ex (bd_and (mem var0 var3)
          (subst_bounded_formula_open (φ.liftAt 3 2) var1)))))
  bdAllsFrom (n + 1) (bd_imp premise (bd_ex boundedImage))

def isTransitiveF : bounded_formula L_ZFC 1 :=
  bd_all (bd_imp (mem var0 var1) (subsetF var0 var1))

def epsilonTrichotomyF : bounded_formula L_ZFC 1 :=
  bd_all (bd_imp (mem var0 var1)
    (bd_all (bd_imp (mem var0 var2)
      (bd_or (bd_or (bd_equal var1 var0) (mem var1 var0)) (mem var0 var1)))))

def epsilonWellFoundedF : bounded_formula L_ZFC 1 :=
  bd_all (bd_imp (subsetF var0 var1)
    (bd_imp (bd_not (bd_equal var0 emptyset))
      (bd_ex (bd_and (mem var0 var1)
        (bd_all (bd_imp (mem var0 var2) (bd_not (mem var0 var1))))))))

def ewoF : bounded_formula L_ZFC 1 :=
  bd_and epsilonTrichotomyF epsilonWellFoundedF

def OrdF : bounded_formula L_ZFC 1 :=
  bd_and ewoF isTransitiveF

def axiomOfInfinity : sentence L_ZFC :=
  bd_and
    (bd_and (mem emptyset omega)
      (bd_all (bd_imp (mem var0 omega)
        (bd_ex (bd_and (mem var0 omega) (mem var1 var0))))))
    (bd_and
      (bd_ex (bd_and OrdF (bd_equal omega var0)))
      (bd_all (bd_imp OrdF
        (bd_imp
          (bd_and (mem emptyset var0)
            (bd_all (bd_imp (mem var0 var1)
              (bd_ex (bd_and (mem var0 var2) (mem var1 var0))))))
          (subsetF omega var0)))))

def axiomOfRegularity : sentence L_ZFC :=
  bd_all (bd_imp (bd_not (bd_equal var0 emptyset))
    (bd_ex (bd_and (mem var0 var1)
      (bd_all (bd_imp (mem var0 var2) (bd_not (mem var0 var1)))))))

def zornsLemma : sentence L_ZFC :=
  bd_all (bd_imp (bd_not (bd_equal var0 emptyset))
    (bd_imp
      (bd_all (bd_imp
        (bd_and (subsetF var0 var1)
          (bd_all (bd_all
            (bd_imp (bd_and (mem var1 var2) (mem var0 var2))
              (bd_or (subsetF var1 var0) (subsetF var0 var1))))))
        (mem (union var0) var1)))
      (bd_ex (bd_and (mem var0 var1)
        (bd_all (bd_imp (mem var0 var2)
          (bd_imp (subsetF var1 var0) (bd_equal var1 var0))))))))

def isFuncF : bounded_formula L_ZFC 1 :=
  bd_all (bd_all (bd_all (bd_all
    (bd_imp (bd_and (mem (pair var3 var1) var4) (mem (pair var2 var0) var4))
      (bd_imp (bd_equal var3 var2) (bd_equal var1 var0))))))

def isTotalF : bounded_formula L_ZFC 3 :=
  bd_all (bd_imp (mem var0 var3)
    (bd_ex (bd_and (mem var0 var3) (mem (pair var1 var0) var2))))

def isTotalRevF : bounded_formula L_ZFC 3 :=
  bd_all (bd_imp (mem var0 var2)
    (bd_ex (bd_and (mem var0 var4) (mem (pair var1 var0) var2))))

def isFuncPrimeF : bounded_formula L_ZFC 3 :=
  bd_and (isFuncF.cast (by omega)) isTotalF

def isFuncPrimeRevF : bounded_formula L_ZFC 3 :=
  bd_and (isFuncF.cast (by omega)) isTotalRevF

def isInjF : bounded_formula L_ZFC 1 :=
  bd_all (bd_all (bd_all (bd_all
    (bd_imp (bd_and (bd_and (mem (pair var3 var1) var4) (mem (pair var2 var0) var4))
        (bd_equal var1 var0))
      (bd_equal var3 var2)))))

def injectsIntoF : bounded_formula L_ZFC 2 :=
  bd_ex (bd_and isFuncPrimeF (isInjF.cast (by omega)))

def nonEmptyF : bounded_formula L_ZFC 1 :=
  bd_not (bd_equal var0 emptyset)

def atMostF : bounded_formula L_ZFC 2 :=
  bd_ex (bd_ex (bd_and
    (bd_and (subsetF var1 var3) (isFuncPrimeRevF.cast (by omega)))
    (bd_all (bd_imp (mem var0 var3)
      (bd_ex (bd_and (mem var0 var3) (mem (pair var0 var1) var2)))))))

/-- A relation is total from a subset to `P(omega)`, with the codomain specialized syntactically. -/
def isFuncPrimePowersetOmegaRevF : bounded_formula L_ZFC 3 :=
  bd_and (isFuncF.cast (by omega))
    (bd_all (bd_imp (mem var0 var2)
      (bd_ex (bd_and (mem var0 (powerset omega)) (mem (pair var1 var0) var2)))))

def atMostOmegaF : bounded_formula L_ZFC 1 :=
  bd_ex (bd_ex (bd_and
    (bd_and (subsetF var1 omega) isFuncPrimeRevF)
    (bd_all (bd_imp (mem var0 var3)
      (bd_ex (bd_and (mem var0 var3) (mem (pair var0 var1) var2)))))))

def atMostPowersetOmegaF : bounded_formula L_ZFC 1 :=
  bd_ex (bd_ex (bd_and
    (bd_and (subsetF var1 var2) isFuncPrimePowersetOmegaRevF)
    (bd_all (bd_imp (mem var0 (powerset omega))
      (bd_ex (bd_and (mem var0 var3) (mem (pair var0 var1) var2)))))))

def CH_f : sentence L_ZFC :=
  bd_all (bd_imp OrdF (bd_or atMostOmegaF atMostPowersetOmegaF))

def ZFC : Theory L_ZFC :=
  ({axiomOfEmptyset, axiomOfOrderedPairs, axiomOfExtensionality, axiomOfUnion,
    axiomOfPowerset, axiomOfInfinity, axiomOfRegularity, zornsLemma} : Set (sentence L_ZFC)) ∪
  Set.iUnion (fun n : Nat =>
    (fun φ : bounded_formula L_ZFC (n + 2) => axiomOfCollection φ) '' Set.univ)

lemma B_ext_left_realize_bounded_formula {n : Nat}
    (φ : bounded_formula L_ZFC (n + 1)) (xs : dvector (V β) n) :
    B_ext (fun x : bSet β => boolean_realize_bounded_formula (S := V β) (x :: xs) φ []) := by
  intro x y
  exact boolean_realize_bounded_formula_congr_head (S := V β) x y xs φ

lemma B_ext_right_realize_bounded_formula {n : Nat}
    (φ : bounded_formula L_ZFC (n + 2)) (xs : dvector (V β) n) :
    ∀ x y z : bSet β,
      x =ᴮ y ⊓ boolean_realize_bounded_formula (S := V β) (z :: x :: xs) φ [] ≤
        boolean_realize_bounded_formula (S := V β) (z :: y :: xs) φ [] := by
  intro x y z
  exact boolean_realize_bounded_formula_congr_second (S := V β) z x y xs φ

@[simp] lemma boolean_realize_collection_liftAt1 {n : Nat}
    (φ : bounded_formula L_ZFC (n + 2)) (xs : dvector (V β) n)
    (x y u : V β) :
    boolean_realize_bounded_formula (S := V β) (y :: x :: u :: xs)
        (φ.liftAt 1 2) [] =
      boolean_realize_bounded_formula (S := V β) (y :: x :: xs) φ [] := by
  simpa [dvector.insertAt] using
    boolean_realize_bounded_formula_liftAt_insert (S := V β)
      (h := (by omega : 2 ≤ n + 2)) (f := φ) (v := y :: x :: xs) u []

@[simp] lemma boolean_realize_collection_liftAt2 {n : Nat}
    (φ : bounded_formula L_ZFC (n + 2)) (xs : dvector (V β) n)
    (x y B u : V β) :
    boolean_realize_bounded_formula (S := V β) (y :: x :: B :: u :: xs)
        (φ.liftAt 2 2) [] =
      boolean_realize_bounded_formula (S := V β) (y :: x :: xs) φ [] := by
  simpa [dvector.insertAt] using
    boolean_realize_bounded_formula_liftAt_insert₂ (S := V β)
      (h := (by omega : 2 ≤ n + 2)) (f := φ) (v := y :: x :: xs) B u []

@[simp] lemma boolean_realize_collection_liftAt3 {n : Nat}
    (φ : bounded_formula L_ZFC (n + 2)) (xs : dvector (V β) n)
    (x y z B u : V β) :
    boolean_realize_bounded_formula (S := V β) (y :: x :: z :: B :: u :: xs)
        (φ.liftAt 3 2) [] =
      boolean_realize_bounded_formula (S := V β) (y :: x :: xs) φ [] := by
  simpa [dvector.insertAt] using
    boolean_realize_bounded_formula_liftAt_insert₃ (S := V β)
      (h := (by omega : 2 ≤ n + 2)) (f := φ) (v := y :: x :: xs) z B u []

@[simp] lemma boolean_realize_collection_subst_liftAt3 {n : Nat}
    (φ : bounded_formula L_ZFC (n + 2)) (xs : dvector (V β) n)
    (x y B u : V β) :
    boolean_realize_bounded_formula (S := V β) (x :: y :: B :: u :: xs)
        (subst_bounded_formula_open (φ.liftAt 3 2) var1) [] =
      boolean_realize_bounded_formula (S := V β) (y :: x :: xs) φ [] := by
  rw [boolean_realize_bounded_formula_subst_open]
  simp [var1, var, bd_var]

def collectionSubstFormula {n : Nat} (φ : bounded_formula L_ZFC (n + 2)) :
    preformula L_ZFC 0 :=
  subst_formula (↑(bounded_preformula.liftAt φ 3 2))
    (↑(var1 : bounded_term L_ZFC (n + 4))) 0

@[simp] lemma boolean_realize_collection_subst_liftAt3_raw {n m : Nat}
    (φ : bounded_formula L_ZFC (n + 2)) (xs : dvector (V β) n)
    (x y B u : V β)
    (hBound :
      bounded_formula_at
        (subst_formula (φ.liftAt 3 2).fst (var1 (n := m)).fst 0)
        (n + 4)) :
    boolean_realize_bounded_formula (S := V β) (x :: y :: B :: u :: xs)
        (⟨subst_formula (φ.liftAt 3 2).fst (var1 (n := m)).fst 0,
          hBound⟩ : bounded_formula L_ZFC (n + 4)) [] =
      boolean_realize_bounded_formula (S := V β) (y :: x :: xs) φ [] := by
  have hterm :
      (↑(var1 (n := m)) : preterm L_ZFC 0) =
        (↑(var1 : bounded_term L_ZFC (n + 4)) : preterm L_ZFC 0) := by
    simp [var1, var, bd_var, bounded_preterm.fst]
  have hfst :
      bounded_preformula.fst
        (⟨subst_formula (φ.liftAt 3 2).fst (var1 (n := m)).fst 0,
          hBound⟩ : bounded_formula L_ZFC (n + 4)) =
        (subst_bounded_formula_open (φ.liftAt 3 2)
          (var1 : bounded_term L_ZFC (n + 4))).fst := by
    simpa [bounded_preformula.fst, subst_bounded_formula_open_fst] using
      congrArg (fun t => subst_formula (φ.liftAt 3 2).fst t 0) hterm
  rw [boolean_realize_bounded_formula_fst_eq hfst []]
  exact boolean_realize_collection_subst_liftAt3 φ xs x y B u

@[simp] lemma boolean_realize_collection_subst_liftAt3_named {n : Nat}
    (φ : bounded_formula L_ZFC (n + 2)) (xs : dvector (V β) n)
    (x y B u : V β)
    (hBound : bounded_formula_at (collectionSubstFormula φ) (n + 4)) :
    boolean_realize_bounded_formula (S := V β) (x :: y :: B :: u :: xs)
        (⟨collectionSubstFormula φ, hBound⟩ : bounded_formula L_ZFC (n + 4)) [] =
      boolean_realize_bounded_formula (S := V β) (y :: x :: xs) φ [] := by
  simpa [collectionSubstFormula, bounded_preformula.fst, bounded_preterm.fst] using
    boolean_realize_collection_subst_liftAt3_raw (β := β) (m := n + 2)
      φ xs x y B u hBound

@[simp] lemma boolean_realize_collection_subst_liftAt3_coe_mk {n : Nat}
    (φ : bounded_formula L_ZFC (n + 2)) (xs : dvector (V β) n)
    (x y B u : V β)
    (hBound :
      bounded_formula_at
        (subst_formula
          (↑(bounded_preformula.liftAt φ 3 2) : preformula L_ZFC 0)
          (↑(var1 (n := n + 2) : bounded_term L_ZFC (n + 4)) : term L_ZFC)
          0)
        (n + 4)) :
    boolean_realize_bounded_formula (S := V β) (x :: y :: B :: u :: xs)
        (⟨_, hBound⟩ : bounded_formula L_ZFC (n + 4)) [] =
      boolean_realize_bounded_formula (S := V β) (y :: x :: xs) φ [] := by
  simpa [bounded_preformula.fst, bounded_preterm.fst] using
    boolean_realize_collection_subst_liftAt3_raw (β := β) (m := n + 2)
      φ xs x y B u hBound

@[simp] lemma boolean_realize_collection_subst_liftAt3_of_eq {n : Nat}
    (φ : bounded_formula L_ZFC (n + 2)) (xs : dvector (V β) n)
    (x y B u : V β) {f : preformula L_ZFC 0}
    (hf : f = subst_formula (φ.liftAt 3 2).fst (var1 (n := n + 2)).fst 0)
    (hBound : bounded_formula_at f (n + 4)) :
    boolean_realize_bounded_formula (S := V β) (x :: y :: B :: u :: xs)
        (⟨f, hBound⟩ : bounded_formula L_ZFC (n + 4)) [] =
      boolean_realize_bounded_formula (S := V β) (y :: x :: xs) φ [] := by
  subst f
  exact boolean_realize_collection_subst_liftAt3_raw (β := β) (m := n + 2)
    φ xs x y B u hBound

@[simp] theorem boolean_realize_bounded_term_emptyset {n : Nat} {v : dvector (V β) n} :
    boolean_realize_bounded_term v (emptyset : bounded_term L_ZFC n) [] = (∅ : bSet β) :=
  by simp [emptyset, bd_const, bd_func, boolean_realize_bounded_term, V, bSetModelFunMap]

@[simp] theorem boolean_realize_bounded_term_omega {n : Nat} {v : dvector (V β) n} :
    boolean_realize_bounded_term v (omega : bounded_term L_ZFC n) [] = (bSet.omega : bSet β) :=
  by simp [omega, bd_const, bd_func, boolean_realize_bounded_term, V, bSetModelFunMap]

@[simp] theorem boolean_realize_bounded_term_powerset {n : Nat} {v : dvector (V β) n}
    (t : bounded_term L_ZFC n) :
    boolean_realize_bounded_term v (powerset t) [] =
      bv_powerset (boolean_realize_bounded_term v t []) :=
  by simp [powerset, bd_app, bd_func, boolean_realize_bounded_term, V, bSetModelFunMap]

@[simp] theorem boolean_realize_bounded_term_union {n : Nat} {v : dvector (V β) n}
    (t : bounded_term L_ZFC n) :
    boolean_realize_bounded_term v (union t) [] =
      bv_union (boolean_realize_bounded_term v t []) :=
  by simp [union, bd_app, bd_func, boolean_realize_bounded_term, V, bSetModelFunMap]

@[simp] theorem boolean_realize_bounded_term_pair {n : Nat} {v : dvector (V β) n}
    (t₁ t₂ : bounded_term L_ZFC n) :
    boolean_realize_bounded_term v (pair t₁ t₂) [] =
      bSet.pair (boolean_realize_bounded_term v t₁ [])
        (boolean_realize_bounded_term v t₂ []) :=
  by simp [pair, bd_apps, bd_app, bd_func, boolean_realize_bounded_term, V, bSetModelFunMap]

@[simp] theorem boolean_realize_bounded_term_var0 {n : Nat} {x : V β}
    {v : dvector (V β) n} :
    boolean_realize_bounded_term (x :: v) var0 [] = x := by
  simp [var0, var, bd_var, boolean_realize_bounded_term]

@[simp] theorem boolean_realize_bounded_term_var1 {n : Nat} {x₀ x₁ : V β}
    {v : dvector (V β) n} :
    boolean_realize_bounded_term (x₀ :: x₁ :: v) var1 [] = x₁ := by
  simp [var1, var, bd_var, boolean_realize_bounded_term]

@[simp] theorem boolean_realize_bounded_term_var2 {n : Nat} {x₀ x₁ x₂ : V β}
    {v : dvector (V β) n} :
    boolean_realize_bounded_term (x₀ :: x₁ :: x₂ :: v) var2 [] = x₂ := by
  simp [var2, var, bd_var, boolean_realize_bounded_term]

@[simp] theorem boolean_realize_bounded_term_var3 {n : Nat} {x₀ x₁ x₂ x₃ : V β}
    {v : dvector (V β) n} :
    boolean_realize_bounded_term (x₀ :: x₁ :: x₂ :: x₃ :: v) var3 [] = x₃ := by
  simp [var3, var, bd_var, boolean_realize_bounded_term]

@[simp] theorem boolean_realize_bounded_term_var4 {n : Nat} {x₀ x₁ x₂ x₃ x₄ : V β}
    {v : dvector (V β) n} :
    boolean_realize_bounded_term (x₀ :: x₁ :: x₂ :: x₃ :: x₄ :: v) var4 [] = x₄ := by
  simp [var4, var, bd_var, boolean_realize_bounded_term]

@[simp] theorem boolean_realize_bounded_term_bd_var0 {n : Nat} {x : V β}
    {v : dvector (V β) n} {h : 0 < n + 1} :
    boolean_realize_bounded_term (x :: v) (bd_var ⟨0, h⟩ : bounded_term L_ZFC (n + 1)) [] =
      x := by
  simp [bd_var, boolean_realize_bounded_term]

@[simp] theorem boolean_realize_bounded_term_bd_var1 {n : Nat} {x₀ x₁ : V β}
    {v : dvector (V β) n} {h : 1 < n + 2} :
    boolean_realize_bounded_term (x₀ :: x₁ :: v)
      (bd_var ⟨1, h⟩ : bounded_term L_ZFC (n + 2)) [] = x₁ := by
  simp [bd_var, boolean_realize_bounded_term]

@[simp] theorem boolean_realize_bounded_term_bd_var2 {n : Nat} {x₀ x₁ x₂ : V β}
    {v : dvector (V β) n} {h : 2 < n + 3} :
    boolean_realize_bounded_term (x₀ :: x₁ :: x₂ :: v)
      (bd_var ⟨2, h⟩ : bounded_term L_ZFC (n + 3)) [] = x₂ := by
  simp [bd_var, boolean_realize_bounded_term]

@[simp] theorem boolean_realize_bounded_term_bd_var3 {n : Nat} {x₀ x₁ x₂ x₃ : V β}
    {v : dvector (V β) n} {h : 3 < n + 4} :
    boolean_realize_bounded_term (x₀ :: x₁ :: x₂ :: x₃ :: v)
      (bd_var ⟨3, h⟩ : bounded_term L_ZFC (n + 4)) [] = x₃ := by
  simp [bd_var, boolean_realize_bounded_term]

@[simp] theorem boolean_realize_bounded_term_bd_var4 {n : Nat} {x₀ x₁ x₂ x₃ x₄ : V β}
    {v : dvector (V β) n} {h : 4 < n + 5} :
    boolean_realize_bounded_term (x₀ :: x₁ :: x₂ :: x₃ :: x₄ :: v)
      (bd_var ⟨4, h⟩ : bounded_term L_ZFC (n + 5)) [] = x₄ := by
  simp [bd_var, boolean_realize_bounded_term]

@[simp] theorem boolean_realize_bounded_formula_mem {n : Nat} {v : dvector (V β) n}
    (t₁ t₂ : bounded_term L_ZFC n) :
    boolean_realize_bounded_formula v (mem t₁ t₂) [] =
      boolean_realize_bounded_term v t₁ [] ∈ᴮ boolean_realize_bounded_term v t₂ [] :=
  by simp [mem, bd_apps_rel, bd_apprel, bd_rel, boolean_realize_bounded_formula, V, bSetModelRelMap]

@[simp] theorem boolean_realize_bounded_formula_subsetF {n : Nat} {v : dvector (V β) n}
    (t₁ t₂ : bounded_term L_ZFC n) :
    boolean_realize_bounded_formula v (subsetF t₁ t₂) [] =
      boolean_realize_bounded_term v t₁ [] ⊆ᴮ boolean_realize_bounded_term v t₂ [] := by
  apply le_antisymm
  · apply (subset_unfold').2
    simp [subsetF, var0, var, bd_var, boolean_realize_bounded_term]
  · have h :
        boolean_realize_bounded_term v t₁ [] ⊆ᴮ boolean_realize_bounded_term v t₂ [] ≤
          ⨅ z : bSet β,
            lattice.imp (z ∈ᴮ boolean_realize_bounded_term v t₁ [])
              (z ∈ᴮ boolean_realize_bounded_term v t₂ []) :=
      (subset_unfold').1 le_rfl
    simpa [subsetF, var0, var, bd_var, boolean_realize_bounded_term] using h

@[simp] theorem boolean_realize_bounded_formula_isTransitiveF {x : V β} :
    boolean_realize_bounded_formula (x :: []) isTransitiveF [] =
      is_transitive (x : bSet β) := by
  simp [isTransitiveF, is_transitive, var0, var1, var, bd_var, boolean_realize_bounded_term]

@[simp] theorem boolean_realize_bounded_formula_epsilonTrichotomyF {x : V β} :
    boolean_realize_bounded_formula (x :: []) epsilonTrichotomyF [] =
      epsilon_trichotomy (x : bSet β) := by
  simp [epsilonTrichotomyF, epsilon_trichotomy, var0, var1, var2, var, bd_var,
    boolean_realize_bounded_term, sup_assoc]

@[simp] theorem boolean_realize_bounded_formula_epsilonWellFoundedF {x : V β} :
    boolean_realize_bounded_formula (x :: []) epsilonWellFoundedF [] =
      epsilon_well_founded (x : bSet β) := by
  simp [epsilonWellFoundedF, epsilon_well_founded, var0, var1, var2, var, bd_var,
    boolean_realize_bounded_term]

@[simp] theorem boolean_realize_bounded_formula_ewoF {x : V β} :
    boolean_realize_bounded_formula (x :: []) ewoF [] =
      ewo (x : bSet β) := by
  simp [ewoF, ewo, epsilon_well_orders]

@[simp] theorem boolean_realize_bounded_formula_OrdF {x : V β} :
    boolean_realize_bounded_formula (x :: []) OrdF [] =
      bSet.Ord (x : bSet β) := by
  simp [OrdF, bSet.Ord, ewo]

@[simp] theorem boolean_realize_bounded_formula_isFuncF {f : V β} :
    boolean_realize_bounded_formula (f :: []) isFuncF [] =
      is_func (f : bSet β) := by
  simp [isFuncF, is_func, var0, var1, var2, var3, var4, var, bd_var,
    boolean_realize_bounded_term]

@[simp] theorem boolean_realize_bounded_formula_isTotalF {x y f : V β} :
    boolean_realize_bounded_formula (f :: y :: x :: []) isTotalF [] =
      is_total (x : bSet β) (y : bSet β) (f : bSet β) := by
  simp [isTotalF, is_total, var0, var1, var2, var3, var, bd_var,
    boolean_realize_bounded_term]

@[simp] theorem boolean_realize_bounded_formula_isTotalRevF {x y f : V β} :
    boolean_realize_bounded_formula (f :: y :: x :: []) isTotalRevF [] =
      is_total (y : bSet β) (x : bSet β) (f : bSet β) := by
  simp [isTotalRevF, is_total, var0, var1, var2, var4, var, bd_var,
    boolean_realize_bounded_term]

@[simp] theorem boolean_realize_bounded_formula_isInjF {f : V β} :
    boolean_realize_bounded_formula (f :: []) isInjF [] =
      is_inj (f : bSet β) := by
  simp [isInjF, is_inj, var0, var1, var2, var3, var4, var, bd_var,
    boolean_realize_bounded_term, inf_assoc]

@[simp] theorem boolean_realize_bounded_formula_isFuncF_cast3 {x y f : V β} :
    boolean_realize_bounded_formula (f :: y :: x :: [])
      (isFuncF.cast (by omega : 1 ≤ 3)) [] =
      is_func (f : bSet β) := by
  simp [dvector.take]

@[simp] theorem boolean_realize_bounded_formula_isFuncPrimeF {x y f : V β} :
    boolean_realize_bounded_formula (f :: y :: x :: []) isFuncPrimeF [] =
      is_func' (x : bSet β) (y : bSet β) (f : bSet β) := by
  simp [isFuncPrimeF, is_func', inf_comm, inf_left_comm, inf_assoc]

@[simp] theorem boolean_realize_bounded_formula_isFuncPrimeRevF {x y f : V β} :
    boolean_realize_bounded_formula (f :: y :: x :: []) isFuncPrimeRevF [] =
      is_func' (y : bSet β) (x : bSet β) (f : bSet β) := by
  simp [isFuncPrimeRevF, is_func', inf_comm, inf_left_comm, inf_assoc]

@[simp] theorem boolean_realize_bounded_formula_isInjF_cast3 {x y f : V β} :
    boolean_realize_bounded_formula (f :: y :: x :: [])
      (isInjF.cast (by omega : 1 ≤ 3)) [] =
      is_inj (f : bSet β) := by
  simp [dvector.take]

@[simp] theorem boolean_realize_bounded_formula_injectsIntoF {x y : V β} :
    boolean_realize_bounded_formula (y :: x :: []) injectsIntoF [] =
      injects_into (x : bSet β) (y : bSet β) := by
  simp [injectsIntoF, injects_into, inf_comm, inf_left_comm, inf_assoc]

@[simp] theorem boolean_realize_bounded_formula_isFuncPrimeRevF_cast4 {x y S f : V β} :
    boolean_realize_bounded_formula (f :: S :: y :: x :: [])
      (isFuncPrimeRevF.cast (by omega : 3 ≤ 4)) [] =
      is_func' (S : bSet β) (y : bSet β) (f : bSet β) := by
  simp [dvector.take]

@[simp] theorem boolean_realize_bounded_formula_atMostF {x y : V β} :
    boolean_realize_bounded_formula (y :: x :: []) atMostF [] =
      larger_than (x : bSet β) (y : bSet β) := by
  simp [atMostF, larger_than, is_surj, inf_comm, inf_left_comm, inf_assoc]

@[simp] theorem boolean_realize_bounded_formula_isFuncPrimePowersetOmegaRevF {x S f : V β} :
    boolean_realize_bounded_formula (f :: S :: x :: []) isFuncPrimePowersetOmegaRevF [] =
      is_func' (S : bSet β) (bv_powerset bSet.omega : bSet β) (f : bSet β) := by
  simp [isFuncPrimePowersetOmegaRevF, is_func', is_total, inf_comm, inf_left_comm, inf_assoc]

@[simp] theorem boolean_realize_bounded_formula_atMostOmegaF {x : V β} :
    boolean_realize_bounded_formula (x :: []) atMostOmegaF [] =
      larger_than (bSet.omega : bSet β) (x : bSet β) := by
  simp [atMostOmegaF, larger_than, is_surj, inf_comm, inf_left_comm, inf_assoc]

@[simp] theorem boolean_realize_bounded_formula_atMostPowersetOmegaF {x : V β} :
    boolean_realize_bounded_formula (x :: []) atMostPowersetOmegaF [] =
      larger_than (x : bSet β) (bv_powerset bSet.omega : bSet β) := by
  simp [atMostPowersetOmegaF, larger_than, is_surj, inf_comm, inf_left_comm, inf_assoc]

theorem CH_f_is_CH : ⟦CH_f⟧[V β] = CH₂ := by
  simp [CH_f, CH₂, compl_iSup, lattice.imp, inf_assoc, sup_assoc]

theorem CH_f_sound {Γ : β} : forces Γ (V β) CH_f ↔ Γ ≤ CH₂ := by
  change Γ ≤ ⟦CH_f⟧[V β] ↔ Γ ≤ CH₂
  rw [CH_f_is_CH]

theorem neg_CH_f_sound {Γ : β} : forces Γ (V β) (∼CH_f) ↔ Γ ≤ CH₂ᶜ := by
  have hbot : boolean_realize_bounded_formula (S := V β) [] (⊥ : sentence L_ZFC) [] = ⊥ := by
    change boolean_realize_bounded_formula (S := V β) []
      (⟨preformula.falsum, trivial⟩ : sentence L_ZFC) [] = ⊥
    unfold boolean_realize_bounded_formula
    rfl
  simp [forces, fol.sentence.not, fol.sentence.imp, boolean_realize_sentence,
    boolean_realize_bounded_formula, CH_f_is_CH, lattice.imp, hbot]

theorem bSet_models_emptyset : forces (⊤ : β) (V β) axiomOfEmptyset := by
  change (⊤ : β) ≤ ⟦axiomOfEmptyset⟧[V β]
  simp [axiomOfEmptyset, mem_empty, lattice.imp]

theorem bSet_models_ordered_pairs :
    forces (⊤ : β) (V β) axiomOfOrderedPairs := by
  change (⊤ : β) ≤ ⟦axiomOfOrderedPairs⟧[V β]
  simp [axiomOfOrderedPairs]
  intro x y z w
  apply top_le_iff.mp
  rw [lattice.bv_biimp_iff]
  intro Γ _
  constructor
  · intro h
    exact le_inf (eq_of_eq_pair_left' h) (eq_of_eq_pair_right' h)
  · intro h
    exact pair_congr (h.trans inf_le_left) (h.trans inf_le_right)

theorem bSet_models_extensionality :
    forces (⊤ : β) (V β) axiomOfExtensionality := by
  change (⊤ : β) ≤ ⟦axiomOfExtensionality⟧[V β]
  simp [axiomOfExtensionality]
  intro x y
  apply top_le_iff.mp
  apply lattice.bv_imp_intro
  exact mem_ext_of_biimp inf_le_right

theorem bSet_models_union : forces (⊤ : β) (V β) axiomOfUnion := by
  change (⊤ : β) ≤ ⟦axiomOfUnion⟧[V β]
  simp [axiomOfUnion]
  intro x z
  apply top_le_iff.mp
  rw [lattice.bv_biimp_iff]
  intro Γ _
  exact mem_bv_union_iff

theorem bSet_models_powerset :
    forces (⊤ : β) (V β) axiomOfPowerset := by
  change (⊤ : β) ≤ ⟦axiomOfPowerset⟧[V β]
  simp [axiomOfPowerset]
  intro z y
  apply top_le_iff.mp
  rw [lattice.bv_biimp_iff]
  intro Γ _
  constructor
  · intro h
    exact subset_unfold'.mp (bv_powerset_spec.mpr h)
  · intro h
    exact bv_powerset_spec.mp (subset_unfold'.mpr h)

theorem bSet_models_infinity : forces (⊤ : β) (V β) axiomOfInfinity := by
  change (⊤ : β) ≤ ⟦axiomOfInfinity⟧[V β]
  simp [axiomOfInfinity]
  constructor
  · have h := top_le_iff.mp (bSet_axiom_of_infinity' : (⊤ : β) ≤
      ((∅ : bSet β) ∈ᴮ (_root_.Flypitch.bSet.omega : bSet β)) ⊓
        (⨅ x : bSet β,
          lattice.imp (x ∈ᴮ (_root_.Flypitch.bSet.omega : bSet β))
            (⨆ y : bSet β, y ∈ᴮ (_root_.Flypitch.bSet.omega : bSet β) ⊓ x ∈ᴮ y)))
    simpa [lattice.imp] using h
  constructor
  · apply top_le_iff.mp
    apply le_iSup_of_le (_root_.Flypitch.bSet.omega : bSet β)
    exact le_inf Ord_omega (by rw [bv_eq_refl])
  · intro i
    apply top_le_iff.mp
    apply lattice.bv_imp_intro
    apply lattice.bv_imp_intro
    exact omega_subset_of_Ord_inductive
      (inf_le_left.trans inf_le_right)
      (inf_le_right.trans inf_le_left)
      (inf_le_right.trans inf_le_right)

theorem bSet_models_regularity :
    forces (⊤ : β) (V β) axiomOfRegularity := by
  change (⊤ : β) ≤ ⟦axiomOfRegularity⟧[V β]
  simp [axiomOfRegularity]
  intro x
  apply top_le_iff.mp
  apply lattice.bv_imp_intro
  exact bSet_axiom_of_regularity_unfolded x inf_le_right

set_option maxHeartbeats 1000000 in
-- The collection bridge unfolds several layers of bounded substitution and Boolean realization.
theorem bSet_models_collection {n : Nat} (φ : bounded_formula L_ZFC (n + 2)) :
    forces (⊤ : β) (V β) (axiomOfCollection φ) := by
  change (⊤ : β) ≤ ⟦axiomOfCollection φ⟧[V β]
  unfold axiomOfCollection
  rw [boolean_realize_bdAllsFrom]
  apply le_iInf
  intro xs
  cases xs with
  | cons u xs =>
      have h :=
        bSet_axiom_of_collection
          (fun x y : bSet β =>
            boolean_realize_bounded_formula (S := V β) (y :: x :: xs) φ [])
          (by
            intro x
            exact B_ext_left_realize_bounded_formula φ (x :: xs))
          (by
            intro y x x'
            exact B_ext_right_realize_bounded_formula φ xs x x' y)
          u
      convert h using 1 <;> simp [lattice.imp, boolean_realize_bounded_formula_liftAt_insert,
        boolean_realize_bounded_formula_liftAt_insert₂,
        boolean_realize_bounded_formula_liftAt_insert₃,
        boolean_realize_bounded_formula_subst_open,
        boolean_realize_collection_subst_liftAt3_raw,
        boolean_realize_collection_subst_liftAt3_named,
        boolean_realize_collection_subst_liftAt3_coe_mk,
        boolean_realize_collection_subst_liftAt3_of_eq,
        collectionSubstFormula, bounded_preformula.fst, bounded_preterm.fst,
        inf_comm, inf_left_comm, inf_assoc]

theorem bSet_models_zorn : forces (⊤ : β) (V β) zornsLemma := by
  change (⊤ : β) ≤ ⟦zornsLemma⟧[V β]
  simpa [zornsLemma] using (bSet_zorns_lemma' (Γ := (⊤ : β)))

theorem bSet_models_ZFC : forces_theory (⊤ : β) (V β) ZFC := by
  classical
  change (⊤ : β) ≤ ⨅ f : sentence L_ZFC, ⨅ _ : f ∈ ZFC, ⟦f⟧[V β]
  apply le_iInf
  intro f
  apply le_iInf
  intro hf
  change f ∈
    (({axiomOfEmptyset, axiomOfOrderedPairs, axiomOfExtensionality, axiomOfUnion,
      axiomOfPowerset, axiomOfInfinity, axiomOfRegularity, zornsLemma} :
        Set (sentence L_ZFC)) ∪
      Set.iUnion (fun n : Nat =>
        (fun φ : bounded_formula L_ZFC (n + 2) => axiomOfCollection φ) '' Set.univ)) at hf
  simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_iUnion,
    Set.mem_image, Set.mem_univ, true_and] at hf
  rcases hf with hbase | hcollection
  · rcases hbase with
    hf | hf | hf | hf | hf | hf | hf | hf
    · subst hf
      exact bSet_models_emptyset
    · subst hf
      exact bSet_models_ordered_pairs
    · subst hf
      exact bSet_models_extensionality
    · subst hf
      exact bSet_models_union
    · subst hf
      exact bSet_models_powerset
    · subst hf
      exact bSet_models_infinity
    · subst hf
      exact bSet_models_regularity
    · subst hf
      exact bSet_models_zorn
  · rcases hcollection with ⟨n, φ, _, rfl⟩
    exact bSet_models_collection φ

theorem neg_CH_f_unprovable : ¬ (ZFC ⊢' ∼CH_f) := by
  let β : Type := collapse_algebra.𝔹_collapse.{0}
  have hCH : forces (⊤ : β) (V β) CH_f :=
    (CH_f_sound (β := β) (Γ := ⊤)).2 collapse_algebra.CH₂_true
  have hNotNotCH : forces (⊤ : β) (V β) (∼∼CH_f) :=
    forced_not_not_of_forced hCH
  exact unprovable_of_model_neg (S := V β) (f := ∼CH_f)
    (bSet_models_ZFC (β := β)) (hNonzero := (bot_lt_top : (⊥ : β) < ⊤)) hNotNotCH

theorem CH_f_unprovable : ¬ (ZFC ⊢' CH_f) := by
  let β : Type := 𝔹_cohen.{0}
  have hNotCH : forces (⊤ : β) (V β) (∼CH_f) :=
    (neg_CH_f_sound (β := β) (Γ := ⊤)).2 not_CH₂
  exact unprovable_of_model_neg (S := V β) (f := CH_f)
    (bSet_models_ZFC (β := β)) (hNonzero := (bot_lt_top : (⊥ : β) < ⊤)) hNotCH

end ZFC

export ZFC (L_ZFC V emptyset omega powerset union pair mem subsetF isTransitiveF
  epsilonTrichotomyF epsilonWellFoundedF ewoF OrdF isFuncF isTotalF isFuncPrimeF
  isInjF injectsIntoF nonEmptyF atMostF atMostOmegaF atMostPowersetOmegaF CH_f
  CH_f_is_CH CH_f_sound neg_CH_f_sound bSet_models_emptyset bSet_models_ordered_pairs
  bSet_models_extensionality bSet_models_union bSet_models_powerset bSet_models_infinity
  bSet_models_regularity bSet_models_collection bSet_models_zorn bSet_models_ZFC
  neg_CH_f_unprovable CH_f_unprovable)

end Flypitch
