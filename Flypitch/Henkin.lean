import Flypitch.Colimit
import Flypitch.Completion
import Flypitch.LanguageExtension

universe u v

namespace Flypitch

open fol

/-!
`Flypitch.Henkin` constructs the omega-chain of language extensions that adjoin witness
constants, forms its colimit language `LInfty`, and compares the colimit syntax with the
bounded syntax already present in the tower. The later part of the file packages these maps
into the Henkin theory used by the completeness argument.
-/

set_option linter.missingDocs false
set_option linter.style.longLine false
set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false

namespace colimit

local infixr:80 " ∘ᴸ " => fol.Lhom.comp

private theorem hom_ext {L₁ L₂ : Language} {F G : L₁ →ᴸ L₂}
    (h_fun : ∀ n x, @Lhom.on_function _ _ F n x = @Lhom.on_function _ _ G n x)
    (h_rel : ∀ n x, @Lhom.on_relation _ _ F n x = @Lhom.on_relation _ _ G n x) : F = G := by
  cases F with
  | mk onfF onrF =>
      cases G with
      | mk onfG onrG =>
          have hF := funext (fun n => funext (fun x => h_fun n x))
          have hR := funext (fun n => funext (fun x => h_rel n x))
          cases hF
          cases hR
          rfl

structure directed_diagram_language (D : directed_type.{u}) : Type (max u v + 1) where
  obj : D.carrier → Language.{v}
  mor : ∀ {x y}, D.rel x y → ((obj x) →ᴸ (obj y))
  h_mor : ∀ {x y z} {f₁ : D.rel x y} {f₂ : D.rel y z} {f₃ : D.rel x z},
    mor f₃ = mor f₂ ∘ᴸ mor f₁

@[reducible] def diagram_functions {D : directed_type.{u}} {F : directed_diagram_language D}
    (n : Nat) : directed_diagram D :=
  { obj := fun x => (F.obj x).functions n
    mor := fun h => (F.mor h).on_function
    h_mor := by
      intro x y z f₁ f₂ f₃
      funext a
      simpa [Lhom.comp] using congrArg (fun ϕ => @Lhom.on_function _ _ ϕ n a)
        (F.h_mor (f₁ := f₁) (f₂ := f₂) (f₃ := f₃)) }

@[reducible] def diagram_relations {D : directed_type.{u}} {F : directed_diagram_language D}
    (n : Nat) : directed_diagram D :=
  { obj := fun x => (F.obj x).relations n
    mor := fun h => (F.mor h).on_relation
    h_mor := by
      intro x y z f₁ f₂ f₃
      funext a
      simpa [Lhom.comp] using congrArg (fun ϕ => @Lhom.on_relation _ _ ϕ n a)
        (F.h_mor (f₁ := f₁) (f₂ := f₂) (f₃ := f₃)) }

def colimit_language {D : directed_type.{u}} (F : directed_diagram_language D) : Language :=
  ⟨fun n => colimit (diagram_functions (F := F) n), fun n => colimit (diagram_relations (F := F) n)⟩

def canonical_map_language {D : directed_type.{u}} {F : directed_diagram_language D}
    (i : D.carrier) : F.obj i →ᴸ colimit_language F :=
  ⟨fun {n} => canonical_map (F := diagram_functions (F := F) n) i,
    fun {n} => canonical_map (F := diagram_relations (F := F) n) i⟩

structure cocone_language {D : directed_type.{u}} (F : directed_diagram_language D) where
  vertex : Language
  map : Π i : D.carrier, F.obj i →ᴸ vertex
  h_compat : ∀ {i j}, ∀ h : D.rel i j, map i = map j ∘ᴸ F.mor h

def cocone_of_colimit_language {D : directed_type.{u}} (F : directed_diagram_language D) :
    cocone_language F := by
  refine ⟨colimit_language F, canonical_map_language, ?_⟩
  intro i j h
  apply hom_ext
  · intro n x
    apply Quotient.sound
    have h_refl : D.rel j j := D.h_reflexive j
    refine ⟨j, (F.mor h).on_function x, h, h_refl, rfl, ?_⟩
    have hmor := congrArg (fun ϕ => @Lhom.on_function _ _ ϕ n x)
      (F.h_mor (f₁ := h) (f₂ := h_refl) (f₃ := h))
    simpa [Lhom.comp] using hmor.symm
  · intro n x
    apply Quotient.sound
    have h_refl : D.rel j j := D.h_reflexive j
    refine ⟨j, (F.mor h).on_relation x, h, h_refl, rfl, ?_⟩
    have hmor := congrArg (fun ϕ => @Lhom.on_relation _ _ ϕ n x)
      (F.h_mor (f₁ := h) (f₂ := h_refl) (f₃ := h))
    simpa [Lhom.comp] using hmor.symm

def universal_map_language {D : directed_type.{u}} {F : directed_diagram_language D}
    {V : cocone_language F} : colimit_language F →ᴸ V.vertex := by
  refine ⟨?_, ?_⟩
  · intro n
    refine Quotient.lift (fun p => (V.map p.1).on_function p.2) ?_
    intro p q hpq
    rcases p with ⟨i, x⟩
    rcases q with ⟨j, y⟩
    rcases hpq with ⟨k, z, f₁, f₂, h₁, h₂⟩
    calc
      (V.map i).on_function x = (V.map k).on_function ((F.mor f₁).on_function x) := by
        simpa [Lhom.comp] using congrArg (fun ϕ => @Lhom.on_function _ _ ϕ n x) (V.h_compat f₁)
      _ = (V.map k).on_function z := by
        simpa using congrArg (fun t => (V.map k).on_function t) h₁
      _ = (V.map k).on_function ((F.mor f₂).on_function y) := by
        simpa using congrArg (fun t => (V.map k).on_function t) h₂.symm
      _ = (V.map j).on_function y := by
        simpa [Lhom.comp] using congrArg (fun ϕ => @Lhom.on_function _ _ ϕ n y) (V.h_compat f₂).symm
  · intro n
    refine Quotient.lift (fun p => (V.map p.1).on_relation p.2) ?_
    intro p q hpq
    rcases p with ⟨i, x⟩
    rcases q with ⟨j, y⟩
    rcases hpq with ⟨k, z, f₁, f₂, h₁, h₂⟩
    calc
      (V.map i).on_relation x = (V.map k).on_relation ((F.mor f₁).on_relation x) := by
        simpa [Lhom.comp] using congrArg (fun ϕ => @Lhom.on_relation _ _ ϕ n x) (V.h_compat f₁)
      _ = (V.map k).on_relation z := by
        simpa using congrArg (fun t => (V.map k).on_relation t) h₁
      _ = (V.map k).on_relation ((F.mor f₂).on_relation y) := by
        simpa using congrArg (fun t => (V.map k).on_relation t) h₂.symm
      _ = (V.map j).on_relation y := by
        simpa [Lhom.comp] using congrArg (fun ϕ => @Lhom.on_relation _ _ ϕ n y) (V.h_compat f₂).symm

end colimit

namespace henkin

open colimit

local infixr:80 " ∘ᴸ " => Lhom.comp

inductive languageFunctions (L : Language.{u}) : Nat → Type u
  | inc : ∀ {n}, L.functions n → languageFunctions L n
  | wit : bounded_formula L 1 → languageFunctions L 0

@[reducible] def languageStep (L : Language.{u}) : Language.{u} :=
  ⟨languageFunctions L, L.relations⟩

def wit' {L : Language.{u}} : bounded_formula L 1 → (languageStep L).constants :=
  languageFunctions.wit

def inclusion {L : Language.{u}} : L →ᴸ languageStep L :=
  ⟨fun {_n} f => languageFunctions.inc f, fun {_n} R => R⟩

lemma inclusion_inj {L : Language.{u}} : Lhom.is_injective (@inclusion L) := by
  refine ⟨?_, ?_⟩
  · intro n x y hxy
    exact languageFunctions.inc.inj hxy
  · intro n x y hxy
    exact hxy

@[reducible] def chainObjects (L : Language.{u}) : Nat → Language.{u}
  | 0 => L
  | n + 1 => languageStep (chainObjects L n)

def chainMaps (L : Language.{u}) : ∀ x y, x ≤ y → ((chainObjects L x) →ᴸ (chainObjects L y))
  | x, 0, h => by
      have hx : x = 0 := Nat.eq_zero_of_le_zero h
      subst hx
      exact Lhom.id L
  | x, y + 1, h => by
      by_cases hxy : x = y + 1
      · subst hxy
        exact Lhom.id (chainObjects L (y + 1))
      · exact inclusion ∘ᴸ chainMaps L x y (Nat.lt_succ_iff.mp (lt_of_le_of_ne h hxy))

lemma chainMaps_comp (L : Language.{u}) :
    ∀ {x y z : Nat} (f₁ : x ≤ y) (f₂ : y ≤ z),
      chainMaps L x z (Nat.le_trans f₁ f₂) = chainMaps L y z f₂ ∘ᴸ chainMaps L x y f₁
  | x, y, 0, f₁, f₂ => by
      have hy : y = 0 := Nat.eq_zero_of_le_zero f₂
      have hx : x = 0 := Nat.eq_zero_of_le_zero (hy ▸ f₁)
      subst hy
      subst hx
      simp [chainMaps]
  | x, y, z + 1, f₁, f₂ => by
      by_cases hy : y = z + 1
      · subst hy
        by_cases hx : x = z + 1
        · subst hx
          simp [chainMaps]
        · simp [chainMaps, hx]
      · have hy' : y ≤ z := Nat.lt_succ_iff.mp (lt_of_le_of_ne f₂ hy)
        have hx : x ≠ z + 1 := by
          intro hx
          have hle : z + 1 ≤ z := by
            simpa [hx] using Nat.le_trans f₁ hy'
          exact Nat.not_succ_le_self z hle
        rw [chainMaps, dif_neg hx, chainMaps, dif_neg hy]
        rw [chainMaps_comp (L := L) f₁ hy']

lemma chainMaps_inj (L : Language.{u}) :
    ∀ x y (h : x ≤ y), Lhom.is_injective (chainMaps L x y h)
  | x, 0, h => by
      have hx : x = 0 := Nat.eq_zero_of_le_zero h
      subst hx
      refine ⟨?_, ?_⟩ <;> intro n a b hab <;> simpa [chainMaps] using hab
  | x, y + 1, h => by
      by_cases hxy : x = y + 1
      · subst hxy
        refine ⟨?_, ?_⟩ <;> intro n a b hab <;> simpa [chainMaps] using hab
      · have hxy' : x ≤ y := Nat.lt_succ_iff.mp (lt_of_le_of_ne h hxy)
        have ih := chainMaps_inj L x y hxy'
        refine ⟨?_, ?_⟩
        · intro n a b hab
          have hinc :
              inclusion.on_function ((chainMaps L x y hxy').on_function a) =
                inclusion.on_function ((chainMaps L x y hxy').on_function b) := by
            simpa [chainMaps, hxy, Lhom.comp] using hab
          have hmid :
              (chainMaps L x y hxy').on_function a = (chainMaps L x y hxy').on_function b :=
            (inclusion_inj (L := chainObjects L y)).on_function hinc
          exact ih.on_function hmid
        · intro n a b hab
          have hinc :
              inclusion.on_relation ((chainMaps L x y hxy').on_relation a) =
                inclusion.on_relation ((chainMaps L x y hxy').on_relation b) := by
            simpa [chainMaps, hxy, Lhom.comp] using hab
          have hmid :
              (chainMaps L x y hxy').on_relation a = (chainMaps L x y hxy').on_relation b :=
            (inclusion_inj (L := chainObjects L y)).on_relation hinc
          exact ih.on_relation hmid

def languageChain {L : Language.{u}} : directed_diagram_language ℕ' :=
  { obj := chainObjects L
    mor := fun h => chainMaps L _ _ h
    h_mor := by
      intro x y z f₁ f₂ f₃
      have hf₃ : f₃ = Nat.le_trans f₁ f₂ := Subsingleton.elim _ _
      subst hf₃
      exact chainMaps_comp (L := L) f₁ f₂ }

def LInfty (L : Language.{u}) : Language.{u} :=
  colimit_language (languageChain (L := L))

def canonicalMap {L : Language.{u}} (m : Nat) : chainObjects L m →ᴸ LInfty L :=
  canonical_map_language (F := languageChain (L := L)) m

lemma canonicalMap_inj {L : Language.{u}} (m : Nat) : Lhom.is_injective (@canonicalMap L m) := by
  refine ⟨?_, ?_⟩
  · intro n
    simpa [canonicalMap, canonical_map_language] using
      (canonical_map_inj_of_transition_maps_inj
        (D := ℕ') (F := diagram_functions (F := languageChain (L := L)) n) m
        (by
          intro i j h
          exact (chainMaps_inj L i j h).on_function))
  · intro n
    simpa [canonicalMap, canonical_map_language] using
      (canonical_map_inj_of_transition_maps_inj
        (D := ℕ') (F := diagram_relations (F := languageChain (L := L)) n) m
        (by
          intro i j h
          exact (chainMaps_inj L i j h).on_relation))

def termChain {L : Language.{u}} (l : Nat) : directed_diagram ℕ' :=
  { obj := fun k => preterm (chainObjects L k) l
    mor := fun h => Lhom.on_term (chainMaps L _ _ h)
    h_mor := by
      intro x y z f₁ f₂ f₃
      have hf₃ : f₃ = Nat.le_trans f₁ f₂ := Subsingleton.elim _ _
      subst hf₃
      funext t
      simp [chainMaps_comp (L := L) f₁ f₂] }

def formulaChain {L : Language.{u}} (l : Nat) : directed_diagram ℕ' :=
  { obj := fun k => preformula (chainObjects L k) l
    mor := fun h => Lhom.on_formula (chainMaps L _ _ h)
    h_mor := by
      intro x y z f₁ f₂ f₃
      have hf₃ : f₃ = Nat.le_trans f₁ f₂ := Subsingleton.elim _ _
      subst hf₃
      funext f
      simp [chainMaps_comp (L := L) f₁ f₂] }

def boundedTermChain {L : Language.{u}} (n l : Nat) : directed_diagram ℕ' :=
  { obj := fun k => bounded_preterm (chainObjects L k) n l
    mor := fun h => Lhom.on_bounded_term (chainMaps L _ _ h)
    h_mor := by
      intro x y z f₁ f₂ f₃
      have hf₃ : f₃ = Nat.le_trans f₁ f₂ := Subsingleton.elim _ _
      subst hf₃
      funext t
      simp [chainMaps_comp (L := L) f₁ f₂] }

@[reducible] def boundedTermChain' {L : Language.{u}} : directed_diagram ℕ' :=
  boundedTermChain (L := L) 1 0

def boundedFormulaChain {L : Language.{u}} (n l : Nat) : directed_diagram ℕ' :=
  { obj := fun k => bounded_preformula (chainObjects L k) n l
    mor := fun h => Lhom.on_bounded_formula (chainMaps L _ _ h)
    h_mor := by
      intro x y z f₁ f₂ f₃
      have hf₃ : f₃ = Nat.le_trans f₁ f₂ := Subsingleton.elim _ _
      subst hf₃
      funext f
      simp [chainMaps_comp (L := L) f₁ f₂] }

@[reducible] def boundedFormulaChain' {L : Language.{u}} : directed_diagram ℕ' :=
  boundedFormulaChain (L := L) 1 0

def coconeOfLInfty {L : Language.{u}} : cocone_language (languageChain (L := L)) :=
  cocone_of_colimit_language (languageChain (L := L))

def coconeOfTermLInfty {L : Language.{u}} (l : Nat) : cocone (termChain (L := L) l) := by
  refine ⟨preterm (LInfty L) l, fun i => Lhom.on_term (canonicalMap (L := L) i), ?_⟩
  intro i j h
  funext t
  have hmap := congrArg (fun ϕ => @Lhom.on_term _ _ ϕ l t) ((coconeOfLInfty (L := L)).h_compat h)
  calc
    Lhom.on_term (canonicalMap (L := L) i) t =
      Lhom.on_term (canonicalMap (L := L) j ∘ᴸ chainMaps L i j h) t := by
        simpa [coconeOfLInfty, canonicalMap, languageChain] using hmap
    _ = Lhom.on_term (canonicalMap (L := L) j) (Lhom.on_term (chainMaps L i j h) t) := by
        simp

def coconeOfFormulaLInfty {L : Language.{u}} (l : Nat) : cocone (formulaChain (L := L) l) := by
  refine ⟨preformula (LInfty L) l, fun i => Lhom.on_formula (canonicalMap (L := L) i), ?_⟩
  intro i j h
  funext f
  have hmap := congrArg (fun ϕ => @Lhom.on_formula _ _ ϕ l f) ((coconeOfLInfty (L := L)).h_compat h)
  calc
    Lhom.on_formula (canonicalMap (L := L) i) f =
      Lhom.on_formula (canonicalMap (L := L) j ∘ᴸ chainMaps L i j h) f := by
        simpa [coconeOfLInfty, canonicalMap, languageChain] using hmap
    _ = Lhom.on_formula (canonicalMap (L := L) j) (Lhom.on_formula (chainMaps L i j h) f) := by
        simp

def coconeOfBoundedTermLInfty {L : Language.{u}} (n l : Nat) :
    cocone (boundedTermChain (L := L) n l) := by
  refine ⟨bounded_preterm (LInfty L) n l, fun i => Lhom.on_bounded_term (canonicalMap (L := L) i), ?_⟩
  intro i j h
  funext t
  have hmap := congrArg (fun ϕ => @Lhom.on_bounded_term _ _ ϕ n l t) ((coconeOfLInfty (L := L)).h_compat h)
  calc
    Lhom.on_bounded_term (canonicalMap (L := L) i) t =
      Lhom.on_bounded_term (canonicalMap (L := L) j ∘ᴸ chainMaps L i j h) t := by
        simpa [coconeOfLInfty, canonicalMap, languageChain] using hmap
    _ = Lhom.on_bounded_term (canonicalMap (L := L) j) (Lhom.on_bounded_term (chainMaps L i j h) t) := by
        simp

def coconeOfBoundedFormulaLInfty {L : Language.{u}} (n l : Nat) :
    cocone (boundedFormulaChain (L := L) n l) := by
  refine ⟨bounded_preformula (LInfty L) n l, fun i => Lhom.on_bounded_formula (canonicalMap (L := L) i), ?_⟩
  intro i j h
  funext f
  have hmap := congrArg (fun ϕ => @Lhom.on_bounded_formula _ _ ϕ n l f) ((coconeOfLInfty (L := L)).h_compat h)
  calc
    Lhom.on_bounded_formula (canonicalMap (L := L) i) f =
      Lhom.on_bounded_formula (canonicalMap (L := L) j ∘ᴸ chainMaps L i j h) f := by
        simpa [coconeOfLInfty, canonicalMap, languageChain] using hmap
    _ = Lhom.on_bounded_formula (canonicalMap (L := L) j) (Lhom.on_bounded_formula (chainMaps L i j h) f) := by
        simp

def coconeOfBoundedFormulaPrimeLInfty {L : Language.{u}} :
    cocone (boundedFormulaChain' (L := L)) := by
  simpa [boundedFormulaChain'] using coconeOfBoundedFormulaLInfty (L := L) 1 0

def termComparison {L : Language.{u}} (l : Nat) :
    colimit (termChain (L := L) l) → preterm (LInfty L) l :=
  universal_map (F := termChain (L := L) l) (V := coconeOfTermLInfty (L := L) l)

def formulaComparison {L : Language.{u}} (l : Nat) :
    colimit (formulaChain (L := L) l) → preformula (LInfty L) l :=
  universal_map (F := formulaChain (L := L) l) (V := coconeOfFormulaLInfty (L := L) l)

def boundedTermComparison {L : Language.{u}} (n l : Nat) :
    colimit (boundedTermChain (L := L) n l) → bounded_preterm (LInfty L) n l :=
  universal_map (F := boundedTermChain (L := L) n l) (V := coconeOfBoundedTermLInfty (L := L) n l)

@[reducible] def boundedTermComparison' {L : Language.{u}} :
    colimit (boundedTermChain' (L := L)) → bounded_term (LInfty L) 1 :=
  boundedTermComparison (L := L) 1 0

def boundedFormulaComparison {L : Language.{u}} (n l : Nat) :
    colimit (boundedFormulaChain (L := L) n l) → bounded_preformula (LInfty L) n l :=
  universal_map (F := boundedFormulaChain (L := L) n l) (V := coconeOfBoundedFormulaLInfty (L := L) n l)

@[reducible] def boundedFormulaComparison' {L : Language.{u}} :
    colimit (boundedFormulaChain' (L := L)) → bounded_formula (LInfty L) 1 :=
  boundedFormulaComparison (L := L) 1 0

private theorem termComparison_surjective {L : Language.{u}} :
    {l : Nat} → (t : preterm (LInfty L) l) →
      ∃ x : colimit (termChain (L := L) l), termComparison l x = t
  | _, .var k => by
      refine ⟨canonical_map (F := termChain (L := L) 0) 0 (&k), ?_⟩
      simp [termComparison, coconeOfTermLInfty]
  | l, .func f => by
      rcases germ_rep f with ⟨⟨i, x⟩, hx⟩
      change (chainObjects L i).functions l at x
      refine ⟨canonical_map (F := termChain (L := L) l) i (preterm.func x), ?_⟩
      have hx' : (canonicalMap (L := L) i).on_function x = f := by
        simpa [canonicalMap, canonical_map_language] using hx
      simp [termComparison, coconeOfTermLInfty, hx']
  | l, .app t₁ t₂ => by
      rcases termComparison_surjective t₁ with ⟨u₁, hu₁⟩
      rcases termComparison_surjective t₂ with ⟨u₂, hu₂⟩
      rcases germ_rep u₁ with ⟨⟨i, x⟩, hx⟩
      rcases germ_rep u₂ with ⟨⟨j, y⟩, hy⟩
      refine ⟨canonical_map (F := termChain (L := L) l) (i + j)
        (preterm.app (push_to_sum_r (F := termChain (L := L) (l + 1)) x j)
          (push_to_sum_l (F := termChain (L := L) 0) y i)), ?_⟩
      have hx' :
          canonical_map (F := termChain (L := L) (l + 1)) i x = u₁ := by
        simpa [canonical_map] using hx
      have hy' :
          canonical_map (F := termChain (L := L) 0) j y = u₂ := by
        simpa [canonical_map] using hy
      have htx :
          termComparison (L := L) (l + 1)
            (canonical_map (F := termChain (L := L) (l + 1)) (i + j)
              (push_to_sum_r (F := termChain (L := L) (l + 1)) x j)) = t₁ := by
        calc
          termComparison (L := L) (l + 1)
              (canonical_map (F := termChain (L := L) (l + 1)) (i + j)
                (push_to_sum_r (F := termChain (L := L) (l + 1)) x j)) =
            termComparison (L := L) (l + 1)
              (canonical_map (F := termChain (L := L) (l + 1)) i x) := by
                rw [← same_fiber_as_push_to_r (F := termChain (L := L) (l + 1)) x j]
          _ = termComparison (L := L) (l + 1) u₁ := by rw [hx']
          _ = t₁ := hu₁
      have hty :
          termComparison (L := L) 0
            (canonical_map (F := termChain (L := L) 0) (i + j)
              (push_to_sum_l (F := termChain (L := L) 0) y i)) = t₂ := by
        calc
          termComparison (L := L) 0
              (canonical_map (F := termChain (L := L) 0) (i + j)
                (push_to_sum_l (F := termChain (L := L) 0) y i)) =
            termComparison (L := L) 0
              (canonical_map (F := termChain (L := L) 0) j y) := by
                rw [← same_fiber_as_push_to_l (F := termChain (L := L) 0) y i]
          _ = termComparison (L := L) 0 u₂ := by rw [hy']
          _ = t₂ := hu₂
      have htx' :
          (canonicalMap (L := L) (i + j)).on_term
            (push_to_sum_r (F := termChain (L := L) (l + 1)) x j) = t₁ := by
        simpa [termComparison, coconeOfTermLInfty] using htx
      have hty' :
          (canonicalMap (L := L) (i + j)).on_term
            (push_to_sum_l (F := termChain (L := L) 0) y i) = t₂ := by
        simpa [termComparison, coconeOfTermLInfty] using hty
      simpa [termComparison, coconeOfTermLInfty, htx', hty']

theorem termComparison_bijective {L : Language.{u}} (l : Nat) :
    Function.Bijective (@termComparison L l) := by
  refine ⟨?_, ?_⟩
  · unfold termComparison
    apply universal_map_inj_of_components_inj
    intro i
    dsimp [coconeOfTermLInfty]
    exact Lhom.on_term_inj (canonicalMap_inj (L := L) i)
  · intro t
    exact termComparison_surjective t

private theorem formulaComparison_surjective {L : Language.{u}} :
    {l : Nat} → (f : preformula (LInfty L) l) →
      ∃ x : colimit (formulaChain (L := L) l), formulaComparison l x = f
  | _, .falsum => by
      refine ⟨canonical_map (F := formulaChain (L := L) 0) 0 (preformula.falsum), ?_⟩
      change (⊥ : formula (LInfty L)) = preformula.falsum
      rfl
  | _, .equal t₁ t₂ => by
      rcases termComparison_surjective t₁ with ⟨u₁, hu₁⟩
      rcases termComparison_surjective t₂ with ⟨u₂, hu₂⟩
      rcases germ_rep u₁ with ⟨⟨i, x⟩, hx⟩
      rcases germ_rep u₂ with ⟨⟨j, y⟩, hy⟩
      refine ⟨canonical_map (F := formulaChain (L := L) 0) (i + j)
        (push_to_sum_r (F := termChain (L := L) 0) x j ≃
          push_to_sum_l (F := termChain (L := L) 0) y i), ?_⟩
      have hx' :
          canonical_map (F := termChain (L := L) 0) i x = u₁ := by
        simpa [canonical_map] using hx
      have hy' :
          canonical_map (F := termChain (L := L) 0) j y = u₂ := by
        simpa [canonical_map] using hy
      have htx :
          termComparison (L := L) 0
            (canonical_map (F := termChain (L := L) 0) (i + j)
              (push_to_sum_r (F := termChain (L := L) 0) x j)) = t₁ := by
        calc
          termComparison (L := L) 0
              (canonical_map (F := termChain (L := L) 0) (i + j)
                (push_to_sum_r (F := termChain (L := L) 0) x j)) =
            termComparison (L := L) 0
              (canonical_map (F := termChain (L := L) 0) i x) := by
                rw [← same_fiber_as_push_to_r (F := termChain (L := L) 0) x j]
          _ = termComparison (L := L) 0 u₁ := by rw [hx']
          _ = t₁ := hu₁
      have hty :
          termComparison (L := L) 0
            (canonical_map (F := termChain (L := L) 0) (i + j)
              (push_to_sum_l (F := termChain (L := L) 0) y i)) = t₂ := by
        calc
          termComparison (L := L) 0
              (canonical_map (F := termChain (L := L) 0) (i + j)
                (push_to_sum_l (F := termChain (L := L) 0) y i)) =
            termComparison (L := L) 0
              (canonical_map (F := termChain (L := L) 0) j y) := by
                rw [← same_fiber_as_push_to_l (F := termChain (L := L) 0) y i]
          _ = termComparison (L := L) 0 u₂ := by rw [hy']
          _ = t₂ := hu₂
      have htx' :
          (canonicalMap (L := L) (i + j)).on_term
            (push_to_sum_r (F := termChain (L := L) 0) x j) = t₁ := by
        simpa [termComparison, coconeOfTermLInfty] using htx
      have hty' :
          (canonicalMap (L := L) (i + j)).on_term
            (push_to_sum_l (F := termChain (L := L) 0) y i) = t₂ := by
        simpa [termComparison, coconeOfTermLInfty] using hty
      simpa [formulaComparison, coconeOfFormulaLInfty, htx', hty']
  | l, .rel R => by
      rcases germ_rep R with ⟨⟨i, x⟩, hx⟩
      change (chainObjects L i).relations l at x
      refine ⟨canonical_map (F := formulaChain (L := L) l) i (preformula.rel x), ?_⟩
      have hx' : (canonicalMap (L := L) i).on_relation x = R := by
        simpa [canonicalMap, canonical_map_language] using hx
      simp [formulaComparison, coconeOfFormulaLInfty, hx']
  | l, .apprel f t => by
      rcases formulaComparison_surjective f with ⟨u₁, hu₁⟩
      rcases termComparison_surjective t with ⟨u₂, hu₂⟩
      rcases germ_rep u₁ with ⟨⟨i, x⟩, hx⟩
      rcases germ_rep u₂ with ⟨⟨j, y⟩, hy⟩
      refine ⟨canonical_map (F := formulaChain (L := L) l) (i + j)
        (preformula.apprel
          (push_to_sum_r (F := formulaChain (L := L) (l + 1)) x j)
          (push_to_sum_l (F := termChain (L := L) 0) y i)), ?_⟩
      have hx' :
          canonical_map (F := formulaChain (L := L) (l + 1)) i x = u₁ := by
        simpa [canonical_map] using hx
      have hy' :
          canonical_map (F := termChain (L := L) 0) j y = u₂ := by
        simpa [canonical_map] using hy
      have hfx :
          formulaComparison (L := L) (l + 1)
            (canonical_map (F := formulaChain (L := L) (l + 1)) (i + j)
              (push_to_sum_r (F := formulaChain (L := L) (l + 1)) x j)) = f := by
        calc
          formulaComparison (L := L) (l + 1)
              (canonical_map (F := formulaChain (L := L) (l + 1)) (i + j)
                (push_to_sum_r (F := formulaChain (L := L) (l + 1)) x j)) =
            formulaComparison (L := L) (l + 1)
              (canonical_map (F := formulaChain (L := L) (l + 1)) i x) := by
                rw [← same_fiber_as_push_to_r (F := formulaChain (L := L) (l + 1)) x j]
          _ = formulaComparison (L := L) (l + 1) u₁ := by rw [hx']
          _ = f := hu₁
      have hty :
          termComparison (L := L) 0
            (canonical_map (F := termChain (L := L) 0) (i + j)
              (push_to_sum_l (F := termChain (L := L) 0) y i)) = t := by
        calc
          termComparison (L := L) 0
              (canonical_map (F := termChain (L := L) 0) (i + j)
                (push_to_sum_l (F := termChain (L := L) 0) y i)) =
            termComparison (L := L) 0
              (canonical_map (F := termChain (L := L) 0) j y) := by
                rw [← same_fiber_as_push_to_l (F := termChain (L := L) 0) y i]
          _ = termComparison (L := L) 0 u₂ := by rw [hy']
          _ = t := hu₂
      have hfx' :
          (canonicalMap (L := L) (i + j)).on_formula
            (push_to_sum_r (F := formulaChain (L := L) (l + 1)) x j) = f := by
        simpa [formulaComparison, coconeOfFormulaLInfty] using hfx
      have hty' :
          (canonicalMap (L := L) (i + j)).on_term
            (push_to_sum_l (F := termChain (L := L) 0) y i) = t := by
        simpa [termComparison, coconeOfTermLInfty] using hty
      simpa [formulaComparison, coconeOfFormulaLInfty, hfx', hty']
  | _, .imp f₁ f₂ => by
      rcases formulaComparison_surjective f₁ with ⟨u₁, hu₁⟩
      rcases formulaComparison_surjective f₂ with ⟨u₂, hu₂⟩
      rcases germ_rep u₁ with ⟨⟨i, x⟩, hx⟩
      rcases germ_rep u₂ with ⟨⟨j, y⟩, hy⟩
      refine ⟨canonical_map (F := formulaChain (L := L) 0) (i + j)
        (push_to_sum_r (F := formulaChain (L := L) 0) x j ⟹
          push_to_sum_l (F := formulaChain (L := L) 0) y i), ?_⟩
      have hx' :
          canonical_map (F := formulaChain (L := L) 0) i x = u₁ := by
        simpa [canonical_map] using hx
      have hy' :
          canonical_map (F := formulaChain (L := L) 0) j y = u₂ := by
        simpa [canonical_map] using hy
      have hfx :
          formulaComparison (L := L) 0
            (canonical_map (F := formulaChain (L := L) 0) (i + j)
              (push_to_sum_r (F := formulaChain (L := L) 0) x j)) = f₁ := by
        calc
          formulaComparison (L := L) 0
              (canonical_map (F := formulaChain (L := L) 0) (i + j)
                (push_to_sum_r (F := formulaChain (L := L) 0) x j)) =
            formulaComparison (L := L) 0
              (canonical_map (F := formulaChain (L := L) 0) i x) := by
                rw [← same_fiber_as_push_to_r (F := formulaChain (L := L) 0) x j]
          _ = formulaComparison (L := L) 0 u₁ := by rw [hx']
          _ = f₁ := hu₁
      have hgy :
          formulaComparison (L := L) 0
            (canonical_map (F := formulaChain (L := L) 0) (i + j)
              (push_to_sum_l (F := formulaChain (L := L) 0) y i)) = f₂ := by
        calc
          formulaComparison (L := L) 0
              (canonical_map (F := formulaChain (L := L) 0) (i + j)
                (push_to_sum_l (F := formulaChain (L := L) 0) y i)) =
            formulaComparison (L := L) 0
              (canonical_map (F := formulaChain (L := L) 0) j y) := by
                rw [← same_fiber_as_push_to_l (F := formulaChain (L := L) 0) y i]
          _ = formulaComparison (L := L) 0 u₂ := by rw [hy']
          _ = f₂ := hu₂
      have hfx' :
          (canonicalMap (L := L) (i + j)).on_formula
            (push_to_sum_r (F := formulaChain (L := L) 0) x j) = f₁ := by
        simpa [formulaComparison, coconeOfFormulaLInfty] using hfx
      have hgy' :
          (canonicalMap (L := L) (i + j)).on_formula
            (push_to_sum_l (F := formulaChain (L := L) 0) y i) = f₂ := by
        simpa [formulaComparison, coconeOfFormulaLInfty] using hgy
      simpa [formulaComparison, coconeOfFormulaLInfty, hfx', hgy']
  | _, .all f => by
      rcases formulaComparison_surjective f with ⟨u, hu⟩
      rcases germ_rep u with ⟨⟨i, x⟩, hx⟩
      refine ⟨canonical_map (F := formulaChain (L := L) 0) i (∀' x), ?_⟩
      have hx' : canonical_map (F := formulaChain (L := L) 0) i x = u := by
        simpa [canonical_map] using hx
      have hfx : formulaComparison (L := L) 0
          (canonical_map (F := formulaChain (L := L) 0) i x) = f := by
        rw [hx']
        exact hu
      have hfx' : (canonicalMap (L := L) i).on_formula x = f := by
        simpa [formulaComparison, coconeOfFormulaLInfty] using hfx
      simpa [formulaComparison, coconeOfFormulaLInfty, hfx']

theorem formulaComparison_bijective {L : Language.{u}} (l : Nat) :
    Function.Bijective (@formulaComparison L l) := by
  refine ⟨?_, ?_⟩
  · unfold formulaComparison
    apply universal_map_inj_of_components_inj
    intro i
    dsimp [coconeOfFormulaLInfty]
    exact Lhom.on_formula_inj (canonicalMap_inj (L := L) i)
  · intro f
    exact formulaComparison_surjective f

private theorem boundedTermComparison_surjective {L : Language.{u}} :
    {n l : Nat} → (t : bounded_preterm (LInfty L) n l) →
      ∃ x : colimit (boundedTermChain (L := L) n l), boundedTermComparison n l x = t
  | n, _, ⟨.var k, hk⟩ => by
      refine ⟨canonical_map (F := boundedTermChain (L := L) n 0) 0 (bd_var ⟨k, hk⟩), ?_⟩
      simp [boundedTermComparison, coconeOfBoundedTermLInfty, bd_var]
  | n, l, ⟨.func f, _⟩ => by
      rcases germ_rep f with ⟨⟨i, x⟩, hx⟩
      change (chainObjects L i).functions l at x
      refine ⟨canonical_map (F := boundedTermChain (L := L) n l) i (bd_func x), ?_⟩
      have hx' : (canonicalMap (L := L) i).on_function x = f := by
        simpa [canonicalMap, canonical_map_language] using hx
      apply Subtype.ext
      simp [boundedTermComparison, coconeOfBoundedTermLInfty, bd_func, hx']
  | n, l, ⟨.app t s, hts⟩ => by
      rcases boundedTermComparison_surjective ⟨t, hts.1⟩ with ⟨u₁, hu₁⟩
      rcases boundedTermComparison_surjective ⟨s, hts.2⟩ with ⟨u₂, hu₂⟩
      rcases germ_rep u₁ with ⟨⟨i, x⟩, hx⟩
      rcases germ_rep u₂ with ⟨⟨j, y⟩, hy⟩
      refine ⟨canonical_map (F := boundedTermChain (L := L) n l) (i + j)
        (bd_app (push_to_sum_r (F := boundedTermChain (L := L) n (l + 1)) x j)
          (push_to_sum_l (F := boundedTermChain (L := L) n 0) y i)), ?_⟩
      have hx' :
          canonical_map (F := boundedTermChain (L := L) n (l + 1)) i x = u₁ := by
        simpa [canonical_map] using hx
      have hy' :
          canonical_map (F := boundedTermChain (L := L) n 0) j y = u₂ := by
        simpa [canonical_map] using hy
      have htx :
          boundedTermComparison (L := L) n (l + 1)
            (canonical_map (F := boundedTermChain (L := L) n (l + 1)) (i + j)
              (push_to_sum_r (F := boundedTermChain (L := L) n (l + 1)) x j)) = ⟨t, hts.1⟩ := by
        calc
          boundedTermComparison (L := L) n (l + 1)
              (canonical_map (F := boundedTermChain (L := L) n (l + 1)) (i + j)
                (push_to_sum_r (F := boundedTermChain (L := L) n (l + 1)) x j)) =
            boundedTermComparison (L := L) n (l + 1)
              (canonical_map (F := boundedTermChain (L := L) n (l + 1)) i x) := by
                rw [← same_fiber_as_push_to_r (F := boundedTermChain (L := L) n (l + 1)) x j]
          _ = boundedTermComparison (L := L) n (l + 1) u₁ := by rw [hx']
          _ = ⟨t, hts.1⟩ := hu₁
      have hty :
          boundedTermComparison (L := L) n 0
            (canonical_map (F := boundedTermChain (L := L) n 0) (i + j)
              (push_to_sum_l (F := boundedTermChain (L := L) n 0) y i)) = ⟨s, hts.2⟩ := by
        calc
          boundedTermComparison (L := L) n 0
              (canonical_map (F := boundedTermChain (L := L) n 0) (i + j)
                (push_to_sum_l (F := boundedTermChain (L := L) n 0) y i)) =
            boundedTermComparison (L := L) n 0
              (canonical_map (F := boundedTermChain (L := L) n 0) j y) := by
                rw [← same_fiber_as_push_to_l (F := boundedTermChain (L := L) n 0) y i]
          _ = boundedTermComparison (L := L) n 0 u₂ := by rw [hy']
          _ = ⟨s, hts.2⟩ := hu₂
      have htx' :
          (canonicalMap (L := L) (i + j)).on_bounded_term
            (push_to_sum_r (F := boundedTermChain (L := L) n (l + 1)) x j) = ⟨t, hts.1⟩ := by
        simpa [boundedTermComparison, coconeOfBoundedTermLInfty] using htx
      have hty' :
          (canonicalMap (L := L) (i + j)).on_bounded_term
            (push_to_sum_l (F := boundedTermChain (L := L) n 0) y i) = ⟨s, hts.2⟩ := by
        simpa [boundedTermComparison, coconeOfBoundedTermLInfty] using hty
      have htxv :
          ((canonicalMap (L := L) (i + j)).on_bounded_term
            (push_to_sum_r (F := boundedTermChain (L := L) n (l + 1)) x j)).1 = t := by
        simpa using congrArg Subtype.val htx'
      have htyv :
          ((canonicalMap (L := L) (i + j)).on_bounded_term
            (push_to_sum_l (F := boundedTermChain (L := L) n 0) y i)).1 = s := by
        simpa using congrArg Subtype.val hty'
      have htxt :
          (canonicalMap (L := L) (i + j)).on_term
            (push_to_sum_r (F := boundedTermChain (L := L) n (l + 1)) x j).1 = t := by
        simpa using htxv
      have htys :
          (canonicalMap (L := L) (i + j)).on_term
            (push_to_sum_l (F := boundedTermChain (L := L) n 0) y i).1 = s := by
        simpa using htyv
      apply Subtype.ext
      simpa [boundedTermComparison, coconeOfBoundedTermLInfty, bd_app] using And.intro htxt htys
termination_by
  n l t => sizeOf t.1
decreasing_by
  all_goals
    try simp_wf
    try omega

theorem boundedTermComparison_bijective {L : Language.{u}} (n l : Nat) :
    Function.Bijective (@boundedTermComparison L n l) := by
  refine ⟨?_, ?_⟩
  · unfold boundedTermComparison
    apply universal_map_inj_of_components_inj
    intro i
    dsimp [coconeOfBoundedTermLInfty]
    exact Lhom.on_bounded_term_inj (canonicalMap_inj (L := L) i)
  · intro t
    exact boundedTermComparison_surjective t

private theorem boundedFormulaComparison_surjective {L : Language.{u}} :
    {n l : Nat} → (f : bounded_preformula (LInfty L) n l) →
      ∃ x : colimit (boundedFormulaChain (L := L) n l), boundedFormulaComparison n l x = f
  | n, _, ⟨.falsum, _⟩ => by
      refine ⟨canonical_map (F := boundedFormulaChain (L := L) n 0) 0 (bd_falsum), ?_⟩
      apply Subtype.ext
      rfl
  | n, _, ⟨.equal t₁ t₂, hts⟩ => by
      rcases boundedTermComparison_surjective ⟨t₁, hts.1⟩ with ⟨u₁, hu₁⟩
      rcases boundedTermComparison_surjective ⟨t₂, hts.2⟩ with ⟨u₂, hu₂⟩
      rcases germ_rep u₁ with ⟨⟨i, x⟩, hx⟩
      rcases germ_rep u₂ with ⟨⟨j, y⟩, hy⟩
      refine ⟨canonical_map (F := boundedFormulaChain (L := L) n 0) (i + j)
        (bd_equal (push_to_sum_r (F := boundedTermChain (L := L) n 0) x j)
          (push_to_sum_l (F := boundedTermChain (L := L) n 0) y i)), ?_⟩
      have hx' :
          canonical_map (F := boundedTermChain (L := L) n 0) i x = u₁ := by
        simpa [canonical_map] using hx
      have hy' :
          canonical_map (F := boundedTermChain (L := L) n 0) j y = u₂ := by
        simpa [canonical_map] using hy
      have htx :
          boundedTermComparison (L := L) n 0
            (canonical_map (F := boundedTermChain (L := L) n 0) (i + j)
              (push_to_sum_r (F := boundedTermChain (L := L) n 0) x j)) = ⟨t₁, hts.1⟩ := by
        calc
          boundedTermComparison (L := L) n 0
              (canonical_map (F := boundedTermChain (L := L) n 0) (i + j)
                (push_to_sum_r (F := boundedTermChain (L := L) n 0) x j)) =
            boundedTermComparison (L := L) n 0
              (canonical_map (F := boundedTermChain (L := L) n 0) i x) := by
                rw [← same_fiber_as_push_to_r (F := boundedTermChain (L := L) n 0) x j]
          _ = boundedTermComparison (L := L) n 0 u₁ := by rw [hx']
          _ = ⟨t₁, hts.1⟩ := hu₁
      have hty :
          boundedTermComparison (L := L) n 0
            (canonical_map (F := boundedTermChain (L := L) n 0) (i + j)
              (push_to_sum_l (F := boundedTermChain (L := L) n 0) y i)) = ⟨t₂, hts.2⟩ := by
        calc
          boundedTermComparison (L := L) n 0
              (canonical_map (F := boundedTermChain (L := L) n 0) (i + j)
                (push_to_sum_l (F := boundedTermChain (L := L) n 0) y i)) =
            boundedTermComparison (L := L) n 0
              (canonical_map (F := boundedTermChain (L := L) n 0) j y) := by
                rw [← same_fiber_as_push_to_l (F := boundedTermChain (L := L) n 0) y i]
          _ = boundedTermComparison (L := L) n 0 u₂ := by rw [hy']
          _ = ⟨t₂, hts.2⟩ := hu₂
      have htx' :
          (canonicalMap (L := L) (i + j)).on_bounded_term
            (push_to_sum_r (F := boundedTermChain (L := L) n 0) x j) = ⟨t₁, hts.1⟩ := by
        simpa [boundedTermComparison, coconeOfBoundedTermLInfty] using htx
      have hty' :
          (canonicalMap (L := L) (i + j)).on_bounded_term
            (push_to_sum_l (F := boundedTermChain (L := L) n 0) y i) = ⟨t₂, hts.2⟩ := by
        simpa [boundedTermComparison, coconeOfBoundedTermLInfty] using hty
      have htxv :
          ((canonicalMap (L := L) (i + j)).on_bounded_term
            (push_to_sum_r (F := boundedTermChain (L := L) n 0) x j)).1 = t₁ := by
        simpa using congrArg Subtype.val htx'
      have htyv :
          ((canonicalMap (L := L) (i + j)).on_bounded_term
            (push_to_sum_l (F := boundedTermChain (L := L) n 0) y i)).1 = t₂ := by
        simpa using congrArg Subtype.val hty'
      have htxt :
          (canonicalMap (L := L) (i + j)).on_term
            (push_to_sum_r (F := boundedTermChain (L := L) n 0) x j).1 = t₁ := by
        simpa using htxv
      have htyt :
          (canonicalMap (L := L) (i + j)).on_term
            (push_to_sum_l (F := boundedTermChain (L := L) n 0) y i).1 = t₂ := by
        simpa using htyv
      apply Subtype.ext
      simpa [boundedFormulaComparison, coconeOfBoundedFormulaLInfty, bd_equal] using
        And.intro htxt htyt
  | n, l, ⟨.rel R, _⟩ => by
      rcases germ_rep R with ⟨⟨i, x⟩, hx⟩
      change (chainObjects L i).relations l at x
      refine ⟨canonical_map (F := boundedFormulaChain (L := L) n l) i (bd_rel x), ?_⟩
      have hx' : (canonicalMap (L := L) i).on_relation x = R := by
        simpa [canonicalMap, canonical_map_language] using hx
      apply Subtype.ext
      simp [boundedFormulaComparison, coconeOfBoundedFormulaLInfty, bd_rel, hx']
  | n, l, ⟨.apprel f t, hft⟩ => by
      rcases boundedFormulaComparison_surjective ⟨f, hft.1⟩ with ⟨u₁, hu₁⟩
      rcases boundedTermComparison_surjective ⟨t, hft.2⟩ with ⟨u₂, hu₂⟩
      rcases germ_rep u₁ with ⟨⟨i, x⟩, hx⟩
      rcases germ_rep u₂ with ⟨⟨j, y⟩, hy⟩
      refine ⟨canonical_map (F := boundedFormulaChain (L := L) n l) (i + j)
        (bd_apprel (push_to_sum_r (F := boundedFormulaChain (L := L) n (l + 1)) x j)
          (push_to_sum_l (F := boundedTermChain (L := L) n 0) y i)), ?_⟩
      have hx' :
          canonical_map (F := boundedFormulaChain (L := L) n (l + 1)) i x = u₁ := by
        simpa [canonical_map] using hx
      have hy' :
          canonical_map (F := boundedTermChain (L := L) n 0) j y = u₂ := by
        simpa [canonical_map] using hy
      have hfx :
          boundedFormulaComparison (L := L) n (l + 1)
            (canonical_map (F := boundedFormulaChain (L := L) n (l + 1)) (i + j)
              (push_to_sum_r (F := boundedFormulaChain (L := L) n (l + 1)) x j)) = ⟨f, hft.1⟩ := by
        calc
          boundedFormulaComparison (L := L) n (l + 1)
              (canonical_map (F := boundedFormulaChain (L := L) n (l + 1)) (i + j)
                (push_to_sum_r (F := boundedFormulaChain (L := L) n (l + 1)) x j)) =
            boundedFormulaComparison (L := L) n (l + 1)
              (canonical_map (F := boundedFormulaChain (L := L) n (l + 1)) i x) := by
                rw [← same_fiber_as_push_to_r (F := boundedFormulaChain (L := L) n (l + 1)) x j]
          _ = boundedFormulaComparison (L := L) n (l + 1) u₁ := by rw [hx']
          _ = ⟨f, hft.1⟩ := hu₁
      have hty :
          boundedTermComparison (L := L) n 0
            (canonical_map (F := boundedTermChain (L := L) n 0) (i + j)
              (push_to_sum_l (F := boundedTermChain (L := L) n 0) y i)) = ⟨t, hft.2⟩ := by
        calc
          boundedTermComparison (L := L) n 0
              (canonical_map (F := boundedTermChain (L := L) n 0) (i + j)
                (push_to_sum_l (F := boundedTermChain (L := L) n 0) y i)) =
            boundedTermComparison (L := L) n 0
              (canonical_map (F := boundedTermChain (L := L) n 0) j y) := by
                rw [← same_fiber_as_push_to_l (F := boundedTermChain (L := L) n 0) y i]
          _ = boundedTermComparison (L := L) n 0 u₂ := by rw [hy']
          _ = ⟨t, hft.2⟩ := hu₂
      have hfx' :
          (canonicalMap (L := L) (i + j)).on_bounded_formula
            (push_to_sum_r (F := boundedFormulaChain (L := L) n (l + 1)) x j) = ⟨f, hft.1⟩ := by
        simpa [boundedFormulaComparison, coconeOfBoundedFormulaLInfty] using hfx
      have hty' :
          (canonicalMap (L := L) (i + j)).on_bounded_term
            (push_to_sum_l (F := boundedTermChain (L := L) n 0) y i) = ⟨t, hft.2⟩ := by
        simpa [boundedTermComparison, coconeOfBoundedTermLInfty] using hty
      have hfxv :
          ((canonicalMap (L := L) (i + j)).on_bounded_formula
            (push_to_sum_r (F := boundedFormulaChain (L := L) n (l + 1)) x j)).1 = f := by
        simpa using congrArg Subtype.val hfx'
      have htyv :
          ((canonicalMap (L := L) (i + j)).on_bounded_term
            (push_to_sum_l (F := boundedTermChain (L := L) n 0) y i)).1 = t := by
        simpa using congrArg Subtype.val hty'
      have hfxf :
          (canonicalMap (L := L) (i + j)).on_formula
            (push_to_sum_r (F := boundedFormulaChain (L := L) n (l + 1)) x j).1 = f := by
        simpa using hfxv
      have htyt :
          (canonicalMap (L := L) (i + j)).on_term
            (push_to_sum_l (F := boundedTermChain (L := L) n 0) y i).1 = t := by
        simpa using htyv
      apply Subtype.ext
      simpa [boundedFormulaComparison, coconeOfBoundedFormulaLInfty, bd_apprel] using
        And.intro hfxf htyt
  | n, _, ⟨.imp f₁ f₂, hff⟩ => by
      rcases boundedFormulaComparison_surjective ⟨f₁, hff.1⟩ with ⟨u₁, hu₁⟩
      rcases boundedFormulaComparison_surjective ⟨f₂, hff.2⟩ with ⟨u₂, hu₂⟩
      rcases germ_rep u₁ with ⟨⟨i, x⟩, hx⟩
      rcases germ_rep u₂ with ⟨⟨j, y⟩, hy⟩
      refine ⟨canonical_map (F := boundedFormulaChain (L := L) n 0) (i + j)
        (bd_imp (push_to_sum_r (F := boundedFormulaChain (L := L) n 0) x j)
          (push_to_sum_l (F := boundedFormulaChain (L := L) n 0) y i)), ?_⟩
      have hx' :
          canonical_map (F := boundedFormulaChain (L := L) n 0) i x = u₁ := by
        simpa [canonical_map] using hx
      have hy' :
          canonical_map (F := boundedFormulaChain (L := L) n 0) j y = u₂ := by
        simpa [canonical_map] using hy
      have hfx :
          boundedFormulaComparison (L := L) n 0
            (canonical_map (F := boundedFormulaChain (L := L) n 0) (i + j)
              (push_to_sum_r (F := boundedFormulaChain (L := L) n 0) x j)) = ⟨f₁, hff.1⟩ := by
        calc
          boundedFormulaComparison (L := L) n 0
              (canonical_map (F := boundedFormulaChain (L := L) n 0) (i + j)
                (push_to_sum_r (F := boundedFormulaChain (L := L) n 0) x j)) =
            boundedFormulaComparison (L := L) n 0
              (canonical_map (F := boundedFormulaChain (L := L) n 0) i x) := by
                rw [← same_fiber_as_push_to_r (F := boundedFormulaChain (L := L) n 0) x j]
          _ = boundedFormulaComparison (L := L) n 0 u₁ := by rw [hx']
          _ = ⟨f₁, hff.1⟩ := hu₁
      have hgy :
          boundedFormulaComparison (L := L) n 0
            (canonical_map (F := boundedFormulaChain (L := L) n 0) (i + j)
              (push_to_sum_l (F := boundedFormulaChain (L := L) n 0) y i)) = ⟨f₂, hff.2⟩ := by
        calc
          boundedFormulaComparison (L := L) n 0
              (canonical_map (F := boundedFormulaChain (L := L) n 0) (i + j)
                (push_to_sum_l (F := boundedFormulaChain (L := L) n 0) y i)) =
            boundedFormulaComparison (L := L) n 0
              (canonical_map (F := boundedFormulaChain (L := L) n 0) j y) := by
                rw [← same_fiber_as_push_to_l (F := boundedFormulaChain (L := L) n 0) y i]
          _ = boundedFormulaComparison (L := L) n 0 u₂ := by rw [hy']
          _ = ⟨f₂, hff.2⟩ := hu₂
      have hfx' :
          (canonicalMap (L := L) (i + j)).on_bounded_formula
            (push_to_sum_r (F := boundedFormulaChain (L := L) n 0) x j) = ⟨f₁, hff.1⟩ := by
        simpa [boundedFormulaComparison, coconeOfBoundedFormulaLInfty] using hfx
      have hgy' :
          (canonicalMap (L := L) (i + j)).on_bounded_formula
            (push_to_sum_l (F := boundedFormulaChain (L := L) n 0) y i) = ⟨f₂, hff.2⟩ := by
        simpa [boundedFormulaComparison, coconeOfBoundedFormulaLInfty] using hgy
      have hfxv :
          ((canonicalMap (L := L) (i + j)).on_bounded_formula
            (push_to_sum_r (F := boundedFormulaChain (L := L) n 0) x j)).1 = f₁ := by
        simpa using congrArg Subtype.val hfx'
      have hgyv :
          ((canonicalMap (L := L) (i + j)).on_bounded_formula
            (push_to_sum_l (F := boundedFormulaChain (L := L) n 0) y i)).1 = f₂ := by
        simpa using congrArg Subtype.val hgy'
      have hfxf :
          (canonicalMap (L := L) (i + j)).on_formula
            (push_to_sum_r (F := boundedFormulaChain (L := L) n 0) x j).1 = f₁ := by
        simpa using hfxv
      have hgyg :
          (canonicalMap (L := L) (i + j)).on_formula
            (push_to_sum_l (F := boundedFormulaChain (L := L) n 0) y i).1 = f₂ := by
        simpa using hgyv
      apply Subtype.ext
      simpa [boundedFormulaComparison, coconeOfBoundedFormulaLInfty, bd_imp] using
        And.intro hfxf hgyg
  | n, _, ⟨.all f, hf⟩ => by
      rcases boundedFormulaComparison_surjective ⟨f, hf⟩ with ⟨u, hu⟩
      rcases germ_rep u with ⟨⟨i, x⟩, hx⟩
      refine ⟨canonical_map (F := boundedFormulaChain (L := L) n 0) i (bd_all x), ?_⟩
      have hx' : canonical_map (F := boundedFormulaChain (L := L) (n + 1) 0) i x = u := by
        simpa [canonical_map] using hx
      have hfx :
          boundedFormulaComparison (L := L) (n + 1) 0
            (canonical_map (F := boundedFormulaChain (L := L) (n + 1) 0) i x) = ⟨f, hf⟩ := by
        rw [hx']
        exact hu
      have hfx' : (canonicalMap (L := L) i).on_bounded_formula x = ⟨f, hf⟩ := by
        simpa [boundedFormulaComparison, coconeOfBoundedFormulaLInfty] using hfx
      have hfxv : ((canonicalMap (L := L) i).on_bounded_formula x).1 = f := by
        simpa using congrArg Subtype.val hfx'
      have hfxf : (canonicalMap (L := L) i).on_formula x.1 = f := by
        simpa using hfxv
      apply Subtype.ext
      simpa [boundedFormulaComparison, coconeOfBoundedFormulaLInfty, bd_all] using hfxf
termination_by
  n l f => sizeOf f.1
decreasing_by
  all_goals
    try simp_wf
    try omega

theorem boundedFormulaComparison_bijective {L : Language.{u}} (n l : Nat) :
    Function.Bijective (@boundedFormulaComparison L n l) := by
  refine ⟨?_, ?_⟩
  · unfold boundedFormulaComparison
    apply universal_map_inj_of_components_inj
    intro i
    dsimp [coconeOfBoundedFormulaLInfty]
    exact Lhom.on_bounded_formula_inj (canonicalMap_inj (L := L) i)
  · intro f
    exact boundedFormulaComparison_surjective f

theorem boundedFormulaComparison'_bijective {L : Language.{u}} :
    Function.Bijective (@boundedFormulaComparison' L) := by
  simpa [boundedFormulaComparison'] using
    (boundedFormulaComparison_bijective (L := L) 1 0)

noncomputable def equivBoundedFormulaComparison {L : Language.{u}} :
    colimit (boundedFormulaChain' (L := L)) ≃ bounded_formula (LInfty L) 1 :=
  Equiv.ofBijective (boundedFormulaComparison' (L := L))
    boundedFormulaComparison'_bijective

@[reducible] def witProperty {L : Language.{u}} (f : bounded_formula L 1) (c : L.constants) :
    sentence L :=
  ⟨(bd_ex f).fst ⟹ subst_formula f.fst (bd_const c).fst 0,
    by
      simpa [bounded_formula_at] using
        (And.intro (bd_ex f).2
          (bounded_formula_at_subst_closed (f := f.fst) (n := 0)
            (s := (bd_const (L := L) (n := 0) c).fst) f.2 (bd_const (L := L) (n := 0) c).2))⟩

def has_enough_constants {L : Language.{u}} (T : Theory L) : Prop :=
  ∃ C : bounded_formula L 1 → L.constants, ∀ f : bounded_formula L 1, T ⊢' witProperty f (C f)

lemma has_enough_constants.intro {L : Language.{u}} (T : Theory L)
    (H : ∀ f : bounded_formula L 1, ∃ c : L.constants, T ⊢' witProperty f c) :
    has_enough_constants T := by
  classical
  choose C hC using H
  exact ⟨C, hC⟩

lemma has_enough_constants_of_subset {L : Language.{u}} {T T' : Theory L}
    (hsub : Theory.Subset T T') (hT : has_enough_constants T) :
    has_enough_constants T' := by
  rcases hT with ⟨C, hC⟩
  refine ⟨C, ?_⟩
  intro f
  rcases hC f with ⟨hf⟩
  exact ⟨sweakening hsub hf⟩

def henkinTheoryStep {L : Language.{u}} (T : Theory L) : Theory (languageStep L) :=
  Lhom.Theory_induced (inclusion (L := L)) T ∪
    ((fun f : bounded_formula L 1 =>
        witProperty
          (L := languageStep L)
          (Lhom.on_bounded_formula (inclusion (L := L)) f)
          (wit' f)) '' (Set.univ : Set (bounded_formula L 1)))

def henkinTheoryChain {L : Language.{u}} (T : Theory L) :
    (n : Nat) → Theory (chainObjects L n)
  | 0 => T
  | n + 1 => henkinTheoryStep (henkinTheoryChain T n)

/-- The one-variable formula whose existential closure is always provable in the witness step. -/
@[reducible] def henkinWitnessBody {L : Language.{u}} (f : bounded_formula L 1) :
    bounded_formula L 1 :=
  bd_imp (bounded_preformula.cast1 (bd_ex f)) f

/-- The concrete witness axiom adjoined for `f` in `henkinTheoryStep`. -/
@[reducible] def henkinWitnessSentence {L : Language.{u}} (f : bounded_formula L 1) :
    sentence (languageStep L) :=
  Lhom.boundedFormulaSubstSentence
    (henkinWitnessBody (Lhom.on_bounded_formula (inclusion (L := L)) f))
    (bd_const (L := languageStep L) (n := 0) (wit' f))

/-- The explicit witness sentence agrees with the older `witProperty` presentation. -/
lemma henkinWitnessSentence_eq_witProperty {L : Language.{u}} (f : bounded_formula L 1) :
    henkinWitnessSentence (L := L) f =
      witProperty
        (L := languageStep L)
        (Lhom.on_bounded_formula (inclusion (L := L)) f)
        (wit' f) := by
  apply Subtype.ext
  change
    subst_formula
        (((bounded_preformula.cast1
          (bd_ex (Lhom.on_bounded_formula (inclusion (L := L)) f))).fst) ⟹
          (Lhom.on_bounded_formula (inclusion (L := L)) f).fst)
        (bd_const (L := languageStep L) (n := 0) (wit' f)).fst 0 =
      ((bd_ex (Lhom.on_bounded_formula (inclusion (L := L)) f)).fst ⟹
        subst_formula (Lhom.on_bounded_formula (inclusion (L := L)) f).fst
          (bd_const (L := languageStep L) (n := 0) (wit' f)).fst 0)
  have hCast :
      subst_formula
          (bounded_preformula.cast1
            (bd_ex (Lhom.on_bounded_formula (inclusion (L := L)) f))).fst
          (bd_const (L := languageStep L) (n := 0) (wit' f)).fst 0 =
        (bd_ex (Lhom.on_bounded_formula (inclusion (L := L)) f)).fst := by
    simpa [bounded_preformula.cast1_fst] using
      subst_sentence_irrel
        (bd_ex (Lhom.on_bounded_formula (inclusion (L := L)) f))
        ((bd_const (L := languageStep L) (n := 0) (wit' f)).fst)
  calc
    subst_formula
        (((bounded_preformula.cast1
          (bd_ex (Lhom.on_bounded_formula (inclusion (L := L)) f))).fst) ⟹
          (Lhom.on_bounded_formula (inclusion (L := L)) f).fst)
        (bd_const (L := languageStep L) (n := 0) (wit' f)).fst 0 =
      subst_formula
          (bounded_preformula.cast1
            (bd_ex (Lhom.on_bounded_formula (inclusion (L := L)) f))).fst
          (bd_const (L := languageStep L) (n := 0) (wit' f)).fst 0 ⟹
        subst_formula (Lhom.on_bounded_formula (inclusion (L := L)) f).fst
          (bd_const (L := languageStep L) (n := 0) (wit' f)).fst 0 := by
            rfl
    _ = ((bd_ex (Lhom.on_bounded_formula (inclusion (L := L)) f)).fst ⟹
        subst_formula (Lhom.on_bounded_formula (inclusion (L := L)) f).fst
          (bd_const (L := languageStep L) (n := 0) (wit' f)).fst 0) := by
            rw [hCast]

/-- The standard existential premise used to show a Henkin witness step is admissible. -/
noncomputable def provable_henkinWitnessBody {L : Language.{u}} {T : Theory L}
    (f : bounded_formula L 1) : T ⊢ bd_ex (henkinWitnessBody f) := by
  change Theory.fst T ⊢ ((bd_ex (henkinWitnessBody f) : sentence L) : formula L)
  apply prf.falsumE
  apply prf.impE (bd_ex f : formula L)
  · apply prf.impI
    apply prf.impE _ axm2
    apply exE axm1
    apply exI (&0 : term L)
    rw [lift_subst_formula_cancel]
    apply prf.impI
    exact axm2
  · apply prf.falsumE
    apply prf.impE _ axm2
    apply exI (&0 : term L)
    apply prf.impI
    apply exfalso
    apply prf.impE _ axm2
    let Γ' : Set (formula L) :=
      insert (((bd_ex f : sentence L) : formula L) ⟹ (⊥ : formula L))
        (insert ((((bd_ex (bd_imp (bounded_preformula.cast1 (bd_ex f)) f) : sentence L) : formula L) ⟹
            (⊥ : formula L))) T.fst)
    have hax :
      insert (subst_formula (bounded_preformula.cast1 (bd_ex f)).fst (&0 : term L) 0) Γ' ⊢
          subst_formula (bounded_preformula.cast1 (bd_ex f)).fst (&0 : term L) 0 := by
      exact prf.axm (by simp [Γ'])
    have hEq :
        subst_formula (bounded_preformula.cast1 (bd_ex f)).fst (&0 : term L) 0 = (bd_ex f : formula L) := by
      simpa [bounded_preformula.cast1_fst] using subst_sentence_irrel (bd_ex f) (&0 : term L)
    exact cast
      (congrArg
        (fun A : formula L =>
          insert (subst_formula (bounded_preformula.cast1 (bd_ex f)).fst (&0 : term L) 0) Γ' ⊢ A)
        hEq)
      hax

lemma wit_not_mem_range_inclusion {L : Language.{u}} (f : bounded_formula L 1) :
    wit' f ∉ Set.range (@Lhom.on_function _ _ (inclusion (L := L)) 0) := by
  rintro ⟨c, hc⟩
  cases hc

lemma wit_not_mem_symbols_witnessBody {L : Language.{u}} (ψ ψ' : bounded_formula L 1) :
    (Sum.inl ⟨0, wit' ψ⟩ : (languageStep L).symbols) ∉
      symbols_in_formula (Lhom.on_bounded_formula (inclusion (L := L)) ψ').fst := by
  exact Lhom.not_mem_function_in_formula_on_formula
    (ϕ := inclusion (L := L)) (wit_not_mem_range_inclusion (L := L) ψ) (ψ' : formula L)

lemma wit_not_mem_symbols_witProperty_of_ne {L : Language.{u}} {ψ ψ' : bounded_formula L 1}
    (hneq : ψ' ≠ ψ) :
    (Sum.inl ⟨0, wit' ψ⟩ : (languageStep L).symbols) ∉
      symbols_in_formula
        ((witProperty
          (L := languageStep L)
          (Lhom.on_bounded_formula (inclusion (L := L)) ψ')
          (wit' ψ') : sentence (languageStep L)) : formula (languageStep L)) := by
  intro hs
  dsimp [witProperty] at hs
  rcases hs with hs | hs
  · exact Lhom.not_mem_function_in_formula_on_formula
      (ϕ := inclusion (L := L)) (wit_not_mem_range_inclusion (L := L) ψ)
      ((bd_ex ψ' : sentence L) : formula L) hs
  · rcases symbols_in_formula_subst
      (f := (Lhom.on_bounded_formula (inclusion (L := L)) ψ').fst)
      (s := (bd_const (wit' ψ')).fst) (n := 0) hs with hsForm | hsTerm
    · exact wit_not_mem_symbols_witnessBody (L := L) ψ ψ' hsForm
    · have hsym :
          (Sum.inl ⟨0, wit' ψ⟩ : (languageStep L).symbols) =
            Sum.inl ⟨0, wit' ψ'⟩ := by
        have hsTerm' :
            (Sum.inl ⟨0, wit' ψ⟩ : (languageStep L).symbols) ∈
              ({Sum.inl ⟨0, wit' ψ'⟩} : Set (languageStep L).symbols) := by
          simpa [bd_const, bd_func] using hsTerm
        exact Set.mem_singleton_iff.mp hsTerm'
      have hwit : wit' ψ = wit' ψ' := by
        have hpairs :
            ((⟨0, wit' ψ⟩ : Σ n, (languageStep L).functions n)) =
              ⟨0, wit' ψ'⟩ := Sum.inl.inj hsym
        cases hpairs
        rfl
      exact hneq (languageFunctions.wit.inj hwit).symm

lemma wit_not_mem_symbols_henkinWitnessBody {L : Language.{u}} (ψ : bounded_formula L 1) :
    (Sum.inl ⟨0, wit' ψ⟩ : (languageStep L).symbols) ∉
      symbols_in_formula
        (henkinWitnessBody
          (Lhom.on_bounded_formula (inclusion (L := L)) ψ)).fst := by
  intro hs
  dsimp [henkinWitnessBody] at hs
  rcases hs with hs | hs
  · have hsEx :
          (Sum.inl ⟨0, wit' ψ⟩ : (languageStep L).symbols) ∈
            symbols_in_formula ((bd_ex (Lhom.on_bounded_formula (inclusion (L := L)) ψ)).fst) := by
        simpa [bounded_preformula.cast1_fst] using hs
    have hs' :
        (Sum.inl ⟨0, wit' ψ⟩ : (languageStep L).symbols) ∈
          symbols_in_formula (Lhom.on_bounded_formula (inclusion (L := L)) ψ).fst := by
      simpa [bd_ex, bd_not, bd_all, bd_imp, bd_falsum] using hsEx
    exact wit_not_mem_symbols_witnessBody (L := L) ψ ψ hs'
  · exact wit_not_mem_symbols_witnessBody (L := L) ψ ψ hs

private theorem is_consistent_insert_instance_of_exists {L : Language.{u}} {T : Theory L}
    (hT : is_consistent T) {f : bounded_formula L 1} {c : L.constants}
    (hΓ : (Sum.inl ⟨0, c⟩ : L.symbols) ∉ Set.sUnion (symbols_in_formula '' Theory.fst T))
    (hf : (Sum.inl ⟨0, c⟩ : L.symbols) ∉ symbols_in_formula f.fst)
    (hex : T ⊢ bd_ex f) :
    is_consistent (insert (Lhom.boundedFormulaSubstSentence f (bd_const c)) T) := by
  intro hBad
  have hNotInst' : T ⊢' ∼(Lhom.boundedFormulaSubstSentence f (bd_const c)) := simpI' hBad
  have hNotInst : T ⊢ Lhom.boundedFormulaSubstSentence (bd_not f) (bd_const c) := by
    simpa [Lhom.boundedFormulaSubstSentence, bd_not, bd_imp, bd_falsum, sentence.not] using
      (Classical.choice hNotInst' : T ⊢ ∼(Lhom.boundedFormulaSubstSentence f (bd_const c)))
  have hfNot : (Sum.inl ⟨0, c⟩ : L.symbols) ∉ symbols_in_formula (bd_not f).fst := by
    simpa [bd_not, bd_imp, bd_falsum] using hf
  have hAllNot : T ⊢ bd_all (bd_not f) :=
    Lhom.sgeneralize_constant c hΓ hfNot hNotInst
  have hExNot : T ⊢' ∼(bd_all (bd_not f)) := by
    simpa [bd_ex, bd_not] using (sprovable_of_sprf hex)
  exact hT (snot_and_self'' ⟨hAllNot⟩ hExNot)

theorem is_consistent_henkinTheoryStep {L : Language.{u}} {T : Theory L}
    (hT : is_consistent T) : is_consistent (henkinTheoryStep T) := by
  classical
  let Tbase : Theory (languageStep L) := Lhom.Theory_induced (inclusion (L := L)) T
  let W : Set (sentence (languageStep L)) :=
    henkinWitnessSentence (L := L) '' (Set.univ : Set (bounded_formula L 1))
  have hbase : is_consistent Tbase := by
    letI : Lhom.has_decidable_range (inclusion (L := L)) :=
      ⟨fun {n} => Classical.decPred _, fun {n} => Classical.decPred _⟩
    dsimp [Tbase]
    exact Lhom.is_consistent_Theory_induced (ϕ := inclusion (L := L)) (inclusion_inj (L := L)) hT
  have hfinite :
      ∀ s : Finset (sentence (languageStep L)),
        ((s : Set (sentence (languageStep L))) ⊆ W) →
          is_consistent (Tbase ∪ finTheory s) := by
    intro s
    refine Finset.induction_on s ?_ ?_
    · intro _
      have hEq : Tbase ∪ finTheory (∅ : Finset (sentence (languageStep L))) = Tbase := by
        ext x
        change x ∈ Tbase.carrier ∪ (finTheory (∅ : Finset (sentence (languageStep L)))).carrier ↔
          x ∈ Tbase.carrier
        simp [finTheory]
      simpa [hEq] using hbase
    · intro ψ s hψs ih hs
      have hsTail : ((s : Set (sentence (languageStep L))) ⊆ W) := by
        intro x hx
        exact hs (by simp [hx])
      have ih' : is_consistent (Tbase ∪ finTheory s) := ih hsTail
      have hψW : ψ ∈ W := hs (by simp)
      rcases hψW with ⟨f, -, rfl⟩
      have hFreshTheory :
          (Sum.inl ⟨0, wit' f⟩ : (languageStep L).symbols) ∉
            Set.sUnion (symbols_in_formula '' Theory.fst (Tbase ∪ finTheory s)) := by
        intro hsSym
        rcases hsSym with ⟨S, hS, hsSym⟩
        rcases hS with ⟨σ, hσ, rfl⟩
        rcases hσ with ⟨θ, hθ, rfl⟩
        change θ ∈ (Tbase ∪ finTheory s).carrier at hθ
        rcases hθ with hθ | hθ
        · change θ ∈ Tbase.carrier at hθ
          rcases hθ with ⟨θ', hθ', rfl⟩
          exact Lhom.not_mem_function_in_formula_on_formula
            (ϕ := inclusion (L := L)) (wit_not_mem_range_inclusion (L := L) f) (θ' : formula L) hsSym
        · have hθs : θ ∈ s := by
            simpa [finTheory] using hθ
          have hθW : θ ∈ W := hsTail hθs
          rcases hθW with ⟨f', -, hf'⟩
          have hneq : f' ≠ f := by
            intro hEq
            subst hEq
            exact hψs (by simpa [hf'] using hθs)
          rw [← hf'] at hsSym
          have hsSym' :
              (Sum.inl ⟨0, wit' f⟩ : (languageStep L).symbols) ∈
                symbols_in_formula
                  ((witProperty
                    (L := languageStep L)
                    (Lhom.on_bounded_formula (inclusion (L := L)) f')
                    (wit' f') : sentence (languageStep L)) : formula (languageStep L)) := by
            simpa [henkinWitnessSentence_eq_witProperty] using hsSym
          exact wit_not_mem_symbols_witProperty_of_ne (L := L) (ψ := f) (ψ' := f') hneq hsSym'
      have hFreshBody :
          (Sum.inl ⟨0, wit' f⟩ : (languageStep L).symbols) ∉
            symbols_in_formula
              (henkinWitnessBody
                (Lhom.on_bounded_formula (inclusion (L := L)) f)).fst :=
        wit_not_mem_symbols_henkinWitnessBody (L := L) f
      have hEx :
          Tbase ∪ finTheory s ⊢
            bd_ex (henkinWitnessBody (Lhom.on_bounded_formula (inclusion (L := L)) f)) :=
        provable_henkinWitnessBody
          (T := Tbase ∪ finTheory s)
          (f := Lhom.on_bounded_formula (inclusion (L := L)) f)
      have hInsert :
          is_consistent
            (insert
              (Lhom.boundedFormulaSubstSentence
                (henkinWitnessBody (Lhom.on_bounded_formula (inclusion (L := L)) f))
                (bd_const (L := languageStep L) (n := 0) (wit' f)))
              (Tbase ∪ finTheory s)) :=
        is_consistent_insert_instance_of_exists ih' hFreshTheory hFreshBody hEx
      have hEq :
          Tbase ∪ finTheory (insert (henkinWitnessSentence (L := L) f) s) =
            insert (henkinWitnessSentence (L := L) f) (Tbase ∪ finTheory s) := by
        ext x
        change x ∈ Tbase.carrier ∪ (finTheory (insert (henkinWitnessSentence (L := L) f) s)).carrier ↔
          x ∈ (insert (henkinWitnessSentence (L := L) f) (Tbase ∪ finTheory s)).carrier
        constructor
        · intro hx
          rcases hx with hx | hx
          · exact Or.inr (Or.inl hx)
          · have hx' : x = henkinWitnessSentence (L := L) f ∨ x ∈ s := by
              simpa [finTheory] using hx
            rcases hx' with rfl | hx'
            · exact Or.inl rfl
            · exact Or.inr (Or.inr hx')
        · intro hx
          change x = henkinWitnessSentence (L := L) f ∨ x ∈ (Tbase ∪ finTheory s).carrier at hx
          rcases hx with rfl | hx
          · exact Or.inr (by simp [finTheory])
          · rcases hx with hx | hx
            · exact Or.inl hx
            · exact Or.inr (by
                change x ∈ ((insert (henkinWitnessSentence (L := L) f) s : Finset (sentence (languageStep L))) :
                  Set (sentence (languageStep L)))
                simp [hx])
      simpa [hEq] using hInsert
  intro hBad
  rcases theory_proof_compactness hBad with ⟨Γ, hΓ, hsub⟩
  let Γw : Finset (sentence (languageStep L)) := Γ.filter fun x => decide (x ∉ Tbase)
  have hΓwW : ((Γw : Set (sentence (languageStep L))) ⊆ W) := by
    intro x hx
    have hx' : x ∈ Γ ∧ x ∉ Tbase := by
      simpa [Γw] using hx
    have hxStep : x ∈ henkinTheoryStep T := hsub hx'.1
    dsimp [henkinTheoryStep] at hxStep
    rcases hxStep with hxBase | hxW
    · exact False.elim (hx'.2 hxBase)
    · simpa [W, henkinWitnessSentence_eq_witProperty] using hxW
  have hSmall : Tbase ∪ finTheory Γw ⊢' (⊥ : sentence (languageStep L)) := by
    rcases hΓ with ⟨hΓ⟩
    exact ⟨sweakening (by
      intro x hx
      change x ∈ (finTheory Γ).carrier at hx
      have hxΓ : x ∈ Γ := hx
      have hxStep : x ∈ henkinTheoryStep T := hsub hx
      have hxUnion : x ∈ Tbase ∪ finTheory Γw := by
        by_cases hxBase : x ∈ Tbase
        · exact Or.inl hxBase
        · have hxΓw : x ∈ Γw := by
            simp [Γw, hxΓ, hxBase]
          exact Or.inr hxΓw
      exact hxUnion) hΓ⟩
  exact (hfinite Γw hΓwW) hSmall

def iota {L : Language.{u}} {T : Theory L} (m : Nat) : Theory (LInfty L) :=
  Lhom.Theory_induced (canonicalMap (L := L) m) (henkinTheoryChain T m)

def TInfty {L : Language.{u}} (T : Theory L) : Theory (LInfty L) :=
  ⟨⋃ n : Nat, (iota (T := T) n).carrier⟩

@[reducible] def henkinLanguage {L : Language.{u}} (T : Theory L) : Language.{u} :=
  let _ := T
  LInfty L

def henkinLanguageOver {L : Language.{u}} {T : Theory L} :
    L →ᴸ henkinLanguage (L := L) T := by
  change chainObjects L 0 →ᴸ LInfty L
  exact canonicalMap (L := L) 0

lemma henkinLanguageOver_injective {L : Language.{u}} {T : Theory L} :
    Lhom.is_injective (henkinLanguageOver (L := L) (T := T)) := by
  simpa [henkinLanguageOver] using canonicalMap_inj (L := L) 0

def completeHenkinTheoryOver {L : Language.{u}} (T : Theory L) (hT : is_consistent T) : Type (u + 1) :=
  Σ' T' : Theory_over T hT, has_enough_constants T'.1 ∧ is_complete T'.1

@[reducible] def henkinization {L : Language.{u}} {T : Theory L} (hT : is_consistent T) :
    Theory (henkinLanguage (L := L) T) :=
  let _ := hT
  TInfty T

noncomputable def witInfty {L : Language.{u}} (f : bounded_formula (LInfty L) 1) :
    Σ c : (LInfty L).constants,
      Σ f' : Σ' x : colimit (boundedFormulaChain' (L := L)),
        equivBoundedFormulaComparison (L := L) x = f,
        Σ' f'' : coproduct_of_directed_diagram (boundedFormulaChain' (L := L)),
          (Quotient.mk'' f'' : colimit (boundedFormulaChain' (L := L))) = f'.1 ∧
            c = (canonicalMap (L := L) (f''.1 + 1)).on_function (wit' f''.2) := by
  let f' : Σ' x : colimit (boundedFormulaChain' (L := L)),
      equivBoundedFormulaComparison (L := L) x = f :=
    ⟨(equivBoundedFormulaComparison (L := L)).symm f,
      (equivBoundedFormulaComparison (L := L)).apply_symm_apply f⟩
  let f'' := germ_rep f'.1
  refine ⟨(canonicalMap (L := L) (f''.1.1 + 1)).on_function (wit' f''.1.2), f', f''.1, ?_, rfl⟩
  simpa using f''.2

lemma inIotaOfInStep {L : Language.{u}} {T : Theory L} (i : Nat)
    (f : sentence (chainObjects L (i + 1))) (hf : f ∈ henkinTheoryChain T (i + 1)) :
    Lhom.on_sentence (canonicalMap (L := L) (i + 1)) f ∈ iota (T := T) (i + 1) :=
  Set.mem_image_of_mem _ hf

@[simp] lemma henkinizationIsHenkin {L : Language.{u}} {T : Theory L} (hT : is_consistent T) :
    has_enough_constants (henkinization (L := L) (T := T) hT) := by
  apply has_enough_constants.intro
  intro f
  rcases witInfty (L := L) f with ⟨c, ⟨⟨f', hf'⟩, ⟨⟨i, f''⟩, hrep, hc⟩⟩⟩
  refine ⟨c, ?_⟩
  refine ⟨saxm ?_⟩
  unfold henkinization TInfty
  refine Set.mem_iUnion.mpr ⟨i + 1, ?_⟩
  have hstep :
      witProperty
        (L := chainObjects L (i + 1))
        (Lhom.on_bounded_formula (inclusion (L := chainObjects L i)) f'')
        (wit' f'') ∈ henkinTheoryChain T (i + 1) := by
    dsimp [henkinTheoryChain, henkinTheoryStep]
    exact Or.inr (Set.mem_image_of_mem _ (by simp))
  have hstage :
      Lhom.on_bounded_formula (canonicalMap (L := L) i) f'' = f := by
    have hq :
        canonical_map (F := boundedFormulaChain' (L := L)) i f'' =
          (Quotient.mk'' (⟨i, f''⟩ : coproduct_of_directed_diagram (boundedFormulaChain' (L := L))) :
            colimit (boundedFormulaChain' (L := L))) := by
      simpa using
        (canonical_map_quotient (F := boundedFormulaChain' (L := L))
          (⟨i, f''⟩ : coproduct_of_directed_diagram (boundedFormulaChain' (L := L))))
    have hcmp :
        boundedFormulaComparison' (L := L)
          (canonical_map (F := boundedFormulaChain' (L := L)) i f'') = f := by
      rw [hq]
      rw [hrep]
      exact hf'
    simpa [boundedFormulaComparison', boundedFormulaComparison, coconeOfBoundedFormulaPrimeLInfty] using hcmp
  have hsucc : chainMaps L i (i + 1) (by simp) = inclusion (L := chainObjects L i) := by
    have hself : chainMaps L i i (Nat.le_refl i) = Lhom.id (chainObjects L i) := by
      induction i with
      | zero =>
          simp [chainMaps]
      | succ i ih =>
          simp [chainMaps]
    calc
      chainMaps L i (i + 1) (Nat.le_succ i) =
        inclusion (L := chainObjects L i) ∘ᴸ chainMaps L i i (Nat.le_refl i) := by
          have hneq : i ≠ i + 1 := Nat.ne_of_lt (Nat.lt_succ_self i)
          simp [chainMaps, hneq, Lhom.comp]
      _ = inclusion (L := chainObjects L i) := by
          rw [hself]
          simp
  have hstageSucc :
      Lhom.on_bounded_formula (canonicalMap (L := L) (i + 1))
        (Lhom.on_bounded_formula (inclusion (L := chainObjects L i)) f'') = f := by
    have hcompat :
        Lhom.on_bounded_formula
            ((canonicalMap (L := L) (i + 1)) ∘ᴸ (chainMaps L i (i + 1) (Nat.le_succ i))) f'' =
          Lhom.on_bounded_formula (canonicalMap (L := L) i) f'' := by
      simpa [canonicalMap, coconeOfLInfty, languageChain, Lhom.comp] using
        congrArg
          (fun ϕ => @Lhom.on_bounded_formula _ _ ϕ 1 0 f'')
          ((coconeOfLInfty (L := L)).h_compat (Nat.le_succ i)).symm
    calc
      Lhom.on_bounded_formula (canonicalMap (L := L) (i + 1))
          (Lhom.on_bounded_formula (inclusion (L := chainObjects L i)) f'') =
        Lhom.on_bounded_formula
          ((canonicalMap (L := L) (i + 1)) ∘ᴸ (inclusion (L := chainObjects L i))) f'' := by
            simp [Lhom.comp]
      _ = Lhom.on_bounded_formula
          ((canonicalMap (L := L) (i + 1)) ∘ᴸ (chainMaps L i (i + 1) (by simp))) f'' := by
            rw [hsucc]
      _ = Lhom.on_bounded_formula (canonicalMap (L := L) i) f'' := by
            exact hcompat
      _ = f := hstage
  have hex :
      (bd_ex
        (Lhom.on_bounded_formula (canonicalMap (L := L) (i + 1))
          (Lhom.on_bounded_formula (inclusion (L := chainObjects L i)) f''))).fst =
        (bd_ex f).fst := by
    simpa using congrArg (fun g => (bd_ex g).fst) hstageSucc
  have hsub :
      subst_formula
          (Lhom.on_bounded_formula (canonicalMap (L := L) (i + 1))
            (Lhom.on_bounded_formula (inclusion (L := chainObjects L i)) f'')).fst
          (bd_const (L := LInfty L) (n := 0)
            ((canonicalMap (L := L) (i + 1)).on_function (wit' f''))).fst 0 =
        subst_formula f.fst (bd_const (L := LInfty L) (n := 0) c).fst 0 := by
    calc
      subst_formula
          (Lhom.on_bounded_formula (canonicalMap (L := L) (i + 1))
            (Lhom.on_bounded_formula (inclusion (L := chainObjects L i)) f'')).fst
          (bd_const (L := LInfty L) (n := 0)
            ((canonicalMap (L := L) (i + 1)).on_function (wit' f''))).fst 0 =
        subst_formula
          (Lhom.on_bounded_formula (canonicalMap (L := L) (i + 1))
            (Lhom.on_bounded_formula (inclusion (L := chainObjects L i)) f'')).fst
          (bd_const (L := LInfty L) (n := 0) c).fst 0 := by
            simp [hc]
      _ = subst_formula f.fst (bd_const (L := LInfty L) (n := 0) c).fst 0 := by
            simpa using congrArg
              (fun g => subst_formula g.fst (bd_const (L := LInfty L) (n := 0) c).fst 0)
              hstageSucc
  have himage :
      Lhom.on_sentence (canonicalMap (L := L) (i + 1))
          (witProperty
            (L := chainObjects L (i + 1))
            (Lhom.on_bounded_formula (inclusion (L := chainObjects L i)) f'')
            (wit' f'')) =
        witProperty (L := LInfty L) f c := by
    apply Subtype.ext
    simpa [witProperty] using And.intro hex hsub
  have hiota :
      Lhom.on_sentence (canonicalMap (L := L) (i + 1))
          (witProperty
            (L := chainObjects L (i + 1))
            (Lhom.on_bounded_formula (inclusion (L := chainObjects L i)) f'')
            (wit' f'')) ∈ (iota (T := T) (i + 1)).carrier := by
    exact inIotaOfInStep (L := L) (T := T) i _ hstep
  rw [himage] at hiota
  exact hiota

lemma henkinTheoryChainInclusionStep {L : Language.{u}} {T : Theory L} {i : Nat}
    {f : sentence (chainObjects L i)} (hf : f ∈ henkinTheoryChain T i) :
    Lhom.on_sentence (inclusion (L := chainObjects L i)) f ∈ henkinTheoryChain T (i + 1) := by
  dsimp [henkinTheoryChain, henkinTheoryStep]
  exact Or.inl (Set.mem_image_of_mem _ hf)

lemma henkinTheoryChainInclusion {L : Language.{u}} {T : Theory L} :
    ∀ {i j : Nat} (h : i ≤ j) {f : sentence (chainObjects L i)},
      f ∈ henkinTheoryChain T i →
        Lhom.on_sentence (chainMaps L i j h) f ∈ henkinTheoryChain T j
  | i, 0, h, f, hf => by
      have hi : i = 0 := Nat.eq_zero_of_le_zero h
      subst hi
      simpa [henkinTheoryChain, chainMaps] using hf
  | i, j + 1, h, f, hf => by
      by_cases hij : i = j + 1
      · subst hij
        simpa [henkinTheoryChain, chainMaps] using hf
      · have hij' : i ≤ j := Nat.lt_succ_iff.mp (lt_of_le_of_ne h hij)
        have ih := henkinTheoryChainInclusion (j := j) hij' hf
        have hmap :
            Lhom.on_sentence (chainMaps L i (j + 1) h) f =
              Lhom.on_sentence (inclusion (L := chainObjects L j))
                (Lhom.on_sentence (chainMaps L i j hij') f) := by
          apply Subtype.ext
          simp [chainMaps, hij, Lhom.comp]
        rw [hmap]
        exact henkinTheoryChainInclusionStep ih

lemma iotaInclusionOfLe {L : Language.{u}} {T : Theory L} :
    ∀ {i j : Nat} (_ : i ≤ j), Theory.Subset (iota (T := T) i) (iota (T := T) j)
  | i, j, h => by
      intro ψ hψ
      change ψ ∈
        (Lhom.on_sentence (canonicalMap (L := L) i) ''
          (henkinTheoryChain T i).carrier) at hψ
      rcases hψ with ⟨f, hf, rfl⟩
      refine ⟨Lhom.on_sentence (chainMaps L i j h) f, ?_, ?_⟩
      · exact henkinTheoryChainInclusion (T := T) h hf
      · apply Subtype.ext
        calc
          (Lhom.on_sentence (canonicalMap (L := L) j)
              (Lhom.on_sentence (chainMaps L i j h) f) : sentence (LInfty L)).1 =
              (((canonicalMap (L := L) j) ∘ᴸ (chainMaps L i j h)).on_formula
                (f : formula (chainObjects L i))) := by
                  simp [Lhom.on_sentence_fst, Lhom.on_formula_comp, Lhom.comp]
          _ = (canonicalMap (L := L) i).on_formula (f : formula (chainObjects L i)) := by
                simpa [coconeOfLInfty, canonicalMap, languageChain] using
                  congrArg
                    (fun ϕ => @Lhom.on_formula _ _ ϕ 0 (f : formula (chainObjects L i)))
                    ((coconeOfLInfty (L := L)).h_compat h).symm

theorem is_consistent_henkinTheoryChain {L : Language.{u}} {T : Theory L}
    (hT : is_consistent T) : ∀ n : Nat, is_consistent (henkinTheoryChain T n)
  | 0 => hT
  | n + 1 => is_consistent_henkinTheoryStep (T := henkinTheoryChain T n)
      (is_consistent_henkinTheoryChain hT n)

theorem is_consistent_iota {L : Language.{u}} {T : Theory L} (hT : is_consistent T) (n : Nat) :
    is_consistent (iota (T := T) n) := by
  letI : Lhom.has_decidable_range (canonicalMap (L := L) n) :=
    ⟨fun {k} => Classical.decPred _, fun {k} => Classical.decPred _⟩
  exact Lhom.is_consistent_Theory_induced
    (ϕ := canonicalMap (L := L) n) (canonicalMap_inj (L := L) n)
    (is_consistent_henkinTheoryChain (T := T) hT n)

lemma finite_subset_iota_of_mem_TInfty {L : Language.{u}} {T : Theory L}
    (Γ : Finset (sentence (LInfty L))) (hΓ : ((Γ : Set (sentence (LInfty L))) ⊆ (TInfty T).carrier)) :
    ∃ n : Nat, ((Γ : Set (sentence (LInfty L))) ⊆ (iota (T := T) n).carrier) := by
  classical
  induction Γ using Finset.induction_on with
  | empty =>
      refine ⟨0, ?_⟩
      intro ψ hψ
      simp at hψ
  | @insert ψ s hψs ih =>
      have hs : ((s : Set (sentence (LInfty L))) ⊆ (TInfty T).carrier) := by
        intro φ hφ
        exact hΓ (by simp [hφ])
      rcases ih hs with ⟨ns, hsns⟩
      have hψTInfty : ψ ∈ TInfty T := hΓ (by simp)
      rcases Set.mem_iUnion.mp hψTInfty with ⟨nψ, hψnψ⟩
      refine ⟨max ns nψ, ?_⟩
      intro φ hφ
      rcases Finset.mem_insert.mp hφ with rfl | hφs
      · exact iotaInclusionOfLe (T := T) (i := nψ) (j := max ns nψ) (Nat.le_max_right _ _) hψnψ
      · exact iotaInclusionOfLe (T := T) (i := ns) (j := max ns nψ) (Nat.le_max_left _ _) (hsns hφs)

theorem is_consistent_TInfty {L : Language.{u}} {T : Theory L} (hT : is_consistent T) :
    is_consistent (TInfty T) := by
  intro hBad
  rcases theory_proof_compactness (T := TInfty T) (ψ := (⊥ : sentence (LInfty L))) hBad with
    ⟨Γ, hΓ, hΓsub⟩
  rcases finite_subset_iota_of_mem_TInfty (T := T) Γ hΓsub with ⟨n, hΓn⟩
  have hBadIota : iota (T := T) n ⊢' (⊥ : sentence (LInfty L)) := by
    rcases hΓ with ⟨hΓ⟩
    exact ⟨sweakening hΓn hΓ⟩
  exact is_consistent_iota (T := T) hT n hBadIota

/-- The Henkinization of a consistent theory is itself consistent. -/
theorem is_consistent_henkinization {L : Language.{u}} {T : Theory L} (hT : is_consistent T) :
    is_consistent (henkinization (L := L) (T := T) hT) := by
  simpa [henkinization] using is_consistent_TInfty (T := T) hT

/-- Complete a consistent Henkinization to a complete Henkin theory over it. -/
noncomputable def completeHenkinizationOfConsis {L : Language.{u}} {T : Theory L}
    (hT : is_consistent T) :
    completeHenkinTheoryOver
      (henkinization (L := L) (T := T) hT)
      (is_consistent_henkinization (L := L) (T := T) hT) := by
  let hHenkin : is_consistent (henkinization (L := L) (T := T) hT) :=
    is_consistent_henkinization (L := L) (T := T) hT
  rcases completion_of_consis (henkinization (L := L) (T := T) hT) hHenkin with ⟨T', hComplete⟩
  refine ⟨T', ?_, hComplete⟩
  exact has_enough_constants_of_subset T'.2.1 (henkinizationIsHenkin (L := L) (T := T) hT)

/-- Upstream-style view of the completed Henkinization, forgetting the Henkin witness payload. -/
@[reducible] noncomputable def completion_of_henkinization_core {L : Language.{u}} {T : Theory L}
    (hT : is_consistent T) :
    Σ' T' :
        Theory_over
          (henkinization (L := L) (T := T) hT)
          (is_consistent_henkinization (L := L) (T := T) hT),
      is_complete T'.1 := by
  exact ⟨(completeHenkinizationOfConsis (L := L) (T := T) hT).1,
    (completeHenkinizationOfConsis (L := L) (T := T) hT).2.2⟩

/-- A canonical complete extension of the Henkinization of a consistent theory. -/
@[reducible] noncomputable def completion_of_henkinization {L : Language.{u}} {T : Theory L}
    (hT : is_consistent T) : Theory (henkinLanguage (L := L) T) :=
  (completion_of_henkinization_core (L := L) (T := T) hT).1.1

@[simp] theorem completion_of_henkinization_contains {L : Language.{u}} {T : Theory L}
    (hT : is_consistent T) :
    Theory.Subset (henkinization (L := L) (T := T) hT)
      (completion_of_henkinization (L := L) (T := T) hT) :=
  (completion_of_henkinization_core (L := L) (T := T) hT).1.2.1

@[simp] theorem completion_of_henkinization_consistent {L : Language.{u}} {T : Theory L}
    (hT : is_consistent T) :
    is_consistent (completion_of_henkinization (L := L) (T := T) hT) :=
  (completion_of_henkinization_core (L := L) (T := T) hT).1.2.2

@[simp] theorem completion_of_henkinization_is_henkin {L : Language.{u}} {T : Theory L}
    (hT : is_consistent T) :
    has_enough_constants (completion_of_henkinization (L := L) (T := T) hT) :=
  (completeHenkinizationOfConsis (L := L) (T := T) hT).2.1

/-- The completed Henkinization is complete. -/
theorem completion_of_henkinization_complete {L : Language.{u}} {T : Theory L}
    (hT : is_consistent T) :
    is_complete (completion_of_henkinization (L := L) (T := T) hT) :=
  (completion_of_henkinization_core (L := L) (T := T) hT).2

/-- In a complete Henkin theory, failure of `∀x f` yields a closed counterexample term. -/
theorem find_counterexample_of_henkin {L : Language.{u}} {T : Theory L}
    (hComplete : is_complete T) (hHenkin : has_enough_constants T) (f : bounded_formula L 1)
    (hNotAll : ¬ T ⊢' bd_all f) :
    ∃ t : closed_term L, T ⊢' ∼(Lhom.boundedFormulaSubstSentence f t) := by
  rcases hHenkin with ⟨C, hC⟩
  refine ⟨bd_const (L := L) (n := 0) (C (bd_not f)), ?_⟩
  have hExNotAll : T ⊢' bd_ex (bd_not f) := by
    rcases notI_of_is_complete hComplete hNotAll with ⟨hNotAll'⟩
    refine ⟨?_⟩
    apply prf.falsumE
    apply prf.impE _ (weakening1 hNotAll')
    apply prf.allI
    apply prf.falsumE
    rw [Set.image_insert_eq]
    apply prf.impE _ axm2
    apply exI (&0 : term L)
    have hs :
        subst_formula (lift_formula_at (bd_not f).fst 1 (0 + 1)) (&0 : term L) 0 = (bd_not f).fst := by
      simpa using lift_subst_formula_cancel (f := (bd_not f).fst) 0
    have hax :
        insert (∼(f : formula L))
            (insert (lift_formula1 ((bd_ex (bd_not f) : sentence L) : formula L) ⟹ ⊥)
              (lift_formula1 '' Theory.fst T)) ⊢ (bd_not f).fst := by
      simpa [bd_not_fst] using (axm1 : insert (∼(f : formula L))
        (insert (lift_formula1 ((bd_ex (bd_not f) : sentence L) : formula L) ⟹ ⊥)
          (lift_formula1 '' Theory.fst T)) ⊢ ∼(f : formula L))
    exact hs.symm ▸ hax
  have hWitness := hC (bd_not f)
  have hInst :
      T ⊢' Lhom.boundedFormulaSubstSentence (bd_not f)
        (bd_const (L := L) (n := 0) (C (bd_not f))) := by
    have hWitness' :
        T ⊢' ((bd_ex (bd_not f) : sentence L) ⟹
          Lhom.boundedFormulaSubstSentence (bd_not f)
            (bd_const (L := L) (n := 0) (C (bd_not f)))) := by
      simpa [witProperty, Lhom.boundedFormulaSubstSentence] using hWitness
    exact simpE' (bd_ex (bd_not f)) hWitness' hExNotAll
  simpa [Lhom.boundedFormulaSubstSentence, bd_not_fst, sentence.not] using hInst

/-- Closed terms are identified when the theory proves them equal. -/
def term_rel {L : Language.{u}} (T : Theory L) (t₁ t₂ : closed_term L) : Prop :=
  Nonempty (Theory.fst T ⊢ (t₁.fst ≃ t₂.fst))

/-- A family of partially applied terms is pointwise equal over a theory. -/
def equal_preterms {L : Language.{u}} (T : Set (formula L)) {l : Nat}
    (t₁ t₂ : preterm L l) : Type u :=
  ∀ ts : dvector (term L) l, T ⊢ apps t₁ ts ≃ apps t₂ ts

/-- Substituting into a lifted argument vector recovers the original vector. -/
theorem map_subst_lift_cancel {L : Language.{u}} {l : Nat} (xs : dvector (term L) l) (s : term L) :
    dvector.map (fun x : term L => subst_term x s 0) (xs.map lift_term1) = xs := by
  induction xs with
  | nil =>
      rfl
  | cons x xs ih =>
      change dvector.cons ((x ↑ 1)[s // 0]) (dvector.map (fun x : term L => x[s // 0]) (xs.map lift_term1)) =
        dvector.cons x xs
      rw [show ((x ↑ 1)[s // 0]) = x by simpa using (lift_term1_subst_term (t := x) (s := s))]
      simpa using ih

/-- Substituting into a lifted argument vector with a fresh head recovers the original data. -/
theorem map_subst_lift_cancel_cons {L : Language.{u}} {l : Nat} (xs : dvector (term L) l)
    (s : term L) :
    dvector.map (fun x : term L => subst_term x s 0)
        (dvector.cons (&0 : term L) (xs.map lift_term1)) =
      dvector.cons s xs := by
  change dvector.cons ((&0 : term L)[s // 0])
      (dvector.map (fun x : term L => x[s // 0]) (xs.map lift_term1)) =
    dvector.cons s xs
  rw [show ((&0 : term L)[s // 0]) = s by simp [subst_term]]
  simpa using (map_subst_lift_cancel (xs := xs) (s := s))

/-- Pointwise equality is preserved when equal arguments are appended. -/
noncomputable def equal_preterms_app {L : Language.{u}} {T : Set (formula L)} {l : Nat}
    {t t' : preterm L (l + 1)} {s s' : term L}
    (ht : equal_preterms T t t') (hs : T ⊢ s ≃ s') :
    equal_preterms T (preterm.app t s) (preterm.app t' s') := by
  intro xs
  apply Flypitch.fol.trans (ht (dvector.cons s xs))
  have h :=
    Flypitch.fol.congr
      (s := apps (t' ↑ 1) (dvector.cons (&0 : term L) (xs.map lift_term1))) hs
  have ht' : (t' ↑ 1)[s // 0] = t' := by
    simpa using (lift_term1_subst_term (t := t') (s := s))
  have ht'' : (t' ↑ 1)[s' // 0] = t' := by
    simpa using (lift_term1_subst_term (t := t') (s := s'))
  simpa only [subst_term_apps, ht', ht'', map_subst_lift_cancel_cons] using h

/-- Every partially applied term is pointwise equal to itself. -/
@[refl] def equal_preterms_refl {L : Language.{u}} (T : Set (formula L)) {l : Nat}
    (t : preterm L l) : equal_preterms T t t :=
  fun ts => prf.ref T (apps t ts)

/-- A family of partially applied formulas is pointwise equivalent over a theory. -/
def equiv_preformulae {L : Language.{u}} (T : Set (formula L)) {l : Nat}
    (f₁ f₂ : preformula L l) : Type u :=
  ∀ ts : dvector (term L) l, T ⊢ biimp (apps_rel f₁ ts) (apps_rel f₂ ts)

/-- Substituting into a lifted argument vector leaves a fully applied relation formula unchanged. -/
theorem apps_rel_map_subst_lift_cancel {L : Language.{u}} {l : Nat}
    (f : preformula L l) (xs : dvector (term L) l) (s : term L) :
    apps_rel f (dvector.map (fun x : term L => subst_term x s 0) (xs.map lift_term1)) =
      apps_rel f xs := by
  induction xs with
  | nil =>
      rfl
  | cons x xs ih =>
      change apps_rel (preformula.apprel f ((x ↑ 1)[s // 0]))
          (dvector.map (fun x : term L => x[s // 0]) (xs.map lift_term1)) =
        apps_rel (preformula.apprel f x) xs
      rw [show ((x ↑ 1)[s // 0]) = x by simpa using (lift_term1_subst_term (t := x) (s := s))]
      simpa using ih (preformula.apprel f x)

/-- Equality of the head argument preserves the corresponding fully applied relation formula. -/
noncomputable def apps_rel_congr {L : Language.{u}} {Γ : Set (formula L)} {l : Nat}
    (f : preformula L (l + 1)) (xs : dvector (term L) l) {s s' : term L}
    (hs : Γ ⊢ s ≃ s') (h : Γ ⊢ apps_rel f (dvector.cons s xs)) :
    Γ ⊢ apps_rel f (dvector.cons s' xs) := by
  have hSubstEq :
      subst_formula (apps_rel (lift_formula f 1) (dvector.cons (&0 : term L) (xs.map lift_term1))) s 0 =
        apps_rel (preformula.apprel f s) (dvector.map (fun x : term L => subst_term x s 0)
          (xs.map lift_term1)) := by
    simp [subst_formula_apps_rel]
  have hSubst :
      Γ ⊢ subst_formula (apps_rel (lift_formula f 1) (dvector.cons (&0 : term L) (xs.map lift_term1))) s 0 := by
    rw [hSubstEq]
    rw [apps_rel_map_subst_lift_cancel]
    exact h
  have hTargetEq :
      subst_formula (apps_rel (lift_formula f 1) (dvector.cons (&0 : term L) (xs.map lift_term1))) s' 0 =
        apps_rel (preformula.apprel f s') (dvector.map (fun x : term L => subst_term x s' 0)
          (xs.map lift_term1)) := by
    simp [subst_formula_apps_rel]
  apply subst (Γ := Γ) (s := s) (t := s')
    (f₁ := apps_rel (lift_formula f 1) (dvector.cons (&0 : term L) (xs.map lift_term1))) hs hSubst
  rw [hTargetEq]
  rw [apps_rel_map_subst_lift_cancel]
  rfl

/-- Every partially applied formula is pointwise equivalent to itself. -/
@[refl] noncomputable def equiv_preformulae_refl {L : Language.{u}} (T : Set (formula L)) {l : Nat}
    (f : preformula L l) : equiv_preformulae T f f :=
  fun ts => biimp_refl T (apps_rel f ts)

/-- Pointwise equivalence is preserved when equal arguments are appended. -/
noncomputable def equiv_preformulae_apprel {L : Language.{u}} {T : Set (formula L)} {l : Nat}
    {f f' : preformula L (l + 1)} {s s' : term L}
    (ht : equiv_preformulae T f f') (hs : T ⊢ s ≃ s') :
    equiv_preformulae T (preformula.apprel f s) (preformula.apprel f' s') := by
  intro xs
  apply biimp_trans (ht (dvector.cons s xs))
  have hForward : insert (apps_rel f' (dvector.cons s xs)) T ⊢ apps_rel f' (dvector.cons s' xs) :=
    apps_rel_congr f' xs (weakening1 hs) axm1
  have hBackward : insert (apps_rel f' (dvector.cons s' xs)) T ⊢ apps_rel f' (dvector.cons s xs) := by
    apply apps_rel_congr f' xs
    · exact weakening1 (Flypitch.fol.symm hs)
    · exact axm1
  exact biimpI hForward hBackward

/-- The quotient relation used for the term model carrier. -/
def term_setoid {L : Language.{u}} (T : Theory L) : Setoid (closed_term L) where
  r := term_rel T
  iseqv := by
    refine ⟨?_, ?_, ?_⟩
    · intro t
      exact ⟨prf.ref (Theory.fst T) t.fst⟩
    · intro t₁ t₂ h
      rcases h with ⟨h⟩
      exact ⟨Flypitch.fol.symm h⟩
    · intro t₁ t₂ t₃ h₁₂ h₂₃
      rcases h₁₂ with ⟨h₁₂⟩
      rcases h₂₃ with ⟨h₂₃⟩
      exact ⟨Flypitch.fol.trans h₁₂ h₂₃⟩

/-- The carrier of the eventual term model is the quotient of closed terms by provable equality. -/
def term_model' {L : Language.{u}} (T : Theory L) : Type u :=
  Quotient (term_setoid T)

/-- Apply a bounded closed term to a tuple of representatives in the raw term model carrier. -/
def term_model_fun' {L : Language.{u}} {T : Theory L} {l : Nat}
    (t : closed_preterm L l) (ts : dvector (closed_term L) l) : term_model' T :=
  Quotient.mk'' (bd_apps t ts)

/-- The raw term-model application respects provable equality of representatives. -/
theorem term_model_fun_eq {L : Language.{u}} {T : Theory L} {l : Nat}
    (t t' : closed_preterm L (l + 1)) (x x' : closed_term L)
    (ht : equal_preterms (Theory.fst T) t.fst t'.fst)
    (hx : Theory.fst T ⊢ x.fst ≃ x'.fst) (ts : dvector (closed_term L) l) :
    term_model_fun' (T := T) (bd_app t x) ts = term_model_fun' (T := T) (bd_app t' x') ts := by
  induction ts generalizing x x' with
  | nil =>
      apply Quotient.sound
      refine ⟨Flypitch.fol.trans (ht (dvector.cons x dvector.nil)) ?_⟩
      exact equal_preterms_app (equal_preterms_refl (Theory.fst T) t'.fst) hx dvector.nil
  | cons y ys ih =>
      apply ih
      · exact equal_preterms_app ht hx
      · simpa using (prf.ref (Theory.fst T) y.fst)

/-- Evaluate a bounded closed term on quotient terms by choosing representatives. -/
noncomputable def term_model_fun {L : Language.{u}} {T : Theory L} {l : Nat}
    (t : closed_preterm L l) (ts : dvector (term_model' T) l) : term_model' T :=
  term_model_fun' (T := T) t (ts.map Quotient.out)

/-- Evaluate a bounded closed relation formula on representatives in the raw term model carrier. -/
def term_model_rel' {L : Language.{u}} {T : Theory L} {l : Nat}
    (f : presentence L l) (ts : dvector (closed_term L) l) : Prop :=
  T ⊢' bd_apps_rel f ts

/-- The raw term-model relation respects provable equality of representatives. -/
theorem term_model_rel_iff {L : Language.{u}} {T : Theory L} {l : Nat}
    (f f' : presentence L (l + 1)) (x x' : closed_term L)
    (ht : equiv_preformulae (Theory.fst T) f.fst f'.fst)
    (hx : Theory.fst T ⊢ x.fst ≃ x'.fst) (ts : dvector (closed_term L) l) :
    term_model_rel' (T := T) (bd_apprel f x) ts ↔ term_model_rel' (T := T) (bd_apprel f' x') ts := by
  induction ts generalizing x x' with
  | nil =>
      have hSelf : equiv_preformulae (Theory.fst T) f.fst f.fst :=
        equiv_preformulae_refl (Theory.fst T) f.fst
      exact (iff_of_biimp (equiv_preformulae_apprel hSelf hx dvector.nil)).trans
        (iff_of_biimp (ht (dvector.cons x'.fst dvector.nil)))
  | cons y ys ih =>
      exact ih (f := bd_apprel f x) (f' := bd_apprel f' x') (x := y) (x' := y)
        (equiv_preformulae_apprel ht hx) (by simpa using (prf.ref (Theory.fst T) y.fst))

/-- Evaluate a bounded closed relation formula on quotient terms by choosing representatives. -/
noncomputable def term_model_rel {L : Language.{u}} {T : Theory L} {l : Nat}
    (f : presentence L l) (ts : dvector (term_model' T) l) : Prop :=
  term_model_rel' (T := T) f (ts.map Quotient.out)

/-- The term model structure on the quotient of closed terms by provable equality. -/
noncomputable def term_model {L : Language.{u}} (T : Theory L) : Structure L where
  carrier := term_model' T
  fun_map := fun f ts => term_model_fun (T := T) (bd_func f) ts
  rel_map := fun R ts => term_model_rel (T := T) (bd_rel R) ts

/-- The canonical quotient class of a closed term in the term model. -/
@[reducible] def term_mk {L : Language.{u}} {T : Theory L} (t : closed_term L) : term_model T :=
  Quotient.mk'' t

/-- Evaluating a term model function on canonical quotient classes recovers the raw application. -/
theorem term_model_fun_mk {L : Language.{u}} {T : Theory L} {l : Nat}
    (t : closed_preterm L l) (ts : dvector (closed_term L) l) :
    term_model_fun (T := T) t (ts.map (term_mk (T := T))) = term_mk (T := T) (bd_apps t ts) := by
  induction ts with
  | nil =>
      rfl
  | cons x xs ih =>
      let xout : closed_term L := Quotient.out (term_mk (T := T) x)
      have hx : Theory.fst T ⊢ xout.fst ≃ x.fst := by
        rcases Quotient.exact (Quotient.out_eq (term_mk (T := T) x)) with hx
        exact Classical.choice hx
      exact (term_model_fun_eq (T := T) t t xout x
        (equal_preterms_refl (Theory.fst T) t.fst) hx ((xs.map (term_mk (T := T))).map Quotient.out)).trans
        (ih (bd_app t x))

/-- Evaluating a term model relation on canonical quotient classes recovers the raw predicate. -/
theorem term_model_rel_mk {L : Language.{u}} {T : Theory L} {l : Nat}
    (f : presentence L l) (ts : dvector (closed_term L) l) :
    term_model_rel (T := T) f (ts.map (term_mk (T := T))) ↔ term_model_rel' (T := T) f ts := by
  induction ts with
  | nil =>
      rfl
  | cons x xs ih =>
      let xout : closed_term L := Quotient.out (term_mk (T := T) x)
      have hx : Theory.fst T ⊢ xout.fst ≃ x.fst := by
        rcases Quotient.exact (Quotient.out_eq (term_mk (T := T) x)) with hx
        exact Classical.choice hx
      have hSelf : equiv_preformulae (Theory.fst T) f.fst f.fst :=
        equiv_preformulae_refl (Theory.fst T) f.fst
      exact (term_model_rel_iff (T := T) f f xout x hSelf hx ((xs.map (term_mk (T := T))).map Quotient.out)).trans
        (ih (bd_apprel f x))

/-- Realizing a closed preterm in the term model on canonical quotient classes matches raw application. -/
lemma realize_closed_preterm_term_model_aux {L : Language.{u}} {T : Theory L} :
    ∀ {l : Nat} (t : preterm L l) (ht : bounded_term_at t 0) (ts : dvector (closed_term L) l),
      realize_bounded_term (dvector.nil : dvector (term_model T) 0) ⟨t, ht⟩ (ts.map (term_mk (T := T))) =
        term_mk (T := T) (bd_apps ⟨t, ht⟩ ts) := by
  intro l t
  induction t with
  | var k =>
      intro ht ts
      cases ht
  | func f =>
      intro ht ts
      simpa [realize_bounded_term, bd_apps] using
        (term_model_fun_mk (T := T) (t := bd_func f) (ts := ts))
  | app t₁ t₂ ih₁ ih₂ =>
      intro ht ts
      have h₂ := ih₂ ht.2 dvector.nil
      have h₁ := ih₁ ht.1 (dvector.cons (bd_apps ⟨t₂, ht.2⟩ dvector.nil) ts)
      simp [term_mk] at h₁ h₂
      rw [h₂.symm] at h₁
      simpa [realize_bounded_term, bd_apps] using h₁

/-- Realizing a closed preterm in the term model matches the canonical quotient class. -/
lemma realize_closed_preterm_term_model {L : Language.{u}} {T : Theory L} {l : Nat}
    (ts : dvector (closed_term L) l) (t : closed_preterm L l) :
    realize_bounded_term (dvector.nil : dvector (term_model T) 0) t (ts.map (term_mk (T := T))) =
      term_mk (T := T) (bd_apps t ts) := by
  cases t with
  | mk t ht =>
      simpa using realize_closed_preterm_term_model_aux (T := T) t ht ts

/-- Realizing a closed term in the term model returns its canonical quotient class. -/
@[simp] lemma realize_closed_term_term_model {L : Language.{u}} {T : Theory L} (t : closed_term L) :
    realize_closed_term (term_model T) t = term_mk (T := T) t := by
  simpa [realize_closed_term] using
    (realize_closed_preterm_term_model (T := T) dvector.nil t)

private theorem dvector_concat_nth_lt {α : Type u} :
    {n : Nat} → (xs : dvector α n) → (x : α) → ∀ m (h : m < n),
      (xs.concat x).nth m (Nat.lt_trans h (Nat.lt_succ_self n)) = xs.nth m h
  | 0, dvector.nil, _, _, h => False.elim (Nat.not_lt_zero _ h)
  | _ + 1, dvector.cons _ _, _, 0, _ => rfl
  | _ + 1, dvector.cons _ ys, x, m + 1, h =>
      dvector_concat_nth_lt ys x m (Nat.lt_of_succ_lt_succ h)

private theorem dvector_concat_nth_eq {α : Type u} {n : Nat} (xs : dvector α n) (x : α) :
    (xs.concat x).nth n (Nat.lt_succ_self n) = x := by
  induction xs with
  | nil =>
      rfl
  | cons y ys ih =>
      simpa using ih

private theorem realize_term_closed {L : Language.{u}} {S : Structure L}
    (t : closed_term L) (v : Nat → S) :
    realize_term v t.fst dvector.nil = realize_closed_term S t := by
  simpa [realize_closed_term] using
    (realize_bounded_term_eq
      (v₁ := (dvector.nil : dvector S 0)) (v₂ := v)
      (hv := by intro k hk; cases hk) (t := t) (xs := dvector.nil)).symm

lemma realize_subst_preterm {L : Language.{u}} {S : Structure L} {n l : Nat}
    (t : bounded_preterm L (n + 1) l) (xs : dvector S l) (s : closed_term L)
    (v : dvector S n) :
    realize_bounded_term v (substmax_bounded_term t s) xs =
      realize_bounded_term (v.concat (realize_closed_term S s)) t xs := by
  let a : S := realize_closed_term S s
  let v' : Nat → S := fun k => if hk : k < n then v.nth k hk else a
  have hv_left : ∀ k (hk : k < n), v.nth k hk = v' k := by
    intro k hk
    simp [v', hk]
  have hs_eval :
      realize_term v' (s.fst ↑ n) dvector.nil = a := by
    rw [show s.fst ↑ n = s.fst by
      simpa [lift_term] using bounded_term_at_lift_irrel (t := s.fst) n 0 s.2]
    simpa [a] using realize_term_closed (t := s) (v := v')
  have hleft :
      realize_bounded_term v (substmax_bounded_term t s) xs =
        realize_term v' (substmax_bounded_term t s).fst xs :=
    realize_bounded_term_eq (v₁ := v) (v₂ := v') (hv := hv_left)
      (t := substmax_bounded_term t s) (xs := xs)
  have hmid :
      realize_term v' (substmax_bounded_term t s).fst xs =
        realize_term (v'[a // n]) t.fst xs := by
    have hsubst :=
      realize_term_subst (v := v') (n := n) (t := t.fst) (s := s.fst) (xs := xs)
    rw [hs_eval] at hsubst
    simpa [a] using hsubst.symm
  have hv_right :
      ∀ k (hk : k < n + 1), (v.concat a).nth k hk = (v'[a // n]) k := by
    intro k hk
    by_cases hlt : k < n
    · rw [dvector_concat_nth_lt (xs := v) (x := a) k hlt]
      simp [v', subst_realize, hlt]
    · have hEq : k = n := by
        omega
      subst hEq
      rw [dvector_concat_nth_eq (xs := v) (x := a)]
      simp [v', subst_realize]
  have hright :
      realize_bounded_term (v.concat a) t xs = realize_term (v'[a // n]) t.fst xs :=
    realize_bounded_term_eq (v₁ := v.concat a) (v₂ := v'[a // n]) (hv := hv_right)
      (t := t) (xs := xs)
  calc
    realize_bounded_term v (substmax_bounded_term t s) xs =
      realize_term v' (substmax_bounded_term t s).fst xs := hleft
    _ = realize_term (v'[a // n]) t.fst xs := hmid
    _ = realize_bounded_term (v.concat a) t xs := hright.symm

lemma realize_subst_term {L : Language.{u}} {S : Structure L} {n : Nat}
    (v : dvector S n) (s : closed_term L) (t : bounded_term L (n + 1)) :
    realize_bounded_term v (substmax_bounded_term t s) dvector.nil =
      realize_bounded_term (v.concat (realize_closed_term S s)) t dvector.nil := by
  simpa using realize_subst_preterm (t := t) (xs := dvector.nil) (s := s) (v := v)

lemma realize_subst_formula {L : Language.{u}} (S : Structure L) {n : Nat}
    (f : bounded_formula L (n + 1)) (t : closed_term L) (v : dvector S n) :
    realize_bounded_formula v (substmax_bounded_formula f t) dvector.nil ↔
      realize_bounded_formula (v.concat (realize_closed_term S t)) f dvector.nil := by
  let a : S := realize_closed_term S t
  let v' : Nat → S := fun k => if hk : k < n then v.nth k hk else a
  have hv_left : ∀ k (hk : k < n), v.nth k hk = v' k := by
    intro k hk
    simp [v', hk]
  have ht_eval :
      realize_term v' (t.fst ↑ n) dvector.nil = a := by
    rw [show t.fst ↑ n = t.fst by
      simpa [lift_term] using bounded_term_at_lift_irrel (t := t.fst) n 0 t.2]
    simpa [a] using realize_term_closed (t := t) (v := v')
  have hleft :
      realize_bounded_formula v (substmax_bounded_formula f t) dvector.nil ↔
        realize_formula v' (substmax_bounded_formula f t).fst dvector.nil :=
    realize_bounded_formula_iff (v₁ := v) (v₂ := v') (hv := hv_left)
      (f := substmax_bounded_formula f t) (xs := dvector.nil)
  have hmid :
      realize_formula v' (substmax_bounded_formula f t).fst dvector.nil ↔
        realize_formula (v'[a // n]) f.fst dvector.nil := by
    have hsubst :=
      realize_formula_subst (v := v') (n := n) (f := f.fst) (s := t.fst)
        (xs := dvector.nil)
    rw [ht_eval] at hsubst
    simpa [a] using hsubst.symm
  have hv_right :
      ∀ k (hk : k < n + 1), (v.concat a).nth k hk = (v'[a // n]) k := by
    intro k hk
    by_cases hlt : k < n
    · rw [dvector_concat_nth_lt (xs := v) (x := a) k hlt]
      simp [v', subst_realize, hlt]
    · have hEq : k = n := by
        omega
      subst hEq
      rw [dvector_concat_nth_eq (xs := v) (x := a)]
      simp [v', subst_realize]
  have hright :
      realize_bounded_formula (v.concat a) f dvector.nil ↔
        realize_formula (v'[a // n]) f.fst dvector.nil :=
    realize_bounded_formula_iff (v₁ := v.concat a) (v₂ := v'[a // n]) (hv := hv_right)
      (f := f) (xs := dvector.nil)
  exact hleft.trans (hmid.trans hright.symm)

lemma realize_subst_formula0 {L : Language.{u}} (S : Structure L) (f : bounded_formula L 1)
    (t : closed_term L) :
    realize_bounded_formula (dvector.nil : dvector S 0) (substmax_bounded_formula f t) dvector.nil ↔
      realize_bounded_formula (dvector.cons (realize_closed_term S t) dvector.nil) f dvector.nil := by
  simpa using realize_subst_formula S (n := 0) f t (dvector.nil : dvector S 0)

lemma term_model_subst0 {L : Language.{u}} {T : Theory L} (f : bounded_formula L 1)
    (t : closed_term L) :
    realize_bounded_formula
        (dvector.nil : dvector (term_model T) 0) (substmax_bounded_formula f t) dvector.nil ↔
      realize_bounded_formula
        (dvector.cons (term_mk (T := T) t) dvector.nil) f dvector.nil := by
  simpa using realize_subst_formula0 (S := term_model T) f t

@[simp] theorem count_quantifiers_subst_formula {L : Language.{u}} {l : Nat}
    (f : preformula L l) (t : term L) (n : Nat) :
    count_quantifiers (subst_formula f t n) = count_quantifiers f := by
  induction f generalizing n with
  | falsum =>
      rfl
  | equal _ _ =>
      rfl
  | rel _ =>
      rfl
  | apprel f s ih =>
      simpa [subst_formula] using ih n
  | imp f₁ f₂ ih₁ ih₂ =>
      simp [subst_formula, ih₁, ih₂]
  | all f ih =>
      simpa [subst_formula] using ih (n + 1)

/-- A Henkin theory has a nonempty term model by choosing any witness constant. -/
theorem nonempty_term_model {L : Language.{u}} {T : Theory L} (hT : has_enough_constants T) :
    Nonempty (term_model T) := by
  rcases hT with ⟨C, _⟩
  refine ⟨Quotient.mk'' (bd_const (L := L) (n := 0)
    (C (bd_equal (bd_var ⟨0, by decide⟩) (bd_var ⟨0, by decide⟩))))⟩

/-- In a complete Henkin theory, provability agrees with truth in the term model. -/
theorem term_model_ssatisfied_iff {L : Language.{u}} {T : Theory L}
    (hComplete : is_complete T) (hHenkin : has_enough_constants T) :
    {n : Nat} → ∀ {l : Nat} (f : presentence L l) (ts : dvector (closed_term L) l),
      count_quantifiers f.fst < n →
        (T ⊢' bd_apps_rel f ts ↔
          realize_bounded_formula (dvector.nil : dvector (term_model T) 0) f
            (ts.map (term_mk (T := T)))) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro l f ts hn
      have hmain :
          ∀ {l : Nat} (f₀ : preformula L l) (hf₀ : bounded_formula_at f₀ 0)
            (ts : dvector (closed_term L) l),
            count_quantifiers f₀ < n →
              (T ⊢' bd_apps_rel ⟨f₀, hf₀⟩ ts ↔
                realize_bounded_formula (dvector.nil : dvector (term_model T) 0) ⟨f₀, hf₀⟩
                  (ts.map (term_mk (T := T)))) := by
        intro l f₀
        induction f₀ with
        | falsum =>
            intro hf₀ ts hn₀
            cases ts
            constructor
            · intro h
              exact False.elim (hComplete.1 h)
            · intro hFalse
              simpa [realize_bounded_formula] using hFalse
        | equal t₁ t₂ =>
            intro hf₀ ts hn₀
            cases ts
            let t₁' : closed_term L := ⟨t₁, hf₀.1⟩
            let t₂' : closed_term L := ⟨t₂, hf₀.2⟩
            constructor
            · intro h
              simpa [t₁', t₂', realize_bounded_formula, realize_closed_term_term_model] using
                (Quotient.sound h : term_mk (T := T) t₁' = term_mk (T := T) t₂')
            · intro hEq
              have hEq' : term_mk (T := T) t₁' = term_mk (T := T) t₂' := by
                simpa [t₁', t₂', realize_bounded_formula, realize_closed_term_term_model] using hEq
              simpa [t₁', t₂'] using (Quotient.exact hEq' : term_rel T t₁' t₂')
        | rel R =>
            intro hf₀ ts hn₀
            simpa [bd_apps_rel, realize_bounded_formula, term_model, term_model_rel'] using
              (term_model_rel_mk (T := T) (f := bd_rel (L := L) (n := 0) R) (ts := ts)).symm
        | apprel f₁ t ih₁ =>
            intro hf₀ ts hn₀
            let t' : closed_term L := ⟨t, hf₀.2⟩
            have hn₁ : count_quantifiers f₁ < n := by
              simpa using hn₀
            simpa [t', bd_apps_rel, realize_bounded_formula, realize_closed_term_term_model] using
              (ih₁ hf₀.1 (dvector.cons t' ts) hn₁)
        | imp f₁ f₂ ih₁ ih₂ =>
            intro hf₀ ts hn₀
            cases ts
            have hnSum : count_quantifiers f₁ + count_quantifiers f₂ < n := by
              simpa using hn₀
            have hn₁ : count_quantifiers f₁ < n := by
              exact lt_of_le_of_lt (Nat.le_add_right _ _) hnSum
            have hn₂ : count_quantifiers f₂ < n := by
              exact lt_of_le_of_lt (Nat.le_add_left _ _) hnSum
            have ih₁' := ih₁ hf₀.1 dvector.nil hn₁
            have ih₂' := ih₂ hf₀.2 dvector.nil hn₂
            constructor
            · intro h
              simp [realize_bounded_formula]
              intro h₁
              have hp₁ : T ⊢' (⟨f₁, hf₀.1⟩ : sentence L) := ih₁'.mpr h₁
              have hp₂ : T ⊢' (⟨f₂, hf₀.2⟩ : sentence L) := by
                exact simpE' (⟨f₁, hf₀.1⟩ : sentence L) (by simpa using h) hp₁
              exact ih₂'.mp hp₂
            · intro hSem
              have hSem' :
                  realize_bounded_formula (dvector.nil : dvector (term_model T) 0) ⟨f₁, hf₀.1⟩ dvector.nil →
                    realize_bounded_formula (dvector.nil : dvector (term_model T) 0) ⟨f₂, hf₀.2⟩
                      dvector.nil := by
                simpa [realize_bounded_formula] using hSem
              simpa using
                impI_of_is_complete hComplete (fun h₁ => ih₂'.mpr (hSem' (ih₁'.mp h₁)))
        | all f₁ ih₁ =>
            intro hf₀ ts hn₀
            cases ts
            let f' : bounded_formula L 1 := ⟨f₁, hf₀⟩
            constructor
            · intro h
              simp [realize_bounded_formula]
              intro x
              refine Quotient.inductionOn x ?_
              intro t
              cases n with
              | zero =>
                  exfalso
                  exact Nat.not_lt_zero _ hn₀
              | succ n' =>
                  have hSub :
                      T ⊢' bd_apps_rel (substmax_bounded_formula f' t) dvector.nil := by
                    simpa [f', bd_apps_rel, substmax_eq_subst0_formula] using
                      (allE₂' (Γ := Theory.fst T) (A := f₁) (t := t.fst)
                        (by simpa [bd_apps_rel] using h))
                  have hnSub : count_quantifiers (substmax_bounded_formula f' t).fst < n' := by
                    simpa [f', count_quantifiers_subst_formula] using Nat.lt_of_succ_lt_succ hn₀
                  have hSubReal :=
                    (ih n' (Nat.lt_succ_self n') (f := substmax_bounded_formula f' t)
                      (ts := dvector.nil) hnSub).mp hSub
                  exact (term_model_subst0 (T := T) f' t).mp hSubReal
            · classical
              intro hReal
              have hReal' :
                  ∀ x : term_model T,
                    realize_bounded_formula (dvector.cons x dvector.nil) f' dvector.nil := by
                simpa [f', realize_bounded_formula] using hReal
              by_contra hNot
              rcases find_counterexample_of_henkin hComplete hHenkin f' hNot with ⟨t, ht⟩
              cases n with
              | zero =>
                  exfalso
                  exact Nat.not_lt_zero _ hn₀
              | succ n' =>
                  have hSubReal :
                      realize_bounded_formula
                        (dvector.nil : dvector (term_model T) 0) (substmax_bounded_formula f' t)
                        dvector.nil := by
                    exact (term_model_subst0 (T := T) f' t).mpr (hReal' (term_mk (T := T) t))
                  have hnSub : count_quantifiers (substmax_bounded_formula f' t).fst < n' := by
                    simpa [f', count_quantifiers_subst_formula] using Nat.lt_of_succ_lt_succ hn₀
                  have hPosSub :
                      T ⊢' bd_apps_rel (substmax_bounded_formula f' t) dvector.nil :=
                    (ih n' (Nat.lt_succ_self n') (f := substmax_bounded_formula f' t)
                      (ts := dvector.nil) hnSub).mpr hSubReal
                  have hPos : T ⊢' Lhom.boundedFormulaSubstSentence f' t := by
                    simpa [Lhom.boundedFormulaSubstSentence, f', bd_apps_rel, substmax_eq_subst0_formula] using hPosSub
                  exact hComplete.1 (simpE' (Lhom.boundedFormulaSubstSentence f' t) ht hPos)
      exact hmain f.fst f.2 ts hn

/-- The term model of a complete Henkin theory satisfies the theory. -/
theorem term_model_ssatisfied {L : Language.{u}} {T : Theory L}
    (hComplete : is_complete T) (hHenkin : has_enough_constants T) :
    all_realize_sentence (term_model T) T := by
  intro f hf
  let f₀ : bounded_formula L 0 := f
  have hq : count_quantifiers f₀.fst < count_quantifiers f₀.fst + 1 :=
    Nat.lt_succ_self _
  have hReal :
      realize_bounded_formula (dvector.nil : dvector (term_model T) 0) f₀ dvector.nil := by
    exact (term_model_ssatisfied_iff (T := T) hComplete hHenkin
      (n := count_quantifiers f₀.fst + 1) (f := f₀) (ts := dvector.nil) hq).mp ⟨saxm hf⟩
  intro v
  exact (realize_bounded_formula_iff
    (v₁ := dvector.nil) (v₂ := v) (hv := by intro k hk; cases hk)
    (f := f₀) (xs := dvector.nil)).mp hReal

/-- Completeness for complete Henkin theories. -/
lemma completeness' {L : Language.{u}} {T : Theory L}
    (hComplete : is_complete T) (hHenkin : has_enough_constants T) {f : sentence L}
    (H : ssatisfied T f) : T ⊢' f := by
  let f₀ : bounded_formula L 0 := f
  have hq : count_quantifiers f₀.fst < count_quantifiers f₀.fst + 1 :=
    Nat.lt_succ_self _
  have hReal : realize_sentence (term_model T) f := by
    exact H (nonempty_term_model (T := T) hHenkin) (term_model_ssatisfied (T := T) hComplete hHenkin)
  have hBounded :
      realize_bounded_formula (dvector.nil : dvector (term_model T) 0) f₀ dvector.nil := by
    exact (realize_bounded_formula_iff
      (v₁ := dvector.nil) (v₂ := fun _ => Classical.choice (nonempty_term_model (T := T) hHenkin))
      (hv := by intro k hk; cases hk)
      (f := f₀) (xs := dvector.nil)).mpr
      (hReal _)
  exact (term_model_ssatisfied_iff (T := T) hComplete hHenkin
    (n := count_quantifiers f₀.fst + 1) (f := f₀) (ts := dvector.nil) hq).mpr
    hBounded

/-- The original theory embeds into its Henkinization via the base language map. -/
lemma theory_induced_subset_henkinization {L : Language.{u}} {T : Theory L}
    (hT : is_consistent T) :
    Theory.Subset
      (Lhom.Theory_induced (henkinLanguageOver (L := L) (T := T)) T)
      (henkinization (L := L) (T := T) hT) := by
  intro f hf
  unfold henkinization TInfty
  refine Set.mem_iUnion.mpr ⟨0, ?_⟩
  simpa [iota, henkinTheoryChain, henkinLanguageOver]
    using hf

/-- Every consistent theory has a nonempty model, obtained by reduct from its completed
Henkin term model. -/
theorem satisfiable_of_consistent {L : Language.{u}} {T : Theory L}
    (hT : is_consistent T) :
    ∃ M : Structure L, Nonempty M ∧ all_realize_sentence M T := by
  let T' : Theory (henkinLanguage (L := L) T) :=
    completion_of_henkinization (L := L) (T := T) hT
  let M' : Structure (henkinLanguage (L := L) T) := term_model T'
  let M : Structure L := Lhom.reduct (henkinLanguageOver (L := L) (T := T)) M'
  have hAllT' : all_realize_sentence M' T' :=
    term_model_ssatisfied (T := T')
      (completion_of_henkinization_complete (L := L) (T := T) hT)
      (completion_of_henkinization_is_henkin (L := L) (T := T) hT)
  refine ⟨M, ?_, ?_⟩
  · exact Lhom.reduct_nonempty_of_nonempty
      (ϕ := henkinLanguageOver (L := L) (T := T))
      (nonempty_term_model (T := T')
        (completion_of_henkinization_is_henkin (L := L) (T := T) hT))
  · apply Lhom.reduct_all_realize_sentence
      (ϕ := henkinLanguageOver (L := L) (T := T))
    intro f hf
    exact hAllT'
      ((completion_of_henkinization_contains (L := L) (T := T) hT)
        ((theory_induced_subset_henkinization (L := L) (T := T) hT) hf))

/-- Completeness for arbitrary theories. -/
theorem completeness {L : Language.{u}} {T : Theory L} {f : sentence L}
    (H : ssatisfied T f) : T ⊢' f := by
  by_cases hT : is_consistent T
  · by_contra hNot
    have hCons : is_consistent (T ∪ ({∼f} : Theory L)) :=
      consis_not_of_not_provable (T := T) (f := f) hNot
    rcases satisfiable_of_consistent (L := L) (T := T ∪ ({∼f} : Theory L)) hCons with
      ⟨M, hM, hAll⟩
    have hAllT : all_realize_sentence M T := by
      intro g hg
      exact hAll (Or.inl hg)
    have hf : realize_sentence M f := H hM hAllT
    have hNotf : realize_sentence M (∼f) := hAll (Or.inr rfl)
    let v : Nat → M := fun _ => Classical.choice hM
    exact hNotf v (hf v)
  · have hBot : T ⊢' (⊥ : sentence L) := by
      change ¬ ¬ T ⊢' (⊥ : sentence L) at hT
      exact Classical.not_not.mp hT
    apply sfalsumE'
    rcases hBot with ⟨hBot⟩
    exact ⟨sweakening (T' := T) (T := insert (∼f) T)
      (fun x hx => by
        show x ∈ (insert (∼f) T).carrier
        exact Or.inr hx) hBot⟩

end henkin

end Flypitch

attribute [nolint docBlame]
  Flypitch.colimit.directed_diagram_language Flypitch.colimit.directed_diagram_language.obj
  Flypitch.colimit.directed_diagram_language.mor Flypitch.colimit.diagram_functions
  Flypitch.colimit.diagram_relations Flypitch.colimit.colimit_language
  Flypitch.colimit.canonical_map_language Flypitch.colimit.cocone_language
  Flypitch.colimit.cocone_language.vertex Flypitch.colimit.cocone_language.map
  Flypitch.colimit.cocone_of_colimit_language Flypitch.colimit.universal_map_language
  Flypitch.henkin.languageFunctions Flypitch.henkin.languageStep Flypitch.henkin.wit'
  Flypitch.henkin.inclusion Flypitch.henkin.chainObjects Flypitch.henkin.chainMaps
  Flypitch.henkin.languageChain Flypitch.henkin.LInfty Flypitch.henkin.canonicalMap
  Flypitch.henkin.termChain Flypitch.henkin.formulaChain Flypitch.henkin.boundedTermChain
  Flypitch.henkin.boundedTermChain' Flypitch.henkin.boundedFormulaChain
  Flypitch.henkin.boundedFormulaChain' Flypitch.henkin.coconeOfLInfty
  Flypitch.henkin.coconeOfTermLInfty Flypitch.henkin.coconeOfFormulaLInfty
  Flypitch.henkin.coconeOfBoundedTermLInfty Flypitch.henkin.coconeOfBoundedFormulaLInfty
  Flypitch.henkin.coconeOfBoundedFormulaPrimeLInfty Flypitch.henkin.termComparison
  Flypitch.henkin.formulaComparison Flypitch.henkin.boundedTermComparison
  Flypitch.henkin.boundedTermComparison' Flypitch.henkin.boundedFormulaComparison
  Flypitch.henkin.boundedFormulaComparison' Flypitch.henkin.equivBoundedFormulaComparison
  Flypitch.henkin.witProperty Flypitch.henkin.has_enough_constants
  Flypitch.henkin.henkinTheoryStep Flypitch.henkin.henkinTheoryChain Flypitch.henkin.iota
  Flypitch.henkin.TInfty Flypitch.henkin.henkinLanguage Flypitch.henkin.henkinLanguageOver
  Flypitch.henkin.completeHenkinTheoryOver Flypitch.henkin.henkinization
  Flypitch.henkin.witInfty
