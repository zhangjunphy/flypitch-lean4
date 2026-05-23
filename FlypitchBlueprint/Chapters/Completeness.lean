import Verso
import VersoManual
import VersoBlueprint
import Flypitch.Henkin
import Flypitch.Completion
import Flypitch.Compactness
import Flypitch.LanguageExtension
import Flypitch.Colimit

open Verso.Genre
open Verso.Genre.Manual
open Informal

set_option linter.hashCommand false

#doc (Manual) "The Completeness Theorem and Compactness" =>

The soundness theorem ({uses "thm:classical-soundness"}[]) tells us that
provability implies semantic truth. The completeness theorem is the converse: if
a formula is true in all models of a theory, it is provable from that theory.
Together, soundness and completeness establish that syntactic provability and
semantic entailment coincide for first-order logic.

This chapter develops the proof of completeness via the Henkin construction,
and derives the compactness theorem as a corollary.

# The Completeness Theorem

:::theorem "thm:completeness" (lean := "fol.formula_completeness")
**Gödel's Completeness Theorem.** Let $`T`$ be a theory in a first-order
language. If $`T \models \varphi`$ (every model of $`T`$ satisfies
$`\varphi`$), then $`T \vdash' \varphi`$ (there is a formal proof of
$`\varphi`$ from $`T`$).
:::

The proof proceeds in three stages:

1. **Henkinization.** Extend the language with *witness constants* --- for every
   existential formula $`\exists x\,\varphi(x)`$, add a new constant symbol
   $`c_{\exists x\,\varphi}`$ and the axiom
   $`\exists x\,\varphi(x) \to \varphi(c_{\exists x\,\varphi})`$. This ensures
   that every existential statement true in the theory has an explicit witness.

2. **Completion.** Using Zorn's Lemma, extend the consistent Henkin theory to a
   *maximal consistent* theory. A maximal consistent theory contains either
   $`\varphi`$ or $`\neg\varphi`$ for every sentence $`\varphi`$, and is
   deductively closed.

3. **Term model construction.** Given a maximal consistent Henkin theory
   $`\mathcal{H}`$, construct a model $`\mathcal{M}_{\mathcal{H}}`$ whose
   domain consists of the closed terms of the language modulo provable equality.
   Show that $`\mathcal{M}_{\mathcal{H}} \models \varphi`$ if and only if
   $`\mathcal{H} \vdash' \varphi`$.

Since every consistent theory can be extended to a maximal consistent Henkin
theory, and every such theory has a model, it follows that every consistent
theory has a model. The completeness theorem is equivalent to this statement
(the *model existence* formulation).

# Henkinization and Directed Colimits

The construction of the Henkin language and theory involves building a chain of
language extensions. Each step adds witness constants for the existential
formulas of the previous step, and we take the *colimit* (direct limit) of this
chain to obtain the full Henkin language.

:::definition "def:language-extension" (lean := "Flypitch.LanguageExtension.Lhom")
A *language homomorphism* $`\Phi : \mathcal{L} \to \mathcal{L}'`$ maps function
symbols and relation symbols of $`\mathcal{L}`$ to corresponding symbols of
$`\mathcal{L}'`$ of the same arity. This induces maps on terms, formulas, and
theories.
:::

:::definition "def:directed-colimit" (lean := "Flypitch.Colimit.colimit")
A *directed colimit* of a diagram of structures $`A_0 \to A_1 \to A_2 \to
\cdots`$ (indexed by a directed order) is a structure $`A_\infty`$ together
with canonical maps from each $`A_i`$ that commute with the transition maps,
satisfying the universal property: any compatible family of maps from the
$`A_i`$ to a target factors uniquely through $`A_\infty`$.
:::

:::definition "def:henkin-language" (lean := "Flypitch.Henkin.LInfty")
The *Henkin language* $`\mathcal{L}_\infty`$ for a language $`\mathcal{L}`$
is the colimit of the chain
$`\mathcal{L} = \mathcal{L}_0 \to \mathcal{L}_1 \to \mathcal{L}_2 \to \cdots`$,
where $`\mathcal{L}_{n+1}`$ extends $`\mathcal{L}_n`$ by adding, for each
bounded formula $`\varphi(x)`$ in $`\mathcal{L}_n`$ with one free variable, a
new constant symbol $`c_\varphi`$.
:::

The Henkin axioms are then added to the original theory: for each witness
constant $`c`$ corresponding to $`\exists x\,\varphi(x)`$, we include the
axiom $`\exists x\,\varphi(x) \to \varphi(c)`$.

# Maximal Consistent Extensions

:::definition "def:consistent" (lean := "fol.is_consistent")
A theory $`T`$ is *consistent* if $`T \not\vdash' \bot`$. Equivalently, there
is no sentence $`\varphi`$ such that both $`T \vdash' \varphi`$ and
$`T \vdash' \neg\varphi`$.
:::

:::lemma_ "lem:completion-of-consis" (lean := "fol.completion_of_consis")
Every consistent theory $`T`$ can be extended to a maximal consistent theory
$`T^* \supseteq T`$ that is *complete*: for every sentence $`\varphi`$,
either $`T^* \vdash' \varphi`$ or $`T^* \vdash' \neg\varphi`$.
:::

The proof uses Zorn's Lemma. Consider the set of all consistent extensions of
$`T`$, partially ordered by inclusion. Given a chain of consistent extensions,
their union is also consistent (any proof of $`\bot`$ from the union would
use only finitely many axioms, hence would be a proof from some member of the
chain). Zorn's Lemma yields a maximal element, which is the desired maximal
consistent extension.

# The Term Model

Given a maximal consistent Henkin theory $`\mathcal{H}`$, define an
equivalence relation on closed terms: $`t \sim s`$ if
$`\mathcal{H} \vdash' t \simeq s`$. The domain of the term model
$`\mathcal{M}_{\mathcal{H}}`$ is the set of equivalence classes.

Function symbols are interpreted pointwise:
$`f^{\mathcal{M}}([t_1], \dots, [t_n]) = [f(t_1, \dots, t_n)]`$. Relation
symbols are interpreted by:
$`R^{\mathcal{M}}([t_1], \dots, [t_n])`$ holds iff
$`\mathcal{H} \vdash' R(t_1, \dots, t_n)`$.

The main lemma is the *truth lemma*: for every sentence $`\varphi`$,
$`\mathcal{M}_{\mathcal{H}} \models \varphi`$ if and only if
$`\mathcal{H} \vdash' \varphi`$. This is proved by induction on the structure
of $`\varphi`$. The Henkin axioms ensure that whenever
$`\mathcal{M}_{\mathcal{H}} \models \exists x\,\varphi(x)`$, there is an
explicit witness constant $`c`$ such that
$`\mathcal{H} \vdash' \exists x\,\varphi(x) \to \varphi(c)`$, so
$`\mathcal{H} \vdash' \varphi(c)`$ and by the induction hypothesis,
$`\mathcal{M}_{\mathcal{H}} \models \varphi(c)`$.

:::proof "proof:completeness"
Starting from a consistent theory $`T`$, we extend the language to the Henkin
language $`\mathcal{L}_\infty`$ and add the Henkin axioms to $`T`$ to obtain
$`T_H`$. The Henkin extension preserves consistency. Then we apply Zorn's
Lemma to obtain a maximal consistent extension $`T_H^*`$ of $`T_H`$. The term
model $`\mathcal{M}_{T_H^*}`$ satisfies a sentence $`\varphi`$ exactly when
$`T_H^* \vdash' \varphi`$. In particular, it satisfies all axioms of
$`T`$, so it is a model of $`T`$. This proves that every consistent theory
has a model, which is equivalent to the completeness theorem.
:::

# The Compactness Theorem

An immediate consequence of completeness is the compactness theorem, which
states that a theory is satisfiable if and only if all its finite subsets are
satisfiable.

:::theorem "thm:compactness" (lean := "fol.theory_proof_compactness")
**Compactness Theorem.** Let $`T`$ be a theory and $`\varphi`$ a sentence. If
$`T \vdash' \varphi`$, then there exists a finite subset $`T_0 \subseteq T`$
such that $`T_0 \vdash' \varphi`$.
:::

Equivalently, if every finite subset of $`T`$ has a model, then $`T`$ itself
has a model. The proof is straightforward: if $`T \models \varphi`$, then by
completeness $`T \vdash' \varphi`$. Since proofs are finite, only finitely many
axioms of $`T`$ are used in the proof. Let $`T_0`$ be those axioms; then
$`T_0 \vdash' \varphi`$.

The compactness theorem has numerous applications in model theory. For instance,
it implies the existence of nonstandard models of arithmetic and of set theory,
and it can be used to construct models with specific cardinalities (the
Loewenheim--Skolem theorems).

While the compactness and completeness theorems are cornerstones of first-order
logic, they are not directly used in the CH independence proof via forcing. The
forcing argument requires only the Boolean-valued soundness theorem
({uses "thm:boolean-soundness"}[]). We include this chapter for completeness of
the logical development.
