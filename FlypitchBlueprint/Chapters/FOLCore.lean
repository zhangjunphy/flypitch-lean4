import Verso
import VersoManual
import VersoBlueprint
import Flypitch.FOL
import Flypitch.Compactness
import Flypitch.Completion
import Flypitch.Colimit
import Flypitch.LanguageExtension
import Flypitch.Henkin
import Flypitch.Examples.Abel

open Verso.Genre
open Verso.Genre.Manual
open Informal

set_option linter.hashCommand false
set_option linter.style.emptyLine false

#doc (Manual) "First-Order Logic And Completeness" =>

The independence proof is a statement about formal derivability. Before
forcing enters, the proof needs a precise connection between syntax and
semantics: proofs are finite symbolic objects, while models are mathematical
structures in which sentences can be evaluated.

# Languages, Terms, And Formulas

:::definition "def:fol-language" (lean := "Flypitch.fol.Language")
A first-order language specifies function symbols and relation symbols,
sorted by arity.
:::

For example, the language of groups has a binary multiplication symbol, a
unary inverse symbol, and a constant for the identity. A structure for this
language chooses an underlying type and interprets those symbols as actual
operations. The same formal sentence can then be tested in the integers, in a
finite group, or in any other structure with those operations.

The language of set theory is even smaller at the relation level: it has the
membership relation, together with selected function symbols used by the
formal encoding of the ZFC axioms.

:::definition "def:fol-syntax"
Once a language is fixed, terms are built from variables and function symbols,
and formulas are built from relation symbols, equality, logical connectives,
and quantifiers.

The Lean development uses `preterm`, `preformula`, `bounded_term`, and
`bounded_formula`.
:::

# Derivations And Soundness

:::definition "def:fol-derivability" (lean := "Flypitch.fol.prf")
The relation $`\Gamma \vdash \varphi` means that the formula $`\varphi` has a
formal derivation from the assumptions in $`\Gamma`.
:::

A proof system is useful only if its rules respect the intended semantics.
Soundness is that guarantee: anything derivable from true assumptions is true.

:::definition "def:fol-structure" (lean := "Flypitch.fol.Structure")
An $`L`-structure consists of a carrier together with interpretations of all
function and relation symbols of the language $`L`.
:::

:::theorem "thm:fol-soundness" (lean := "Flypitch.fol.formula_soundness")
If $`\Gamma \vdash \varphi`, then every structure satisfying all formulas in
$`\Gamma` also satisfies $`\varphi`.

This theorem depends on {uses "def:fol-language"}[],
{uses "def:fol-syntax"}[], {uses "def:fol-derivability"}[], and
{uses "def:fol-structure"}[].
:::

The proof is by induction on the derivation. The quantifier and substitution
cases are the main bookkeeping steps, because one must compare formulas before
and after variables are reassigned.

# Compactness And Complete Theories

Formal derivations are finite. This simple fact becomes the compactness
principle used throughout the completeness proof.

:::theorem "thm:proof-compactness" (lean := "Flypitch.fol.proof_compactness")
If a formula is derivable from a set of assumptions, then it is derivable from
some finite subset of those assumptions.

This uses {uses "def:fol-derivability"}[].
:::

At the level of theories, compactness says that inconsistency is already
visible in a finite fragment. This makes it possible to enlarge a consistent
theory one sentence at a time.

:::theorem "thm:completion" (lean := "Flypitch.fol.completion_of_consis")
Every consistent first-order theory has a complete consistent extension.

This theorem uses {uses "thm:proof-compactness"}[].
:::

Completeness here means that every sentence is decided: either the sentence or
its negation belongs to the extended theory. The proof uses the usual maximal
consistent extension argument.

# Henkin Witnesses

To build a model from a consistent theory, existential statements need named
witnesses. The Henkin construction enlarges the language by adding constants
for formulas in one free variable, then adds axioms saying that these constants
serve as witnesses when a witness exists.

:::definition "def:henkin-language" (lean := "Flypitch.henkin.LInfty")
The infinite Henkin language is the directed limit of the languages obtained
by repeatedly adjoining witness constants.

It uses the colimit and language-extension machinery from
{uses "def:language-extension-tools"}[].
:::

:::theorem "thm:complete-henkinization" (lean := "Flypitch.henkin.completeHenkinizationOfConsis")
Every consistent theory admits a complete Henkin extension in a larger
language.

This theorem combines {uses "thm:completion"}[] with the Henkin witness
construction.
:::

:::definition "def:language-extension-tools" (lean := "Flypitch.colimit.colimit, Flypitch.fol.Lhom")
Language maps, reducts, reflected formulas, and directed colimits let formulas
and theories be compared across the languages introduced by Henkin witnesses.
:::

# A Small Example

The abelian-group example illustrates the distinction between language,
theory, and model. The language provides symbols such as addition and zero;
the theory lists the group axioms and commutativity; the integers form a model
because the usual integer operations satisfy those axioms.

:::theorem "thm:abelian-example" (lean := "Flypitch.abel.int_satisfies_of_prf")
The standard integer structure satisfies the formal abelian-group theory.
:::

# Lean Side Notes

The logic side is anchored by the modules `Flypitch.FOL`,
`Flypitch.Compactness`, `Flypitch.Completion`, `Flypitch.Colimit`,
`Flypitch.LanguageExtension`, and `Flypitch.Henkin`. Their role in the
independence proof is to justify the soundness principles that turn formal
ZFC derivations into semantic facts about Boolean-valued universes.
