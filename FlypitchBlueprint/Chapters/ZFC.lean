import Verso
import VersoManual
import VersoBlueprint
import Flypitch.ZFC
import Flypitch.SetTheory
import Flypitch.PSetOrdinal

open Verso.Genre
open Verso.Genre.Manual
open Informal

set_option linter.hashCommand false

#doc (Manual) "ZFC and the Continuum Hypothesis" =>

We now formalize the theory ZFC and the Continuum Hypothesis as a sentence of
first-order logic. We then define the Boolean-valued universe
$`V^{\mathbb{B}}`$ as a Boolean-valued ZFC structure and prove that it
satisfies all ZFC axioms with truth value $`\top`$.

# The Language of ZFC

:::definition "def:zfc-language" (lean := "Flypitch.ZFC.L_ZFC")
The language $`\mathcal{L}_{\text{ZFC}}`$ has:
- one binary relation symbol $`\in`$ (epsilon),
- constant symbols (function symbols of arity $`0`$): $`\emptyset`$
  (empty set), $`\omega`$ (the set of natural numbers),
- function symbols: $`\{-,-\}`$ (unordered pair, arity $`2`$),
  $`\bigcup`$ (union, arity $`1`$), $`\mathcal{P}`$ (powerset,
  arity $`1`$).
:::

This is a minimal but sufficient language for expressing all of ZFC. Other
notions (such as ordered pairs, functions, ordinals, cardinals) are defined as
abbreviations within the language, as is standard in set theory.

# The Axioms of ZFC

The theory ZFC consists of nine axiom schemas expressed as sentences of
$`\mathcal{L}_{\text{ZFC}}`$. We list them here with their formal
counterparts.

:::definition "def:axiom-empty-set" (lean := "Flypitch.ZFC.axiomOfEmptyset")
**Empty Set.** $`\exists x\,\forall y\,(y \notin x)`$. There exists a set with
no elements.
:::

:::definition "def:axiom-extensionality" (lean := "Flypitch.ZFC.axiomOfExtensionality")
**Extensionality.** $`\forall x\,\forall y\,(\forall z\,(z \in x
\leftrightarrow z \in y) \to x = y)`$. Sets are determined by their
elements.
:::

:::definition "def:axiom-pairing" (lean := "Flypitch.ZFC.axiomOfOrderedPairs")
**Pairing.** $`\forall x\,\forall y\,\exists z\,(x \in z \land y \in z)`$.
For any two sets, there is a set containing both. (The formal version uses
ordered pairs to encode the unordered pair.)
:::

:::definition "def:axiom-union" (lean := "Flypitch.ZFC.axiomOfUnion")
**Union.** $`\forall x\,\exists y\,\forall z\,(z \in y \leftrightarrow
\exists w\,(w \in x \land z \in w))`$. The union of a set exists.
:::

:::definition "def:axiom-powerset" (lean := "Flypitch.ZFC.axiomOfPowerset")
**Powerset.** $`\forall x\,\exists y\,\forall z\,(z \in y \leftrightarrow
z \subseteq x)`$. The powerset of a set exists.
:::

:::definition "def:axiom-infinity" (lean := "Flypitch.ZFC.axiomOfInfinity")
**Infinity.** There exists a set containing $`\emptyset`$ and closed under the
successor operation $`x \mapsto x \cup \{x\}`$. This guarantees the existence
of an infinite set, namely $`\omega`$.
:::

:::definition "def:axiom-regularity" (lean := "Flypitch.ZFC.axiomOfRegularity")
**Regularity (Foundation).** Every nonempty set has an
$`\in`$-minimal element. This prevents infinite descending
$`\in`$-chains.
:::

:::definition "def:axiom-collection" (lean := "Flypitch.ZFC.axiomOfCollection")
**Collection (Replacement).** For every formula $`\varphi(x, y, \bar{z})`$,
if $`\forall x\,\exists y\,\varphi(x, y, \bar{z})`$, then for any set
$`A`$ there exists a set $`B`$ such that $`\forall x \in A\,\exists y \in
B\,\varphi(x, y, \bar{z})`$. This schema ensures that the image of a set
under a definable class function is contained in a set.
:::

:::definition "def:axiom-choice" (lean := "Flypitch.ZFC.zornsLemma")
**Choice.** We use Zorn's Lemma as our formulation of the Axiom of Choice: every
partially ordered set in which every chain has an upper bound contains a maximal
element. This is equivalent (over ZF) to the usual formulations involving choice
functions or well-orderings.
:::

:::definition "def:ZFC-theory" (lean := "Flypitch.ZFC.ZFC")
The *theory ZFC* is the set of all the above axiom sentences.
:::

# The Continuum Hypothesis as a Formal Sentence

To express CH in $`\mathcal{L}_{\text{ZFC}}`$, we first need to define
notions of ordinal, cardinality, and countability within set theory. These are
defined as bounded formulas --- formulas whose quantifiers are all bounded by
sets, a crucial property for the forcing argument.

**Ordinals.** A set $`x`$ is an ordinal if it is transitive
($`\forall y \in x\,(y \subseteq x)`$) and its elements are
$`\in`$-comparable and $`\in`$ is well-founded on $`x`$. This is
expressed by the bounded formula $`\text{Ord}(x)`$.

**Functions.** A set $`f`$ is a function from $`x`$ to $`y`$ if it is a
set of ordered pairs with domain $`x`$ and range contained in $`y`$.

**Cardinal comparison.** $`|x| \leq |y|`$ means there exists an injective
function from $`x`$ into $`y`$. $`|x| \leq |\omega|`$ means
$`x`$ is countable. $`|x| \leq |\mathcal{P}(\omega)|`$ means $`x`$
has cardinality at most the continuum.

:::definition "def:CH-f" (lean := "Flypitch.ZFC.CH_f")
The formal Continuum Hypothesis sentence $`\mathrm{CH}_f`$ states: every
ordinal is either at most countable or at most of size continuum. Equivalently,
there is no ordinal whose cardinality lies strictly between $`|\omega|`$ and
$`|\mathcal{P}(\omega)|`$.
:::

We also work with a technically more convenient equivalent formulation
$`\mathrm{CH}_2`$: every ordinal that is at most $`|\mathcal{P}(\omega)|`$
is at most countable, or equivalently, there is no injection from
$`\aleph_1`$ into $`\mathcal{P}(\omega)`$. The equivalence
$`\mathrm{CH}_f \leftrightarrow \mathrm{CH}_2`$ is proved in the
formalization.

:::definition "def:CH2" (lean := "Flypitch.ZFC.CH₂")
$`\mathrm{CH}_2`$ is the bounded formula expressing that every ordinal of
cardinality at most continuum is countable.
:::

# The Boolean-Valued Universe as a ZFC Structure

For any complete Boolean algebra $`\mathbb{B}`$, the Boolean-valued sets
$`bSet \ \mathbb{B}`$ form a Boolean-valued ZFC structure.

:::definition "def:V-beta" (lean := "Flypitch.ZFC.V")
The *Boolean-valued universe* $`V^{\mathbb{B}}`$ is the Boolean-valued
structure $`\mathcal{V}^{\mathbb{B}}`$ for $`\mathcal{L}_{\text{ZFC}}`$
defined by:
- The carrier is $`bSet \ \mathbb{B}`$.
- $`\in`$ is interpreted as Boolean-valued membership $`\in^{\mathbb{B}}`$.
- The constant symbols are interpreted as their standard Boolean-valued
  counterparts: $`\emptyset^{\mathbb{B}}`$, $`\omega^{\mathbb{B}}`$.
- The function symbols (pair, union, powerset) are interpreted as their
  Boolean-valued analogues.
- Equality is interpreted as Boolean-valued equality $`=^{\mathbb{B}}`$.
:::

The key theorem is that this structure indeed models ZFC.

:::theorem "thm:bSet-models-ZFC" (lean := "Flypitch.ZFC.bSet_models_ZFC")
For any complete Boolean algebra $`\mathbb{B}`$, the Boolean-valued universe
$`V^{\mathbb{B}}`$ satisfies every axiom of ZFC with truth value
$`\top`$. That is, $`\top \Vdash_{V^{\mathbb{B}}} \mathrm{ZFC}`$.
:::

The proof verifies each ZFC axiom individually within the Boolean-valued
universe. This is a substantial undertaking in the formalization; each axiom
requires carefully manipulating Boolean truth values using the algebraic laws
established in Chapter {uses "sec:complete-boolean-algebras"}[].

:::proof "proof:bSet-models-ZFC"
We sketch the verification of a few representative axioms.

**Extensionality.** For any $`x, y \in V^{\mathbb{B}}`$, we must show
$`\top \leq \llbracket \forall z\,(z \in x \leftrightarrow z \in y)
\to x = y \rrbracket`$. The Boolean truth value of the universal
quantifier is $`\bigsqcap_z \big((z \in^{\mathbb{B}} x) \leftrightarrow
(z \in^{\mathbb{B}} y)\big) \Rightarrow (x =^{\mathbb{B}} y)`$. This
simplifies to $`\top`$ by the definition of
$`x =^{\mathbb{B}} y`$, which is exactly the statement that $`x`$ and
$`y`$ have the same elements.

**Empty Set.** Since $`\emptyset`$ has an empty type, the Boolean value of
$`x \in^{\mathbb{B}} \emptyset`$ is $`\bot`$ for any $`x`$. The truth
value of $`\exists x\,\forall y\,(y \notin x)`$ is therefore $`\top`$.

**Powerset.** For a given $`x`$, the Boolean-valued powerset
$`\mathcal{P}^{\mathbb{B}}(x)`$ is defined so that $`y
\in^{\mathbb{B}} \mathcal{P}^{\mathbb{B}}(x) = \bigsqcap_z
((z \in^{\mathbb{B}} y) \Rightarrow (z \in^{\mathbb{B}} x))`$, which is
exactly $`y \subseteq^{\mathbb{B}} x`$.

**Infinity.** The Boolean-valued $`\omega`$ contains Boolean-valued versions
of the natural numbers; one verifies that it satisfies the closure properties
defining an inductive set.

**Zorn's Lemma.** This is the most technically involved verification. The proof
uses the mixing lemma and the maximum principle for Boolean-valued models,
adapting the classical proof of Zorn's Lemma to the Boolean-valued setting.

The complete verification of all axioms is found in the Lean formalization.
:::

# Relating CH Formalizations

:::lemma_ "lem:CH-iff-CH2" (lean := "Flypitch.ZFC.CH_f_is_CH")
$`\mathrm{CH}_f`$ and $`\mathrm{CH}_2`$ are equivalent in
$`V^{\mathbb{B}}`$: their Boolean truth values are equal. That is,
$`\llbracket\mathrm{CH}_f\rrbracket^{V^{\mathbb{B}}} =
\llbracket\mathrm{CH}_2\rrbracket^{V^{\mathbb{B}}}`$.
:::

This equivalence allows us to work with $`\mathrm{CH}_2`$ in the forcing
arguments, which is technically more convenient because it is a bounded formula.
