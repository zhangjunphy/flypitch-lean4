import Verso
import VersoManual
import VersoBlueprint
import Flypitch.Summary
import Flypitch.ZFC

open Verso.Genre
open Verso.Genre.Manual
open Informal

set_option linter.hashCommand false

#doc (Manual) "Introduction" =>

# Historical Background

In the 1870s, Georg Cantor founded set theory and developed the theory of
cardinal numbers. He showed that the set of natural numbers $`\mathbb{N}`$ is
countably infinite, with cardinality $`\aleph_0`$, while the set of real
numbers $`\mathbb{R}`$ is uncountable, with cardinality
$`2^{\aleph_0}`$ (the cardinality of the continuum). Cantor then asked a
question that would shape the development of set theory for the next century: is
there a cardinal number strictly between $`\aleph_0`$ and
$`2^{\aleph_0}`$?

The Continuum Hypothesis (CH) is the assertion that no such intermediate
cardinal exists. Equivalently, every infinite subset of $`\mathbb{R}`$ is
either countable (of size $`\aleph_0`$) or has the cardinality of the
continuum ($`2^{\aleph_0}`$). Cantor spent many years attempting to prove
CH, but never succeeded. In 1900, David Hilbert placed CH at the top of his
famous list of twenty-three unsolved problems, underscoring its central
importance to mathematics.

In 1938, Kurt Goedel made the first major breakthrough. He constructed the
constructible universe $`L`$, a carefully defined inner model of set theory,
and showed that within $`L`$, every set is well-ordered in a canonical way and
CH holds. This proved that CH cannot be *disproved* from the axioms of
Zermelo--Fraenkel set theory with the Axiom of Choice (ZFC) --- assuming ZFC
itself is consistent. In other words, $`\text{ZFC} \not\vdash \neg
\mathrm{CH}`$.

The second half of the solution came in 1963, when Paul Cohen introduced the
method of *forcing*. Cohen showed how to extend a given model of ZFC by
adjoining a carefully constructed "generic" object, producing a larger model in
which the continuum has size at least $`\aleph_2`$ (in fact, as large as one
wishes). In this extended model, CH is false. This proved that CH cannot be
*proved* from ZFC either: $`\text{ZFC} \not\vdash \mathrm{CH}`$.

Together, Goedel's and Cohen's results establish that the Continuum Hypothesis
is *independent* of ZFC --- it can neither be proved nor disproved from the
standard axioms of set theory.

# The Formal Proof

This document presents a complete formal proof of the independence of CH, using
the Lean 4 proof assistant. Our formalization follows the *Boolean-valued model*
approach to forcing, developed by Dana Scott and Robert Solovay in the 1960s as
a simplification of Cohen's original presentation. In this approach, one works
within a single universe of Boolean-valued sets $`V^{\mathbb{B}}`$, where
statements take truth values in a complete Boolean algebra
$`\mathbb{B}`$ rather than the two-valued Boolean algebra
$`\{\text{true}, \text{false}\}`$. A sentence is "forced" to be true when its
truth value equals the top element $`\top \in \mathbb{B}`$.

The advantage of this approach for formalization is that it avoids the need to
construct a countable transitive model in the metatheory --- a step that
requires additional set-theoretic assumptions beyond ZFC. Instead, the
Boolean-valued universe $`V^{\mathbb{B}}`$ is defined directly within ZFC,
and one proves that every axiom of ZFC receives truth value $`\top`$ in
$`V^{\mathbb{B}}`$ for any complete Boolean algebra $`\mathbb{B}`$.

# The Two-Model Strategy

To prove CH independent, we construct two different complete Boolean algebras:

- **The Cohen Boolean algebra** $`\mathbb{B}_{\text{Cohen}}`$, obtained
  from the regular open sets of the Cantor space $`2^{\aleph_2 \times
  \mathbb{N}}`$. In $`V^{\mathbb{B}_{\text{Cohen}}}`$, the sentence CH
  receives truth value $`\bot`$ (false). This shows that ZFC does not prove
  CH, since any proof of CH would force CH to be true in all Boolean-valued
  models.

- **The collapse Boolean algebra** $`\mathbb{B}_{\text{Collapse}}`$,
  obtained from the regular open sets of the collapse poset (partial functions
  from $`\aleph_1`$ to $`\mathcal{P}(\mathbb{N})`$ with countable
  domain). In $`V^{\mathbb{B}_{\text{Collapse}}}`$, CH receives truth value
  $`\top`$ (true). This shows that ZFC does not prove the negation of CH.

The key logical ingredient is the *Boolean-valued soundness theorem*: if a
theory $`T`$ proves a sentence $`\varphi`$, then for every Boolean-valued
model $`\mathcal{M}`$ of $`T`$, the truth value of $`\varphi`$ in
$`\mathcal{M}`$ is $`\top`$. Taking the contrapositive, if we exhibit a
Boolean-valued model of ZFC in which CH has truth value $`\bot`$, then CH
cannot be a theorem of ZFC. Similarly, a model in which CH has truth value
$`\top`$ rules out a proof of $`\neg\mathrm{CH}`$.

# Roadmap

This document is organized into nine chapters, following the logical
dependencies of the proof.

**Chapter 2** introduces the syntax and semantics of first-order logic. We
define languages, terms, formulas, and sentences; we define structures and the
satisfaction relation; and we introduce the natural deduction proof system and
the notion of a theory with provability.

**Chapter 3** proves the completeness theorem and the compactness theorem for
first-order logic, via the Henkin construction. Although these results are not
directly needed for the CH independence proof, they establish the robustness of
our first-order logic framework.

**Chapter 4** develops the theory of complete Boolean algebras, focusing on the
key example of regular open sets of a topological space. We define the
pseudocomplement operation and prove the basic properties needed for forcing.

**Chapter 5** introduces Boolean-valued semantics. We define Boolean-valued
sets $`V^{\mathbb{B}}`$, the Boolean-valued connectives
$`\in^{\mathbb{B}}`$, $`=^{\mathbb{B}}`$, and the Boolean-valued
universal and existential quantifiers. We prove the Boolean-valued soundness
theorem.

**Chapter 6** formalizes Zermelo--Fraenkel set theory with Choice. We define the
language $`\mathcal{L}_{\text{ZFC}}`$, the ZFC axioms as formal sentences, and
the Continuum Hypothesis as a sentence $`\mathrm{CH}_f`$ of
$`\mathcal{L}_{\text{ZFC}}`$. We define the Boolean-valued universe
$`V^{\mathbb{B}}`$ as a Boolean-valued ZFC structure and prove that it
satisfies every ZFC axiom with truth value $`\top`$.

**Chapter 7** presents Cohen forcing. We construct the Cantor space
$`2^{\aleph_2 \times \mathbb{N}}`$ and its regular open algebra
$`\mathbb{B}_{\text{Cohen}}`$. For each ordinal $`\nu < \aleph_2`$, we
construct a Boolean-valued subset of $`\mathbb{N}`$ --- a Cohen real --- and
prove that distinct ordinals give distinct Cohen reals. This yields an injection
from $`\aleph_2`$ into $`\mathcal{P}(\mathbb{N})`$ in the Boolean-valued
universe, so CH is forced false.

**Chapter 8** presents collapse forcing. We construct the collapse poset of
partial functions from $`\aleph_1`$ to
$`\mathcal{P}(\mathbb{N})`$ with countable domain, take its regular open
algebra $`\mathbb{B}_{\text{Collapse}}`$, and build a Boolean-valued
surjection from $`\aleph_1`$ onto $`\mathcal{P}(\mathbb{N})`$. This forces
CH to be true in $`V^{\mathbb{B}_{\text{Collapse}}}`$.

**Chapter 9** assembles the two halves into the final independence result. We
state and prove that $`\mathrm{CH}_f`$ is independent of ZFC, concluding the
formal proof.

# The Lean Formalization

Each theorem, definition, and lemma in this document is linked to its formal
counterpart in the Lean codebase. The links appear as `(lean := ...)`
annotations on the theorem and definition blocks. The reader is encouraged to
follow these links to inspect the fully verified proofs.

The central Lean declarations are:

:::definition "def:independent-sentence" (lean := "Flypitch.independent")
For a first-order theory $`T`$ and a sentence $`\varphi`$, we say $`\varphi`$
is *independent* of $`T`$ when $`T`$ proves neither $`\varphi`$ nor
$`\neg\varphi`$.
:::

:::theorem "thm:ch-unprovable" (lean := "Flypitch.CH_unprovable")
ZFC does not prove CH. That is, $`\text{ZFC} \not\vdash \mathrm{CH}_f`$.

This is proved using the Cohen Boolean-valued model
({uses "thm:not-ch-forced"}[]) together with the Boolean-valued soundness
theorem ({uses "thm:boolean-soundness"}[]).
:::

:::theorem "thm:not-ch-unprovable" (lean := "Flypitch.neg_CH_unprovable")
ZFC does not prove the negation of CH. That is,
$`\text{ZFC} \not\vdash \neg\mathrm{CH}_f`$.

This is proved using the collapse Boolean-valued model
({uses "thm:ch-forced"}[]) together with the Boolean-valued soundness theorem
({uses "thm:boolean-soundness"}[]).
:::

:::theorem "thm:independence-of-ch" (lean := "Flypitch.independence_of_CH")
The Continuum Hypothesis is independent of ZFC.
:::
