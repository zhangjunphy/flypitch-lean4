import Verso
import VersoManual
import VersoBlueprint
import Flypitch.Forcing
import Flypitch.CantorSpace
import Flypitch.AlephOne

open Verso.Genre
open Verso.Genre.Manual
open Informal

set_option linter.hashCommand false

#doc (Manual) "Cohen Forcing — CH Fails" =>

We now construct the first of the two Boolean-valued models: the Cohen
extension, in which the Continuum Hypothesis is forced to be false. The idea,
due to Paul Cohen, is to adjoin $`\aleph_2`$ distinct "generic" subsets of
$`\mathbb{N}`$ (called Cohen reals) to the universe. In the resulting
Boolean-valued model, there are at least $`\aleph_2`$ distinct subsets of
$`\mathbb{N}`$, so the continuum has cardinality at least
$`\aleph_2`$ and CH is false.

# The Cantor Space

The underlying topological space for the Cohen algebra is the *Cantor space*.

:::definition "def:cantor-space"
The Cantor space $`2^{\aleph_2 \times \mathbb{N}}`$ is the product of
$`|\aleph_2 \times \mathbb{N}|`$ copies of the discrete two-point space
$`\{0, 1\}`$, equipped with the product topology.
:::

By Tychonoff's theorem, $`2^{\aleph_2 \times \mathbb{N}}`$ is compact.
The standard basis consists of the sets
$`U(p) = \{f \in 2^{\aleph_2 \times \mathbb{N}} \mid f \text{ extends } p\}`$
for finite partial functions $`p : \aleph_2 \times \mathbb{N}
\rightharpoonup \{0, 1\}`$. Each $`U(p)`$ is clopen (both closed and open),
hence regular open.

# The Cohen Boolean Algebra

:::definition "def:Cohen-BA" (lean := "Flypitch.Forcing.𝔹_cohen")
The *Cohen Boolean algebra* $`\mathbb{B}_{\text{Cohen}}`$ is the complete
Boolean algebra of regular open subsets of the Cantor space
$`2^{\aleph_2 \times \mathbb{N}}`$:
$`\mathbb{B}_{\text{Cohen}} = \text{RO}(2^{\aleph_2 \times
\mathbb{N}})`$.
:::

This algebra has the *countable chain condition* (CCC): every family of pairwise
disjoint nonzero elements is at most countable. The CCC property is important
for cardinal preservation: it ensures that cardinals (specifically,
$`\aleph_1`$ and $`\aleph_2`$) are not collapsed in the Cohen
extension.

:::theorem "thm:CCC" (lean := "Flypitch.Forcing.𝔹_CCC")
$`\mathbb{B}_{\text{Cohen}}`$ has the countable chain condition.
:::

:::proof "proof:CCC"
The proof uses the $`\Delta`$-system lemma from combinatorial set theory
({uses "lem:delta-system"}[]). Given an uncountable family of basic open sets
(which correspond to finite partial functions from $`\aleph_2 \times
\mathbb{N}`$ to $`\{0, 1\}`$), the $`\Delta`$-system lemma yields a
subfamily with pairwise compatible functions, hence the corresponding open sets
have nonempty intersection. Therefore no uncountable antichain exists.
:::

# Principal Opens

For each pair $`(\nu, n)`$ with $`\nu < \aleph_2`$ and $`n \in
\mathbb{N}`$, we define a principal open set in the Cantor space: the set of
functions $`f`$ such that $`f(\nu, n) = 1`$. (The complement is the set where
$`f(\nu, n) = 0`$.)

:::definition "def:principal-open" (lean := "Flypitch.Forcing.principal_open")
For $`\nu < \aleph_2`$ and $`n \in \mathbb{N}`$, the *principal open*
$`U_{\nu, n}`$ is the clopen set $`\{f \in 2^{\aleph_2 \times
\mathbb{N}} \mid f(\nu, n) = 1\}`$.
:::

These are regular open (since they are clopen) and are the basic building blocks
for constructing Cohen reals.

# The Cohen Poset

The *Cohen poset* $`\mathcal{C}`$ consists of finite partial functions
$`p : \aleph_2 \times \mathbb{N} \rightharpoonup \{0, 1\}`$, ordered by
reverse inclusion: $`p \leq q`$ iff $`p \supseteq q`$ ($`p`$ extends
$`q`$, containing more information). Each such finite partial function
corresponds to a basic clopen set in the Cantor space. The Cohen algebra is
isomorphic to the regular open algebra of this poset's associated topological
space.

# Cohen Reals

A *Cohen real* is a Boolean-valued subset of $`\mathbb{N}`$ obtained as the
characteristic function of a generic point at coordinate $`\nu`$ in the
Cantor space.

:::definition "def:cohen-real" (lean := "Flypitch.Forcing.cohen_real.mk")
For each ordinal $`\nu < \aleph_2`$, the *Cohen real*
$`c_{\nu}`$ is the Boolean-valued subset of $`\mathbb{N}`$ defined by:
$`n \in^{\mathbb{B}} c_{\nu} = U_{\nu, n}`$
where $`U_{\nu, n}`$ is the principal open in
$`\mathbb{B}_{\text{Cohen}}`$.
:::

Since each $`U_{\nu, n}`$ is a regular open set, $`c_{\nu}`$ is a
Boolean-valued set (specifically, a Boolean-valued subset of
$`\omega`$). The truth value $`n \in^{\mathbb{B}} c_{\nu}`$ is exactly
$`U_{\nu, n} \in \mathbb{B}_{\text{Cohen}}`$.

# Distinct Cohen Reals Are Distinct

The crucial combinatorial lemma is that distinct ordinals give rise to
*genuinely distinct* Cohen reals in the Boolean-valued sense.

:::lemma_ "lem:cohen-inj" (lean := "Flypitch.Forcing.cohen_real.inj")
If $`\nu_1 \neq \nu_2`$ are distinct ordinals below $`\aleph_2`$, then
$`\top \Vdash c_{\nu_1} \neq c_{\nu_2}`$. That is, the Boolean truth value of
$`c_{\nu_1} = c_{\nu_2}`$ is $`\bot`$.
:::

:::proof "proof:cohen-inj"
Since $`\nu_1 \neq \nu_2`$, there exists some $`n \in \mathbb{N}`$ and a
finite partial function $`p`$ where $`p(\nu_1, n) = 1`$ and
$`p(\nu_2, n) = 0`$ (or vice versa). The corresponding basic open set
witnesses that $`n`$ belongs to $`c_{\nu_1}`$ but not to
$`c_{\nu_2}`$ with positive truth value. More precisely, the truth value of
$`n \in^{\mathbb{B}} c_{\nu_1}`$ is $`U_{\nu_1, n}`$, and the truth
value of $`n \in^{\mathbb{B}} c_{\nu_2}`$ is $`U_{\nu_2, n}`$. These two
regular open sets are disjoint (their intersection is empty), so
$`U_{\nu_1, n} \sqcap U_{\nu_2, n} = \bot`$. It follows that the truth
value of $`c_{\nu_1} = c_{\nu_2}`$ is $`\bot`$.
:::

# $`\aleph_2`$ Injects into the Continuum

Assembling the Cohen reals for all $`\nu < \aleph_2`$, we obtain a
Boolean-valued injection from $`\aleph_2`$ into the powerset of
$`\omega`$.

:::definition "def:neg-CH-func" (lean := "Flypitch.Forcing.neg_CH_func")
The Boolean-valued set $`F`$ encodes the injection $`\nu \mapsto
c_{\nu}`$ from $`\aleph_2`$ into $`\mathcal{P}(\omega)`$.
:::

:::theorem "thm:aleph2-injects-continuum" (lean := "Flypitch.Forcing.ℵ₂_injects_𝔠")
In the Cohen Boolean-valued model $`V^{\mathbb{B}_{\text{Cohen}}}`$,
there is an injection from $`\aleph_2`$ into the powerset of
$`\omega`$. Equivalently, $`\aleph_2 \leq 2^{\aleph_0}`$ is forced.
:::

# CH Is Forced False

:::theorem "thm:not-ch-forced" (lean := "Flypitch.Forcing.not_CH₂")
In the Cohen Boolean-valued model $`V^{\mathbb{B}_{\text{Cohen}}}`$, the
continuum hypothesis $`\mathrm{CH}_2`$ receives truth value $`\bot`$.
Equivalently, $`\top`$ forces the negation of $`\mathrm{CH}_2`$:
$`\top \Vdash_{V^{\mathbb{B}_{\text{Cohen}}}} \neg\mathrm{CH}_2`$.
:::

:::proof "proof:not-ch-forced"
Since $`\aleph_2`$ injects into $`\mathcal{P}(\omega)`$ in the
Boolean-valued sense, the statement "$`\aleph_2 \leq
|\mathcal{P}(\omega)|`$" has truth value $`\top`$. But
$`\mathrm{CH}_2`$ asserts that $`\mathcal{P}(\omega)`$ has size at most
$`\aleph_1`$, which is incompatible with an injection from
$`\aleph_2`$ (since $`\aleph_2 > \aleph_1`$). Therefore
$`\llbracket\mathrm{CH}_2\rrbracket = \bot`$.
:::

# Corollary: ZFC Does Not Prove CH

:::corollary "cor:CH-unprovable-from-Cohen" (lean := "Flypitch.ZFC.neg_CH_f_unprovable")
ZFC does not prove $`\neg\mathrm{CH}_f`$. That is,
$`\text{ZFC} \not\vdash' \neg\mathrm{CH}_f`$.
:::

Wait, let us be precise about the logical direction. The Cohen model forces
$`\neg\mathrm{CH}_2`$, which is equivalent to $`\neg\mathrm{CH}_f`$. So
in the Cohen model, CH is false. By Boolean-valued soundness
({uses "thm:boolean-soundness"}[]), if ZFC proved $`\mathrm{CH}_f`$, then
$`\mathrm{CH}_f`$ would be forced true in every Boolean-valued model of ZFC,
including the Cohen model. Since CH is forced false in the Cohen model, ZFC
cannot prove CH. That is, $`\text{ZFC} \not\vdash' \mathrm{CH}_f`$.

The formal Lean statement of this corollary is
{uses "thm:ch-unprovable"}[] in Chapter {uses "sec:independence"}[].
