import Verso
import VersoManual
import VersoBlueprint
import Flypitch.BVM
import Flypitch.BVMExtras
import Flypitch.BFOL
import Flypitch.BVTauto

open Verso.Genre
open Verso.Genre.Manual
open Informal

set_option linter.hashCommand false

#doc (Manual) "Boolean-Valued Semantics" =>

Classical first-order semantics assigns to each formula, relative to a
structure and a valuation, a truth value in $`\{\text{true}, \text{false}\}`$.
Boolean-valued semantics generalizes this: we fix a complete Boolean algebra
$`\mathbb{B}`$ and assign to each formula a truth value in
$`\mathbb{B}`$. The top element $`\top`$ represents "fully true," the bottom
element $`\bot`$ represents "fully false," and intermediate values represent
degrees of truth.

This chapter develops the Boolean-valued universe $`V^{\mathbb{B}}`$, the
Boolean-valued semantics for first-order logic, and the Boolean-valued soundness
theorem.

# Boolean-Valued Sets

:::definition "def:bSet" (lean := "Flypitch.bSet")
Let $`\mathbb{B}`$ be a complete Boolean algebra. A *Boolean-valued set* (or
$`bSet`$) is a set $`x`$ equipped with:
- a type $`\text{type}(x)`$ (the index set of its elements),
- a function $`\text{func}(x) : \text{type}(x) \to bSet\,
  \mathbb{B}`$ (the elements),
- a function $`\text{bval}(x) : \text{type}(x) \to \mathbb{B}`$ (the
  Boolean truth value that each element belongs to $`x`$).
:::

This definition mirrors the cumulative hierarchy of classical set theory, but
membership is now graded by truth values. A Boolean-valued set $`x`$ is
thought of as a "fuzzy set" where each potential element $`\text{func}(x)(i)`$
belongs to $`x`$ with truth value $`\text{bval}(x)(i)`$.

The Boolean-valued universe $`V^{\mathbb{B}}`$ is the proper class of all
$`bSet \ \mathbb{B}`$. Unlike the classical von Neumann hierarchy
$`V`$, the Boolean-valued hierarchy is not stratified by rank in the same way;
elements of a $`bSet`$ can be arbitrary $`bSet`s.

# Boolean-Valued Equality and Membership

The fundamental relations of set theory --- equality and membership --- are
extended to the Boolean-valued setting by mutual recursion.

:::definition "def:bv-eq" (lean := "Flypitch.bSet.bv_eq")
The *Boolean-valued equality* $`x =^{\mathbb{B}} y`$ of two Boolean-valued
sets is defined as:
$`x =^{\mathbb{B}} y = \left(\bigsqcap_{i \in \text{type}(x)}
\text{bval}(x)(i) \Rightarrow ( \text{func}(x)(i) \in^{\mathbb{B}} y )\right)
\sqcap \left(\bigsqcap_{j \in \text{type}(y)}
\text{bval}(y)(j) \Rightarrow ( \text{func}(y)(j)
\in^{\mathbb{B}} x )\right)`$

where $`\Rightarrow`$ is the implication in $`\mathbb{B}`$.
:::

This says: $`x`$ equals $`y`$ to the degree that every element of $`x`$ is a
member of $`y`$ (weighted by its membership degree in $`x`$), and vice versa.
The use of infima generalizes the universal quantifier: "for all elements" means
the infimum over all indices.

:::definition "def:bv-mem" (lean := "Flypitch.bSet.mem")
The *Boolean-valued membership* $`x \in^{\mathbb{B}} y`$ is defined as:
$`x \in^{\mathbb{B}} y = \bigsqcup_{i \in \text{type}(y)}
(\text{bval}(y)(i) \sqcap (x =^{\mathbb{B}} \text{func}(y)(i)))`$
:::

This says: $`x`$ belongs to $`y`$ to the degree that there exists some element
of $`y`$ that $`x`$ equals, weighted by that element's membership degree. The
suprema generalize the existential quantifier.

Both definitions are well-founded: they define $`=^{\mathbb{B}}`$ and
$`\in^{\mathbb{B}}`$ by simultaneous recursion on the well-founded
cumulative structure of sets, using the fact that every $`bSet`$ is a set of
smaller $`bSet`s.

# Boolean-Valued Connectives

The logical connectives of set theory are lifted to operate on truth values in
$`\mathbb{B}`$:

- **Conjunction** (Boolean meet): $`\varphi \land^{\mathbb{B}} \psi`$ has
  truth value $`\llbracket\varphi\rrbracket \sqcap
  \llbracket\psi\rrbracket`$.
- **Disjunction** (Boolean join): $`\varphi \lor^{\mathbb{B}} \psi`$ has
  truth value $`\llbracket\varphi\rrbracket \sqcup
  \llbracket\psi\rrbracket`$.
- **Negation** (Boolean complement): $`\neg^{\mathbb{B}}\varphi`$ has
  truth value $`\llbracket\varphi\rrbracket^c`$.
- **Implication** (Boolean implication):
  $`\varphi \to^{\mathbb{B}} \psi`$ has truth value
  $`\llbracket\varphi\rrbracket \Rightarrow \llbracket\psi\rrbracket`$.
- **Universal quantification**: $`\forall^{\mathbb{B}} x\,\varphi(x)`$
  has truth value $`\bigsqcap_x \llbracket\varphi(x)\rrbracket`$.
- **Existential quantification**: $`\exists^{\mathbb{B}} x\,\varphi(x)`$
  has truth value $`\bigsqcup_x \llbracket\varphi(x)\rrbracket`$.

:::lemma_ "lem:bv-lemmas" (lean := "Flypitch.bSet.le_imp_iff")
The Boolean-valued connectives satisfy all the expected logical laws. For
example, $`\Gamma \sqcap \llbracket\varphi\rrbracket \leq
\llbracket\psi\rrbracket`$ if and only if
$`\Gamma \leq \llbracket\varphi\rrbracket \Rightarrow
\llbracket\psi\rrbracket`$.
:::

# Boolean-Valued First-Order Structures

We now embed the syntax of first-order logic (Chapter
{uses "sec:first-order-logic"}[]) into the Boolean-valued framework.

:::definition "def:bStructure" (lean := "fol.bfol.bStructure")
A *Boolean-valued structure* $`\mathcal{S}`$ for a language
$`\mathcal{L}`$ consists of:
- a carrier type $`S`$ of "elements,"
- for each $`n`$-ary function symbol $`f`$, an interpretation
  $`f^{\mathcal{S}} : S^n \to S`$,
- for each $`n`$-ary relation symbol $`R`$, an interpretation
  $`R^{\mathcal{S}} : S^n \to \mathbb{B}`$,
- an equality interpretation $`\text{eq}^{\mathcal{S}} : S \times S \to
  \mathbb{B}`$,

satisfying axioms that ensure equality is a Boolean-valued equivalence relation
(reflexive, symmetric, transitive in the Boolean sense) and a congruence for
functions and relations.
:::

Given a Boolean-valued structure, we define the *Boolean realization* of terms
and formulas. For a formula $`\varphi`$ and a valuation $`v`$, the Boolean
realization $`\llbracket\varphi\rrbracket^{\mathcal{S}}_v`$ is an element
of $`\mathbb{B}`$, computed by replacing classical logical operations with
their Boolean-valued counterparts.

:::definition "def:boolean-realize-formula" (lean := "fol.bfol.boolean_realize_formula")
The *Boolean realization* interprets:
- atomic formulas using the relation interpretations (which return values in
  $`\mathbb{B}`$),
- logical connectives using Boolean algebra operations as described above,
- quantifiers as infima and suprema over the domain.
:::

# Forcing

The central notion in the Boolean-valued approach to forcing is the *forcing
relation*.

:::definition "def:forces" (lean := "fol.bfol.forces")
Let $`\mathcal{S}`$ be a Boolean-valued structure and $`\Gamma \in
\mathbb{B}`$ a condition. We say $`\Gamma`$ *forces* a sentence
$`\varphi`$, written $`\Gamma \Vdash_{\mathcal{S}} \varphi`$, if
$`\Gamma \leq \llbracket\varphi\rrbracket^{\mathcal{S}}`$.
:::

Intuitively, $`\Gamma`$ forces $`\varphi`$ when the truth value of
$`\varphi`$ is at least $`\Gamma`$. The top condition $`\top`$ forcing
$`\varphi`$ means that $`\varphi`$ is "fully true" in
$`\mathcal{S}`$.

:::definition "def:forces-theory" (lean := "fol.bfol.forces_theory")
A condition $`\Gamma`$ *forces a theory* $`T`$, written
$`\Gamma \Vdash_{\mathcal{S}} T`$, if $`\Gamma \leq
\llbracket\psi\rrbracket^{\mathcal{S}}`$ for every axiom $`\psi \in T`$.
:::

Equivalently, $`\Gamma \Vdash_{\mathcal{S}} T`$ iff
$`\Gamma \leq \bigsqcap_{\psi \in T}
\llbracket\psi\rrbracket^{\mathcal{S}}`$.

# Boolean-Valued Soundness

The fundamental theorem that makes forcing useful for independence proofs is the
Boolean-valued soundness theorem. It is the analogue, in the Boolean-valued
setting, of the classical soundness theorem ({uses "thm:classical-soundness"}[]).

:::theorem "thm:boolean-soundness" (lean := "fol.bfol.boolean_soundness")
**Boolean-Valued Soundness.** If $`T \vdash \varphi`$ (there is a formal proof
of $`\varphi`$ from $`T`$), then $`\varphi`$ is *forced* by the infimum of
the truth values of the axioms of $`T`$ in every Boolean-valued structure. In
particular, if a theory $`T`$ proves $`\varphi`$ and
$`\mathcal{S}`$ is a Boolean-valued structure such that
$`\top \Vdash_{\mathcal{S}} T`$, then
$`\top \Vdash_{\mathcal{S}} \varphi`$.
:::

The proof proceeds by induction on the derivation, verifying that each natural
deduction rule preserves truth in the Boolean-valued setting. The key algebraic
lemmas --- that the Boolean operations satisfy the logical laws of the natural
deduction calculus --- were established in {uses "lem:bv-lemmas"}[].

:::proof "proof:boolean-soundness"
By induction on the derivation $`T \vdash \varphi`$:

- **Axiom case.** If $`\varphi \in T`$, then
  $`\bigsqcap_{\psi \in T} \llbracket\psi\rrbracket \leq
  \llbracket\varphi\rrbracket`$ by the definition of infimum. So the axiom
  infimum forces $`\varphi`$.

- **Implication introduction.** Suppose $`T \cup \{\varphi\} \vdash \psi`$,
  and by induction the infimum of $`T`$-axiom truth values infimum
  $`\llbracket\varphi\rrbracket`$ is below $`\llbracket\psi\rrbracket`$.
  Then by the adjunction $`a \sqcap b \leq c \iff a \leq b
  \Rightarrow c`$, the infimum of $`T`$-axiom truth values is below
  $`\llbracket\varphi\rrbracket \Rightarrow
  \llbracket\psi\rrbracket = \llbracket\varphi \to \psi\rrbracket`$.

- **Implication elimination.** If the infimum forces
  $`\varphi \to \psi`$ and $`\varphi`$, then it is below both
  $`\llbracket\varphi\rrbracket \Rightarrow
  \llbracket\psi\rrbracket`$ and $`\llbracket\varphi\rrbracket`$.
  Since $`a \sqcap (a \Rightarrow b) \leq b`$, the infimum is below
  $`\llbracket\psi\rrbracket`$.

- **Universal introduction and elimination** rely on the infimum and supremum
  manipulations described in Chapter {uses "sec:complete-boolean-algebras"}[].

- **Equality rules** use the Boolean-valued congruence properties of
  $`\text{eq}^{\mathcal{S}}`$.
:::

:::corollary "cor:unprovable-of-model-neg" (lean := "fol.bfol.unprovable_of_model_neg")
If $`\mathcal{S}`$ is a Boolean-valued structure with
$`\top \Vdash_{\mathcal{S}} T`$, and there exists a nonzero condition
$`\Gamma > \bot`$ such that $`\Gamma \Vdash_{\mathcal{S}} \neg\varphi`$,
then $`T \not\vdash' \varphi`$. That is, $`\varphi`$ is not provable from
$`T`$.
:::

This corollary is the engine of the independence proof. To show that CH is not
provable from ZFC, it suffices to exhibit a Boolean-valued structure modeling
ZFC (with truth value $`\top`$) and a nonzero condition forcing
$`\neg\text{CH}`$. The Cohen Boolean-valued model provides exactly this, as
shown in Chapter {uses "sec:cohen-forcing"}[].
