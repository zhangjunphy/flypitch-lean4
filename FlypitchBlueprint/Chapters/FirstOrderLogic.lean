import Verso
import VersoManual
import VersoBlueprint
import Flypitch.FOL.Syntax
import Flypitch.FOL.Semantics
import Flypitch.FOL.Proof
import Flypitch.FOL.Theory

open Verso.Genre
open Verso.Genre.Manual
open Informal

set_option linter.hashCommand false

#doc (Manual) "First-Order Logic" =>

Before we can state and prove the independence of the Continuum Hypothesis, we
must build the logical infrastructure in which such statements are expressed.
This chapter develops the syntax and semantics of first-order logic, the natural
deduction proof system, and the fundamental relationship between provability and
semantic truth: the soundness theorem.

# Syntax: Languages, Terms, and Formulas

:::definition "def:first-order-language" (lean := "fol.Language")
A *first-order language* $`\mathcal{L}`$ consists of:
- a collection of *function symbols*, each with an associated natural number
  (its *arity*), and
- a collection of *relation symbols*, each with an associated natural number
  (its *arity*).

Constant symbols are identified with function symbols of arity $`0`$.
:::

For example, the language of ZFC set theory has one binary relation symbol
$`\in`$ and function symbols for the empty set ($`0`$-ary), unordered pair
($`2`$-ary), union ($`1`$-ary), powerset ($`1`$-ary), and the set
$`\omega`$ ($`0`$-ary). We will define this language precisely in
{uses "sec:zfc-language"}[].

Given a language $`\mathcal{L}`$, we build terms and formulas. Our
formalization uses *de Bruijn indices* for bound variables: instead of naming
variables with letters, we represent them as natural numbers indicating how many
binders outward they refer to. While this encoding is technically convenient for
the formalization, the mathematical content is identical to the usual
presentation with named variables.

:::definition "def:preterm" (lean := "fol.preterm")
A *preterm* over $`\mathcal{L}`$ of level $`l`$ (meaning it may contain
free variables indexed $`0, \dots, l-1`$) is either:
- a variable $`\text{var}(k)`$ where $`k < l`$, or
- a function application $`f(t_1, \dots, t_n)`$ where $`f`$ is an
  $`n`$-ary function symbol and each $`t_i`$ is a preterm of level
  $`l`$.
:::

A *term* is a preterm of level $`0`$ (no free variables), and a *closed term* is
a term with no variables at all. Since we work in a first-order setting without
function symbols of positive arity in the ZFC language, most terms are simply
variables or constant symbols.

:::definition "def:preformula" (lean := "fol.preformula")
A *preformula* over $`\mathcal{L}`$ of level $`l`$ is either:
- $`\bot`$ (falsum),
- an atomic formula $`t_1 \simeq t_2`$ (equality) or $`R(t_1, \dots, t_n)`$
  (relation application), where each $`t_i`$ is a preterm of level $`l`$,
- $`\varphi \to \psi`$ (implication), where $`\varphi`$ and $`\psi`$ are
  preformulas of level $`l`$,
- $`\forall \varphi`$ (universal quantification), where $`\varphi`$ is a
  preformula of level $`l+1`$ (the new variable is $`\text{var}(l)`$).
:::

The other logical connectives are defined in terms of $`\bot`$, $`\to`$, and
$`\forall`$ in the standard way:

- $`\neg \varphi`$ is $`\varphi \to \bot`$
- $`\varphi \land \psi`$ is $`\neg(\varphi \to \neg\psi)`$
- $`\varphi \lor \psi`$ is $`\neg\varphi \to \psi`$
- $`\varphi \leftrightarrow \psi`$ is
  $`(\varphi \to \psi) \land (\psi \to \varphi)`$
- $`\exists \varphi`$ is $`\neg\forall\neg\varphi`$

A *formula* is a preformula of level $`0`$, and a *sentence* is a formula with
no free variables. In the formalization, a sentence is represented as a formula
that is invariant under lifting and substitution, ensuring it truly has no free
variables.

:::definition "def:sentence" (lean := "fol.sentence")
A *sentence* is a closed formula: one in which every variable occurrence is
bound by a quantifier. In the de Bruijn representation, this means the formula
is unchanged by lifting (adding an unused variable to the context).
:::

# Semantics: Structures and Truth

Having defined the syntax, we now interpret formulas in mathematical structures.

:::definition "def:structure" (lean := "fol.Structure")
A *structure* $`\mathcal{M}`$ for a language $`\mathcal{L}`$ consists of:
- a nonempty *domain* $`M`$ (the carrier set),
- for each $`n`$-ary function symbol $`f \in \mathcal{L}`$, an
  interpretation $`f^{\mathcal{M}} : M^n \to M`$,
- for each $`n`$-ary relation symbol $`R \in \mathcal{L}`$, an
  interpretation $`R^{\mathcal{M}} : M^n \to \text{Prop}`$.
:::

A *valuation* (or *assignment*) is a function $`v : \mathbb{N} \to M`$ that
assigns an element of the domain to each variable index. Given a valuation, we
can interpret every term and formula.

:::definition "def:realize-term" (lean := "fol.realize_term")
The *realization* of a term $`t`$ under valuation $`v`$ in structure
$`\mathcal{M}`$, denoted $`\llbracket t \rrbracket^{\mathcal{M}}_v`$, is
defined recursively:
- $`\llbracket \text{var}(k) \rrbracket^{\mathcal{M}}_v = v(k)`$
- $`\llbracket f(t_1, \dots, t_n) \rrbracket^{\mathcal{M}}_v =
  f^{\mathcal{M}}(\llbracket t_1 \rrbracket^{\mathcal{M}}_v, \dots,
  \llbracket t_n \rrbracket^{\mathcal{M}}_v)`$
:::

:::definition "def:realize-formula" (lean := "fol.realize_formula")
The *realization* of a formula $`\varphi`$ under valuation $`v`$ in structure
$`\mathcal{M}`$, denoted $`\llbracket \varphi
\rrbracket^{\mathcal{M}}_v`$, is a proposition defined recursively:
- $`\llbracket \bot \rrbracket = \text{false}`$
- $`\llbracket t_1 \simeq t_2 \rrbracket =
  (\llbracket t_1 \rrbracket = \llbracket t_2 \rrbracket)`$
- $`\llbracket R(t_1, \dots, t_n) \rrbracket =
  R^{\mathcal{M}}(\llbracket t_1 \rrbracket, \dots, \llbracket t_n \rrbracket)`$
- $`\llbracket \varphi \to \psi \rrbracket =
  (\llbracket \varphi \rrbracket \to \llbracket \psi \rrbracket)`$
- $`\llbracket \forall x\,\varphi \rrbracket =
  (\text{for all } a \in M,\ \llbracket \varphi \rrbracket_{v[x \mapsto a]})`$

where $`v[x \mapsto a]`$ denotes the valuation that agrees with $`v`$ except
at $`x`$, where it takes value $`a`$.
:::

A formula $`\varphi`$ is *valid* in a structure $`\mathcal{M}`$, written
$`\mathcal{M} \models \varphi`$, if $`\llbracket \varphi
\rrbracket^{\mathcal{M}}_v`$ holds for every valuation $`v`$.

:::definition "def:satisfied" (lean := "fol.satisfied")
Let $`T`$ be a set of formulas. We write $`T \models \varphi`$ (read
"$`T`$ semantically entails $`\varphi`$") when every structure
$`\mathcal{M}`$ and valuation $`v`$ that satisfies all formulas in $`T`$
also satisfies $`\varphi`$.
:::

# The Natural Deduction Proof System

We use a natural deduction calculus in the style of Gentzen. The derivability
relation $`\Gamma \vdash \varphi`$ means that there exists a finite proof tree
using the rules below whose leaves are either axioms or members of $`\Gamma`$,
and whose root is $`\varphi`$.

:::definition "def:proof-system" (lean := "fol.prf")
The natural deduction rules are:

*Implication introduction*: If $`\Gamma, \varphi \vdash \psi`$, then
$`\Gamma \vdash \varphi \to \psi`$.

*Implication elimination*: If $`\Gamma \vdash \varphi \to \psi`$ and
$`\Gamma \vdash \varphi`$, then $`\Gamma \vdash \psi`$.

*Falsum elimination*: If $`\Gamma, \neg\varphi \vdash \bot`$, then
$`\Gamma \vdash \varphi`$.

*Universal introduction*: If $`\Gamma \vdash \varphi`$ and the variable
$`x`$ does not appear free in $`\Gamma`$, then
$`\Gamma \vdash \forall x\,\varphi`$.

*Universal elimination*: If $`\Gamma \vdash \forall x\,\varphi`$, then
$`\Gamma \vdash \varphi[t/x]`$ for any term $`t`$.

*Reflexivity*: $`\Gamma \vdash t \simeq t`$ for any term $`t`$.

*Substitution*: From $`\Gamma \vdash s \simeq t`$ and
$`\Gamma \vdash \varphi[s/x]`$, deduce $`\Gamma \vdash \varphi[t/x]`$.

*Weakening*: If $`\Gamma \vdash \varphi`$ and $`\Gamma \subseteq \Delta`$,
then $`\Delta \vdash \varphi`$.
:::

# Theories and Provability

:::definition "def:theory" (lean := "fol.Theory")
A *theory* $`T`$ over a language $`\mathcal{L}`$ is a collection of sentences
(the *axioms*) together with a deductive closure: we write $`T \vdash' \varphi`$
to mean that the sentence $`\varphi`$ is provable from the axioms of $`T`$
in the natural deduction system.
:::

In the formalization, a theory is a structure with a set of sentences (the
axioms) as its field. The notation $`T \vdash' \varphi`$ means that
$`\varphi`$ is a syntactic consequence of the *closure* of $`T`$ under the
deduction rules. This is defined as: every sentence in $`T`$ is provable from
the axioms, and the provability relation is closed under the natural deduction
rules.

A theory $`T`$ is *consistent* if it does not prove $`\bot`$. A structure
$`\mathcal{M}`$ is a *model* of $`T`$ if every axiom of $`T`$ is valid in
$`\mathcal{M}`$.

# Classical Soundness

The soundness theorem connects the syntactic notion of provability with the
semantic notion of truth. It states that the proof system is *correct*: anything
provable is true in all relevant structures.

:::theorem "thm:classical-soundness" (lean := "fol.formula_soundness")
**Soundness.** If $`\Gamma \vdash A`$, then $`\Gamma \models A`$. That is,
every structure and valuation that satisfies all formulas in $`\Gamma`$ also
satisfies $`A`$.
:::

The proof proceeds by induction on the derivation $`\Gamma \vdash A`$, checking
that each natural deduction rule preserves semantic truth. For example, suppose
the last rule in the derivation is implication elimination: we have
$`\Gamma \vdash \varphi \to \psi`$ and $`\Gamma \vdash \varphi`$, and we
conclude $`\Gamma \vdash \psi`$. By the induction hypothesis,
$`\Gamma \models \varphi \to \psi`$ and $`\Gamma \models \varphi`$. In any
structure and valuation satisfying $`\Gamma`$, we have both
$`\llbracket \varphi \to \psi \rrbracket`$ and
$`\llbracket \varphi \rrbracket`$ true, which forces
$`\llbracket \psi \rrbracket`$ true. Hence $`\Gamma \models \psi`$. The
other rules are verified similarly.

The classical soundness theorem is the foundation for the entire independence
proof. Its Boolean-valued analogue ({uses "thm:boolean-soundness"}[]) will
play the same role in the forcing argument: anything provable from ZFC must hold
with truth value $`\top`$ in every Boolean-valued model. By contraposition, a
single Boolean-valued model where CH is not $`\top`$ suffices to show that CH
is not a theorem of ZFC.
