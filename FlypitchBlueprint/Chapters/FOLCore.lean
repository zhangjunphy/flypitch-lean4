import Verso
import VersoManual
import VersoBlueprint
import Flypitch.FOL.Semantics
import Flypitch.FOL.Bounded
import Flypitch.FOL.Theory
import Flypitch.Examples.Abel

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "First-Order Logic Core" =>

The first task is to fix a precise first-order language, define its syntax and
semantics, and specify what it means to prove a formula from hypotheses. This
chapter records the formalized core of that theory. It corresponds to the Lean
files `Flypitch/FOL/Syntax.lean`, `Flypitch/FOL/Formula.lean`,
`Flypitch/FOL/Proof.lean`, `Flypitch/FOL/Semantics.lean`,
`Flypitch/FOL/Theory.lean`, and `Flypitch/FOL/Bounded.lean`.

# Languages, Terms, And Formulas

:::definition "def:fol-language"
A first-order language consists of function symbols and relation symbols, each
sorted by arity.
:::

Once a language $`L` is fixed, one forms its terms and formulas in the usual
way. The implementation uses de Bruijn variables, so bound variables are
tracked numerically rather than by names. This choice is mathematically
inessential, but it makes substitution and variable-shifting precise enough for
the later completeness arguments.

The syntax is packaged in a slightly unusual arity-sensitive form: terms and
formulas are first built as partially applied expressions and only later
specialized to the closed cases. The advantage is that the basic structural
operations can be treated uniformly across all arities.

:::definition "def:fol-structural-ops"
The syntax carries two fundamental operations:

- lifting, which raises free variables above a chosen cutoff
- substitution, which replaces a free variable by a term

These operations belong to the syntax attached to {uses "def:fol-language"}[].
:::

These are the bookkeeping operations behind every later argument. They are
needed to formulate quantifier rules, to compare syntax under language maps,
and to express the witness constructions appearing in the Henkin chapter.

# Derivability

:::definition "def:fol-derivability"
For a set $`\Gamma` of formulas, the relation $`\Gamma \vdash A` is defined by
a natural-deduction proof system with rules for assumptions, implication,
universal quantification, falsity, equality, and substitution of equals.

This relation is built on top of {uses "def:fol-language"}[] and
{uses "def:fol-structural-ops"}[].
:::

This is the proof-theoretic core of the development. The formalized system is
strong enough for the compactness and completion arguments later on, and the
repository proves the expected structural facts such as weakening and a family
of derived introduction and elimination rules.

# Structures And Satisfaction

:::definition "def:fol-structure"
An $`L`-structure consists of a carrier set together with interpretations of
all function and relation symbols of $`L`.

This definition depends on {uses "def:fol-language"}[].
:::

Given a structure $`M` and a valuation of variables in $`M`, every term
acquires an interpretation in $`M` and every formula acquires a truth value.
Closed formulas may therefore be discussed without reference to a valuation,
and one obtains the usual notion of semantic consequence.

The central compatibility theorem in this part of the development identifies
syntactic substitution with semantic reassignment of variables. This is what
allows the proof system to interact correctly with semantics.

:::theorem "prop:formula-soundness" (lean := "Flypitch.fol.formula_soundness")
If $`\Gamma \vdash A`, then every structure satisfying all formulas in
$`\Gamma` also satisfies $`A`.

$$`\Gamma \vdash A \implies \Gamma \models A`

This proposition combines {uses "def:fol-derivability"}[],
{uses "def:fol-structure"}[], and {uses "def:fol-structural-ops"}[].
:::

:::proof "prop:formula-soundness"
The proof is by induction on a derivation. Each inference rule is checked
directly against the semantic definition of truth, with the lifting and
substitution lemmas handling the quantifier and equality cases.
:::

# Sentences, Theories, And Bounded Syntax

The later chapters work primarily with closed formulas, that is, with
sentences. A theory is therefore taken to be a set of sentences. At this level
one can define theory-level provability and satisfaction, together with the
familiar notions of consistency and completeness.

The development also isolates formulas with a prescribed number of free
variables. This is not merely a technical refinement. The Henkin construction
needs to speak uniformly about formulas in one free variable and then
substitute closed terms into them.

:::definition "def:fol-bounded-syntax"
For each natural number $`n`, a bounded term or formula is a term or formula
whose free variables lie among the first $`n` variables.

This is a bounded version of the syntax built from
{uses "def:fol-structural-ops"}[].
:::

These bounded objects are the correct language for witness formulas, witness
constants, and the quantified generalization arguments that appear later.

# A Model-Theoretic Example

The file `Flypitch/Examples/Abel.lean` supplies a concrete example in the
language of abelian groups. The axioms are interpreted in the integers, and the
formalization verifies that the integer structure satisfies them.

:::theorem "prop:abelian-example" (lean := "Flypitch.int_satisfies_of_prf")
The standard structure on $`\mathbb{Z}` is a model of the chosen theory of
abelian groups.

This example depends on {uses "prop:formula-soundness"}[].
:::

This example has a clear mathematical purpose. It shows that the syntax,
semantics, and proof system already interact correctly in a familiar setting
before the blueprint moves on to the abstract compactness and completion
machinery.

# Formalization Note

In Lean, the basic objects are implemented as the structures and types
`Language`, `preterm`, `preformula`, `prf`, `Structure`, `Theory`,
`bounded_term`, and `bounded_formula`. These names are useful when reading the
code, but the mathematical content of the chapter is the ordinary first-order
framework described above.
