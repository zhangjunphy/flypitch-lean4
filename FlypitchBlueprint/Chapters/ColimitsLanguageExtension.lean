import Verso
import VersoManual
import VersoBlueprint
import Flypitch.ZFC

open Verso.Genre
open Verso.Genre.Manual
open Informal

set_option linter.hashCommand false
set_option linter.style.emptyLine false

#doc (Manual) "Encoding ZFC And CH" =>

The forcing argument speaks mathematically about CH, but the final theorem is
about a formal first-order sentence. This chapter explains the bridge between
the informal set-theoretic statement and the Lean sentence `CH_f`.

# The Language Of Set Theory

:::definition "def:zfc-language" (lean := "Flypitch.ZFC.L_ZFC")
`L_ZFC` is the first-order language used for set theory in the proof. It has a
binary membership relation and selected function symbols for the set-forming
operations used in the axioms.
:::

The relation symbol is membership. The function symbols name operations such
as the empty set, ordered pairing, union, powerset, and omega. These symbols
make the formal axioms concise while preserving the ordinary first-order
nature of the theory.

:::definition "def:zfc-theory" (lean := "Flypitch.ZFC.ZFC")
`ZFC` is the theory containing the formal ZFC axioms in the language `L_ZFC`,
including the collection scheme.

This theory is written in the language from {uses "def:zfc-language"}[].
:::

# The Formal Continuum Hypothesis

Inside the formal language, CH is expressed by saying that every set which is
larger than omega but not larger than the powerset of omega has the size of
the first uncountable cardinal. The Lean development packages this as one
closed sentence.

:::definition "def:ch-formula" (lean := "Flypitch.ZFC.CH_f")
`CH_f` is the first-order sentence of `L_ZFC` expressing the continuum
hypothesis.

It is a sentence over {uses "def:zfc-language"}[].
:::

At the Boolean-valued level, the same mathematical assertion is represented by
a Boolean-valued predicate named `CH₂`.

:::definition "def:ch-two" (lean := "Flypitch.bSet.CH₂")
`CH₂` is the Boolean value of the continuum hypothesis inside a
Boolean-valued universe of sets.
:::

# The Soundness Bridge For CH

The syntactic sentence and the Boolean-valued predicate must agree. This is
where the formula encoding is checked against the semantic interpretation of
Boolean-valued sets.

:::theorem "thm:ch-formula-sound" (lean := "Flypitch.ZFC.CH_f_sound")
A Boolean condition forces the sentence `CH_f` exactly when it lies below the
Boolean value `CH₂`.

This theorem connects {uses "def:ch-formula"}[] and {uses "def:ch-two"}[].
:::

:::theorem "thm:not-ch-formula-sound" (lean := "Flypitch.ZFC.neg_CH_f_sound")
A Boolean condition forces the negation of `CH_f` exactly when it lies below
the Boolean complement of `CH₂`.

This theorem is the negated companion of {uses "thm:ch-formula-sound"}[].
:::

# Why The Encoding Matters

The forcing chapters prove statements about `CH₂`: one Boolean algebra makes
`CH₂` false, another makes `CH₂` true. The final independence theorem is about
the sentence `CH_f`. The bridge theorems above are what convert between these
two levels.

:::theorem "thm:zfc-bset-soundness-package" (lean := "Flypitch.ZFC.bSet_models_ZFC")
The Boolean-valued universe forces the formal theory `ZFC`, so soundness can
be applied to derivations from the ZFC axioms.

This packages {uses "def:zfc-theory"}[] with the Boolean-valued model from
{uses "thm:bset-models-zfc"}[].
:::

# Lean Side Notes

The declarations to keep in view are `L_ZFC`, `ZFC`, `CH_f`,
`CH_f_sound`, `neg_CH_f_sound`, and `bSet_models_ZFC`. They are the formal
interface between the first-order proof statement and the Boolean-valued CH
calculations.
