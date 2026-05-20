import Verso
import VersoManual
import VersoBlueprint
import Flypitch.ForcingCH
import Flypitch.ZFC

open Verso.Genre
open Verso.Genre.Manual
open Informal

set_option linter.hashCommand false
set_option linter.style.emptyLine false
set_option linter.style.longLine false

#doc (Manual) "The Model Where CH Holds" =>

To show that ZFC cannot prove the negation of CH, the proof uses a second
Boolean-valued universe. This one is built from a collapse algebra. Its role
is to make the continuum no larger than `aleph_one`, while the usual lower
bound by omega remains in place.

# The Collapse Algebra

The collapse algebra is designed so that the powerset of omega in the
Boolean-valued universe is covered by a relation whose domain has size
`aleph_one`. Informally, it names enough data to make every real appear in a
list indexed by the first uncountable cardinal.

:::definition "def:collapse-algebra" (lean := "Flypitch.collapse_algebra.𝔹_collapse")
The collapse Boolean algebra supplies the Boolean-valued universe in which CH
holds.
:::

# The Surjection Argument

The central construction is a relation from `aleph_one` onto the internal
powerset of omega. Once this relation is shown to be functional and
surjective in the Boolean-valued sense, the continuum is at most `aleph_one`.

At the same time, the continuum cannot be countable. The result is exactly the
cardinal characterization of CH: the continuum is the first uncountable
cardinal.

:::theorem "thm:collapse-continuum-bound" (lean := "Flypitch.collapse_algebra.CH₂_true_of_check_functions_eq")
The collapse construction gives the Boolean-valued cardinal comparison needed
to prove `CH₂`.
:::

:::theorem "thm:ch-forced" (lean := "Flypitch.collapse_algebra.CH₂_true")
In the collapse Boolean-valued model, every condition lies below `CH₂`;
equivalently, the model forces CH.

This theorem uses {uses "def:ch-two"}[] and
{uses "thm:collapse-continuum-bound"}[].
:::

# From CH To Unprovability Of Not-CH

Suppose ZFC proved not-CH. By Boolean-valued soundness, the collapse model
would force not-CH. But this model forces CH. Hence ZFC cannot prove the
negation of CH.

:::theorem "thm:not-ch-unprovable-from-collapse" (lean := "Flypitch.ZFC.neg_CH_f_unprovable")
The formal theory `ZFC` does not prove the negation of the formal sentence
`CH_f`.

This theorem combines {uses "thm:ch-forced"}[],
{uses "thm:ch-formula-sound"}[], and {uses "thm:bset-models-zfc"}[].
:::

# Lean Side Notes

The forcing endpoint is `collapse_algebra.CH₂_true`. The syntactic endpoint
is `ZFC.neg_CH_f_unprovable`, re-exported in the final namespace as
`Flypitch.neg_CH_unprovable`.
