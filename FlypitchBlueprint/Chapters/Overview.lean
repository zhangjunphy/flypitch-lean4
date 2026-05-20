import Verso
import VersoManual
import VersoBlueprint
import Flypitch.Summary

open Verso.Genre
open Verso.Genre.Manual
open Informal

set_option linter.hashCommand false
set_option linter.style.emptyLine false

#doc (Manual) "The Independence Theorem" =>

The continuum hypothesis, abbreviated CH, says that every infinite subset of
the real line is either countable or has the same size as the real line. In the
language of cardinals, there is no cardinal strictly between the size of the
natural numbers and the size of the powerset of the natural numbers.

ZFC is the standard first-order axiom system for sets. A sentence is provable
from ZFC when it has a formal derivation from those axioms. A sentence is
independent of ZFC when neither the sentence nor its negation is provable from
ZFC.

:::definition "def:independent-sentence" (lean := "Flypitch.independent")
For a first-order theory $`T` and a sentence $`\varphi`, independence means
that $`T` proves neither $`\varphi` nor $`\neg\varphi`.
:::

# The Two-Model Strategy

The proof uses Boolean-valued models. These are models in which a sentence has
a truth value in a complete Boolean algebra rather than only the values true
and false. The top element of the Boolean algebra means "fully true", and the
bottom element means "fully false".

There are two Boolean-valued universes in the proof.

- In the Cohen-style universe, CH has Boolean value bottom. Equivalently, the
  universe forces not-CH.
- In the collapse universe, CH has Boolean value top. Equivalently, the
  universe forces CH.

The reason this proves independence is soundness. If ZFC proves a sentence,
then every Boolean-valued model of ZFC forces that sentence. A model forcing
not-CH therefore rules out a proof of CH, and a model forcing CH rules out a
proof of not-CH.

:::theorem "thm:ch-unprovable" (lean := "Flypitch.CH_unprovable")
ZFC does not prove CH.

This theorem uses the Boolean-valued model from
{uses "thm:not-ch-forced"}[] together with Boolean-valued soundness from
{uses "thm:boolean-soundness"}[].
:::

:::theorem "thm:not-ch-unprovable" (lean := "Flypitch.neg_CH_unprovable")
ZFC does not prove the negation of CH.

This theorem uses the collapse model from {uses "thm:ch-forced"}[] together
with Boolean-valued soundness from {uses "thm:boolean-soundness"}[].
:::

:::theorem "thm:independence-of-ch" (lean := "Flypitch.independence_of_CH")
The continuum hypothesis is independent of ZFC.

In Lean, the final statement says that the syntactic sentence `CH_f` is
independent of the theory `ZFC`.
:::

# Lean Side Notes

The final theorem is `Flypitch.independence_of_CH`. It is a compact wrapper
around the two unprovability statements `Flypitch.CH_unprovable` and
`Flypitch.neg_CH_unprovable`, each of which is proved by evaluating CH in a
Boolean-valued universe.
