import Verso
import VersoManual
import VersoBlueprint
import Flypitch.Summary

open Verso.Genre
open Verso.Genre.Manual
open Informal

set_option linter.hashCommand false
set_option linter.style.emptyLine false

#doc (Manual) "Putting The Proof Together" =>

The proof now has all of its pieces.

1. First-order soundness says that formal derivations are respected by
   semantics.
2. Boolean-valued soundness gives the same conclusion for Boolean-valued
   structures.
3. The Boolean-valued universe of `bSet`s forces ZFC.
4. The Cohen Boolean algebra forces not-CH.
5. The collapse Boolean algebra forces CH.

# The Soundness Argument

If ZFC proved CH, then every Boolean-valued model of ZFC would force CH. The
Cohen model is a Boolean-valued model of ZFC, but it forces not-CH. Therefore
ZFC does not prove CH.

If ZFC proved not-CH, then every Boolean-valued model of ZFC would force
not-CH. The collapse model is a Boolean-valued model of ZFC, but it forces CH.
Therefore ZFC does not prove not-CH.

:::theorem "thm:final-ch-unprovable" (lean := "Flypitch.CH_unprovable")
ZFC does not prove the formal sentence `CH_f`.

This is the final form of {uses "thm:ch-unprovable-from-cohen"}[].
:::

:::theorem "thm:final-not-ch-unprovable" (lean := "Flypitch.neg_CH_unprovable")
ZFC does not prove the formal negation of `CH_f`.

This is the final form of {uses "thm:not-ch-unprovable-from-collapse"}[].
:::

# Independence

Independence is the conjunction of the two unprovability statements. The final
Lean theorem is short because the preceding chapters have already done the
mathematical work: one side comes from the Cohen model, the other from the
collapse model.

:::theorem "thm:final-independence-of-ch" (lean := "Flypitch.independence_of_CH")
The continuum hypothesis is independent of ZFC.

This theorem combines {uses "thm:final-ch-unprovable"}[] and
{uses "thm:final-not-ch-unprovable"}[].
:::

# Reading The Lean Statement

The theorem `Flypitch.independence_of_CH` states `independent ZFC CH_f`.
Here `ZFC` is the formal theory, `CH_f` is the formal sentence expressing CH,
and `independent` means that neither `CH_f` nor its negation is derivable from
the theory.

Thus the final formal statement matches the mathematical conclusion: ZFC
settles neither CH nor its negation.
