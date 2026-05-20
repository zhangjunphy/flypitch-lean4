import Verso
import VersoManual
import VersoBlueprint
import Flypitch.Forcing
import Flypitch.ZFC

open Verso.Genre
open Verso.Genre.Manual
open Informal

set_option linter.hashCommand false
set_option linter.style.emptyLine false

#doc (Manual) "The Model Where CH Fails" =>

To show that ZFC cannot prove CH, it is enough to find a Boolean-valued model
of ZFC in which not-CH holds. The model in Flypitch is built from a
Cohen-style Boolean algebra adding many new reals at once.

# Many Cohen Reals

The index set has size `aleph_two`. For each index, the forcing construction
produces a Boolean-valued subset of omega. Intuitively, these are the new
reals. Distinct indices are forced to give distinct reals, so the model sees
an injection from `aleph_two` into the powerset of omega.

:::definition "def:cohen-algebra" (lean := "Flypitch.𝔹_cohen")
The Cohen Boolean algebra used for the not-CH model is built from regular
opens over the space of functions from `aleph_two x omega` to two values.
:::

:::theorem "thm:aleph-two-injects-continuum" (lean := "Flypitch.ℵ₂_injects_𝔠")
In the Cohen Boolean-valued model, `aleph_two` injects into the internal
continuum.
:::

# Cardinal Preservation

Adding many reals is not enough by itself. One must also know that the forcing
does not collapse the relevant cardinals. The countable chain condition
controls antichains in the Boolean algebra and gives the preservation
arguments needed to keep `aleph_one` and `aleph_two` separated.

Mathematically, the proof combines two facts:

- there are at least `aleph_two` many reals in the extension
- `aleph_one` remains strictly below `aleph_two`

Together they contradict CH, which would place the continuum at `aleph_one`.

:::theorem "thm:not-ch-forced" (lean := "Flypitch.not_CH₂")
In the Cohen Boolean-valued model, every condition lies below the complement
of `CH₂`; equivalently, the model forces not-CH.

This theorem uses {uses "def:ch-two"}[] and
{uses "thm:aleph-two-injects-continuum"}[].
:::

# From Failure Of CH To Unprovability

Suppose ZFC proved CH. By Boolean-valued soundness, every Boolean-valued model
of ZFC would force CH. But the Cohen model forces not-CH. Hence no such proof
exists.

:::theorem "thm:ch-unprovable-from-cohen" (lean := "Flypitch.ZFC.CH_f_unprovable")
The formal theory `ZFC` does not prove the formal sentence `CH_f`.

This theorem combines {uses "thm:not-ch-forced"}[],
{uses "thm:not-ch-formula-sound"}[], and
{uses "thm:bset-models-zfc"}[].
:::

# Lean Side Notes

The forcing endpoint is `not_CH₂`. The syntactic endpoint is
`ZFC.CH_f_unprovable`, re-exported in the final namespace as
`Flypitch.CH_unprovable`.
