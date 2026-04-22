import Verso
import VersoManual
import VersoBlueprint

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Status And Next Frontier" =>

The present blueprint now tells a complete logic-side story: it starts with
first-order syntax and semantics, passes through compactness and completion,
develops the language-extension machinery needed for witness arguments, and
ends with complete Henkin extensions of consistent theories.

# What The Current Port Delivers

From a mathematical point of view, the Lean 4 repository already contains:

- a first-order proof system together with soundness
- the theory-level notions of consistency and completeness
- compactness in the form needed for finite-fragment arguments
- maximal and complete consistent extensions
- the language-colimit and reflection tools needed to manage enlarging
  languages
- the Henkin construction through complete Henkin extensions

This is already substantial. It means that the model-theoretic infrastructure
behind the classical Henkin proof is no longer merely planned; it is present in
verified Lean 4 code.

# What Is Not Yet Present

The current state should not be overstated.

- the later completeness-side packaging beyond the present Henkin layer is not
  yet part of the documented Lean 4 surface
- the forcing-side development has not yet been ported
- the final integration leading to independence of the continuum hypothesis is
  therefore still absent

So the repository has reached a meaningful stopping point on the logic side,
but not the full Flypitch endpoint.

# The Next Frontier

According to the current project boundary, the next major missing development is
`pSet_ordinal`. This marks the beginning of the forcing-side branch.

Once that side of the project begins to land in Lean 4, the natural blueprint
continuation will move from the present model-theoretic story to the
set-theoretic and Boolean-valued constructions used in forcing.

# How The Blueprint Should Grow

The rule for future chapters should remain the same as in this pass:

- document only mathematics that is already verified in Lean 4
- write the chapters as mathematical explanations rather than code tours
- use Lean names to orient the reader, not to replace the mathematics

When the forcing branch is ported, the next chapters should therefore begin
with the underlying mathematics of that branch rather than with a list of Lean
modules.
