import Verso
import VersoManual
import VersoBlueprint

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Overview" =>

The long-term goal of Flypitch is a formal proof that the continuum hypothesis
is independent of ZFC. The original project reaches that endpoint by combining
three strands:

- a first-order logic and completeness development
- forcing and Boolean-valued models
- set-theoretic infrastructure connecting those two sides

The current Lean 4 port has not reached that full endpoint yet. What is
already formalized is the logic-side development leading from first-order
syntax through complete Henkin extensions of consistent theories.

# Migration Status

This chapter is the first `verso-blueprint` placeholder. It establishes the
document structure and keeps the migration boundary explicit:

- the current published blueprint source still lives in `blueprint/src/`
- the new Verso blueprint is being ported in parallel under
  `FlypitchBlueprint/`
- chapter content will move over incrementally, with labels and Lean links
  added as each chapter is converted

# Reading Order

The intended mathematical reading order matches the current LaTeX blueprint:

1. first-order logic core
2. compactness and completion
3. colimits and language extensions
4. Henkinization
5. current status and next frontier

# Formalization Boundary

The next serious gap after the current logic-side port is not elementary
first-order logic. It is the remaining packaging around completeness, followed
by the forcing-side branch beginning around `Flypitch/PSetOrdinal.lean`.
