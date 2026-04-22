import Verso
import VersoManual
import VersoBlueprint

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Overview" =>

The long-term goal of Flypitch is a formal proof that the continuum hypothesis
is independent of ZFC. Mathematically, the original project reaches this goal
by combining three ingredients:

- a first-order logic and completeness development
- the forcing and Boolean-valued-model machinery
- the set-theoretic infrastructure connecting these two sides

The present Lean 4 repository does not yet cover this entire story. What is
already formalized is the logic-side development leading from first-order
syntax to complete Henkin extensions of consistent theories. This blueprint is
therefore written as an account of the mathematics that is currently available,
rather than as a premature sketch of the final independence proof.

# What Has Been Built

The existing Lean 4 development already contains a coherent model-theoretic
thread. Starting from the syntax and semantics of first-order logic, it proves
soundness, establishes compactness in the proof-theoretic form needed for later
consistency arguments, constructs maximal consistent extensions, and develops
the language-extension machinery required for Henkinization. The endpoint of
the present port is a complete Henkin extension of any consistent theory.

This means that the current repository already supports a substantial part of
the standard completeness argument. What is still missing is the later
packaging of completeness itself and, beyond that, the forcing and set-theoretic
constructions that are needed for the independence result.

# How To Read The Blueprint

This blueprint is organized as a mathematical progression.

- the next chapter develops first-order languages, syntax, derivability,
  semantics, and theories
- the compactness and completion chapter explains how consistency can be
  reduced to finite fragments and how consistent theories are enlarged to
  complete ones
- the colimits and language extensions chapter introduces the language maps,
  reducts, colimits, and reflection arguments needed to compare syntax across
  enlarging languages
- the Henkinization chapter uses these ingredients to build the Henkin
  language, the limit theory, and finally a complete Henkin extension
- the final status chapter records the current boundary of the Lean 4 port

The intended reading is therefore not "which file was written first", but
rather "which mathematical idea depends on which earlier one".

# The Current Frontier

The main point of this blueprint is that the frontier of the Lean 4 port no
longer lies in the elementary first-order material. The logic-side development
has already progressed through the Henkin construction. The next serious gap is
after this stage: first the remaining completeness-side packaging, and then the
forcing branch beginning with the still-unported `Flypitch/PSetOrdinal.lean`
development.

# Formalization Note

The source files behind this blueprint include the first-order logic modules,
the compactness and completion files, the colimit and language-extension files,
and the Henkin file. Their role in the present document is supportive: the
chapters below describe the mathematical constructions first, and only then
indicate where those constructions are realized in Lean.
