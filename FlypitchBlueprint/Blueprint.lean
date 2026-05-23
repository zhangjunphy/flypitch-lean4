import Verso
import VersoManual
import VersoBlueprint
import VersoBlueprint.Commands.Graph
import VersoBlueprint.Commands.Summary
import FlypitchBlueprint.Chapters.Introduction
import FlypitchBlueprint.Chapters.FirstOrderLogic
import FlypitchBlueprint.Chapters.Completeness
import FlypitchBlueprint.Chapters.BooleanAlgebra
import FlypitchBlueprint.Chapters.BooleanValuedSemantics
import FlypitchBlueprint.Chapters.ZFC
import FlypitchBlueprint.Chapters.CohenForcing
import FlypitchBlueprint.Chapters.CollapseForcing
import FlypitchBlueprint.Chapters.Independence

open Verso.Genre
open Verso.Genre.Manual
open Informal

set_option verso.blueprint.numbering "global"
set_option linter.hashCommand false

#doc (Manual) "Flypitch: The Independence of the Continuum Hypothesis" =>

In 1878, Georg Cantor conjectured that every infinite subset of the real numbers
is either countable or has the cardinality of the continuum. This statement,
known as the Continuum Hypothesis (CH), became the first of Hilbert's famous
twenty-three problems in 1900. In 1938, Kurt Goedel showed that CH cannot be
disproved from the axioms of Zermelo--Fraenkel set theory with Choice (ZFC), by
exhibiting a model --- the constructible universe $`L` --- in which CH holds.
In 1963, Paul Cohen introduced the method of forcing and constructed a model of
ZFC in which CH fails, thereby proving that CH cannot be proved from ZFC either.
Together, these two results establish that the continuum hypothesis is
independent of ZFC.

This document presents a complete, self-contained exposition of the independence
proof, formalized in the Lean 4 proof assistant. Each definition and theorem is
linked to its formal counterpart in the Lean codebase, so the reader can inspect
the fully verified proof at any point. The proof follows the Boolean-valued
model approach to forcing, which avoids the need to construct a countable
transitive model in the metatheory and is particularly well-suited to
formalization.

The strategy is as follows. We first develop the syntax and semantics of
first-order logic, including the notions of proof, theory, and soundness. We
then introduce complete Boolean algebras and Boolean-valued semantics, which
assign to each formula a truth value in a complete Boolean algebra rather than a
simple true/false. Within this framework, we construct two specific
Boolean-valued models of ZFC: one via Cohen forcing, in which CH receives truth
value $`\bot`$ (false), and one via collapse forcing, in which CH receives
truth value $`\top`$ (true). By the soundness theorem for Boolean-valued
semantics, any theorem of ZFC must hold with truth value $`\top`$ in every
Boolean-valued model. Since CH does not hold in the Cohen model, it cannot be a
theorem of ZFC; since its negation does not hold in the collapse model, the
negation cannot be a theorem either. Hence CH is independent.

{include 0 FlypitchBlueprint.Chapters.Introduction}
{include 0 FlypitchBlueprint.Chapters.FirstOrderLogic}
{include 0 FlypitchBlueprint.Chapters.Completeness}
{include 0 FlypitchBlueprint.Chapters.BooleanAlgebra}
{include 0 FlypitchBlueprint.Chapters.BooleanValuedSemantics}
{include 0 FlypitchBlueprint.Chapters.ZFC}
{include 0 FlypitchBlueprint.Chapters.CohenForcing}
{include 0 FlypitchBlueprint.Chapters.CollapseForcing}
{include 0 FlypitchBlueprint.Chapters.Independence}

{blueprint_graph}
{blueprint_summary}
