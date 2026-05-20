import Verso
import VersoManual
import VersoBlueprint
import VersoBlueprint.Commands.Graph
import VersoBlueprint.Commands.Summary
import FlypitchBlueprint.Chapters.Overview
import FlypitchBlueprint.Chapters.FOLCore
import FlypitchBlueprint.Chapters.CompactnessCompletion
import FlypitchBlueprint.Chapters.ColimitsLanguageExtension
import FlypitchBlueprint.Chapters.Henkinization
import FlypitchBlueprint.Chapters.StatusNextFrontier
import FlypitchBlueprint.Chapters.PuttingProofTogether

open Verso.Genre
open Verso.Genre.Manual
open Informal

set_option verso.blueprint.numbering "global"
set_option linter.hashCommand false

#doc (Manual) "Flypitch: The Independence Of CH" =>

This blueprint explains the mathematical proof that the continuum hypothesis
is independent of ZFC, with Lean declarations serving as verification anchors.

The proof has the classical shape. First-order logic turns formal derivations
into semantic consequences. Boolean-valued models then give two semantic
tests: one Boolean-valued universe satisfies CH, while another satisfies its
negation. Since every theorem of ZFC is valid in every Boolean-valued model of
ZFC, these two universes rule out derivations of both CH and not-CH.

{include 0 FlypitchBlueprint.Chapters.Overview}
{include 0 FlypitchBlueprint.Chapters.FOLCore}
{include 0 FlypitchBlueprint.Chapters.CompactnessCompletion}
{include 0 FlypitchBlueprint.Chapters.ColimitsLanguageExtension}
{include 0 FlypitchBlueprint.Chapters.Henkinization}
{include 0 FlypitchBlueprint.Chapters.StatusNextFrontier}
{include 0 FlypitchBlueprint.Chapters.PuttingProofTogether}

{blueprint_graph}
{blueprint_summary}
