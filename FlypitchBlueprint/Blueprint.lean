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

open Verso.Genre
open Verso.Genre.Manual
open Informal

set_option verso.blueprint.numbering "global"

#doc (Manual) "Flypitch Lean 4 Blueprint" =>

This Blueprint is the planned `verso-blueprint` port of the repository's
current LaTeX blueprint.

The initial scaffold keeps the existing TeX pipeline untouched while the
content is migrated chapter by chapter into Verso modules. Until the migration
is complete, the current source of truth for published blueprint prose remains
under `blueprint/src/`.

{include 0 FlypitchBlueprint.Chapters.Overview}
{include 0 FlypitchBlueprint.Chapters.FOLCore}
{include 0 FlypitchBlueprint.Chapters.CompactnessCompletion}
{include 0 FlypitchBlueprint.Chapters.ColimitsLanguageExtension}
{include 0 FlypitchBlueprint.Chapters.Henkinization}
{include 0 FlypitchBlueprint.Chapters.StatusNextFrontier}

{blueprint_graph}
{blueprint_summary}
