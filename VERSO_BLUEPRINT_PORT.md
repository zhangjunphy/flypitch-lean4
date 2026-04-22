# Verso Blueprint Port Plan

This file tracks the migration from the current LaTeX blueprint under
`blueprint/src/` to the new `verso-blueprint` scaffold under
`FlypitchBlueprint/`.

## Current State

- The published blueprint is still the LaTeX version.
- The Verso scaffold exists in parallel and is not yet part of CI or Pages.
- The first migration milestone is structure, not feature parity.

## Porting Rules

- Keep the current LaTeX blueprint build working until the Verso version is
  ready to replace it.
- Reuse chapter boundaries from the current blueprint.
- Preserve mathematical narrative first; add Lean declaration links second.
- Keep labels stable wherever `verso-blueprint` accepts the existing naming
  scheme cleanly.
- When a direct port is awkward, keep a short placeholder in Verso and record
  the source file that still needs to be converted.

## Chapter Mapping

- `blueprint/src/chapters/overview.tex`
  -> `FlypitchBlueprint/Chapters/Overview.lean`
- `blueprint/src/chapters/fol_core.tex`
  -> `FlypitchBlueprint/Chapters/FOLCore.lean`
- `blueprint/src/chapters/compactness_completion.tex`
  -> `FlypitchBlueprint/Chapters/CompactnessCompletion.lean`
- `blueprint/src/chapters/colimits_language_extension.tex`
  -> `FlypitchBlueprint/Chapters/ColimitsLanguageExtension.lean`
- `blueprint/src/chapters/henkinization.tex`
  -> `FlypitchBlueprint/Chapters/Henkinization.lean`
- `blueprint/src/chapters/status_next_frontier.tex`
  -> `FlypitchBlueprint/Chapters/StatusNextFrontier.lean`

## Migration Order

1. Port chapter prose and headings.
2. Convert statements and proofs into Blueprint blocks.
3. Recreate cross-references with Blueprint labels.
4. Attach Lean declarations for the most important results.
5. Add graph and summary pages only after enough labels exist to make them
   useful.
6. Replace the deployment pipeline only after the rendered Verso site is a
   credible substitute for the current web blueprint.

## Lean Linking Priority

Start with the highest-value theorem nodes:

- soundness
- proof compactness
- theory compactness
- maximal consistent extension
- completion of a consistent theory
- proof transport / reflection
- one-step Henkin consistency
- consistency along the Henkin chain

## Deployment Plan

- Short term: keep the current Jekyll homepage and LaTeX blueprint deploy.
- Mid term: build `flypitch-blueprint` in CI as a non-blocking parallel check.
- Final step: either publish `_out/site/html-multi` directly or copy it into
  `homepage/blueprint` during the Pages workflow.
