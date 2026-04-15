# Flypitch Lean 4 Port Status

This file tracks the actual port sequence and the checks used to verify progress.

## Target

- Upstream repository: `https://github.com/flypitch/flypitch`
- End goal: port `src/summary.lean` and recover the theorem `independence_of_CH`

## Dependency Split

The upstream project breaks into two large branches that meet in `zfc.lean`.

1. Logic/completeness branch
   - `to_mathlib`
   - `fol`
   - `compactness`
   - `completion`
   - `colimit`
   - `language_extension`
   - `henkin`
   - `completeness`
2. Set-theory/forcing branch
   - `bv_tauto`
   - `pSet_ordinal`
   - `set_theory`
   - `regular_open_algebra`
   - `cantor_space`
   - `collapse`
   - `bvm`
   - `bvm_extras`
   - `bvm_extras2`
   - `aleph_one`
   - `forcing`
   - `forcing_CH`
3. Integration branch
   - `bfol`
   - `zfc`
   - `print_formula`
   - `summary`

## Worker Boundaries

- `Compat.Core`: logic-side subset of upstream `to_mathlib`
- `FOL.Core`: first-order syntax, substitution, proof system
- `FOL.Semantics`: structures, realizations, satisfaction, soundness
- `CompactnessCompletion`: compactness and maximal consistent extensions
- `ColimitLanguageExtension`: directed colimits and language morphisms
- `HenkinCompleteness`: witness extension and completeness theorem
- `PSetOrdinal`: `pSet`/ordinal/cardinal groundwork
- `ForcingTopology`: `set_theory`, `regular_open_algebra`, `cantor_space`
- `Collapse`: collapse poset and Boolean algebra
- `BooleanValuedModels`: `bv_tauto`, `bvm`, `bvm_extras*`, `aleph_one`
- `ForcingResults`: `forcing`, `forcing_CH`
- `ZFCIntegration`: `bfol`, `zfc`, `print_formula`, `summary`

## Milestones

- [x] Normalize the Lean 4 project around a Mathlib-backed `Flypitch` library.
- [x] Record a dependency-ordered port plan grounded in the upstream module graph.
- [x] Port the first shared compat layer in `Flypitch/Compat/Core.lean`.
- [x] Port the initial FOL term syntax layer in `Flypitch/FOL/Syntax.lean`.
- [x] Port FOL formula syntax and structural term/formula operations in `Flypitch/FOL/Formula.lean`.
- [x] Port the basic proof-tree layer and weakening infrastructure in `Flypitch/FOL/Proof.lean`.
- [x] Port the proof-transport lemmas that depend on lift/substitution commutation.
- [x] Extend `Flypitch.FOL` through semantics and soundness.
- [x] Port a small regression target analogous to upstream `abel.lean`.
- [x] Port the front formula-level tranche of `compactness.lean`.
- [x] Port sentence/theory infrastructure from upstream `fol.lean` in `Flypitch/FOL/Theory.lean`.
- [x] Finish the theory-level compactness lemmas in `Flypitch/Compactness.lean`.
- [x] Port maximal consistent extension machinery from upstream `completion.lean` in `Flypitch/Completion.lean`.
- [x] Port the directed-colimit and language-extension layer in `Flypitch/Colimit.lean` and `Flypitch/LanguageExtension.lean`.
- [x] Port the early Henkin language-colimit slice in `Flypitch/Henkin.lean`.
- [x] Port Henkin term/formula/bounded-formula chains and comparison maps into `LInfty`.
- [x] Prove bijectivity of the term/formula comparison maps into `LInfty`.
- [x] Port bounded-term/bounded-formula comparison bijectivity and the induced equivalence at bounded formulas.
- [x] Port Henkin witness properties, `witInfty`, the raw `ι`/`T_infty` theory-chain scaffolding, and the enough-constants proof for `henkinization`.
- [x] Port the fresh-constant generalization layer in `Flypitch/LanguageExtension.lean` (`boundedFormulaSubstSentence`, `generalize_constant`, `sgeneralize_constant`).
- [x] Finish the henkinization/completed-theory bridge on top of the now-ported `henkinTheoryStep`, `ι`-chain, and `T_infty` consistency proofs.
- [x] Port the first Boolean-valued tautology helper file in `Flypitch/BVTauto.lean`.
- [ ] Port the remaining term-model/completeness tail needed for upstream `completeness.lean`.
- [ ] Port the forcing-side root files `pSet_ordinal.lean` and `set_theory.lean`.
- [ ] Port the topology/regular-open/collapse stack.
- [ ] Port Boolean-valued models.
- [ ] Reconnect both branches in `zfc`.
- [ ] Re-establish `independence_of_CH`.

## Verification Policy

Every completed milestone must satisfy both checks:

1. `lake build`
2. A concrete imported module corresponding to the milestone compiles cleanly without `axiom` placeholders.

## Current Verified Surface

- `Flypitch/Compat/Core.lean`
- `Flypitch/FOL/Syntax.lean`
- `Flypitch/FOL/Formula.lean`
- `Flypitch/FOL/Proof.lean`
- `Flypitch/FOL/Semantics.lean`
- `Flypitch/FOL/Theory.lean`
- `Flypitch/Compactness.lean`
- `Flypitch/Completion.lean`
- `Flypitch/Colimit.lean`
- `Flypitch/LanguageExtension.lean`
- `Flypitch/Henkin.lean`
- `Flypitch/BVTauto.lean`
- `Flypitch/Examples/Abel.lean`
- `Flypitch/PSetOrdinal.lean`

## Next Blocker

`lake build` currently succeeds, but the repository is not as far along as the old plan
suggested.

Evidence-backed status:

- The logic/Henkin chain now builds through `Flypitch/Henkin.lean`, including the completed
  Henkinization bridge to a complete Henkin extension.
- The upstream `completeness.lean` file is still **not** ported, and the supporting late-`fol`
  term-model material used by upstream completeness (`term_model`, `nonempty_term_model`,
  `completion_of_henkinization`, and the reduct-to-`T` satisfaction lemmas) is also still
  absent from the Lean 4 tree.
- On the forcing side, `Flypitch/PSetOrdinal.lean` is only an initial bridge layer rather than a
  complete port of upstream `pSet_ordinal.lean`.
- `Flypitch/BVTauto.lean` is now present as the first fully ported forcing-root utility file.
- `Flypitch/PSetOrdinal.lean` now contains the initial ordinal/cardinal bridge layer, the first
  structural `PSet` well-foundedness/transitivity lemmas used to model ordinal-shaped pre-sets,
  a first pass of function-graph infrastructure (`pair`, `prod`, `is_func`, `functions`,
  injectivity/surjectivity predicates), and the first finite-ordinal subset/membership lemmas
  (`subset_of_le`, `of_nat_mem_of_lt`, `of_nat_is_transitive`) needed by later forcing/set-theory
  files.
- `Flypitch/SetTheory.lean` now exists and contains the first delta-system tranche from upstream:
  the core definition plus the basic preimage/image/reindexing preservation lemmas.

So the real near-term blockers are split across **both** major branches:

1. finish the remaining logic-side completeness prerequisites and port `completeness.lean`;
2. finish the two forcing root files `pSet_ordinal.lean` and `set_theory.lean`, which unblock
   the downstream forcing/topology stack.

The next Lean 4 tranche should therefore be chosen from these root blockers based on local
traction rather than the older linear estimate. After the current `BVTauto` milestone, the two
most direct large targets are:

- `pSet_ordinal.lean`
- `set_theory.lean`

while the main logic-side blocker remains:

- `completeness.lean` together with its missing term-model support.
