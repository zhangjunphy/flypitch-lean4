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
- [x] Port the `functions x 2 ↪ powerset x` injection tranche in `Flypitch/PSetOrdinal.lean`
  (`f2ip`, `mem_f2ip_iff`, `functions_to_2_eq`, `functions_2_injects_into_powerset`).
- [x] Close the next `PSetOrdinal` API tranche around function congruence/extensionality and
  `injects_into` transport (`is_func_congr_right`, `is_extensional_of_is_func`,
  `mk_is_injective_function`, `injects_into_refl`, `injects_into_congr_*`).
- [x] Add the next `PSetOrdinal` compatibility/helper tranche (`is_func_iff`,
  `is_extensional_of_mem_functions`, `set_of_indicator`, `powerset_sound`).
- [x] Add the next upstream-name compatibility tranche around weak function lifts
  (`function_lift_spec`, `function_lift'_spec`, `mem_fun_of_function_lift'_graph`,
  `function_lift_graph_of_mem_fun_inj`, `surj_lift'`).
- [x] Add the next set-level soundness bridge in `PSetOrdinal` (`prod_sound`).
- [x] Add the next quotient/membership compatibility tranche in `PSetOrdinal`
  (`equiv_of_eq`, `equiv_iff_eq`, `mem_iff`, `not_mem_iff`, `mem_sound`,
  `mem_insert`, `mem_insert'`, `Set.subset_iff_all_mem`, `empty_empty`,
  `Set.mk_unfold`).
- [x] Add the next tiny compatibility aliases and soundness bridge
  (`pair_mem.congr_left/right`, `function_lift'_graph_of_mem_fun_inj`, `is_func_sound`).
- [x] Add the next ordinal/cardinal compatibility aliases
  (`mk_type_mk_eq`, `ordinal.mk_card`, `two_eq_succ_one`, `add_one_lt_add_one`, `one_lt_two`).
- [x] Add the next structural compatibility tranche (`mk_eq`, `eta`, `mk_zero_type`,
  `mk_zero_cast`, `mk_zero_cast'`, `mk_zero_forall`, `mk_succ`, `succ_type_cast*`,
  `option_cast'`, `succ_func_*`, `succ_type_forall/exists`, `option_succ_type_forall`).
- [x] Expand `Flypitch/SetTheory.lean` beyond the initial delta-system core with the next
  upstream-compatible helper tranche (`Set.finite_of_finite_image_of_inj_on`,
  `Set.countable_of_embedding`, `Set.eqOn'`, `Set.eqOn'_iff`,
  `countable_chain_condition`, `countable_chain_condition_of_nonempty`,
  `countable_chain_condition_of_countable`).
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
- `Flypitch/AlephOne.lean`
- `Flypitch/Examples/Abel.lean`
- `Flypitch/PSetOrdinal.lean`

## Next Blocker

`lake build` currently succeeds, but the repository is not as far along as the old plan
suggested.

Evidence-backed status:

- The logic/Henkin chain now builds through `Flypitch/Henkin.lean`, including the completed
  Henkinization bridge to a complete Henkin extension and upstream-style
  `completion_of_henkinization*` wrappers.
- The bounded-syntax layer now includes bounded term/formula realization together with bridge
  lemmas back to the ordinary semantics (`realize_bounded_term_eq`,
  `realize_bounded_formula_iff`, `realize_bounded_formula_iff_of_fst`) and closed-term top-variable
  substitution helpers.
- The completeness tail is now ported end-to-end. In addition to
  `find_counterexample_of_henkin`, the term-model quotient scaffold, quotient-respecting
  function/relation lifts, canonical-class bridge lemmas, bounded realization/substitution bridge,
  and the complete-Henkin-model induction (`count_quantifiers_subst_formula`,
  `term_model_ssatisfied_iff`, `term_model_ssatisfied`, `completeness'`), the file now also has
  the final public wrappers:
  `theory_induced_subset_henkinization`, `satisfiable_of_consistent`, and `completeness`.
- The theory-side wrappers in `Flypitch/FOL/Theory.lean` are now in place too:
  `Th`, `realize_sentence_Th`, `is_complete_Th`, `in_theory_iff_satisfied`, `L_empty`, `T_empty`,
  and `T_equality`.
- As a result, the old logic-side blocker around the reduct/model-existence bridge is no longer the
  frontier. The main remaining repo-level blocker has shifted back to the forcing side.
- `Flypitch/BVTauto.lean` is now present as the first fully ported forcing-root utility file.
- `Flypitch/PSetOrdinal.lean` now appears effectively complete relative to upstream
  `pSet_ordinal.lean`: it includes the ordinal/cardinal bridge layer, the `PSet` structural
  well-foundedness/transitivity lemmas, the function-graph infrastructure, the `functions x 2 ↪
  powerset x` injection section, and several extra Lean 4 compatibility lemmas not present as
  separate upstream theorems.
- A new module `Flypitch/AlephOne.lean` now starts the upstream `aleph_one.lean` port. The first
  pure-`pSet` tranche is in place: `regularity`, `aleph_one`, `aleph_one_Ord`,
  `aleph_one_weak_Ord_spec`, `epsilon_trichotomy`, `compl`, `binary_inter`, `Ord_of_mem_Ord`,
  and the first ordinal-comparison lemmas
  (`Ord.lt_of_ne_and_le`, `Ord.le_or_le`, `Ord.trichotomy`, `Ord.lt_of_le_of_lt`,
  `Ord.le_iff_lt_or_eq`).
- `Flypitch/SetTheory.lean` now exists and contains the first delta-system tranche from upstream:
  the core definition plus the basic preimage/image/reindexing preservation lemmas, the first
  small `Set` helper tranche (`finite_of_finite_image_of_inj_on`, `countable_of_embedding`,
  `eqOn'`, `eqOn'_iff`), and the opening countable-chain-condition API
  (`countable_chain_condition`, `countable_chain_condition_of_nonempty`,
  `countable_chain_condition_of_countable`).

So the real near-term blockers are now concentrated on the forcing side:

1. continue the remaining `aleph_one.lean` pSet/cardinal tail and then its downstream `bSet`
   well-ordering section;
2. continue `set_theory.lean`, which still only contains an opening delta-system/CCC tranche.

The next Lean 4 tranche should therefore come from:

- `aleph_one.lean`
- `set_theory.lean`
