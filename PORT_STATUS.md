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
- [x] Extend the `SetTheory` CCC tranche through the next upstream basis/separable-space lemmas
  (`countable_chain_condition_of_topological_basis`,
  `countable_chain_condition_of_separable_space`).
- [x] Start the `SetTheory` product-topology section with the subbasic-open definitions and
  immediate lemmas (`standard_open`, `pi_subbasis`, `mem_pi_subbasis_iff`,
  `isOpen_standard_open`, `isOpen_of_mem_pi_subbasis`).
- [x] Add the next `SetTheory` `pi`-section scaffold around finite subbasic intersections
  (`pi_basis`, `nonempty_of_mem_pi_basis`).
- [x] Add the first forward basic-open membership lemma for the `SetTheory` `pi` section
  (`mem_pi_basis_of_pi`).
- [x] Promote the `SetTheory` finite-cylinder family to an actual product-topology basis
  (`isOpen_of_mem_pi_basis`, `isTopologicalBasis_pi_basis`).
- [x] Add the missing finite-subbasis normal form for the `SetTheory` product basis
  (`sInter_eq_pi_of_finite_subbasis`, `mem_pi_basis_iff`).
- [x] Close the explicit `pi_basis` normal-form equality in `SetTheory`
  (`pi_basis_eq`).
- [x] Add the next upstream support tranche for `SetTheory` product cylinders
  (`support`, `support_pi`, `support_elim`,
  `finite_support_of_pi_subbasis`, `finite_support_of_pi_basis`).
- [x] Add the first finite-coordinate-support API for `SetTheory` product cylinders
  (`pi_set_support`, `finite_pi_set_support_of_eq_univ_outside`,
  `exists_eq_pi_with_finite_support_of_mem_pi_basis`,
  `exists_finite_pi_set_support_of_mem_pi_basis`).
- [x] Add the first support-based membership congruence lemmas for `SetTheory` cylinders
  (`mem_pi_pi_set_support_iff`, `mem_pi_pi_set_support_congr`, `mem_pi_basis_congr`).
- [x] Add the first countable cylinder-family candidate for the `SetTheory` product basis
  (`pi_basis_from_finset`, `pi_basis_from`, `countable_pi_basis_from_finset`,
  `countable_pi_basis_from`, `mem_pi_basis_of_mem_pi_basis_from*`).
- [x] Specialize the `SetTheory` cylinder-family candidate to actual countable product bases
  (`isTopologicalBasis_pi_basis_from`, `countable_pi_basis_from_countableBasis`,
  `isTopologicalBasis_pi_basis_from_countableBasis`,
  `secondCountableTopology_pi_of_countable`).
- [x] Add the corresponding CCC corollary for countable products of second-countable spaces
  (`countable_chain_condition_pi_of_countable`).
- [x] Add the first Mathlib-4 cofinality/initial-segment helper tranche for the remaining
  `SetTheory` delta-system proof (`orderType`, `unbounded_lt_iff_isCofinal`,
  `cof_eq_mk_of_isRegular`, `exists_unbounded_of_unbounded_iUnion`,
  `exists_minimal_unbounded_parameter`, `mk_Iio_lt_of_ord_eq`, `mk_lt_of_bounded`).
- [x] Add the next ordinal-supremum helper tranche for the remaining `SetTheory` delta-system
  proof (`isSuccLimit_orderType_of_isRegular`, `iSup_lt_orderType_of_isRegular`,
  `iSup_succ_lt_orderType_of_isRegular`).
- [x] Add the outer `α₀` supremum-bound helper tranche for `SetTheory`
  (`mk_Iio_lt_of_lt_card`, `mk_subtype_lt_of_lt_card`,
  `iSup_Iio_lt_orderType_of_isRegular`).
- [x] Add the inner `α₀` supremum-bound helper tranche for `SetTheory`
  (`isWellOrder_lt_of_linearOrder`, `iSup_succ_typein_range_lt_of_bounded`,
  `inner_iSup_lt_of_minimal_unbounded_parameter`).
- [x] Assemble the full `α₀` double-supremum bound for the remaining `SetTheory`
  delta-system proof (`alpha0_lt_orderType_of_minimal_unbounded_parameter`).
- [x] Package the opening of `delta_system_lemma_2` through the minimal unbounded parameter and
  associated `α₀` bound (`exists_minimal_parameter_with_alpha0_bound`).
- [x] Add the `sub_α₀` smallness and strict-domination helpers needed before the recursive pick
  construction (`mk_typein_initial_segment_lt`,
  `exists_minimal_parameter_with_small_alpha0_segment`, `exists_gt_of_isSuccLimit_orderType`,
  `exists_range_gt_of_unbounded`).
- [x] Add the ordinal-based selection helpers used by the recursive pick construction
  (`exists_index_above_ordinal_of_unbounded`, `choose_index_above_ordinal_of_unbounded`,
  `choose_index_above_ordinal_of_unbounded_spec`).
- [x] Extend the pure-`pSet` `aleph_one.lean` port through the first countability/specification
  tranche (`mk_injects_into_of_mk_le_omega`, `injects_into_omega_of_mem_aleph_one`,
  `aleph_one_satisfies_spec`).
- [x] Extend the `AlephOne` `pSet` tail through the remaining repo-local uniqueness wrapper
  after the non-countability step (`equiv_aleph_one_of_weak_spec`).
- [x] Add the next `SetTheory` product-CCC helper for the uncountable product proof
  (`disjoint_restrict_image_of_support_inter_subset`).
- [x] Package the Δ-system root consequence for the product-CCC proof
  (`pairwise_disjoint_restrict_image_of_delta_supports`,
  `pairwiseDisjoint_restrict_image_range_of_delta_supports`).
- [x] Package the cardinal lower-bound side of the restricted-image family step
  (`mk_restrict_image_range_eq_of_delta_supports`,
  `aleph0_lt_mk_restrict_image_range_of_delta_supports`).
- [x] Package the openness side of the restricted-image family step
  (`isOpen_of_mem_restrict_image_range`).
- [x] Package the nonemptiness and final contradiction wrappers for the restricted-image family
  (`nonempty_restrict_image_of_delta_member`, `nonempty_of_mem_restrict_image_range`,
  `restrict_image_range_subset_open`, `restrict_image_range_subset_nonempty`,
  `not_countable_of_lift_aleph0_lt_mk`,
  `not_countable_restrict_image_range_of_delta_supports`,
  `not_countable_of_restrict_image_range_ccc_contradiction`).
- [x] Package the finite-root and root-subproduct CCC side of the same argument
  (`finite_support_of_delta_member`, `finite_supports_of_delta_family`,
  `finite_root_of_delta_supports`, `countable_chain_condition_root_subproduct_of_finite`,
  `countable_chain_condition_root_subproduct_of_delta_supports`,
  `countable_restrict_image_range_of_root_ccc`,
  `countable_restrict_image_range_of_delta_supports`,
  `false_of_uncountable_delta_supports_and_finite_root_ccc`).
- [x] Add uncountability-derived public wrappers for the product-CCC contradiction
  (`two_le_mk_of_aleph0_lt_mk`, `finite_root_of_uncountable_delta_supports`,
  `countable_chain_condition_root_subproduct_of_uncountable_delta_supports`,
  `countable_restrict_image_range_of_uncountable_delta_supports`,
  `false_of_uncountable_delta_supports`).
- [x] Add packaged Δ-system support wrappers that accept `delta_system.is_delta_system` directly
  (`finite_root_of_uncountable_delta_support_system`,
  `countable_chain_condition_root_subproduct_of_delta_support_system`,
  `exists_false_of_uncountable_delta_support_system`).
- [x] Add the indexed-family bridge from a pairwise-disjoint product-basis family with Δ-system
  supports to countability of its index type
  (`aleph0_lt_mk_of_not_countable`,
  `not_aleph0_lt_mk_of_pairwiseDisjoint_indexed_pi_basis_of_delta_support_system`,
  `countable_index_of_pairwiseDisjoint_pi_basis_of_delta_support_system`).
- [x] Generalize the product-CCC contradiction chain from second-countability to an arbitrary
  finite-root CCC hypothesis and isolate the final product-CCC wiring theorem conditional on the
  public uncountable Δ-system lemma
  (`exists_uncountable_fiber_of_countable_coloring`,
  `exists_uncountable_fixed_finite_cardinal`,
  `exists_aleph_one_subset`,
  `mk_iUnion_le_aleph_one_of_fixed_finite_cardinal`,
  `mk_toType_ord_succ_aleph0`,
  `ord_mk_toType_ord_succ_aleph0`,
  `powerlt_aleph0_lt_succ_aleph0`,
  `relIso_fin_of_finite_card`,
  `relIso_ulift_fin_of_finite_card`,
  `fixed_finite_delta_system_on_aleph_one`,
  `delta_system_lemma_uncountable`,
  `countable_index_of_pairwiseDisjoint_pi_basis_of_delta_support_system_of_finite_root_ccc`,
  `countable_chain_condition_pi_of_delta_system_lemma_uncountable`,
  `countable_chain_condition_pi`).
- [x] Start the topology/regular-open/collapse stack with compiling Lean 4 modules for
  `regular_open_algebra.lean`, the opening `cantor_space.lean` finite-cylinder API, and
  `collapse.lean` (`regular_opens`, `principal_open`, `standard_basis`, `collapse_poset`,
  `collapse_space`, `collapse_algebra`).
- [x] Extend the `CantorSpace` finite-cylinder tranche with upstream-style intersection normal forms
  and the standard-basic-cylinder nonemptiness witness
  (`principal_open_finset_eq_inter`, `co_principal_open_finset_eq_inter`,
  `intersection_standard_basis_nonempty'`, `nonempty_of_standard_basic_cylinder`).
- [x] Add the next `CantorSpace` standard-basis finite-intersection wrappers
  (`standard_basis_reindex`, `intersection_standard_basis_nonempty`).
- [x] Add the next `CantorSpace` cylinder-intersection compatibility helpers used by the standard
  basis intersection proof (`ins₁_out₂_disjoint`, `out₁_ins₂_disjoint`,
  `disjoint_union_of_inter_nonempty`).
- [ ] Port the remaining term-model/completeness tail needed for upstream `completeness.lean`.
- [ ] Port the forcing-side root files `pSet_ordinal.lean` and `set_theory.lean`.
- [ ] Continue the topology/regular-open/collapse stack beyond the initial compiling tranche.
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
- `Flypitch/RegularOpenAlgebra.lean`
- `Flypitch/CantorSpace.lean`
- `Flypitch/Collapse.lean`

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
- `Flypitch/AlephOne.lean` now also includes the next countability/specification step from
  upstream: the `ordinal.mk η ↪ ω` construction for countable ordinals together with
  `injects_into_omega_of_mem_aleph_one` and the witness that `aleph_one` satisfies the intended
  weak ordinal specification.
- The `AlephOne` `pSet` tranche now also has the converse non-countability step at `aleph_one`
  itself: `mk_le_omega_of_injects_into` turns a `pSet` injection `ordinal.mk η ↪ ω` back into the
  cardinal inequality on the underlying ordinal type, and `aleph_one_not_injects_into_omega`
  shows `aleph_one` is genuinely uncountable in the `pSet` sense.
- The `AlephOne` `pSet` file now also includes the repo-local uniqueness wrapper
  `equiv_aleph_one_of_weak_spec`. Because the current `aleph_one_weak_Ord_spec` is intentionally
  weak, this wrapper is exposed in the correct curried form: from the weak spec one obtains
  `¬ injects_into x ω → x ≃ aleph_one`.
- `Flypitch/SetTheory.lean` now exists and contains the first delta-system tranche from upstream:
  the core definition plus the basic preimage/image/reindexing preservation lemmas, the first
  small `Set` helper tranche (`finite_of_finite_image_of_inj_on`, `countable_of_embedding`,
  `eqOn'`, `eqOn'_iff`), and the opening countable-chain-condition API
  (`countable_chain_condition`, `countable_chain_condition_of_nonempty`,
  `countable_chain_condition_of_countable`).
- The `SetTheory` file now also continues through the next CCC corollaries from upstream:
  `countable_chain_condition_of_topological_basis` and
  `countable_chain_condition_of_separable_space`.
- `Flypitch/SetTheory.lean` now also starts the upstream `pi` section with the product-topology
  subbasic opens: `standard_open`, `pi_subbasis`, and the immediate membership/open-ness lemmas
  needed before porting the larger `pi_basis` and support machinery.
- The `SetTheory` `pi` section now also has the first finite-intersection scaffold:
  `pi_basis` and `nonempty_of_mem_pi_basis`.
- The `SetTheory` `pi` section now also has the easy forward cylinder-membership lemma
  `mem_pi_basis_of_pi`, which is the first half of the larger `pi_basis_eq` normal-form proof.
- The `SetTheory` `pi` section now also shows that these nonempty finite cylinders really form a
  product-topology basis: `isOpen_of_mem_pi_basis` and `isTopologicalBasis_pi_basis` are now in
  place, so later support/countability arguments can use `pi_basis` directly instead of reasoning
  from `isOpen_pi_iff` each time.
- The `SetTheory` `pi` section now also has the finite-subbasis normalization that had still been
  missing from the earlier tranche: `sInter_eq_pi_of_finite_subbasis` rewrites any finite
  intersection of subbasic cylinders into a single finite `Set.pi` cylinder, and `mem_pi_basis_iff`
  packages this as the expected normal form for basis elements.
- That normalization thread is now fully closed: `pi_basis_eq` identifies the product basis itself
  with the expected finite-cylinder normal form modulo removal of `∅`.
- The next upstream support layer is now in place too: `support` records which coordinates can
  affect membership in a cylinder, `support_pi` computes it for finite cylinders, `support_elim`
  gives the corresponding extensionality principle, and the basic finiteness lemmas
  `finite_support_of_pi_subbasis` / `finite_support_of_pi_basis` are now available for the later
  delta-system/CCC-on-products argument.
- The `SetTheory` `pi` section now also begins the downstream support machinery: `pi_set_support`
  records the coordinates where a cylinder differs from `univ`, it is finite whenever the family is
  `univ` off a finite set, and every `pi_basis` member is now shown to admit such a finite-support
  presentation.
- The same `SetTheory` support tranche now also has the first behavioral consequence of finite
  support: membership in a supported cylinder depends only on equality on the supported coordinates
  (`mem_pi_pi_set_support_congr`), and the repo now has a corresponding `pi_basis` membership
  congruence wrapper (`mem_pi_basis_congr`).
- On top of that, `SetTheory` now has a genuine countable-basis candidate built from countable
  per-coordinate families: `pi_basis_from_finset` and `pi_basis_from` package finitely supported
  cylinders whose active fibers come from chosen families, `countable_pi_basis_from*` proves these
  families are countable when the index type and each coordinate family are countable, and
  `mem_pi_basis_of_mem_pi_basis_from*` links nonempty members back to the ambient `pi_basis`.
- That candidate is now also connected back to real topology data: if each coordinate family is a
  topological basis, then `pi_basis_from` is itself a topological basis
  (`isTopologicalBasis_pi_basis_from`), and specializing to Mathlib's `countableBasis` now yields a
  concrete countable product basis together with a local second-countability theorem for countable
  products (`countable_pi_basis_from_countableBasis`,
  `isTopologicalBasis_pi_basis_from_countableBasis`,
  `secondCountableTopology_pi_of_countable`).
- That countable-product topology package now also feeds back into the original forcing-side CCC
  thread: countable products of second-countable spaces now carry the countable chain condition via
  `countable_chain_condition_pi_of_countable`.
- The local product-topology helper block immediately before the uncountable-product CCC theorem is
  now ported too: `extend`, `isOpenMap_apply`, `restrict_image_pi`, and `isOpenMap_restrict` are in
  place together with upstream-style compatibility names `is_open_map_apply`,
  `is_topological_basis_pi`, and `is_open_map_restrict`.
- The next `SetTheory` delta-system helper tranche is now in place and compiling. It bridges the
  Lean 3 relation-style proof to Mathlib 4's typeclass-based cofinality API via
  `unbounded_lt_iff_isCofinal`, `cof_eq_mk_of_isRegular`,
  `exists_unbounded_of_unbounded_iUnion`, and `exists_minimal_unbounded_parameter`. It also adds the
  first bounded-initial-segment cardinality helpers (`mk_Iio_lt_of_ord_eq`, `mk_lt_of_bounded`)
  needed for the upcoming `α₀` construction in `delta_system_lemma_2`.
- The `SetTheory` helper layer now also has the first regular-order-type supremum bounds:
  `isSuccLimit_orderType_of_isRegular`, `iSup_lt_orderType_of_isRegular`, and
  `iSup_succ_lt_orderType_of_isRegular`. These give the Mathlib 4-native replacement for the
  Lean 3 `ord_is_limit` / `sup_lt_ord_of_is_regular` pieces used in the `α₀` construction.
- The outer half of the `α₀` construction is now isolated in compiling helpers:
  `mk_Iio_lt_of_lt_card`, `mk_subtype_lt_of_lt_card`, and
  `iSup_Iio_lt_orderType_of_isRegular`. The remaining hard piece for `delta_system_lemma_2` is the
  inner supremum bound for each fixed parameter below the minimal unbounded one.
- The inner half of the `α₀` construction is now also isolated in compiling helpers:
  `iSup_succ_typein_range_lt_of_bounded` turns boundedness of a realized range into a bound on the
  supremum of successor type-indices, and `inner_iSup_lt_of_minimal_unbounded_parameter` packages
  this for parameters below the minimal unbounded parameter.
- The two halves are now combined by `alpha0_lt_orderType_of_minimal_unbounded_parameter`, which
  proves the exact double-supremum bound needed for the `α₀` used in `delta_system_lemma_2`.
- The opening of `delta_system_lemma_2` is now packaged through
  `exists_minimal_parameter_with_alpha0_bound`: from the unbounded union hypotheses it selects the
  minimal unbounded parameter and produces the associated `α₀ < orderType θ` bound in one compiled
  step.
- The next proof setup for `delta_system_lemma_2` is in place: `mk_typein_initial_segment_lt` proves
  the smallness of the `sub_α₀` initial segment, and `exists_range_gt_of_unbounded` packages the
  strict domination step needed to define the recursive picking function from the unbounded range of
  the minimal parameter.
- The recursive-pick selection step is now also isolated: from any ordinal bound below
  `orderType θ`, `choose_index_above_ordinal_of_unbounded` selects an index whose realized value in
  the minimal unbounded range lies strictly above the corresponding `enum` point.
- The recursive `pick` construction from `delta_system_lemma_2` is now packaged in compiling
  helpers: `pickAboveOrdinalRec`, its unfolding equation, the strict type-index increase lemma, the
  strict monotonicity of realized picked values, and cardinality lemmas showing both the realized
  picked values and the picked index range have full cardinality.
- The actual Lean 3-style parameterized `pick` construction is now also isolated in compiling
  helpers: `pickParamAboveOrdinalRec` chooses indices whose distinguished coordinate dominates a
  fixed base bound and all previously picked coordinates across the small parameter type, with
  lemmas `base_lt_pickParamAboveOrdinalRec` and `typein_param_lt_pickParamAboveOrdinalRec` matching
  the inequalities used in the intersection-in-`sub_α₀` part of `delta_system_lemma_2`.
- The first pieces of the intersection-in-`sub_α₀` argument now compile separately:
  `typein_lt_alpha0_of_param_lt` handles the branch where the local parameter is below `ξ₀`, and
  `param_lt_of_mem_and_pick_bound` packages the rel-isomorphism contradiction branch used to force
  that inequality from membership plus the parameterized pick bound.
- These pieces are now combined by `picked_inter_subset_alpha0`, which proves that pairwise
  intersections of the parameterized picked family lie inside the typein-initial segment below the
  constructed `α₀` base. This completes the main intersection-subset step before the final infinite
  pigeonhole argument in `delta_system_lemma_2`.
- The bounded-codomain estimate for that final pigeonhole step is now also isolated:
  `picked_alpha0_inter_mk_le` proves each picked member's intersection with the `α₀` initial segment
  has cardinality at most the parameter type, via the rel-isomorphism inverse into `{η // η < ξ₀}`.
- The final constant-color and assembly steps are now isolated too:
  `exists_large_constant_picked_alpha0_inter` applies infinite pigeonhole to the colors
  `x ↦ A (pick x) ∩ sub_α₀`, and `is_delta_system_of_constant_picked_alpha0_inter` turns the
  constant-color output plus the intersection-subset theorem into an actual delta-system on the
  selected stage set.
- The product-CCC proof now has its central splicing/disjointness argument isolated as
  `disjoint_restrict_image_of_support_inter_subset`: when two product-basis opens have support
  intersection contained in a root `R`, their images under restriction to `R` are disjoint.
- The next product-CCC helper is now isolated too: a Δ-system equation on supports gives a pairwise
  disjoint family of restricted images, both in indexed form and as a `Set.range` family. This is
  the reusable middle step between the Δ-system lemma and the final cardinality contradiction in
  upstream `countable_chain_condition_pi`.
- The cardinality half of that restricted-image step is also compiled: under the same Δ-system
  support hypotheses, the restricted-image range has the lifted cardinality of the index type, and
  therefore remains uncountable after universe lifting. This leaves the final product-CCC proof with
  an explicit open/pairwise-disjoint uncountable family in the finite root subproduct.
- The openness half of the same restricted-image family is now compiled as well: every member of the
  restricted-image range is open in the root subproduct, by `isOpenMap_restrict` applied to the
  corresponding `pi_basis` open.
- The restricted-image family is now packaged in the form needed by the final contradiction too:
  every member is nonempty/open, the range itself is uncountable whenever the original Δ-system is
  uncountable, and a dedicated contradiction wrapper applies CCC on the finite root subproduct to
  close the impossible countability conclusion.
- The finite-root side of the same product-CCC argument is now compiled: selected product-basis
  supports are finite, Δ-system roots of those supports are finite, finite root subproducts inherit
  CCC from second-countability, and the resulting countability theorem is packaged both as a
  root-CCC wrapper and as the final contradiction against an uncountable Δ-system.
- A final layer of uncountability-derived wrappers now removes the separate two-point-index
  hypothesis from the product-CCC contradiction chain, so downstream callers can use the single
  assumption `ℵ₀ < Cardinal.mk ι` to obtain the finite-root CCC contradiction.
- The same contradiction chain now has packaged wrappers that accept
  `delta_system.is_delta_system (fun i => support β (A i))` directly, avoiding repeated manual
  root extraction in downstream uses of `delta_system_lemma_1`.
- The next indexed-family bridge is compiled too: any pairwise-disjoint indexed family of
  product-basis opens whose supports form a Δ-system is countably indexed. This is the usable
  contradiction shape for applying the support Δ-system machinery before the final
  `countable_chain_condition_pi` wrapper.
- The same indexed-family contradiction is now generalized to the exact finite-root hypothesis used
  by upstream `countable_chain_condition_pi`: instead of requiring every coordinate to be
  second-countable, it accepts `∀ R : Set α, R.Finite → countable_chain_condition (∀ x : R, β x)`.
- The final topological-basis reduction is compiled as
  `countable_chain_condition_pi_of_delta_system_lemma_uncountable`; the remaining input is the
  arbitrary finite-family public Δ-system wrapper.
- The first thinning helpers for that public wrapper now compile: an uncountable family colored by a
  countable type has an uncountable fiber, and an uncountable finite-set family can be thinned to an
  uncountable subfamily whose members have one fixed finite cardinality.
- The public uncountable Δ-system wrapper and final product-CCC theorem now compile:
  `delta_system_lemma_uncountable` thins an uncountable finite-set family through a fixed finite
  cardinality and an `ℵ₁`-sized subtype before applying the compiled `delta_system_lemma_1` stack;
  `countable_chain_condition_pi` instantiates the previously isolated product-CCC wiring theorem.

Longer-horizon route to upstream `countable_chain_condition_pi`:

1. use the newly exposed `countable_chain_condition_pi` as the upstream product-CCC input for the
   next topology/forcing files;
2. continue with the remaining forcing-side route beyond `set_theory.lean`.

So the real near-term blockers are now concentrated on the forcing side:

1. continue the downstream `aleph_one.lean` `bSet` well-ordering section once the supporting
   `bSet` infrastructure exists in Lean 4;
2. continue `set_theory.lean` through the missing delta-system lemma chain and the resulting
   uncountable-product CCC theorem `countable_chain_condition_pi`.

The next Lean 4 tranche should therefore come from:

- `aleph_one.lean`
- `set_theory.lean`

Additional check against the original Lean 3 `src/aleph_one.lean`:

- The current Lean 4 `Flypitch/AlephOne.lean` only covers the opening `pSet` section.
- The entire downstream `bSet` well-ordering / `a1` construction from the Lean 3 file remains
  unported, and the present repository does not yet contain the supporting `bSet` infrastructure
  needed to continue that half of the file in-place.
