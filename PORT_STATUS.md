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

Completed work is grouped by phase. The fine-grained theorem/API names live in the Lean files and
the verified-surface summary below.

- [x] Project setup and dependency-ordered upstream port plan.
- [x] Logic/completeness branch through compat, FOL syntax/proofs/semantics/theories,
  compactness, completion, colimits, language extension, Henkinization, and public completeness.
- [x] Forcing groundwork through `Flypitch/BVTauto.lean`, `Flypitch/PSetOrdinal.lean`, and the
  pure-`pSet` part of `Flypitch/AlephOne.lean`.
- [x] Set-theory/product-topology branch through delta-system machinery, product bases/supports,
  countability/CCC helpers, the uncountable delta-system wrapper, and `countable_chain_condition_pi`.
- [x] Topology/collapse stack through regular opens, Cantor-space and collapse-space bases, dense
  omega-closed principal opens, and the CH collapse Boolean algebra endpoint.
- [x] Boolean-valued model core through `bSet`, check names, extensionality/substitution,
  bounded quantifiers, epsilon induction, comprehension, infinity, union, and powerset.
- [x] `BVMExtras` started through singleton/intersection, union/successor, pair/product,
  checked-name bridges, first Boolean-valued ordinal predicates, and the first
  `bvm_extras2` product/ordinal-intersection, relative-complement, regularity, and ordinal
  comparison helpers through trichotomy, ordinal equality/ordering resolution, and sub-ordinal
  trichotomy/well-foundedness wrappers, the first limit/successor predicates, and finite
  ordinal-name facts needed by `exists_two`, including the forward and reverse
  `exists_two`/not-one bridges, plus the opening function/injection/surjection and
  epsilon-isomorphism predicate layer, and the checked-function preservation bridge.
- [x] Continue the `bvm_extras`/`bvm_extras2` Boolean-valued model compatibility layer (BVMExtras.lean now complete with zero sorries, including `CH_iff_CH₂`).
- [x] Continue the downstream `aleph_one.lean` `bSet` well-ordering and `a1` construction
  (the Boolean-valued relation/product-map definition layer has started in `Flypitch/AlephOne.lean`,
  including `is_rel`, `is_wo`, `mem_rel`, `mem_mem_rel_iff`, `prod.map`,
  `prod.map_self`, `induced_epsilon_rel`, the first `a1` predicate/candidate definitions,
  `a1.B_ext_ϕ`, `a1.mem_candidates_iff`, congruence support for `mem_rel`, bounded `image`,
  and `prod.map_self`, plus `a1.B_ext_ψ`, candidate witness extraction, the auxiliary choice
  function, the public `a1` name with ordinal membership projection, the public membership normal
  form for `a1`, the zero/empty equality bridge, the induced-epsilon equality-to-ordinal-equality
  bridge, `a1_Ord`, `a1_spec`, `a1_le_of_omega_lt`, and the checked `aleph_one` subset bridge).
- [x] Port the current `forcing.lean` Cohen/`¬CH` side through the cardinal-preservation bridge
  used by `AE_of_check_larger_than_check`; `Flypitch/Forcing.lean` now compiles with zero
  placeholders and is imported by `Flypitch.lean`.
- [x] Port `forcing_CH.lean` through the collapse/`CH` endpoint: collapse relation
  extensionality/functionality/totality/surjectivity, dense-basis reflection for checked
  `omega -> 2` functions, `check_functions_eq_functions`, `continuum_le_continuum_check`,
  `CH₂_true`, and `CH_true`.
- [x] Reconnect the logic and forcing branches through `bfol`, `zfc`, and `summary`
  (`print_formula` was not needed for the theorem path).
- [x] Re-establish `independence_of_CH`.

## Verification Policy

Every completed milestone must satisfy both checks:

1. `lake build`
2. A concrete imported module corresponding to the milestone compiles cleanly without `axiom` placeholders.

## Current Verified Surface

Grouped module status is the source of truth here; fine-grained theorem names stay in the Lean
files themselves.

- Logic/completeness branch: complete through `Flypitch/Henkin.lean`, including the public
  completeness wrappers.
- Set-theory groundwork: `Flypitch/PSetOrdinal.lean`, `Flypitch/SetTheory.lean`, and
  `Flypitch/AlephOne.lean` cover the current `pSet`, ordinal, product-CCC, and opening aleph-one
  surface.
- Topology/collapse branch: `Flypitch/RegularOpenAlgebra.lean`, `Flypitch/CantorSpace.lean`, and
  `Flypitch/Collapse.lean` compile through the collapse Boolean algebra endpoint and dense
  omega-closed principal-open package.
- Boolean-valued models: `Flypitch/BVTauto.lean` and `Flypitch/BVM.lean` compile through the core
  `bSet` API, check-name truth facts, extensionality, substitution, bounded quantifiers,
  comprehension, infinity, union, and powerset. `Flypitch/BVMExtras.lean` has started the
  `bvm_extras`/`bvm_extras2` compatibility layer through singleton/pair/product helpers,
  checked-name bridges, first Boolean-valued ordinal predicates, and product/ordinal-intersection
  relative-complement, regularity, self/two/three-cycle membership contradiction, and ordinal
  comparison helpers through `Ord.trichotomy`, `Ord.eq_iff_not_mem`, `Ord.le_iff_lt_or_eq`,
  `Ord.lt_of_not_le`, `Ord.resolve_lt`, `Ord_of_mem_Ord`, and the first sub-ordinal
  trichotomy/well-foundedness wrappers. It also now includes `is_limit`, `Ord_succ`, and
  `Ord.succ_le_of_lt`.
  The finite ordinal-name surface now covers `Ord_empty`, `Ord_zero`, `Ord_one`, `Ord_ofNat`,
  `zero_mem_one`, `eq_zero_of_mem_one`, `exists_two`, `B_ext_exists_two`, and
  `one_mem_of_not_zero_and_not_one`, plus both directions and the iff form of the
  `exists_two`/not-one bridge.
  The next `eps_iso` prerequisites now include Boolean-valued function, totality, functionality,
  injection, surjection, `larger_than`, `injects_into`, `injection_into`, `strong_eps_hom`,
  `eps_iso`, and their basic projection lemmas. The bounded function-image layer has also started:
  `image`, `preimage`, membership/subset lemmas, domain/codomain extraction from `is_function`,
  and the factor-through-image wrappers for functions and injective functions now compile. The
  inverse-function block now includes `inj_inverse`, its membership introduction/elimination API,
  function/total/surjective/injective structure lemmas, and the packaged
  `injective_function_inverse` wrappers. The next relation-level names are also open:
  `is_surj_onto`, `surjects_onto`, `larger_than_of_surjects_onto`,
  `injects_into_of_injection_into`, and the bounded composition graph shell `is_func'_comp`.
  The composition membership API (`mem_is_func'_comp_components`, `mem_is_func'_comp`,
  `mem_is_func'_comp_iff`), function/total/function-prime structure lemmas, and the packaged
  `function_comp` / `function_comp_is_function` wrappers now compile. Injective composition is now
  available too via `eq_of_is_inj_of_eq`, `is_func'_comp_inj`, `injective_function_comp`,
  `injective_function_comp_is_injective_function`, `injective_function_comp_is_function`, and
  `injects_into_trans`. Surjective composition is packaged as `is_func'_comp_surj`. The bounded
  function-family name `functions` now exists, with `functions_subset_powerset`,
  `mem_functions_iff`, `is_function_of_mem_functions`, and `mem_functions`. The relation
  restriction wrapper `function_of_func'` is also available with subset, membership, function,
  surjection, and injection preservation lemmas, and `injects_into` is now equivalent to the
  packaged `injection_into` presentation. The image/surjection layer now also includes
  `surj_image`, `image_eq_codomain_of_surj`, `exists_surjection_of_surjects_onto`, and
  `larger_than_domain_subset`. The checked-name bridge has picked up contextual reflection helpers,
  checked indexed membership, `check_is_total`, `check_subset_prod_of_is_func`, `check_is_func`,
  `check_is_injective_function`, `check_powerset_subset_powerset`,
  `check_functions_subset_functions`, and Boolean-valued finite natural helpers `ofNat_inj` /
  `ofNat_mem_of_lt`. The Boolean-valued `function.mk'` constructor layer now includes the graph
  constructor, simp facts, product-subset bound, totality, functionality, function packaging, and
  injectivity structure lemma. The powerset-to-characteristic-functions path has started with the
  `powerset_injects.F` index map into `functions x 2`; the zero fiber now has the expected
  membership iff, equality of generated characteristic graphs reflects back to equality of the
  source Boolean-valued subsets, and the generated characteristic graph is now packaged as an
  internal injective function from `bv_powerset x` into `functions x 2` via
  `powerset_injects_into_functions`. The epsilon-isomorphism layer now includes `eps_iso_mono`,
  `eq_of_Ord_eps_iso_aux`, `larger_than_of_larger_than_and_injects`,
  `not_larger_of_not_larger_and_injects`, `larger_than_empty`, `injects_into_refl`,
  `bv_subset_refl`, and the equivalence `CH_iff_CH₂` of the two Continuum Hypothesis
  formulations. The core/mixing layer needed for Zorn now also includes the upstream-style
  `subset'_inductive`, `core_aux_lemma2`, top-valued `bSet_zorns_lemma`, and contextual
  `bSet_zorns_lemma'`. BVMExtras.lean is now complete with zero `sorry` blocks.
- Integration branch: `Flypitch/BFOL.lean` is now connected to `Flypitch.lean` with the
  Boolean-valued structure, term/formula evaluators, sentence forcing, and theory forcing
  interface needed by the ZFC bridge. It now also has evaluator simp lemmas for the derived
  bounded connectives `bd_falsum`, `bd_not`, `bd_and`, `bd_or`, `bd_biimp`, and `bd_ex`,
  plus the bounded open-substitution realization theorem
  `boolean_realize_bounded_formula_subst_open`, formula-level Boolean soundness, sentence-level
  forcing soundness, and the `unprovable_of_model_neg` bridge from Boolean-valued countermodels
  to syntactic unprovability.
  `Flypitch/ZFC.lean` is also connected with the `L_ZFC`
  language, the Boolean-valued universe `V`, the set-forming function/relation interpretations,
  and the first evaluator simp lemmas for membership, equality, emptyset, omega, pair, powerset,
  and union. The finite ZFC axiom sentence surface is now ported through emptyset, ordered pairs,
  extensionality, union, powerset, infinity, regularity, and Zorn, and the current finite
  `ZFC.ZFC` theory plus `CH_f` syntax compile. The CH semantic endpoints
  `CH_f_is_CH`, `CH_f_sound`, and `neg_CH_f_sound` are now available. Boolean-valued model lemmas
  are now connected for emptyset, ordered pairs, extensionality, union, powerset, infinity,
  regularity, and
  the collection schema. The collection bridge uses the lower Boolean-valued witness construction
  in `BVMExtras` (`collection_witness`, `collection_image`, and `bSet_axiom_of_collection`), the
  `bdAllsFrom` realization helper in `ZFC`, bounded lift-at realization lemmas for the
  `φ.liftAt k 2` occurrences, and a coercion-shaped substitution simplifier for the final
  collection witness formula. The contextual Zorn bridge is now connected through
  `bSet_models_zorn`, and the full Boolean-valued model theorem `bSet_models_ZFC` compiles. The
  collapse-side unprovability theorem `neg_CH_f_unprovable` is now connected via
  `ForcingCH.CH₂_true` and the Boolean-valued double-negation helper
  `forced_not_not_of_forced`. The Cohen `¬CH₂` endpoint is connected as `Forcing.not_CH₂`,
  yielding `CH_f_unprovable`. `Flypitch/Summary.lean` now exposes `independent`,
  `CH_unprovable`, `neg_CH_unprovable`, and `independence_of_CH`.
- Forcing branch: `Flypitch/Forcing.lean` is connected to `Flypitch.lean` and compiles without
  placeholders through the Cohen forcing cardinal-preservation argument, including the extension
  from a subset-surjection witness in `larger_than x y` plus nonemptiness of `y` to an internal
  surjection from `x` onto `y`.
- Aleph-one branch: `Flypitch/AlephOne.lean` now imports the Boolean-valued model extras and has
  begun the downstream `bSet` well-ordering layer with relation/product-map definitions and the
  membership characterization and congruence theorem for `mem_rel`; bounded image congruence is
  available on both the source and graph arguments. The product-map layer now includes a general
  product witness extractor, the `prod.map_self` membership characterization, congruence in the
  first argument, the induced-epsilon membership characterization, injective reflection back to
  source membership, image-projection lemmas, the first induced-epsilon pair decomposition
  lemma, and the induced-relation nonemptiness chain through
  `nonempty_induced_rel_iff_not_zero_and_not_one`. The induced-epsilon comparison bridge now
  includes codomain extensionality/transport support for Boolean-valued functions, injective
  functions, and surjections, plus the image equality lemmas
  `image_eq_of_eq_induced_epsilon_rel_aux` and
  `image_eq_of_eq_induced_epsilon_rel`. The composition map used by the next ordinal-equality
  bridge is now packaged as `induced_epsilon_comp`, with verified `is_function` and `is_surj`
  structure lemmas. The first `a1`
  predicate
  layer (`a1.ϕ`, `a1.B_ext_ϕ`, `a1.candidates`,
  `a1.mem_candidates_iff`, `a1.ψ`, `a1.B_ext_ψ`, `a1.candidates_AE`, `a1.func`,
  `a1.func_spec`, `a1.aux`, `a1.Ord_of_mem_aux`, public `a1`, and `Ord_of_mem_a1`) also compiles.
  The public `mem_a1_iff₀` normal form and `eq_zero_iff_eq_empty` bridge are also available. The
  induced-epsilon composition bridge is now complete through `induced_epsilon_comp_strong_eps_hom`,
  `induced_epsilon_comp_eps_iso`, and `eq_of_eq_induced_epsilon_rel`. The Boolean-valued aleph-one
  API now includes `mem_a1_of_injects_into_omega_aux`, `mem_a1_iff`, `a1_transitive`, `a1_ewo`,
  `a1_Ord`, `a1_spec`, `a1_le_of_omega_lt`, and `aleph_one_check_sub_aleph_one_aux`.
- `forcing_CH` branch: `Flypitch/ForcingCH.lean` is now connected to `Flypitch.lean` and has the
  upstream opening layer: the `bSet.aleph_one` wrapper, the checked `aleph_one` equality/leastness
  bridges under `omega < aleph_one`, the generic checked bounded-forall helper, relation
  construction from Boolean arrays, left/right projection lemmas, functionality/totality/surjectivity
  for suitably tall/wide/extensional arrays, and the public collapse Boolean-algebra alias. The
  collapse-specific layer has also started with the cardinal helper proving every collapse condition
  leaves an `aleph_one` coordinate outside its domain, the singleton regular-open array `π_af`, the
  relation `π`, dense-open proofs `π_af_wide` and `π_af_tall`, and the packaged `π_is_total` /
  `π_is_surj` facts. It now also includes ordinal-index injectivity for the checked `aleph_one`,
  the `π_af` disjointness/extensionality bridge, the packaged `π_is_func'` fact, the generic
  `larger_than_of_larger_than_and_domain_injects` domain-lift lemma, the packaged
  `aleph_one_larger_than_powerset_omega_check`, its lift to Boolean-valued `aleph_one`,
  `aleph_one_injects_into_of_omega_not_larger`, the derived checked-continuum comparison
  `powerset_omega_larger_than_of_omega_not_larger`, the context-level transfer
  `bv_powerset_omega_larger_than_of_omega_not_larger`, the conditional continuum-injection
  reduction `continuum_le_continuum_check_of_check_functions_eq`, the conditional CH₂ endpoints
  `CH₂_true_of_continuum_le_continuum_check` and `CH₂_true_of_check_functions_eq`, and the first
  dense-principal-open witness helper `AE_of_check_func_check'` for checked functions. The
  omega-closed reflection bridge for checked `omega -> 2` functions is now closed via
  `function_reflect_of_omega_closed_two`, `functions_subset_check_functions`,
  `check_functions_eq_functions`, `continuum_le_continuum_check`, `CH₂_true`, and `CH_true`, so
  this milestone is complete with zero placeholders.

## Current Frontier

`lake build` succeeds for the current port surface. The final theorem path is connected through:

1. `Forcing.not_CH₂` for the Cohen `¬CH₂` endpoint.
2. `ForcingCH.CH₂_true` for the collapse `CH₂` endpoint.
3. `ZFC.CH_f_unprovable` and `ZFC.neg_CH_f_unprovable`.
4. `Summary.independence_of_CH`.

## Remaining Target

The repository proves `Flypitch.independence_of_CH`; `Flypitch/Summary.lean` represents the
upstream summary endpoint without the executable pretty-printing layer, which is not needed for
the theorem.
