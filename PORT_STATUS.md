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
- [ ] Continue the `bvm_extras`/`bvm_extras2` Boolean-valued model compatibility layer.
- [ ] Continue the downstream `aleph_one.lean` `bSet` well-ordering and `a1` construction.
- [ ] Port `forcing.lean` and `forcing_CH.lean`.
- [ ] Reconnect the logic and forcing branches through `bfol`, `zfc`, `print_formula`, and `summary`.
- [ ] Re-establish `independence_of_CH`.

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
  `powerset_injects_into_functions`.
- Integration branch: `bfol`, `zfc`, `print_formula`, `summary`, and `independence_of_CH` remain unported/unreconnected.

## Current Frontier

`lake build` succeeds for the current port surface. The remaining work is concentrated on the
forcing side, not the completed logic/completeness branch.

Next useful tranches:

1. Continue `bvm_extras.lean`/`bvm_extras2.lean` beyond the current pair, product, checked-name,
   ordinal-predicate, ordinal-intersection, relative-complement, regularity, ordinal comparison,
   ordinal-of-member, sub-ordinal predicate helpers, opening successor/limit ordinal helpers, and
   finite ordinal-name support for `exists_two`; continue from the downstream `eps_iso` /
   cardinal-comparison section now that the powerset-to-functions injection endpoint compiles.
2. Continue the downstream `aleph_one.lean` `bSet` well-ordering and `a1` construction once enough
   supporting `bSet` API is available.
3. Port `forcing.lean` and `forcing_CH.lean` after the Boolean-valued model layer exposes the
   needed internal set-theoretic predicates and CH-specific constructions.
4. Reconnect the logic and forcing branches through `bfol`, `zfc`, `print_formula`, and finally
   `summary`.

## Remaining Target

The repository still does not prove `independence_of_CH`. The final goal remains open until
`src/summary.lean` is represented and the theorem is recovered in Lean 4.
