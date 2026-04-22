import Verso
import VersoManual
import VersoBlueprint
import Flypitch.Compactness
import Flypitch.Completion

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Compactness And Completion" =>

The next step is to understand how consistency behaves under enlarging a
theory. The formalized route is the classical one: first prove that any proof
uses only finitely many assumptions, then use this finitary principle to build
maximal and hence complete consistent extensions. This chapter corresponds to
`Flypitch/Compactness.lean` and `Flypitch/Completion.lean`.

# Compactness As A Finitary Principle

The later Henkin construction repeatedly adds new sentences to a theory. To
show that these enlargements preserve consistency, it is enough to know that an
inconsistency can already be witnessed inside some finite fragment. The
repository proves exactly this statement in proof-theoretic form.

:::theorem "thm:proof-compactness" (lean := "Flypitch.fol.proof_compactness")
If a formula $`\psi` is derivable from a set $`T` of formulas, then there
exists a finite subset $`\Gamma \subseteq T` such that $`\Gamma \vdash \psi`.

This theorem is phrased in terms of {uses "def:fol-derivability"}[].
:::

:::proof "thm:proof-compactness"
The proof is by induction on a derivation of $`\psi`. Each inference rule uses
only finitely many assumptions, and finite supports are combined by taking
finite unions. The only delicate point is universal introduction, where one
must descend from a lifted theory back to a finite family of original
assumptions.
:::

This is the precise finiteness statement needed later: a contradiction cannot
depend essentially on infinitely many hypotheses at once.

# Compactness For Theories

The rest of the development is phrased in terms of theories of sentences rather
than arbitrary sets of formulas, so the same result is repackaged at the
theory level.

:::theorem "thm:theory-proof-compactness" (lean := "Flypitch.fol.theory_proof_compactness")
If a sentence $`\psi` is provable from a theory $`T`, then there is a finite
subtheory $`\Gamma \subseteq T` from which $`\psi` is already provable.

This is the theory-level form of {uses "thm:proof-compactness"}[] and uses
the sentence language provided by {uses "def:fol-bounded-syntax"}[].
:::

This is the form used in later consistency arguments. Whenever a large theory
is inconsistent, the obstruction already appears in a finite collection of its
sentences.

# Controlled Unions

Compactness immediately gives a useful principle for enlarging consistent
theories.

:::theorem "prop:consistent-union" (lean := "Flypitch.fol.is_consistent_union")
Let $`T_1` be a consistent theory. Suppose that every sentence $`\psi` in a
second theory $`T_2` can be added to $`T_1` without forcing inconsistency in
the relevant one-step sense. Then the union $`T_1 \cup T_2` is consistent.

This theorem is driven by {uses "thm:theory-proof-compactness"}[].
:::

:::proof "prop:consistent-union"
Assume the union were inconsistent. Then
{uses "thm:theory-proof-compactness"}[] produces a finite fragment that is
already inconsistent. One then adds the finitely many sentences coming from
$`T_2` one at a time and uses the hypothesis at each step to rule out the
appearance of a contradiction.
:::

This is the first general tool showing that a large extension can be handled by
checking one sentence at a time. It will be reused in the Henkin chapter.

# Chains Of Consistent Extensions

To pass from a consistent theory to a maximal one, one considers the partially
ordered set of all consistent extensions ordered by inclusion. The key point is
that any chain of such extensions has an upper bound, namely its union.

:::theorem "lem:finite-subset-limit-theory"
Let $`c` be a nonempty chain of consistent extensions of a theory $`T`. Every
finite subset of the union of the chain is already contained in a single member
of the chain.
:::

This is immediate from finite induction and total comparability inside the
chain.

:::theorem "prop:consis-limit" (lean := "Flypitch.fol.consis_limit")
The union of a chain of consistent extensions of $`T` is again consistent.

This uses {uses "lem:finite-subset-limit-theory"}[] together with
{uses "thm:theory-proof-compactness"}[].
:::

:::proof "prop:consis-limit"
If the union were inconsistent, compactness would produce a finite inconsistent
subtheory. By {uses "lem:finite-subset-limit-theory"}[], that finite fragment
would already lie in one element of the chain, contradicting the consistency of
that element.
:::

# Maximal Consistent Extensions

Once unions of chains are known to preserve consistency, Zorn's lemma applies.

:::theorem "thm:maximal-extension" (lean := "Flypitch.fol.maximal_extension")
Every consistent theory has a maximal consistent extension.

This theorem depends on {uses "prop:consis-limit"}[].
:::

Maximality then yields the expected dichotomy for sentences.

:::theorem "prop:maximal-is-complete" (lean := "Flypitch.fol.complete_maximal_extension_of_consis")
If $`T_{\max}` is maximal among the consistent extensions of a theory $`T`,
then $`T_{\max}` is complete.

This combines {uses "thm:maximal-extension"}[] and
{uses "prop:consistent-union"}[].
:::

:::proof "prop:maximal-is-complete"
Let $`\psi` be any sentence. If neither $`\psi` nor $`\neg \psi` lies in
$`T_{\max}`, then one of the two one-sentence enlargements remains consistent.
That contradicts maximality.
:::

:::corollary "cor:completion-of-consistent-theory" (lean := "Flypitch.fol.completion_of_consis")
Every consistent theory has a complete consistent extension.

This is the immediate consequence of {uses "thm:maximal-extension"}[] and
{uses "prop:maximal-is-complete"}[].
:::

# Why This Matters Later

The role of this chapter is straightforward.

- compactness turns inconsistency questions into finite calculations
- controlled unions show how to adjoin families of new sentences while
  tracking consistency
- completion turns a merely consistent theory into one that decides every
  sentence

These are exactly the abstract ingredients needed before witness constants can
be adjoined systematically in the Henkin construction.

# Formalization Note

The Lean development packages these ideas through the theorems
`proof_compactness`, `theory_proof_compactness`, `is_consistent_union`,
`consis_limit`, `maximal_extension`, and
`complete_maximal_extension_of_consis`. The mathematical content, however, is
the standard compactness-and-Zorn argument just described.
