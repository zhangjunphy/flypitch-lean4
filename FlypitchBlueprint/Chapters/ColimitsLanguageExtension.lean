import Verso
import VersoManual
import VersoBlueprint
import Flypitch.Colimit
import Flypitch.LanguageExtension

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Colimits And Language Extensions" =>

The Henkin construction enlarges the language repeatedly. To control this
process one needs a way to compare formulas written in different languages, to
restrict structures along language maps, and to form the direct limit of an
infinite chain of languages. This chapter describes that infrastructure. It is
implemented in `Flypitch/Colimit.lean` and `Flypitch/LanguageExtension.lean`.

# Directed Systems And Their Colimits

Suppose one has a directed family of objects connected by compatible transition
maps. The relevant colimit is obtained by taking the disjoint union of all
stages and identifying two representatives when they eventually agree at some
later common stage.

:::definition "def:directed-diagram" (lean := "Flypitch.colimit.directed_diagram")
A directed diagram is a family of objects indexed by a directed preorder,
together with compatible transition maps along the preorder.
:::

:::definition "def:diagram-colimit" (lean := "Flypitch.colimit.colimit")
The colimit of a directed diagram is the quotient of the disjoint union of the
stages by eventual equality.

This construction is built from {uses "def:directed-diagram"}[].
:::

This is the right construction for the infinite Henkin language: a symbol or
formula appearing at some finite stage should be regarded as the same object as
its image in every later stage.

:::theorem "prop:colimit-universal" (lean := "Flypitch.colimit.canonical_map, Flypitch.colimit.universal_map")
Each stage maps canonically into the colimit, and the colimit satisfies the
expected universal property with respect to compatible families of maps out of
the diagram.

This is the universal property attached to {uses "def:diagram-colimit"}[].
:::

When the transition maps are injective, the canonical maps into the colimit are
injective as well. This allows the finite stages to be viewed as genuine
substructures of the limit object.

# Maps Of Languages

:::definition "def:language-hom" (lean := "Flypitch.fol.Lhom")
A homomorphism of first-order languages $`L \to L'` is an arity-preserving map
on function symbols together with an arity-preserving map on relation symbols.

This extends the language notion from {uses "def:fol-language"}[].
:::

Such a map sends every term and formula over $`L` to a corresponding term or
formula over $`L'`. In effect, one may reinterpret a proof written in the
smaller language inside the larger one.

# Symbol Support And Filtered Languages

Later witness arguments require careful control over which constants actually
occur in a term or formula. For that reason the development records the set of
symbols appearing in a given syntactic object and studies how this set behaves
under lifting, substitution, and transport along language maps.

:::definition "def:filtered-language" (lean := "Flypitch.fol.Lhom.filter_symbols, Flypitch.fol.Lhom.filter_symbols_Lhom")
Given a predicate on the symbols of a language $`L`, the filtered language
keeps exactly the symbols satisfying that predicate.

This construction is expressed using {uses "def:language-hom"}[].
:::

The key point is reconstruction: if every symbol appearing in a term or formula
satisfies the predicate, then that term or formula already comes from the
filtered language. This is the mechanism later used to remove a forbidden
constant from the ambient language.

# Proof Transport And Reducts

Language maps act on both syntax and semantics.

:::theorem "prop:on-prf" (lean := "Flypitch.fol.Lhom.on_prf")
A derivation in a language $`L` can be transported along a language map
$`L \to L'` to a derivation in the larger language $`L'`.

This transport uses {uses "def:language-hom"}[] together with
{uses "def:fol-derivability"}[].
:::

In the opposite direction, an $`L'`-structure can be restricted to an
$`L`-structure by forgetting the interpretations of symbols not coming from
$`L`.

:::definition "def:language-reduct" (lean := "Flypitch.fol.Lhom.reduct")
Given a language map $`\varphi : L \to L'` and an $`L'`-structure $`M`, the
reduct of $`M` along $`\varphi` is the $`L`-structure obtained by restricting
the interpretation to the image of $`L`.

This definition combines {uses "def:language-hom"}[] and
{uses "def:fol-structure"}[].
:::

This restriction behaves exactly as expected: a transported formula is true in
$`M` if and only if the original formula is true in the reduct.

# Reflection Along Injective Language Maps

Transporting syntax forward is easy. Going backward is subtler, because symbols
in the larger language need not come from the smaller one. The formalized
solution is a controlled reflection procedure.

:::definition "def:language-reflection" (lean := "Flypitch.fol.Lhom.reflect_formula, Flypitch.fol.Lhom.reflect_term")
For an injective language map with decidable image, reflection attempts to pull
terms and formulas in the larger language back to the smaller language. Symbols
outside the image are replaced by variables.

This definition uses {uses "def:language-hom"}[] and
{uses "def:filtered-language"}[].
:::

The mathematical point is that genuinely new constants are not ignored; they
are turned into open slots. This makes it possible to convert a proof involving
a fresh constant into a proof of a universally quantified statement.

At the proof-theoretic level, reflection shows that injective language
extensions preserve consistency of the theories induced from the smaller
language.

# Fresh Constants And Generalization

:::definition "def:bounded-subst-sentence" (lean := "Flypitch.fol.Lhom.boundedFormulaSubstSentence")
If $`f(x)` is a bounded formula in one free variable and $`t` is a closed term,
then one may form the sentence $`f(t)` by substitution.

This sentence-level substitution uses {uses "def:fol-bounded-syntax"}[].
:::

The main application of reflection is the following familiar principle.

:::theorem "thm:generalize-constant" (lean := "Flypitch.fol.Lhom.sgeneralize_constant, Flypitch.fol.Lhom.generalize_constant")
Suppose a constant symbol $`c` does not occur in the assumptions $`\Gamma` and
does not occur in the formula $`f(x)`. If $`\Gamma` proves the sentence
$`f(c)`, then $`\Gamma` proves $`\forall x\, f(x)`.

This theorem combines {uses "def:filtered-language"}[],
{uses "def:language-reflection"}[], {uses "def:bounded-subst-sentence"}[], and
{uses "prop:on-prf"}[].
:::

:::proof "thm:generalize-constant"
One removes the forbidden constant from the language by passing to a filtered
language in which $`c` is absent. Since neither the assumptions nor the formula
mention $`c`, they can be reconstructed inside that smaller language.
Reflection then turns the proof of $`f(c)` into a proof of the same formula
with the constant replaced by a variable, which is exactly what is needed for
universal generalization.
:::

This theorem is the technical heart of the later witness argument. It explains
why a proof using a genuinely fresh constant may be converted into a proof of a
universal statement with no reference to that constant.

# Role In Henkinization

This chapter serves three purposes at once.

- directed colimits provide the eventual infinite language
- language maps and reducts let syntax, proofs, and models move between
  different stages of that language
- reflection and fresh-constant generalization supply the key argument that
  one-step witness adjunction preserves consistency

# Formalization Note

The supporting Lean declarations include `colimit`, `canonical_map`, `Lhom`,
`on_prf`, `reduct`, `reflect_formula`, and `generalize_constant`. They are
best read as implementations of the mathematical constructions above, not as
substitutes for them.
