import Verso
import VersoManual
import VersoBlueprint
import Flypitch.Henkin

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Henkinization" =>

We now reach the central construction on the logic side. Starting from a
consistent theory, one adjoins enough witness constants to ensure that every
existential statement has a named witness in an enlarged language. The output
is a consistent Henkin theory, and after applying completion one obtains a
complete Henkin extension. This chapter documents the part of that argument
implemented in `Flypitch/Henkin.lean`.

# Adjoining Witness Constants In One Step

Given a language $`L`, the first move is to enlarge it by adding one new
constant for each bounded formula in one free variable.

:::definition "def:henkin-one-step-language" (lean := "Flypitch.henkin.languageStep")
The one-step Henkin extension of $`L` is the language obtained by adjoining, for
every bounded formula $`f(x)`, a new constant intended to witness $`f`.

This language extension is indexed by {uses "def:fol-bounded-syntax"}[].
:::

This is the formal version of the usual idea from the completeness proof: if
one wants existential statements to have canonical witnesses, one expands the
language so that such witnesses can be named.

# Iterating The Construction

One application of the previous step is not enough, because after adjoining new
constants, one obtains new formulas that may themselves require witnesses. The
construction is therefore iterated along the natural numbers.

:::definition "def:henkin-language-chain" (lean := "Flypitch.henkin.languageChain")
The Henkin language chain starts from the original language at stage $`0` and
applies the one-step witness extension at each successor stage.

This chain uses {uses "def:henkin-one-step-language"}[] and
{uses "def:language-hom"}[].
:::

The transition maps between stages are injective, so each finite stage embeds
faithfully into every later one.

# The Infinite Henkin Language

:::definition "def:linfty-language" (lean := "Flypitch.henkin.LInfty")
The infinite Henkin language $`L_\infty` is the directed colimit of the finite
Henkin language chain.

This combines {uses "def:henkin-language-chain"}[] with
{uses "def:diagram-colimit"}[].
:::

Mathematically, $`L_\infty` is the language obtained by adjoining all witness
constants produced at all finite stages and identifying symbols that are the
same after passing sufficiently far along the chain.

# Finite-Stage Representatives

The crucial structural fact about $`L_\infty` is that terms and formulas over
the limit language still come from finite stages.

:::theorem "thm:henkin-comparison-bijective" (lean := "Flypitch.henkin.equivBoundedFormulaComparison")
Every term, formula, bounded term, and bounded formula over $`L_\infty` is
represented by a unique compatible germ of corresponding syntax at a finite
stage of the Henkin chain.

This theorem uses {uses "def:linfty-language"}[],
{uses "prop:colimit-universal"}[], and {uses "def:fol-bounded-syntax"}[].
:::

:::proof "thm:henkin-comparison-bijective"
Injectivity comes from the injectivity of the canonical maps into the colimit.
Surjectivity is proved by structural recursion: each finite syntactic piece of
an $`L_\infty`-expression already uses only finitely many symbols, so all of
them appear together at some sufficiently high finite stage.
:::

This theorem is what allows witness arguments in the limit language to be
reduced to witness arguments at finite stages.

# Witness Sentences And Enough Constants

:::definition "def:henkin-witness-property" (lean := "Flypitch.henkin.witProperty")
For a formula $`f(x)` and a constant $`c`, the witness property is the sentence

$$`\exists x\, f(x) \to f(c)`

This witness sentence is phrased using {uses "def:fol-bounded-syntax"}[].
:::

A theory has enough constants if every bounded one-variable formula has some
constant satisfying this witness property.

# The One-Step Theory Extension

:::definition "def:henkin-theory-step" (lean := "Flypitch.henkin.henkinTheoryStep")
Given a theory $`T` over $`L`, the one-step Henkin extension is obtained by
transporting $`T` into the one-step Henkin language and adjoining all witness
sentences for bounded one-variable formulas over $`L`.

This is the theory-level companion to {uses "def:henkin-one-step-language"}[]
and {uses "def:henkin-witness-property"}[].
:::

This is the natural theory-level companion to the language extension: each new
constant is accompanied by the axiom asserting that it behaves as a witness.

# Consistency Of One Henkin Step

:::theorem "thm:henkin-step-consistent" (lean := "Flypitch.henkin.is_consistent_henkinTheoryStep")
If $`T` is consistent, then its one-step Henkin extension is also consistent.

This theorem combines {uses "def:henkin-theory-step"}[],
{uses "thm:generalize-constant"}[], and
{uses "thm:theory-proof-compactness"}[].
:::

:::proof "thm:henkin-step-consistent"
The key point is that each newly adjoined witness constant is fresh. If a
finite collection of witness axioms produced a contradiction, one could add
them one at a time. At each stage, the fresh-constant generalization theorem
converts any illicit proof using the new constant into a proof that no longer
depends on it. Compactness reduces the argument to finitely many such steps.
:::

This is the decisive consistency-preservation result in the entire Henkin
construction.

# Passing To The Limit Theory

The one-step theorem is then iterated along the chain of finite Henkin stages,
and each finite-stage theory is transported into the limit language
$`L_\infty`. Their union is the limit theory usually denoted $`T_\infty`.

:::definition "def:tinfty-theories" (lean := "Flypitch.henkin.TInfty")
The theory $`T_\infty` is the union, inside $`L_\infty`, of the images of all
finite Henkin stages of the original theory.

This definition uses {uses "def:linfty-language"}[] and
{uses "def:henkin-theory-step"}[].
:::

:::theorem "thm:henkin-tinfty-consistent" (lean := "Flypitch.henkin.is_consistent_TInfty")
If $`T` is consistent, then every finite Henkin stage is consistent, the
corresponding theories inside $`L_\infty` are consistent, and the limit theory
$`T_\infty` is consistent.

This theorem uses {uses "thm:henkin-step-consistent"}[],
{uses "thm:theory-proof-compactness"}[], and
{uses "def:tinfty-theories"}[].
:::

:::proof "thm:henkin-tinfty-consistent"
Finite-stage consistency is an induction using
{uses "thm:henkin-step-consistent"}[]. The consistency of the union again comes
from compactness: any finite inconsistent fragment of $`T_\infty` already lies
in a single finite stage.
:::

# Enough Constants In The Limit

The next point is to show that the limit theory really has the Henkin witness
property. Given a bounded one-variable formula over $`L_\infty`, the
comparison theorem above represents it at some finite stage. The corresponding
witness sentence has already been inserted at the next stage, and therefore
appears in the limit theory after transport to $`L_\infty`.

:::theorem "prop:henkinization-has-enough-constants" (lean := "Flypitch.henkin.henkinizationIsHenkin")
The consistent limit theory obtained from the Henkin chain has enough
constants.

This proposition uses {uses "thm:henkin-comparison-bijective"}[] and
{uses "def:henkin-witness-property"}[].
:::

# Complete Henkin Extensions

:::definition "def:henkin-language-over" (lean := "Flypitch.henkin.henkinLanguage, Flypitch.henkin.henkinLanguageOver")
The Henkin language of a theory $`T` is the limit language constructed from the
language underlying $`T`.

This is the theory-relative form of {uses "def:linfty-language"}[].
:::

:::theorem "thm:complete-henkinization" (lean := "Flypitch.henkin.completeHenkinizationOfConsis")
Every consistent theory admits a complete Henkin extension in its Henkin
language.

This theorem combines {uses "thm:henkin-tinfty-consistent"}[],
{uses "cor:completion-of-consistent-theory"}[],
{uses "prop:henkinization-has-enough-constants"}[], and
{uses "def:henkin-language-over"}[].
:::

:::proof "thm:complete-henkinization"
The Henkin construction yields a consistent theory with enough constants. One
then applies the completion theorem from the previous chapter. Since the
witness property is monotone under extension, the resulting complete theory
remains Henkin.
:::

# Present Boundary

This chapter is the current endpoint of the formalized logic-side story. The
repository already reaches:

- the iterative witness-extension languages
- the limit language $`L_\infty`
- consistency of the finite and infinite Henkin theories
- the existence of complete Henkin extensions of consistent theories

What lies beyond this is not more basic Henkin machinery. The next missing
pieces are the later completeness-side packaging and then the forcing and
set-theoretic branch of Flypitch.

# Formalization Note

The Lean file packages these constructions via declarations such as
`languageStep`, `LInfty`, `witProperty`, `henkinTheoryStep`, `TInfty`, and
`completeHenkinizationOfConsis`. Their mathematical role is exactly the Henkin
construction described above.
