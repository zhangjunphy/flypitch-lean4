import Verso
import VersoManual
import VersoBlueprint
import Flypitch.BFOL
import Flypitch.BVM
import Flypitch.BVMExtras
import Flypitch.ZFC

open Verso.Genre
open Verso.Genre.Manual
open Informal

set_option linter.hashCommand false
set_option linter.style.emptyLine false

#doc (Manual) "Boolean-Valued Models" =>

Classical first-order semantics evaluates each sentence as true or false. A
Boolean-valued model refines this by assigning each sentence an element of a
complete Boolean algebra. The top element represents full truth, the bottom
element full falsity, and intermediate elements record conditions under which
the sentence holds.

# Complete Boolean Algebras As Truth Values

For forcing, the Boolean algebra is not decoration. Its elements are
conditions, and the order expresses strengthening. Infima behave like logical
"and", suprema like "or", and complement like negation.

:::definition "def:boolean-valued-structure" (lean := "Flypitch.fol.bStructure")
A Boolean-valued structure interprets relation symbols as Boolean-valued
relations and function symbols as ordinary functions on the underlying type.
:::

:::theorem "thm:boolean-soundness" (lean := "Flypitch.fol.boolean_soundness")
If a theory proves a sentence and a Boolean-valued structure forces the
theory, then it also forces the sentence.

This is the Boolean-valued analogue of {uses "thm:fol-soundness"}[].
:::

# The Universe Of Boolean-Valued Sets

The forcing models in the proof are built from Boolean-valued sets, written
`bSet`. A Boolean-valued set is a tree of possible members, where each member
is attached to a Boolean truth value.

:::definition "def:bset" (lean := "Flypitch.bSet")
For a complete Boolean algebra $`B`, `bSet B` is the type of Boolean-valued
sets over $`B`.
:::

Membership and equality are themselves Boolean-valued:

- `x ∈ᴮ y` is the Boolean value of "x is a member of y".
- `x =ᴮ y` is the Boolean value of extensional equality.

This is the key idea that makes set theory available inside a Boolean algebra.
Set-theoretic formulas are interpreted by recursively evaluating membership,
equality, connectives, and quantifiers in the Boolean algebra.

# Ground-Model Sets

Every ordinary set from the ground universe has a canonical Boolean-valued
name. In Lean this operation is written `check`.

:::definition "def:check-name" (lean := "Flypitch.bSet.check")
The checked name `check x` embeds an ordinary pre-set into the Boolean-valued
universe.
:::

Checked names let the forcing construction compare the internal universe with
familiar objects such as `omega`, `aleph_one`, and `aleph_two`.

# Forcing Notation

If $`\Gamma` is an element of the Boolean algebra and $`\varphi` is a formula,
then saying that $`\Gamma` forces $`\varphi` means that $`\Gamma` lies below
the Boolean value of $`\varphi`. In particular, top forces a sentence exactly
when the sentence has Boolean value top.

:::definition "def:forces" (lean := "Flypitch.fol.forces")
The forcing relation records that a Boolean condition is below the Boolean
truth value of a formula in a Boolean-valued structure.
:::

# Boolean-Valued ZFC

The Boolean-valued set universe is not merely a model of a fragment. It
forces the ZFC axioms used by the proof.

:::theorem "thm:bset-models-zfc" (lean := "Flypitch.ZFC.bSet_models_ZFC")
For every complete Boolean algebra, the Boolean-valued universe of `bSet`s
forces the theory `ZFC`.

This theorem combines {uses "def:bset"}[], {uses "def:forces"}[], and the
set-theoretic encoding described in {uses "def:zfc-theory"}[].
:::

Together, Boolean-valued soundness and the theorem that `bSet` forces ZFC form
the semantic engine of the independence proof: a formal theorem of ZFC must
hold in every Boolean-valued universe.

# Lean Side Notes

The main Lean objects are `bStructure`, `forces`, `bSet`, Boolean membership
`∈ᴮ`, Boolean equality `=ᴮ`, and checked names `check`. The theorem
`bSet_models_ZFC` supplies the model-of-ZFC premise used in both
unprovability arguments.
