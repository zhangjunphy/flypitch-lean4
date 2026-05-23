import Verso
import VersoManual
import VersoBlueprint
import Flypitch.Summary

open Verso.Genre
open Verso.Genre.Manual
open Informal

set_option linter.hashCommand false

#doc (Manual) "Independence" =>

We now assemble the two halves of the proof --- the Cohen model where CH fails
and the collapse model where CH holds --- into the final result: the Continuum
Hypothesis is independent of ZFC.

# Recap of the Strategy

The proof rests on two pillars:

1. **Boolean-valued soundness** ({uses "thm:boolean-soundness"}[]): if a
   theory $`T`$ proves a sentence $`\varphi`$, then every Boolean-valued
   model of $`T`$ forces $`\varphi`$. Taking the contrapositive: if there
   exists a Boolean-valued model of $`T`$ that forces
   $`\neg\varphi`$, then $`T`$ does not prove $`\varphi`$.

2. **Two Boolean-valued models of ZFC**:
   - The Cohen model $`V^{\mathbb{B}_{\text{Cohen}}}`$
     ({uses "thm:not-ch-forced"}[]), in which CH is forced false. By
     soundness, this means ZFC does not prove CH.
   - The collapse model $`V^{\mathbb{B}_{\text{Collapse}}}`$
     ({uses "thm:ch-forced"}[]), in which CH is forced true. By soundness,
     this means ZFC does not prove $`\neg\mathrm{CH}`$.

Together, neither CH nor its negation is provable from ZFC.

# The Main Theorems

:::theorem "thm:ch-unprovable" (lean := "Flypitch.CH_unprovable")
ZFC does not prove CH. That is, $`\text{ZFC} \not\vdash' \mathrm{CH}_f`$.
:::

:::proof "proof:ch-unprovable"
We use the Cohen Boolean algebra $`\mathbb{B}_{\text{Cohen}}`$
({uses "def:Cohen-BA"}[]). By {uses "thm:bSet-models-ZFC"}[], the
Boolean-valued universe $`V^{\mathbb{B}_{\text{Cohen}}}`$ is a model of ZFC:
$`\top \Vdash_{V^{\mathbb{B}_{\text{Cohen}}}} \text{ZFC}`$.

By {uses "thm:not-ch-forced"}[],
$`\top \Vdash_{V^{\mathbb{B}_{\text{Cohen}}}} \neg\mathrm{CH}_2`$,
and by {uses "lem:CH-iff-CH2"}[],
$`\llbracket\mathrm{CH}_f\rrbracket^{V^{\mathbb{B}_{\text{Cohen}}}} =
\llbracket\mathrm{CH}_2\rrbracket^{V^{\mathbb{B}_{\text{Cohen}}}} =
\bot`$.

Now suppose for contradiction that $`\text{ZFC} \vdash' \mathrm{CH}_f`$. By
Boolean-valued soundness ({uses "thm:boolean-soundness"}[]), this would imply
$`\top \Vdash_{V^{\mathbb{B}_{\text{Cohen}}}}
\mathrm{CH}_f`$, contradicting the fact that $`\llbracket\mathrm{CH}_f\rrbracket
= \bot`$. Therefore $`\text{ZFC} \not\vdash' \mathrm{CH}_f`$.
:::

:::theorem "thm:not-ch-unprovable" (lean := "Flypitch.neg_CH_unprovable")
ZFC does not prove the negation of CH. That is,
$`\text{ZFC} \not\vdash' \neg\mathrm{CH}_f`$.
:::

:::proof "proof:not-ch-unprovable"
We use the collapse Boolean algebra $`\mathbb{B}_{\text{Collapse}}`$
({uses "def:collapse-BA"}[]). By {uses "thm:bSet-models-ZFC"}[], the
Boolean-valued universe $`V^{\mathbb{B}_{\text{Collapse}}}`$ is a model of
ZFC: $`\top \Vdash_{V^{\mathbb{B}_{\text{Collapse}}}} \text{ZFC}`$.

By {uses "thm:ch-forced"}[],
$`\top \Vdash_{V^{\mathbb{B}_{\text{Collapse}}}} \mathrm{CH}_2`$,
hence $`\llbracket\mathrm{CH}_f\rrbracket^{V^{\mathbb{B}_{\text{Collapse}}}} =
\top`$ by {uses "lem:CH-iff-CH2"}[].

Now suppose for contradiction that $`\text{ZFC} \vdash'
\neg\mathrm{CH}_f`$. By Boolean-valued soundness
({uses "thm:boolean-soundness"}[]), this would imply
$`\top \Vdash_{V^{\mathbb{B}_{\text{Collapse}}}}
\neg\mathrm{CH}_f`$, so $`\llbracket\mathrm{CH}_f\rrbracket =
\bot`$, contradicting $`\llbracket\mathrm{CH}_f\rrbracket = \top`$. Therefore
$`\text{ZFC} \not\vdash' \neg\mathrm{CH}_f`$.
:::

# The Final Result

:::definition "def:independent" (lean := "Flypitch.independent")
Let $`T`$ be a theory and $`\varphi`$ a sentence. We say $`\varphi`$ is
*independent* of $`T`$ if $`T`$ proves neither $`\varphi`$ nor
$`\neg\varphi`$. Formally:
$`\text{independent}(T, \varphi) \iff (\neg(T \vdash' \varphi)) \land
(\neg(T \vdash' \neg\varphi))`$.
:::

:::theorem "thm:independence-of-ch-final" (lean := "Flypitch.independence_of_CH")
The Continuum Hypothesis is independent of ZFC. That is,
$`\text{independent}(\text{ZFC}, \mathrm{CH}_f)`$.
:::

:::proof "proof:independence-final"
Immediate from {uses "thm:ch-unprovable"}[] and
{uses "thm:not-ch-unprovable"}[]:
$`\neg(\text{ZFC} \vdash' \mathrm{CH}_f) \land
\neg(\text{ZFC} \vdash' \neg\mathrm{CH}_f)`$.
:::

# Conclusion

We have presented a complete proof that the Continuum Hypothesis is independent
of the axioms of Zermelo--Fraenkel set theory with Choice. The proof uses the
method of Boolean-valued models (forcing) and is fully formalized in the Lean 4
proof assistant.

The structure of the proof highlights a key advantage of the Boolean-valued
approach: we never need to pass to a "generic extension" or construct a
countable transitive model. Instead, we work entirely within the ordinary
universe of sets, interpreting ZFC in the Boolean-valued universe
$`V^{\mathbb{B}}`$ for two carefully chosen complete Boolean algebras
$`\mathbb{B}`$. The truth values in these algebras tell us that CH cannot be
decided by the axioms of ZFC.

The formalization in Lean encompasses the entire development: the syntax and
semantics of first-order logic, the natural deduction proof system with its
soundness theorem, the theory of complete Boolean algebras and Boolean-valued
semantics, the ZFC axioms and their Boolean-valued verification, and the two
specific forcing constructions (Cohen and collapse). Every step has been
mechanically verified, providing the highest standard of mathematical
correctness.

The final Lean declaration `Flypitch.independence_of_CH` encapsulates the main
theorem. The reader is invited to inspect the formal proof in the source code
and to explore the rich infrastructure built to support it.
