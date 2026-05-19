import Flypitch.ZFC

namespace Flypitch

open ZFC

/--
The Continuum Hypothesis is independent of ZFC.
Neither CH nor its negation is provable from ZFC.
-/
theorem independence_of_CH : ¬ (ZFC ⊢' CH_f) ∧ ¬ (ZFC ⊢' ∼CH_f) :=
  ⟨CH_f_unprovable, neg_CH_f_unprovable⟩

end Flypitch
