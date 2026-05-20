import Flypitch.ZFC

namespace Flypitch

open fol
open ZFC

/-- A sentence is independent of a theory when neither it nor its negation is provable. -/
def independent {L : Language} (T : Theory L) (f : sentence L) : Prop :=
  ¬ (T ⊢' f) ∧ ¬ (T ⊢' ∼f)

/-- ZFC does not prove CH. -/
theorem CH_unprovable : ¬ (ZFC ⊢' CH_f) :=
  CH_f_unprovable

/-- ZFC does not prove the negation of CH. -/
theorem neg_CH_unprovable : ¬ (ZFC ⊢' ∼CH_f) :=
  neg_CH_f_unprovable

/--
The Continuum Hypothesis is independent of ZFC.
Neither CH nor its negation is provable from ZFC.
-/
theorem independence_of_CH : independent ZFC CH_f :=
  ⟨CH_unprovable, neg_CH_unprovable⟩

end Flypitch
