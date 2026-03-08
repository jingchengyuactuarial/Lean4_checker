import Formalization.RiskMeasure.RandomVariable

/-!
# Law Invariance

Law invariance is a central hypothesis in the AES proof: it is what turns
event-based constructions into one-dimensional profiles indexed by probability.
-/

open MeasureTheory

namespace RiskMeasure

section

variable {Ω : Type*} [MeasurableSpace Ω]
variable (P : Measure Ω) [IsProbabilityMeasure P]
variable {C : Type*}

/-- A risk functional is law-invariant if equal laws imply equal evaluations. -/
def LawInvariant (ρ : RandomVariable P → C) : Prop :=
  ∀ ⦃X Y : RandomVariable P⦄, law P X = law P Y → ρ X = ρ Y

/-- A risk functional factors through law if it is induced by a map on probability laws. -/
def FactorsThroughLaw (ρ : RandomVariable P → C) : Prop :=
  ∃ f : Measure ℝ → C, ∀ X : RandomVariable P, ρ X = f (law P X)

end

end RiskMeasure
