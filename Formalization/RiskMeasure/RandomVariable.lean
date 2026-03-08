import Mathlib.Probability.HasLaw
import Mathlib.Topology.UnitInterval

/-!
# Random Variables and Laws

This file isolates the basic objects used by the AES proof:

- confidence levels in `[0,1]`;
- almost-everywhere measurable real-valued random variables under a fixed measure;
- pushforward laws of such random variables.
-/

noncomputable section

open MeasureTheory

namespace RiskMeasure

/-- Confidence levels live in the unit interval `[0,1]`. -/
abbrev Level := unitInterval

section

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Real-valued random variables represented by almost-everywhere measurable functions. -/
abbrev RandomVariable (P : Measure Ω) := {X : Ω → ℝ // AEMeasurable X P}

variable (P : Measure Ω) [IsProbabilityMeasure P]

/-- The law of an almost-everywhere measurable real-valued random variable. -/
def law (X : RandomVariable P) : Measure ℝ :=
  P.map X

instance instIsProbabilityMeasureLaw (X : RandomVariable P) :
    IsProbabilityMeasure (law P X) :=
  Measure.isProbabilityMeasure_map X.2

end

end RiskMeasure
