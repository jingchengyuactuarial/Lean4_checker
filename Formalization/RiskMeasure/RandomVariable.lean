import Mathlib.MeasureTheory.Function.EssSup
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
open Filter

namespace RiskMeasure

/-- Confidence levels live in the unit interval `[0,1]`. -/
abbrev Level := unitInterval

section

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Real-valued random variables represented by almost-everywhere measurable functions. -/
abbrev RandomVariable (P : Measure Ω) := {X : Ω → ℝ // AEMeasurable X P}

variable (P : Measure Ω)

/-- The law of an almost-everywhere measurable real-valued random variable. -/
def law (X : RandomVariable P) : Measure ℝ :=
  P.map X

section

variable [IsProbabilityMeasure P]

instance instIsProbabilityMeasureLaw (X : RandomVariable P) :
    IsProbabilityMeasure (law P X) :=
  Measure.isProbabilityMeasure_map X.2

end

/-- Constant random variable under the reference measure `P`. -/
def const (c : ℝ) : RandomVariable P :=
  ⟨fun _ => c, by fun_prop⟩

/-- Essential upper bound of a random variable. -/
def essUpperBound (X : RandomVariable P) : ℝ :=
  essSup X P

/-- Essential lower bound of a random variable. -/
def essLowerBound (X : RandomVariable P) : ℝ :=
  essInf X P

/-- A random variable is essentially bounded if it is almost surely bounded above and below. -/
def EssentiallyBounded (X : RandomVariable P) : Prop :=
  Filter.IsBoundedUnder (· ≤ ·) (ae P) X.1 ∧ Filter.IsBoundedUnder (· ≥ ·) (ae P) X.1

/-- An essentially bounded random variable is almost surely bounded above by its essential upper
bound. -/
theorem ae_le_essUpperBound (X : RandomVariable P) (hX : EssentiallyBounded P X) :
    ∀ᵐ ω ∂P, X.1 ω ≤ essUpperBound P X := by
  simpa [essUpperBound] using (ae_le_essSup (μ := P) (f := X.1) (hf := hX.1))

/-- An essentially bounded random variable is almost surely bounded below by its essential lower
bound. -/
theorem ae_essLowerBound_le (X : RandomVariable P) (hX : EssentiallyBounded P X) :
    ∀ᵐ ω ∂P, essLowerBound P X ≤ X.1 ω := by
  simpa [essLowerBound] using (ae_essInf_le (μ := P) (f := X.1) (hf := hX.2))

end

end RiskMeasure
