import Formalization.RiskMeasure.RandomVariable

/-!
# Indicator Positions

The AES proof reduces many arguments to positions of the form `λ 1_A`.
This file isolates that representation.
-/

noncomputable section

open MeasureTheory

namespace RiskMeasure

section

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Indicator payoff of an event. -/
def eventIndicator (A : Set Ω) : Ω → ℝ :=
  Set.indicator A fun _ => (1 : ℝ)

/-- A measurable event indicator is almost-everywhere measurable under any measure. -/
lemma aemeasurable_eventIndicator (P : Measure Ω) {A : Set Ω} (hA : MeasurableSet A) :
    AEMeasurable (eventIndicator A) P := by
  simpa [eventIndicator] using (Measurable.indicator measurable_const hA).aemeasurable

/-- Event indicators packaged as random variables. -/
def indicatorRV (P : Measure Ω) (A : Set Ω) (hA : MeasurableSet A) : RandomVariable P :=
  ⟨eventIndicator A, aemeasurable_eventIndicator P hA⟩

/-- A scaled indicator position `c 1_A`. -/
def scaledIndicator (c : ℝ) (A : Set Ω) : Ω → ℝ :=
  fun ω => c * eventIndicator A ω

/-- Scaled indicators packaged as random variables. -/
def scaledIndicatorRV (P : Measure Ω) (c : ℝ) (A : Set Ω) (hA : MeasurableSet A) :
    RandomVariable P := by
  refine ⟨scaledIndicator c A, ?_⟩
  simpa [scaledIndicator] using (aemeasurable_eventIndicator P hA).const_mul c

end

end RiskMeasure
