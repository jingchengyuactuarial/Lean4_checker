import Mathlib.Probability.IdentDistrib
import Formalization.RiskMeasure.Linf
import Formalization.RiskMeasure.RandomVariable

/-!
# Indicator Positions

The AES proof reduces many arguments to positions of the form `λ 1_A`.
This file isolates that representation.
-/

noncomputable section

open MeasureTheory
open ProbabilityTheory

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

/-- The scaled indicator is the usual constant-valued indicator function. -/
@[simp] lemma scaledIndicator_eq_indicator_const (c : ℝ) (A : Set Ω) :
    scaledIndicator c A = A.indicator (fun _ => c) := by
  funext ω
  by_cases hω : ω ∈ A
  · simp [scaledIndicator, eventIndicator, hω]
  · simp [scaledIndicator, eventIndicator, hω]

/-- Scaled indicators packaged as random variables. -/
def scaledIndicatorRV (P : Measure Ω) (c : ℝ) (A : Set Ω) (hA : MeasurableSet A) :
    RandomVariable P := by
  refine ⟨scaledIndicator c A, ?_⟩
  simpa [scaledIndicator_eq_indicator_const (Ω := Ω) c A] using
    (Measurable.indicator measurable_const hA).aemeasurable

section Probability

variable (P : Measure Ω) [IsProbabilityMeasure P]

/-- If two measurable events have the same probability, then the corresponding scaled indicators
have the same distribution. -/
theorem law_scaledIndicatorRV_eq_of_measure_eq (c : ℝ) {A B : Set Ω}
    (hA : MeasurableSet A) (hB : MeasurableSet B) (hAB : P A = P B) :
    law P (scaledIndicatorRV P c A hA) = law P (scaledIndicatorRV P c B hB) := by
  classical
  ext s hs
  rw [law, law,
    Measure.map_apply_of_aemeasurable (scaledIndicatorRV P c A hA).2 hs,
    Measure.map_apply_of_aemeasurable (scaledIndicatorRV P c B hB).2 hs]
  change P ((scaledIndicator c A) ⁻¹' s) = P ((scaledIndicator c B) ⁻¹' s)
  · by_cases hc : c ∈ s
    · by_cases h0 : (0 : ℝ) ∈ s
      · rw [scaledIndicator_eq_indicator_const, scaledIndicator_eq_indicator_const,
          Set.indicator_const_preimage_eq_union, Set.indicator_const_preimage_eq_union]
        simp [hc, h0]
      · rw [scaledIndicator_eq_indicator_const, scaledIndicator_eq_indicator_const,
          Set.indicator_const_preimage_eq_union, Set.indicator_const_preimage_eq_union]
        simp [hc, h0, hAB]
    · by_cases h0 : (0 : ℝ) ∈ s
      · have hcompl : P Aᶜ = P Bᶜ := by
          rw [measure_compl hA (by simp), measure_compl hB (by simp), hAB]
        rw [scaledIndicator_eq_indicator_const, scaledIndicator_eq_indicator_const,
          Set.indicator_const_preimage_eq_union, Set.indicator_const_preimage_eq_union]
        simp [hc, h0, hcompl]
      · rw [scaledIndicator_eq_indicator_const, scaledIndicator_eq_indicator_const,
          Set.indicator_const_preimage_eq_union, Set.indicator_const_preimage_eq_union]
        simp [hc, h0]

/-- If two measurable events have the same probability, then the corresponding scaled indicators
are identically distributed. -/
theorem identDistrib_scaledIndicator_of_measure_eq (c : ℝ) {A B : Set Ω}
    (hA : MeasurableSet A) (hB : MeasurableSet B) (hAB : P A = P B) :
    IdentDistrib (scaledIndicator c A) (scaledIndicator c B) P P := by
  refine ⟨(scaledIndicatorRV P c A hA).2, (scaledIndicatorRV P c B hB).2, ?_⟩
  simpa [law, scaledIndicatorRV] using law_scaledIndicatorRV_eq_of_measure_eq (P := P) c hA hB hAB

end Probability

section Linf

variable (P : Measure Ω) [IsFiniteMeasure P]

/-- The `L^\infty` indicator position agrees almost everywhere with the subtype-based indicator
position already used in the AES proof skeleton. -/
theorem ofLinf_linfIndicator_ae_eq_scaledIndicatorRV (c : ℝ) {A : Set Ω} (hA : MeasurableSet A) :
    ((RandomVariable.ofLinf (μ := P) (linfIndicator P A hA c) : RandomVariable P) : Ω → ℝ)
      =ᵐ[P] scaledIndicatorRV P c A hA := by
  refine (coeFn_linfIndicator (μ := P) A hA c).trans ?_
  exact Filter.EventuallyEq.of_eq (scaledIndicator_eq_indicator_const (Ω := Ω) c A).symm

end Linf

end

end RiskMeasure
