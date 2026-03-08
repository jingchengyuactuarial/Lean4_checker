import Mathlib.MeasureTheory.Measure.Typeclasses.NoAtoms
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-!
# Atomless-Space Support

The AES proof needs more than `NoAtoms`: it repeatedly uses exact splitting of
measurable events by prescribed mass. This file records that stronger property
as an explicit project-level definition.
-/

open MeasureTheory

namespace RiskMeasure

section

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Exact event splitting by prescribed mass inside a measurable event. -/
def HasFullEventSplitting (P : Measure Ω) : Prop :=
  ∀ ⦃A : Set Ω⦄ (_hA : MeasurableSet A) (t : ENNReal), t ≤ P A →
    ∃ B, B ⊆ A ∧ MeasurableSet B ∧ P B = t

/-- The stronger atomless condition naturally used in the AES proof. -/
def StronglyAtomless (P : Measure Ω) : Prop :=
  MeasureTheory.NoAtoms P ∧ HasFullEventSplitting P

end

section Probability

variable {Ω : Type*} [MeasurableSpace Ω]
variable (P : Measure Ω) [IsProbabilityMeasure P]

/-- Under exact event splitting, any real mass between `0` and `P(A)` is realized by a measurable
subset of `A`. -/
theorem exists_subset_measurableSet_measureReal_eq (hsplit : HasFullEventSplitting P)
    {A : Set Ω} (hA : MeasurableSet A) {t : ℝ}
    (ht0 : 0 ≤ t) (htA : t ≤ P.real A) :
    ∃ B, B ⊆ A ∧ MeasurableSet B ∧ P.real B = t := by
  have h_ofReal : ENNReal.ofReal t ≤ P A := by
    exact (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top P A)).2 htA
  rcases hsplit hA (ENNReal.ofReal t) h_ofReal with ⟨B, hBA, hB, hPB⟩
  refine ⟨B, hBA, hB, ?_⟩
  rw [Measure.real, hPB, ENNReal.toReal_ofReal ht0]

/-- Under exact event splitting, every real mass in `[0,1]` is realized by a measurable event. -/
theorem exists_measurableSet_measureReal_eq (hsplit : HasFullEventSplitting P)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ∃ A, MeasurableSet A ∧ P.real A = t := by
  have ht_univ : t ≤ P.real (Set.univ : Set Ω) := by
    simpa using ht1
  rcases exists_subset_measurableSet_measureReal_eq
      (P := P) hsplit MeasurableSet.univ ht0 ht_univ with
    ⟨A, _hAuniv, hA, hAreal⟩
  exact ⟨A, hA, hAreal⟩

end Probability

end RiskMeasure
