import Mathlib.MeasureTheory.Measure.Typeclasses.NoAtoms

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

end RiskMeasure
