import Formalization.RiskMeasure.RandomVariable
import Formalization.RiskMeasure.LawInvariant

/-!
# Certainty Equivalents

This file isolates generalized inverses and certainty equivalents of the form
`ℓ⁻¹ (E[ℓ(X)])`. This is a natural next target after the AES infrastructure,
since it uses law invariance and bounded random variables but avoids the
quantile/shortfall profile layer.
-/

noncomputable section

open MeasureTheory

namespace RiskMeasure

/-- Generalized inverse of a real function, in the lower-inverse convention. -/
def generalizedInverse (ℓ : ℝ → ℝ) (y : ℝ) : ℝ :=
  sInf {x : ℝ | y ≤ ℓ x}

/-- Distribution-level certainty equivalent induced by a loss function `ℓ`. -/
def distCE (μ : Measure ℝ) [IsProbabilityMeasure μ] (ℓ : ℝ → ℝ) : ℝ :=
  generalizedInverse ℓ (∫ x, ℓ x ∂μ)

section

variable {Ω : Type*} [MeasurableSpace Ω]
variable (P : Measure Ω) [IsProbabilityMeasure P]

/-- Certainty equivalent for random variables under the reference probability measure `P`. -/
def CE (ℓ : ℝ → ℝ) (X : RandomVariable P) : ℝ :=
  distCE (law P X) ℓ

/-- Long-form alias for `CE`. -/
abbrev CertaintyEquivalent := CE P

/-- `CE` factors through the law of the underlying random variable. -/
theorem CE_factorsThroughLaw (ℓ : ℝ → ℝ) : FactorsThroughLaw P (CE P ℓ) := by
  refine ⟨fun μ => by
    let _ : IsProbabilityMeasure μ.1 := μ.2
    exact distCE μ.1 ℓ, ?_⟩
  intro X
  rfl

/-- `CE` is law-invariant. -/
theorem CE_lawInvariant (ℓ : ℝ → ℝ) : LawInvariant P (CE P ℓ) :=
  (CE_factorsThroughLaw (P := P) ℓ).lawInvariant (P := P)

end

end RiskMeasure
