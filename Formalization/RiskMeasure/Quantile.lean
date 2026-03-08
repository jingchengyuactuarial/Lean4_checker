import Formalization.RiskMeasure.RandomVariable
import Mathlib.Probability.CDF

/-!
# Quantiles and Value-at-Risk

This file contains the quantile-based layer that underlies both `VaR` and `ES`.
-/

noncomputable section

open MeasureTheory

namespace RiskMeasure

/-- Lower quantile of a real probability law, defined via the cumulative distribution function. -/
def distLowerQuantile (μ : Measure ℝ) [IsProbabilityMeasure μ] (p : ℝ) : ℝ :=
  sInf {x : ℝ | p ≤ ProbabilityTheory.cdf μ x}

/-- Distribution-level Value-at-Risk. -/
def distVaR (μ : Measure ℝ) [IsProbabilityMeasure μ] (p : Level) : ℝ :=
  distLowerQuantile μ (p : ℝ)

section

variable {Ω : Type*} [MeasurableSpace Ω]
variable (P : Measure Ω) [IsProbabilityMeasure P]

/-- Value-at-Risk for random variables under the reference probability measure `P`. -/
def VaR (p : Level) (X : RandomVariable P) : ℝ :=
  distVaR (law P X) p

/-- Long-form alias for `VaR`. -/
abbrev ValueAtRisk := VaR P

end

end RiskMeasure
