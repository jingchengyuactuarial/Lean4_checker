import Formalization.RiskMeasure.Quantile
import Mathlib.Probability.Notation

/-!
# Deviation-Type Risk Functionals

This file groups the auxiliary risk functionals that are useful for comparisons
and counterexamples around the AES proof.
-/

noncomputable section

open MeasureTheory
open scoped ProbabilityTheory

namespace RiskMeasure

/-- Absolute deviation around a chosen center. -/
def distAbsDeviationAt (μ : Measure ℝ) (c : ℝ) : ℝ :=
  ∫ x, |x - c| ∂μ

/-- Distribution-level mean absolute deviation. -/
def distMAD (μ : Measure ℝ) [IsProbabilityMeasure μ] : ℝ :=
  distAbsDeviationAt μ (μ[id])

/-- Distribution-level lower median, defined as the `1/2` lower quantile. -/
def distMedian (μ : Measure ℝ) [IsProbabilityMeasure μ] : ℝ :=
  distLowerQuantile μ (1 / 2 : ℝ)

/-- Distribution-level mean median deviation. -/
def distMMD (μ : Measure ℝ) [IsProbabilityMeasure μ] : ℝ :=
  distAbsDeviationAt μ (distMedian μ)

/-- Distribution-level variance reusing `mathlib`. -/
def distVariance (μ : Measure ℝ) [IsProbabilityMeasure μ] : ℝ :=
  Var[id; μ]

section

variable {Ω : Type*} [MeasurableSpace Ω]
variable (P : Measure Ω) [IsProbabilityMeasure P]

/-- Mean absolute deviation for random variables. -/
def MAD (X : RandomVariable P) : ℝ :=
  distMAD (law P X)

/-- Long-form alias for `MAD`. -/
abbrev MeanAbsoluteDeviation := MAD P

/-- Lower median for random variables under the reference probability measure `P`. -/
def median (X : RandomVariable P) : ℝ :=
  distMedian (law P X)

/-- Mean median deviation for random variables. -/
def MMD (X : RandomVariable P) : ℝ :=
  distMMD (law P X)

/-- Long-form alias for `MMD`. -/
abbrev MeanMedianDeviation := MMD P

/-- Variance for random variables, reusing `mathlib`'s `Var`. -/
def variance (X : RandomVariable P) : ℝ :=
  Var[X; P]

/-- Long-form alias for `variance`. -/
abbrev Variance := variance P

end

end RiskMeasure
