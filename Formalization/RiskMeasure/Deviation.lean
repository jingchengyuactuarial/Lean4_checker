import Formalization.RiskMeasure.Quantile
import Formalization.RiskMeasure.LawInvariant
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

/-- `MAD` factors through the law of the underlying random variable. -/
theorem MAD_factorsThroughLaw : FactorsThroughLaw P (MAD P) := by
  refine ⟨fun μ => by
    let _ : IsProbabilityMeasure μ.1 := μ.2
    exact distMAD μ.1, ?_⟩
  intro X
  rfl

/-- `MAD` is law-invariant. -/
theorem MAD_lawInvariant : LawInvariant P (MAD P) :=
  MAD_factorsThroughLaw (P := P) |>.lawInvariant (P := P)

/-- Lower median for random variables under the reference probability measure `P`. -/
def median (X : RandomVariable P) : ℝ :=
  distMedian (law P X)

/-- `median` factors through the law of the underlying random variable. -/
theorem median_factorsThroughLaw : FactorsThroughLaw P (median P) := by
  refine ⟨fun μ => by
    let _ : IsProbabilityMeasure μ.1 := μ.2
    exact distMedian μ.1, ?_⟩
  intro X
  rfl

/-- `median` is law-invariant. -/
theorem median_lawInvariant : LawInvariant P (median P) :=
  median_factorsThroughLaw (P := P) |>.lawInvariant (P := P)

/-- Mean median deviation for random variables. -/
def MMD (X : RandomVariable P) : ℝ :=
  distMMD (law P X)

/-- Long-form alias for `MMD`. -/
abbrev MeanMedianDeviation := MMD P

/-- `MMD` factors through the law of the underlying random variable. -/
theorem MMD_factorsThroughLaw : FactorsThroughLaw P (MMD P) := by
  refine ⟨fun μ => by
    let _ : IsProbabilityMeasure μ.1 := μ.2
    exact distMMD μ.1, ?_⟩
  intro X
  rfl

/-- `MMD` is law-invariant. -/
theorem MMD_lawInvariant : LawInvariant P (MMD P) :=
  MMD_factorsThroughLaw (P := P) |>.lawInvariant (P := P)

/-- Variance for random variables, reusing `mathlib`'s `Var`. -/
def variance (X : RandomVariable P) : ℝ :=
  Var[X; P]

/-- Long-form alias for `variance`. -/
abbrev Variance := variance P

/-- The random-variable-level variance agrees with the distribution-level variance of the law. -/
theorem variance_eq_distVariance_law (X : RandomVariable P) :
    variance P X = distVariance (law P X) := by
  simpa [variance, distVariance, law] using
    (ProbabilityTheory.variance_id_map (μ := P) (X := X) X.2).symm

/-- `variance` factors through the law of the underlying random variable. -/
theorem variance_factorsThroughLaw : FactorsThroughLaw P (variance P) := by
  refine ⟨fun μ => by
    let _ : IsProbabilityMeasure μ.1 := μ.2
    exact distVariance μ.1, ?_⟩
  intro X
  exact variance_eq_distVariance_law (P := P) X

/-- `variance` is law-invariant. -/
theorem variance_lawInvariant : LawInvariant P (variance P) :=
  variance_factorsThroughLaw (P := P) |>.lawInvariant (P := P)

end

end RiskMeasure
