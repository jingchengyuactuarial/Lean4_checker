import Formalization.RiskMeasure.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Probability.CDF
import Mathlib.Probability.HasLaw
import Mathlib.Topology.UnitInterval

/-!
# Common Risk Measures

This file records concrete measure-theoretic definitions for several standard
risk measures. The guiding choice is to define each object first on a real
probability law, and then lift it to real-valued random variables by pushforward.

At the current stage:

- `variance` reuses the existing `mathlib` definition `Var[X; P]`;
- `VaR` is defined through the lower quantile built from `cdf`;
- `ES` is defined as the normalized integral of `VaR`;
- `ESg` and `AES` are defined through a penalty/supremum envelope;
- `MAD` is defined around the mean;
- `median` is defined as the lower median, i.e. the `1/2` quantile;
- `MMD` is defined from that median.
-/

noncomputable section

open MeasureTheory
open scoped ProbabilityTheory

namespace RiskMeasure

/-- Confidence levels live in the unit interval `[0,1]`. -/
abbrev Level := unitInterval

section DistributionLevel

/-- Lower quantile of a real probability law, defined via the cumulative distribution function. -/
def distLowerQuantile (μ : Measure ℝ) [IsProbabilityMeasure μ] (p : ℝ) : ℝ :=
  sInf {x : ℝ | p ≤ ProbabilityTheory.cdf μ x}

/-- Distribution-level Value-at-Risk. -/
def distVaR (μ : Measure ℝ) [IsProbabilityMeasure μ] (p : Level) : ℝ :=
  distLowerQuantile μ (p : ℝ)

/-- The endpoint quantile used for the `p = 1` branch of expected shortfall. -/
def distUpperQuantile (μ : Measure ℝ) [IsProbabilityMeasure μ] : ℝ :=
  distLowerQuantile μ 1

/-- The unnormalized integral appearing in the standard quantile representation of ES. -/
def distESIntegral (μ : Measure ℝ) [IsProbabilityMeasure μ] (p : Level) : ℝ :=
  ∫ q in (p : ℝ)..1, distLowerQuantile μ q

/-- Distribution-level expected shortfall. -/
def distES (μ : Measure ℝ) [IsProbabilityMeasure μ] (p : Level) : ℝ :=
  if _ : (p : ℝ) < 1 then
    (1 - (p : ℝ))⁻¹ * distESIntegral μ p
  else
    distUpperQuantile μ

/-- Penalized expected shortfall at the distribution level. -/
def distESg (μ : Measure ℝ) [IsProbabilityMeasure μ] (g : Level → ℝ) : ℝ :=
  sSup (Set.range fun p : Level => distES μ p - g p)

/-- Adjusted expected shortfall at the distribution level. -/
abbrev distAES (μ : Measure ℝ) [IsProbabilityMeasure μ] (g : Level → ℝ) : ℝ :=
  distESg μ g

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

end DistributionLevel

section RandomVariables

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Real-valued random variables represented by almost-everywhere measurable functions. -/
abbrev RandomVariable (P : Measure Ω) := {X : Ω → ℝ // AEMeasurable X P}

variable (P : Measure Ω) [IsProbabilityMeasure P]

/-- The law of an almost-everywhere measurable real random variable. -/
def law (X : RandomVariable P) : Measure ℝ :=
  P.map X

instance instIsProbabilityMeasureLaw (X : RandomVariable P) :
    IsProbabilityMeasure (law P X) :=
  Measure.isProbabilityMeasure_map X.2

/-- Value-at-Risk for random variables under the reference probability measure `P`. -/
def VaR (p : Level) (X : RandomVariable P) : ℝ :=
  distVaR (law P X) p

/-- Long-form alias for `VaR`. -/
abbrev ValueAtRisk := VaR P

/-- Expected shortfall for random variables under the reference probability measure `P`. -/
def ES (p : Level) (X : RandomVariable P) : ℝ :=
  distES (law P X) p

/-- Long-form alias for `ES`. -/
abbrev ExpectedShortfall := ES P

/-- Penalized expected shortfall for random variables. -/
def ESg (g : Level → ℝ) (X : RandomVariable P) : ℝ :=
  distESg (law P X) g

/-- Adjusted expected shortfall for random variables. -/
abbrev AES (g : Level → ℝ) (X : RandomVariable P) : ℝ :=
  ESg P g X

/-- Long-form alias for `AES`. -/
abbrev AdjustedExpectedShortfall := AES P

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

end RandomVariables

end RiskMeasure
