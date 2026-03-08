import Formalization.RiskMeasure.Quantile
import Formalization.RiskMeasure.LawInvariant
import Mathlib.MeasureTheory.Function.EssSup
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Expected Shortfall and AES-Type Envelopes

This file contains the ES layer that is directly relevant to the AES proof.
-/

noncomputable section

open MeasureTheory

namespace RiskMeasure

/-- The endpoint quantile used for the `p = 1` branch of expected shortfall. -/
def distUpperQuantile (μ : Measure ℝ) [IsProbabilityMeasure μ] : ℝ :=
  essSup id μ

/-- The unnormalized integral appearing in the standard quantile representation of ES. -/
def distESIntegral (μ : Measure ℝ) [IsProbabilityMeasure μ] (p : Level) : ℝ :=
  ∫ q in (p : ℝ)..1, distLowerQuantile μ q

/-- Distribution-level expected shortfall. -/
def distES (μ : Measure ℝ) [IsProbabilityMeasure μ] (p : Level) : ℝ :=
  if _ : (p : ℝ) < 1 then
    (1 - (p : ℝ))⁻¹ * distESIntegral μ p
  else
    distUpperQuantile μ

/-- The expected-shortfall profile of a distribution. -/
def distESProfile (μ : Measure ℝ) [IsProbabilityMeasure μ] : Level → ℝ :=
  distES μ

/-- Monotonicity of the expected-shortfall profile on the open unit interval. -/
def distESProfileMonotoneOnIoo (μ : Measure ℝ) [IsProbabilityMeasure μ] : Prop :=
  MonotoneOn (distESProfile μ) {p : Level | 0 < (p : ℝ) ∧ (p : ℝ) < 1}

/-- Continuity of the expected-shortfall profile on the whole unit interval.

This is the paper-level property one eventually wants for bounded positions. -/
def distESProfileContinuous (μ : Measure ℝ) [IsProbabilityMeasure μ] : Prop :=
  Continuous (distESProfile μ)

/-- Penalized expected shortfall at the distribution level. -/
def distESg (μ : Measure ℝ) [IsProbabilityMeasure μ] (g : Level → ℝ) : ℝ :=
  sSup (Set.range fun p : Level => distES μ p - g p)

/-- Adjusted expected shortfall at the distribution level. -/
abbrev distAES (μ : Measure ℝ) [IsProbabilityMeasure μ] (g : Level → ℝ) : ℝ :=
  distESg μ g

section

variable {Ω : Type*} [MeasurableSpace Ω]
variable (P : Measure Ω) [IsProbabilityMeasure P]

/-- Expected shortfall for random variables under the reference probability measure `P`. -/
def ES (p : Level) (X : RandomVariable P) : ℝ :=
  distES (law P X) p

/-- The expected-shortfall profile of a random variable. -/
def ESProfile (X : RandomVariable P) : Level → ℝ :=
  fun p => ES P p X

/-- Monotonicity of the expected-shortfall profile on the open unit interval. -/
def ESProfileMonotoneOnIoo (X : RandomVariable P) : Prop :=
  MonotoneOn (ESProfile P X) {p : Level | 0 < (p : ℝ) ∧ (p : ℝ) < 1}

/-- Continuity of the expected-shortfall profile on the whole unit interval.

This is the paper-level property one eventually wants for bounded random variables. -/
def ESProfileContinuous (X : RandomVariable P) : Prop :=
  Continuous (ESProfile P X)

/-- Long-form alias for `ES`. -/
abbrev ExpectedShortfall := ES P

/-- `ES` factors through the law of the underlying random variable. -/
theorem ES_factorsThroughLaw (p : Level) : FactorsThroughLaw P (ES P p) := by
  refine ⟨fun μ => by
    let _ : IsProbabilityMeasure μ.1 := μ.2
    exact distES μ.1 p, ?_⟩
  intro X
  rfl

/-- `ES` is law-invariant. -/
theorem ES_lawInvariant (p : Level) : LawInvariant P (ES P p) :=
  (ES_factorsThroughLaw (P := P) p).lawInvariant (P := P)

/-- The ES profile factors through law. -/
theorem ESProfile_factorsThroughLaw : FactorsThroughLaw P (ESProfile P) := by
  refine ⟨fun μ => by
    let _ : IsProbabilityMeasure μ.1 := μ.2
    exact distESProfile μ.1, ?_⟩
  intro X
  rfl

/-- The ES profile is law-invariant. -/
theorem ESProfile_lawInvariant : LawInvariant P (ESProfile P) :=
  ESProfile_factorsThroughLaw (P := P) |>.lawInvariant (P := P)

/-- Penalized expected shortfall for random variables. -/
def ESg (g : Level → ℝ) (X : RandomVariable P) : ℝ :=
  distESg (law P X) g

/-- `ESg` factors through the law of the underlying random variable. -/
theorem ESg_factorsThroughLaw (g : Level → ℝ) : FactorsThroughLaw P (ESg P g) := by
  refine ⟨fun μ => by
    let _ : IsProbabilityMeasure μ.1 := μ.2
    exact distESg μ.1 g, ?_⟩
  intro X
  rfl

/-- `ESg` is law-invariant. -/
theorem ESg_lawInvariant (g : Level → ℝ) : LawInvariant P (ESg P g) :=
  (ESg_factorsThroughLaw (P := P) g).lawInvariant (P := P)

/-- Adjusted expected shortfall for random variables. -/
abbrev AES (g : Level → ℝ) (X : RandomVariable P) : ℝ :=
  ESg P g X

/-- Long-form alias for `AES`. -/
abbrev AdjustedExpectedShortfall := AES P

/-- `AES` factors through the law of the underlying random variable. -/
theorem AES_factorsThroughLaw (g : Level → ℝ) : FactorsThroughLaw P (AES P g) :=
  ESg_factorsThroughLaw (P := P) g

/-- `AES` is law-invariant. -/
theorem AES_lawInvariant (g : Level → ℝ) : LawInvariant P (AES P g) :=
  ESg_lawInvariant (P := P) g

end

end RiskMeasure
