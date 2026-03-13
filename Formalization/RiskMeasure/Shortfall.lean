import Formalization.RiskMeasure.Quantile
import Formalization.RiskMeasure.LawInvariant
import Formalization.RiskMeasure.Linf
import Formalization.RiskMeasure.Indicators
import Mathlib.Data.ENNReal.Real
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

/-- Levels whose extended-valued penalty is finite. -/
def FinitePenaltyLevels (g : Level → ENNReal) : Set Level := {p : Level | g p < ⊤}

/-- Penalized expected shortfall for extended-valued penalties.

Levels carrying infinite penalty are excluded from the supremum. This is the model needed for the
paper's infinite-left collapse to a single `ES_{p₀}`. -/
def distESgExt (μ : Measure ℝ) [IsProbabilityMeasure μ] (g : Level → ENNReal) : ℝ :=
  sSup (Set.range fun p : {p : Level // p ∈ FinitePenaltyLevels g} =>
    distES μ p.1 - ENNReal.toReal (g p.1))

/-- Adjusted expected shortfall at the distribution level with extended-valued penalties. -/
abbrev distAESExt (μ : Measure ℝ) [IsProbabilityMeasure μ] (g : Level → ENNReal) : ℝ :=
  distESgExt μ g

/-- Embed a nonnegative real-valued penalty into the extended nonnegative reals. -/
def extPenaltyOfReal (g : Level → ℝ) : Level → ENNReal := fun p => ENNReal.ofReal (g p)

/-- Cutoff penalty equal to `0` on `[0,p₀]` and `∞` on `(p₀,1]`. -/
def zeroThenTopPenalty (p0 : Level) : Level → ENNReal := fun p =>
  if p ≤ p0 then 0 else ⊤

/-- Cutoff penalty equal to a finite constant `a` on `[0,p₀]` and `∞` on `(p₀,1]`. -/
def constThenTopPenalty (a : ℝ) (p0 : Level) : Level → ENNReal := fun p =>
  if p ≤ p0 then ENNReal.ofReal a else ⊤

/-- The OCE objective associated with a loss function `ℓ` and cash level `m`. -/
def distOCEObjective (μ : Measure ℝ) (ℓ : ℝ → ℝ) (m : ℝ) : ℝ :=
  m + ∫ x, ℓ (x - m) ∂μ

/-- Distribution-level optimized certainty equivalent. -/
def distOCE (μ : Measure ℝ) [IsProbabilityMeasure μ] (ℓ : ℝ → ℝ) : ℝ :=
  sInf (Set.range (distOCEObjective μ ℓ))

/-- Acceptance set for the shortfall risk induced by `ℓ` and threshold `r`. -/
def distShortfallAcceptance (μ : Measure ℝ) (ℓ : ℝ → ℝ) (r : ℝ) : Set ℝ :=
  {m : ℝ | ∫ x, ℓ (x - m) ∂μ ≤ r}

/-- Distribution-level shortfall risk. -/
def distShortfallRisk (μ : Measure ℝ) [IsProbabilityMeasure μ] (ℓ : ℝ → ℝ) (r : ℝ) : ℝ :=
  sInf (distShortfallAcceptance μ ℓ r)

/-- Adjusted expected shortfall at the distribution level. -/
abbrev distAES (μ : Measure ℝ) [IsProbabilityMeasure μ] (g : Level → ℝ) : ℝ :=
  distESg μ g

/-- The cdf of the point mass at `0` vanishes strictly to the left of the origin. -/
private theorem cdf_dirac_zero_of_lt_zero {x : ℝ} (hx : x < 0) :
    ProbabilityTheory.cdf (Measure.dirac (0 : ℝ)) x = 0 := by
  rw [ProbabilityTheory.cdf_eq_real, measureReal_def, Measure.dirac_apply' _ measurableSet_Iic]
  simp [not_le.mpr hx]

/-- The cdf of the point mass at `0` equals `1` on and to the right of the origin. -/
private theorem cdf_dirac_zero_of_nonneg {x : ℝ} (hx : 0 ≤ x) :
    ProbabilityTheory.cdf (Measure.dirac (0 : ℝ)) x = 1 := by
  rw [ProbabilityTheory.cdf_eq_real, measureReal_def, Measure.dirac_apply' _ measurableSet_Iic]
  simp [hx]

/-- Every lower quantile of `δ₀` on `(0,1]` equals `0`. -/
theorem distLowerQuantile_dirac_zero_eq_zero {q : ℝ} (hq : q ∈ Set.Ioc (0 : ℝ) 1) :
    distLowerQuantile (Measure.dirac (0 : ℝ)) q = 0 := by
  let S : Set ℝ := {x : ℝ | q ≤ ProbabilityTheory.cdf (Measure.dirac (0 : ℝ)) x}
  change sInf S = 0
  apply le_antisymm
  · refine csInf_le ?_ ?_
    · refine ⟨0, ?_⟩
      intro x hx
      by_contra hxneg
      have hxlt : x < 0 := lt_of_not_ge hxneg
      have hcdf : ProbabilityTheory.cdf (Measure.dirac (0 : ℝ)) x = 0 :=
        cdf_dirac_zero_of_lt_zero hxlt
      have : q ≤ 0 := by simpa [S, hcdf] using hx
      exact (not_le_of_gt hq.1) this
    · have hcdf0 : ProbabilityTheory.cdf (Measure.dirac (0 : ℝ)) 0 = 1 :=
        cdf_dirac_zero_of_nonneg le_rfl
      have : q ≤ 1 := hq.2
      simpa [S, hcdf0] using this
  · refine le_csInf ?_ ?_
    · refine ⟨0, ?_⟩
      have hcdf0 : ProbabilityTheory.cdf (Measure.dirac (0 : ℝ)) 0 = 1 :=
        cdf_dirac_zero_of_nonneg le_rfl
      have : q ≤ 1 := hq.2
      simpa [S, hcdf0] using this
    · intro x hx
      by_contra hxneg
      have hxlt : x < 0 := lt_of_not_ge hxneg
      have hcdf : ProbabilityTheory.cdf (Measure.dirac (0 : ℝ)) x = 0 :=
        cdf_dirac_zero_of_lt_zero hxlt
      have : q ≤ 0 := by simpa [S, hcdf] using hx
      exact (not_le_of_gt hq.1) this

/-- The integral term in the quantile representation of `ES` vanishes for `δ₀`. -/
theorem distESIntegral_dirac_zero_eq_zero (p : Level) :
    distESIntegral (Measure.dirac (0 : ℝ)) p = 0 := by
  rw [distESIntegral]
  calc
    ∫ q in (p : ℝ)..1, distLowerQuantile (Measure.dirac (0 : ℝ)) q =
        ∫ q in (p : ℝ)..1, (0 : ℝ) := by
          refine intervalIntegral.integral_congr_ae ?_
          filter_upwards [] with q
          intro hq
          have hp1 : (p : ℝ) ≤ 1 := p.2.2
          have hqIoc : q ∈ Set.Ioc (p : ℝ) 1 := by
            simpa [Set.uIoc, hp1] using hq
          have hq' : q ∈ Set.Ioc (0 : ℝ) 1 := by
            exact ⟨lt_of_le_of_lt p.2.1 hqIoc.1, hqIoc.2⟩
          exact distLowerQuantile_dirac_zero_eq_zero hq'
    _ = 0 := by simp

/-- The endpoint branch of `ES` vanishes for `δ₀`. -/
theorem distUpperQuantile_dirac_zero_eq_zero :
    distUpperQuantile (Measure.dirac (0 : ℝ)) = 0 := by
  unfold distUpperQuantile
  rw [essSup_eq_sInf]
  let S : Set ℝ := {a : ℝ | Measure.dirac (0 : ℝ) {x : ℝ | a < x} = 0}
  refine le_antisymm ?_ ?_
  · refine csInf_le ?_ ?_
    · change BddBelow S
      refine ⟨0, ?_⟩
      intro b hb
      by_contra hneg
      have hbgt : b < 0 := lt_of_not_ge hneg
      have hval : Measure.dirac (0 : ℝ) {x : ℝ | b < x} = 1 := by
        change Measure.dirac (0 : ℝ) (Set.Ioi b) = 1
        rw [Measure.dirac_apply' _ measurableSet_Ioi]
        simp [hbgt]
      rw [show b ∈ S from hb] at hval
      simp at hval
    · change 0 ∈ S
      change Measure.dirac (0 : ℝ) (Set.Ioi 0) = 0
      rw [Measure.dirac_apply' _ measurableSet_Ioi]
      simp
  · refine le_csInf ?_ ?_
    · exact ⟨0, by
        change Measure.dirac (0 : ℝ) (Set.Ioi 0) = 0
        rw [Measure.dirac_apply' _ measurableSet_Ioi]
        simp⟩
    · intro b hb
      by_contra hneg
      have hbgt : b < 0 := lt_of_not_ge hneg
      have hval : Measure.dirac (0 : ℝ) {x : ℝ | b < x} = 1 := by
        change Measure.dirac (0 : ℝ) (Set.Ioi b) = 1
        rw [Measure.dirac_apply' _ measurableSet_Ioi]
        simp [hbgt]
      rw [show b ∈ S from hb] at hval
      simp at hval

/-- Expected shortfall vanishes on the point mass at `0`. -/
theorem distES_dirac_zero_eq_zero (p : Level) :
    distES (Measure.dirac (0 : ℝ)) p = 0 := by
  by_cases hp : (p : ℝ) < 1
  · simp [distES, hp, distESIntegral_dirac_zero_eq_zero]
  · simp [distES, hp, distUpperQuantile_dirac_zero_eq_zero]

/-- The AES envelope vanishes on `δ₀` whenever the penalty is nonnegative and normalized at `0`. -/
theorem distESg_dirac_zero_eq_zero (g : Level → ℝ) (hg0 : g 0 = 0)
    (hgnonneg : ∀ p : Level, 0 ≤ g p) :
    distESg (Measure.dirac (0 : ℝ)) g = 0 := by
  unfold distESg
  apply le_antisymm
  · refine csSup_le ?_ ?_
    · exact ⟨0, ⟨(0 : Level), by simp [distES_dirac_zero_eq_zero, hg0]⟩⟩
    · intro y hy
      rcases hy with ⟨p, rfl⟩
      have hgp := hgnonneg p
      have hes : distES (Measure.dirac (0 : ℝ)) p = 0 := distES_dirac_zero_eq_zero p
      linarith
  · refine le_csSup ?_ ?_
    · change BddAbove (Set.range fun p : Level => distES (Measure.dirac (0 : ℝ)) p - g p)
      refine ⟨0, ?_⟩
      intro y hy
      rcases hy with ⟨p, rfl⟩
      have hgp := hgnonneg p
      have hes : distES (Measure.dirac (0 : ℝ)) p = 0 := distES_dirac_zero_eq_zero p
      linarith
    · exact ⟨(0 : Level), by simp [distES_dirac_zero_eq_zero, hg0]⟩

/-- Real-valued penalties agree with their extended-valued embedding. -/
theorem distESgExt_extPenaltyOfReal_eq_distESg (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (g : Level → ℝ) (hgnonneg : ∀ p : Level, 0 ≤ g p) :
    distESgExt μ (extPenaltyOfReal g) = distESg μ g := by
  unfold distESgExt distESg FinitePenaltyLevels extPenaltyOfReal
  congr 1
  ext y
  constructor
  · rintro ⟨p, rfl⟩
    refine ⟨p.1, ?_⟩
    simp [hgnonneg p.1]
  · rintro ⟨p, rfl⟩
    refine ⟨⟨p, by simp⟩, ?_⟩
    simp [hgnonneg p]

/-- The extended-valued AES envelope still vanishes on `δ₀` when the penalty is normalized at
level `0`, provided that `0` carries finite penalty. -/
theorem distESgExt_dirac_zero_eq_zero (g : Level → ENNReal) (hg0 : g 0 = 0) :
    distESgExt (Measure.dirac (0 : ℝ)) g = 0 := by
  unfold distESgExt FinitePenaltyLevels
  apply le_antisymm
  · refine csSup_le ?_ ?_
    · exact ⟨0, ⟨⟨(0 : Level), by simp [hg0]⟩, by simp [distES_dirac_zero_eq_zero, hg0]⟩⟩
    · intro y hy
      rcases hy with ⟨p, rfl⟩
      have hes : distES (Measure.dirac (0 : ℝ)) p.1 = 0 := distES_dirac_zero_eq_zero p.1
      have hpen : 0 ≤ ENNReal.toReal (g p.1) := ENNReal.toReal_nonneg
      linarith
  · refine le_csSup ?_ ?_
    · refine ⟨0, ?_⟩
      rintro _ ⟨p, rfl⟩
      have hes : distES (Measure.dirac (0 : ℝ)) p.1 = 0 := distES_dirac_zero_eq_zero p.1
      have hpen : 0 ≤ ENNReal.toReal (g p.1) := ENNReal.toReal_nonneg
      linarith
    · exact ⟨⟨(0 : Level), by simp [hg0]⟩, by simp [distES_dirac_zero_eq_zero, hg0]⟩

section

variable {Ω : Type*} [MeasurableSpace Ω]
variable (P : Measure Ω) [IsProbabilityMeasure P]

/-- Expected shortfall for random variables under the reference probability measure `P`. -/
def ES (p : Level) (X : RandomVariable P) : ℝ :=
  distES (law P X) p

/-- Expected shortfall on the `L^\infty` model, transported through `RandomVariable.ofLinf`. -/
def ESLinf (p : Level) (X : Linf P) : ℝ :=
  ES P p (RandomVariable.ofLinf (μ := P) X)

/-- The expected-shortfall profile of a random variable. -/
def ESProfile (X : RandomVariable P) : Level → ℝ :=
  fun p => ES P p X

/-- The expected-shortfall profile of an `L^\infty` position. -/
def ESLinfProfile (X : Linf P) : Level → ℝ :=
  fun p => ESLinf P p X

/-- Monotonicity of the expected-shortfall profile on the open unit interval. -/
def ESProfileMonotoneOnIoo (X : RandomVariable P) : Prop :=
  MonotoneOn (ESProfile P X) {p : Level | 0 < (p : ℝ) ∧ (p : ℝ) < 1}

/-- Continuity of the expected-shortfall profile on the whole unit interval.

This is the paper-level property one eventually wants for bounded random variables. -/
def ESProfileContinuous (X : RandomVariable P) : Prop :=
  Continuous (ESProfile P X)

/-- Long-form alias for `ES`. -/
abbrev ExpectedShortfall := ES P

/-- Long-form alias for `ESLinf`. -/
abbrev LinfExpectedShortfall := ESLinf P

/-- `ES` on `L^\infty` agrees with `ES` on any a.e.-equal packaged random variable. -/
theorem ESLinf_eq_ES_of_ae_eq (p : Level) (X : Linf P) (Y : RandomVariable P)
    (hXY : (X : Ω → ℝ) =ᵐ[P] Y) :
    ESLinf P p X = ES P p Y := by
  unfold ESLinf ES law RandomVariable.ofLinf
  congr 1
  exact Measure.map_congr hXY

/-- The indicator positions already used in the AES reduction induce the same `ES` values in the
subtype-based and `L^\infty` models. -/
theorem ESLinf_linfIndicator_eq_scaledIndicatorRV (p : Level) (c : ℝ) {A : Set Ω}
    (hA : MeasurableSet A) :
    ESLinf P p (linfIndicator P A hA c) = ES P p (scaledIndicatorRV P c A hA) :=
  ESLinf_eq_ES_of_ae_eq (P := P) p (linfIndicator P A hA c) (scaledIndicatorRV P c A hA)
    (ofLinf_linfIndicator_ae_eq_scaledIndicatorRV (P := P) c hA)

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

/-- Penalized expected shortfall for extended-valued penalties. -/
def ESgExt (g : Level → ENNReal) (X : RandomVariable P) : ℝ :=
  distESgExt (law P X) g

/-- Optimized certainty equivalent for random variables. -/
def OCE (ℓ : ℝ → ℝ) (X : RandomVariable P) : ℝ :=
  distOCE (law P X) ℓ

/-- Shortfall risk for random variables. -/
def ShortfallRisk (ℓ : ℝ → ℝ) (r : ℝ) (X : RandomVariable P) : ℝ :=
  distShortfallRisk (law P X) ℓ r

/-- Long-form alias for `ShortfallRisk`. -/
abbrev ShortfallMeasure := ShortfallRisk P

/-- Long-form alias for `OCE`. -/
abbrev OptimizedCertaintyEquivalent := OCE P

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

/-- `OCE` factors through the law of the underlying random variable. -/
theorem OCE_factorsThroughLaw (ℓ : ℝ → ℝ) : FactorsThroughLaw P (OCE P ℓ) := by
  refine ⟨fun μ => by
    let _ : IsProbabilityMeasure μ.1 := μ.2
    exact distOCE μ.1 ℓ, ?_⟩
  intro X
  rfl

/-- `OCE` is law-invariant. -/
theorem OCE_lawInvariant (ℓ : ℝ → ℝ) : LawInvariant P (OCE P ℓ) :=
  (OCE_factorsThroughLaw (P := P) ℓ).lawInvariant (P := P)

/-- `ShortfallRisk` factors through the law of the underlying random variable. -/
theorem ShortfallRisk_factorsThroughLaw (ℓ : ℝ → ℝ) (r : ℝ) :
    FactorsThroughLaw P (ShortfallRisk P ℓ r) := by
  refine ⟨fun μ => by
    let _ : IsProbabilityMeasure μ.1 := μ.2
    exact distShortfallRisk μ.1 ℓ r, ?_⟩
  intro X
  rfl

/-- `ShortfallRisk` is law-invariant. -/
theorem ShortfallRisk_lawInvariant (ℓ : ℝ → ℝ) (r : ℝ) :
    LawInvariant P (ShortfallRisk P ℓ r) :=
  (ShortfallRisk_factorsThroughLaw (P := P) ℓ r).lawInvariant (P := P)

/-- Adjusted expected shortfall for random variables. -/
abbrev AES (g : Level → ℝ) (X : RandomVariable P) : ℝ :=
  ESg P g X

/-- Adjusted expected shortfall for extended-valued penalties. -/
abbrev AESExt (g : Level → ENNReal) (X : RandomVariable P) : ℝ :=
  ESgExt P g X

/-- Long-form alias for `AES`. -/
abbrev AdjustedExpectedShortfall := AES P

/-- Long-form alias for `AESExt`. -/
abbrev ExtendedAdjustedExpectedShortfall := AESExt P

/-- `AES` factors through the law of the underlying random variable. -/
theorem AES_factorsThroughLaw (g : Level → ℝ) : FactorsThroughLaw P (AES P g) :=
  ESg_factorsThroughLaw (P := P) g

/-- `AES` is law-invariant. -/
theorem AES_lawInvariant (g : Level → ℝ) : LawInvariant P (AES P g) :=
  ESg_lawInvariant (P := P) g

/-- `ESgExt` factors through the law of the underlying random variable. -/
theorem ESgExt_factorsThroughLaw (g : Level → ENNReal) : FactorsThroughLaw P (ESgExt P g) := by
  refine ⟨fun μ => by
    let _ : IsProbabilityMeasure μ.1 := μ.2
    exact distESgExt μ.1 g, ?_⟩
  intro X
  rfl

/-- `ESgExt` is law-invariant. -/
theorem ESgExt_lawInvariant (g : Level → ENNReal) : LawInvariant P (ESgExt P g) :=
  (ESgExt_factorsThroughLaw (P := P) g).lawInvariant (P := P)

/-- `AESExt` factors through the law of the underlying random variable. -/
theorem AESExt_factorsThroughLaw (g : Level → ENNReal) : FactorsThroughLaw P (AESExt P g) :=
  ESgExt_factorsThroughLaw (P := P) g

/-- `AESExt` is law-invariant. -/
theorem AESExt_lawInvariant (g : Level → ENNReal) : LawInvariant P (AESExt P g) :=
  ESgExt_lawInvariant (P := P) g

/-- The extended-valued AES envelope agrees with the original real-valued one on nonnegative
penalties. -/
theorem ESgExt_extPenaltyOfReal_eq_ESg (g : Level → ℝ) (hgnonneg : ∀ p : Level, 0 ≤ g p)
    (X : RandomVariable P) :
    ESgExt P (extPenaltyOfReal g) X = ESg P g X := by
  simpa [ESgExt, ESg] using
    (distESgExt_extPenaltyOfReal_eq_distESg (μ := law P X) g hgnonneg)

/-- The extended-valued AES envelope agrees with the original real-valued one on nonnegative
penalties. -/
theorem AESExt_extPenaltyOfReal_eq_AES (g : Level → ℝ) (hgnonneg : ∀ p : Level, 0 ≤ g p)
    (X : RandomVariable P) :
    AESExt P (extPenaltyOfReal g) X = AES P g X := by
  exact ESgExt_extPenaltyOfReal_eq_ESg (P := P) g hgnonneg X

/-- The law of the zero random variable is the point mass at `0`. -/
@[simp] theorem law_zero_eq_dirac_zero : law P (0 : RandomVariable P) = Measure.dirac (0 : ℝ) := by
  change Measure.map (fun _ : Ω => (0 : ℝ)) P = Measure.dirac (0 : ℝ)
  rw [Measure.map_const]
  simp

/-- Expected shortfall vanishes on the zero position. -/
@[simp] theorem ES_zero_eq_zero (p : Level) : ES P p 0 = 0 := by
  simpa [ES] using (distES_dirac_zero_eq_zero p)

/-- Adjusted expected shortfall vanishes on the zero position under the normalized penalty
assumptions used in the AES paper. -/
@[simp] theorem AES_zero_eq_zero (g : Level → ℝ) (hg0 : g 0 = 0)
    (hgnonneg : ∀ p : Level, 0 ≤ g p) :
    AES P g 0 = 0 := by
  simpa [AES, ESg] using (distESg_dirac_zero_eq_zero g hg0 hgnonneg)

/-- Extended-valued adjusted expected shortfall vanishes on the zero position when the penalty is
normalized at level `0`. -/
@[simp] theorem AESExt_zero_eq_zero (g : Level → ENNReal) (hg0 : g 0 = 0) :
    AESExt P g 0 = 0 := by
  simpa [AESExt, ESgExt] using (distESgExt_dirac_zero_eq_zero g hg0)

/-- The finite-penalty levels of the cutoff penalty `zeroThenTopPenalty p₀` are exactly
the levels in `(-∞, p₀]`. -/
@[simp] theorem mem_FinitePenaltyLevels_zeroThenTopPenalty {p0 p : Level} :
    p ∈ FinitePenaltyLevels (zeroThenTopPenalty p0) ↔ p ≤ p0 := by
  unfold FinitePenaltyLevels zeroThenTopPenalty
  by_cases hp : p ≤ p0
  · simp [hp]
  · simp [hp]

/-- The finite-penalty levels of the cutoff penalty `constThenTopPenalty a p₀` are exactly
the levels in `(-∞, p₀]`. -/
@[simp] theorem mem_FinitePenaltyLevels_constThenTopPenalty {a : ℝ} {p0 p : Level} :
    p ∈ FinitePenaltyLevels (constThenTopPenalty a p0) ↔ p ≤ p0 := by
  unfold FinitePenaltyLevels constThenTopPenalty
  by_cases hp : p ≤ p0
  · simp [hp]
  · simp [hp]

/-- A pure cutoff penalty collapses `AESExt` to the level `p₀`, provided the `ES` profile is
monotone in the level parameter. -/
theorem AESExt_zeroThenTopPenalty_eq_ES (X : RandomVariable P) (p0 : Level)
    (hmono : Monotone (ESProfile P X)) :
    AESExt P (zeroThenTopPenalty p0) X = ES P p0 X := by
  unfold AESExt ESgExt distESgExt
  apply le_antisymm
  · refine csSup_le ?_ ?_
    · refine ⟨ES P p0 X, ?_⟩
      refine ⟨⟨p0, ?_⟩, ?_⟩
      · exact (mem_FinitePenaltyLevels_zeroThenTopPenalty (p0 := p0)).2 le_rfl
      · simp [ES, zeroThenTopPenalty]
    · intro y hy
      rcases hy with ⟨p, rfl⟩
      have hp_le : p.1 ≤ p0 :=
        (mem_FinitePenaltyLevels_zeroThenTopPenalty (p0 := p0) (p := p.1)).1 p.2
      have hES : ES P p.1 X ≤ ES P p0 X := hmono hp_le
      have hpen : ENNReal.toReal ((zeroThenTopPenalty p0) p.1) = 0 := by
        simp [zeroThenTopPenalty, hp_le]
      simpa [hpen] using hES
  · refine le_csSup ?_ ?_
    · refine ⟨ES P p0 X, ?_⟩
      intro y hy
      rcases hy with ⟨p, rfl⟩
      have hp_le : p.1 ≤ p0 :=
        (mem_FinitePenaltyLevels_zeroThenTopPenalty (p0 := p0) (p := p.1)).1 p.2
      have hES : ES P p.1 X ≤ ES P p0 X := hmono hp_le
      have hpen : ENNReal.toReal ((zeroThenTopPenalty p0) p.1) = 0 := by
        simp [zeroThenTopPenalty, hp_le]
      simpa [hpen] using hES
    · exact ⟨⟨p0, by exact (mem_FinitePenaltyLevels_zeroThenTopPenalty (p0 := p0)).2 le_rfl⟩,
        by simp [ES, zeroThenTopPenalty]⟩

/-- A constant cutoff penalty collapses `AESExt` to `ES_{p₀} - a`, provided the `ES` profile is
monotone in the level parameter. -/
theorem AESExt_constThenTopPenalty_eq_ES_sub (X : RandomVariable P) {a : ℝ} (ha : 0 ≤ a)
    (p0 : Level) (hmono : Monotone (ESProfile P X)) :
    AESExt P (constThenTopPenalty a p0) X = ES P p0 X - a := by
  unfold AESExt ESgExt distESgExt
  apply le_antisymm
  · refine csSup_le ?_ ?_
    · exact ⟨ES P p0 X - a,
        ⟨⟨p0, by exact (mem_FinitePenaltyLevels_constThenTopPenalty (a := a) (p0 := p0)).2 le_rfl⟩,
          by simp [constThenTopPenalty, ha, ES]⟩⟩
    · intro y hy
      rcases hy with ⟨p, rfl⟩
      have hp_le : p.1 ≤ p0 :=
        (mem_FinitePenaltyLevels_constThenTopPenalty (a := a) (p0 := p0) (p := p.1)).1 p.2
      have hES : ES P p.1 X ≤ ES P p0 X := hmono hp_le
      have hpen : ENNReal.toReal ((constThenTopPenalty a p0) p.1) = a := by
        simp [constThenTopPenalty, hp_le, ha]
      simpa [ES, hpen] using sub_le_sub_right hES a
  · refine le_csSup ?_ ?_
    · refine ⟨ES P p0 X - a, ?_⟩
      intro y hy
      rcases hy with ⟨p, rfl⟩
      have hp_le : p.1 ≤ p0 :=
        (mem_FinitePenaltyLevels_constThenTopPenalty (a := a) (p0 := p0) (p := p.1)).1 p.2
      have hES : ES P p.1 X ≤ ES P p0 X := hmono hp_le
      have hpen : ENNReal.toReal ((constThenTopPenalty a p0) p.1) = a := by
        simp [constThenTopPenalty, hp_le, ha]
      simpa [ES, hpen] using sub_le_sub_right hES a
    · exact ⟨⟨p0, by
          exact (mem_FinitePenaltyLevels_constThenTopPenalty (a := a) (p0 := p0)).2 le_rfl⟩,
        by simp [constThenTopPenalty, ha, ES]⟩

/-- Operator-level glue: once an extended-valued penalty is identified with a pure cutoff, the
corresponding `AESExt` functional is exactly `ES_{p₀}`. -/
theorem AESExt_eq_ES_of_eq_zeroThenTopPenalty {g : Level → ENNReal} (p0 : Level)
    (hg : g = zeroThenTopPenalty p0)
    (hmono : ∀ X : RandomVariable P, Monotone (ESProfile P X)) :
    AESExt P g = fun X => ES P p0 X := by
  subst hg
  funext X
  exact AESExt_zeroThenTopPenalty_eq_ES (P := P) X p0 (hmono X)

/-- Operator-level glue: once an extended-valued penalty is identified with a constant cutoff, the
corresponding `AESExt` functional is exactly `X ↦ ES_{p₀}(X) - a`. -/
theorem AESExt_eq_ES_sub_of_eq_constThenTopPenalty {g : Level → ENNReal} {a : ℝ} (ha : 0 ≤ a)
    (p0 : Level)
    (hg : g = constThenTopPenalty a p0)
    (hmono : ∀ X : RandomVariable P, Monotone (ESProfile P X)) :
    AESExt P g = fun X => ES P p0 X - a := by
  subst hg
  funext X
  exact AESExt_constThenTopPenalty_eq_ES_sub (P := P) X ha p0 (hmono X)

/-- A penalty that is constant on `(-∞, p₀]` and infinite on `(p₀,1]` is exactly the canonical
cutoff penalty `constThenTopPenalty a p₀`. -/
theorem eq_constThenTopPenalty_of_const_below_top_above {g : Level → ENNReal} {a : ℝ}
    (p0 : Level)
    (hconst : ∀ p : Level, p ≤ p0 → g p = ENNReal.ofReal a)
    (htop : ∀ p : Level, p0 < p → g p = ⊤) :
    g = constThenTopPenalty a p0 := by
  funext p
  by_cases hp : p ≤ p0
  · rw [hconst p hp]
    simp [constThenTopPenalty, hp]
  · have hp' : p0 < p := lt_of_not_ge hp
    rw [htop p hp']
    simp [constThenTopPenalty, hp]

/-- Normalized version of `eq_constThenTopPenalty_of_const_below_top_above`. -/
theorem eq_zeroThenTopPenalty_of_zero_below_top_above {g : Level → ENNReal}
    (p0 : Level) (hzero : ∀ p : Level, p ≤ p0 → g p = 0)
    (htop : ∀ p : Level, p0 < p → g p = ⊤) :
    g = zeroThenTopPenalty p0 := by
  funext p
  by_cases hp : p ≤ p0
  · rw [hzero p hp]
    simp [zeroThenTopPenalty, hp]
  · have hp' : p0 < p := lt_of_not_ge hp
    rw [htop p hp']
    simp [zeroThenTopPenalty, hp]

/-- Final cutoff-collapse theorem in the shape used by the AES corollary: if the penalty is
constant on `(-∞, p₀]` and infinite above `p₀`, then the corresponding `AESExt` functional
reduces to a single expected shortfall level. -/
theorem AESExt_eq_ES_sub_of_const_below_top_above {g : Level → ENNReal} {a : ℝ} (ha : 0 ≤ a)
    (p0 : Level) (hconst : ∀ p : Level, p ≤ p0 → g p = ENNReal.ofReal a)
    (htop : ∀ p : Level, p0 < p → g p = ⊤)
    (hmono : ∀ X : RandomVariable P, Monotone (ESProfile P X)) :
    AESExt P g = fun X => ES P p0 X - a := by
  have hg :
      g = constThenTopPenalty a p0 :=
    eq_constThenTopPenalty_of_const_below_top_above (g := g) (a := a) p0 hconst htop
  exact AESExt_eq_ES_sub_of_eq_constThenTopPenalty (P := P) ha p0 hg hmono

/-- Normalized cutoff-collapse theorem used after shifting the penalty by `g(0)`. -/
theorem AESExt_eq_ES_of_zero_below_top_above {g : Level → ENNReal}
    (p0 : Level) (hzero : ∀ p : Level, p ≤ p0 → g p = 0)
    (htop : ∀ p : Level, p0 < p → g p = ⊤)
    (hmono : ∀ X : RandomVariable P, Monotone (ESProfile P X)) :
    AESExt P g = fun X => ES P p0 X := by
  have hg : g = zeroThenTopPenalty p0 :=
    eq_zeroThenTopPenalty_of_zero_below_top_above (g := g) p0 hzero htop
  exact AESExt_eq_ES_of_eq_zeroThenTopPenalty (P := P) p0 hg hmono

/-- Strict-cutoff collapse theorem: if the penalty is normalized at `0`, vanishes strictly below
`p₀`, and is infinite strictly above `p₀`, then `AESExt` reduces to `ES_{p₀}`.

Unlike `AESExt_eq_ES_of_zero_below_top_above`, this statement allows the value at `p₀` itself to
be arbitrary; the final collapse uses continuity of the `ES` profile to pass from the strict
sublevels `p < p₀` to the boundary point `p₀`. -/
theorem AESExt_eq_ES_of_zero_strictBelow_top_strictAbove {g : Level → ENNReal}
    (p0 : Level) (hg0 : g 0 = 0)
    (hzero : ∀ p : Level, (p : ℝ) < (p0 : ℝ) → g p = 0)
    (htop : ∀ p : Level, (p0 : ℝ) < (p : ℝ) → g p = ⊤)
    (hmono : ∀ X : RandomVariable P, Monotone (ESProfile P X))
    (hcont : ∀ X : RandomVariable P, Continuous (ESProfile P X)) :
    AESExt P g = fun X => ES P p0 X := by
  funext X
  let S : Set ℝ := Set.range fun p : {p : Level // p ∈ FinitePenaltyLevels g} =>
    ES P p.1 X - ENNReal.toReal (g p.1)
  have hS_nonempty : S.Nonempty := by
    refine ⟨ES P 0 X - ENNReal.toReal (g 0), ?_⟩
    refine ⟨⟨0, ?_⟩, rfl⟩
    show g 0 < ⊤
    simpa [hg0]
  have hS_upper : ∀ y ∈ S, y ≤ ES P p0 X := by
    rintro y ⟨p, rfl⟩
    rcases lt_trichotomy ((p.1 : Level) : ℝ) (p0 : ℝ) with hlt | heq | hgt
    · have hES : ES P p.1 X ≤ ES P p0 X :=
        (hmono X) (le_of_lt hlt)
      have hpen : 0 ≤ ENNReal.toReal (g p.1) := ENNReal.toReal_nonneg
      linarith
    · have hpen : 0 ≤ ENNReal.toReal (g p.1) := ENNReal.toReal_nonneg
      have hpeq : p.1 = p0 := by
        exact Subtype.ext heq
      subst hpeq
      linarith
    · exfalso
      have hfinite : g p.1 < ⊤ := p.2
      rw [htop p.1 hgt] at hfinite
      exact lt_irrefl _ hfinite
  have hS_bdd : BddAbove S := ⟨ES P p0 X, hS_upper⟩
  unfold AESExt ESgExt distESgExt
  apply le_antisymm
  · exact csSup_le hS_nonempty hS_upper
  · by_cases hp0_zero : g p0 = 0
    · have hp0_fin : p0 ∈ FinitePenaltyLevels g := by
        show g p0 < ⊤
        simpa [hp0_zero]
      refine le_csSup hS_bdd ?_
      refine ⟨⟨p0, hp0_fin⟩, ?_⟩
      simp [hp0_zero, ES]
    · have hp0_pos : 0 < (p0 : ℝ) := by
        by_contra hp0_nonpos
        have hp0_eq : (p0 : ℝ) = 0 := by
          have hp0_ge : 0 ≤ (p0 : ℝ) := p0.2.1
          linarith
        have hp0_level_eq : p0 = 0 := Subtype.ext hp0_eq
        exact hp0_zero <| by simpa [hp0_level_eq] using hg0
      by_contra hnot
      have hsup_lt : sSup S < ES P p0 X := lt_of_not_ge hnot
      let ε : ℝ := (ES P p0 X - sSup S) / 2
      have hε : 0 < ε := by
        dsimp [ε]
        linarith
      have hcontAt : ContinuousAt (ESProfile P X) p0 := (hcont X).continuousAt
      rcases Metric.continuousAt_iff.mp hcontAt ε hε with ⟨δ, hδpos, hδ⟩
      let r : ℝ := (p0 : ℝ) - min (δ / 2) ((p0 : ℝ) / 2)
      have hr_lt : r < (p0 : ℝ) := by
        dsimp [r]
        have hmin_pos : 0 < min (δ / 2) ((p0 : ℝ) / 2) := by
          refine lt_min ?_ ?_
          · linarith
          · linarith
        linarith
      have hr_nonneg : 0 ≤ r := by
        dsimp [r]
        have hmin_le : min (δ / 2) ((p0 : ℝ) / 2) ≤ (p0 : ℝ) / 2 := min_le_right _ _
        linarith
      have hr_le_one : r ≤ 1 := by
        dsimp [r]
        linarith [p0.2.2]
      let q : Level := ⟨r, ⟨hr_nonneg, hr_le_one⟩⟩
      have hq_lt : (q : ℝ) < (p0 : ℝ) := hr_lt
      have hdist : dist q p0 < δ := by
        rw [Subtype.dist_eq, Real.dist_eq]
        have hmin_nonneg : 0 ≤ min (δ / 2) ((p0 : ℝ) / 2) := by positivity
        have hmin_lt : min (δ / 2) ((p0 : ℝ) / 2) < δ := by
          calc
            min (δ / 2) ((p0 : ℝ) / 2) ≤ δ / 2 := min_le_left _ _
            _ < δ := by linarith
        have habs :
            |(q : ℝ) - (p0 : ℝ)| = min (δ / 2) ((p0 : ℝ) / 2) := by
          change |r - (p0 : ℝ)| = min (δ / 2) ((p0 : ℝ) / 2)
          have hsub : r - (p0 : ℝ) = -min (δ / 2) ((p0 : ℝ) / 2) := by
            dsimp [r]
            ring
          rw [hsub, abs_neg, abs_of_nonneg hmin_nonneg]
        rw [habs]
        exact hmin_lt
      have hclose := hδ hdist
      have habs : |ES P q X - ES P p0 X| < ε := by
        simpa [ESProfile, Subtype.dist_eq, Real.dist_eq] using hclose
      have hq_close : ES P p0 X - ε < ES P q X := by
        have hleft := (abs_lt.mp habs).1
        linarith
      have hq_zero : g q = 0 := hzero q hq_lt
      have hq_fin : q ∈ FinitePenaltyLevels g := by
        show g q < ⊤
        simpa [hq_zero]
      have hq_mem : ES P q X ∈ S := by
        refine ⟨⟨q, hq_fin⟩, ?_⟩
        simp [hq_zero]
      have hq_le : ES P q X ≤ sSup S := le_csSup hS_bdd hq_mem
      have hmid : ES P p0 X - ε = (ES P p0 X + sSup S) / 2 := by
        dsimp [ε]
        ring
      have hgap : sSup S < ES P p0 X - ε := by
        rw [hmid]
        linarith
      have hq_gt : sSup S < ES P q X := by
        exact lt_trans hgap hq_close
      linarith

end

end RiskMeasure
