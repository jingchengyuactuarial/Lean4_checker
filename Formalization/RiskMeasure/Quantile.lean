import Formalization.RiskMeasure.RandomVariable
import Mathlib.Probability.CDF

/-!
# Quantiles and Value-at-Risk

This file contains the quantile-based layer that underlies both `VaR` and `ES`.
-/

noncomputable section

open MeasureTheory
open Filter

namespace RiskMeasure

/-- Lower quantile of a real probability law, defined via the cumulative distribution function. -/
def distLowerQuantile (μ : Measure ℝ) [IsProbabilityMeasure μ] (p : ℝ) : ℝ :=
  sInf {x : ℝ | p ≤ ProbabilityTheory.cdf μ x}

/-- For `p < 1`, the upper level set defining the lower quantile is nonempty. -/
lemma upperLevelSet_nonempty (μ : Measure ℝ) [IsProbabilityMeasure μ] {p : ℝ} (hp : p < 1) :
    ({x : ℝ | p ≤ ProbabilityTheory.cdf μ x} : Set ℝ).Nonempty := by
  have h_eventually :
      ∀ᶠ x in atTop, p < ProbabilityTheory.cdf μ x :=
    (ProbabilityTheory.tendsto_cdf_atTop μ).eventually (Ioi_mem_nhds hp)
  have h_eventually' :
      ∀ᶠ x in atTop, p ≤ ProbabilityTheory.cdf μ x :=
    h_eventually.mono fun _ hx => le_of_lt hx
  rcases Filter.eventually_atTop.mp h_eventually' with ⟨a, ha⟩
  exact ⟨max a 0, ha _ (le_max_left _ _)⟩

/-- For `p > 0`, the upper level set defining the lower quantile is bounded below. -/
lemma upperLevelSet_bddBelow (μ : Measure ℝ) [IsProbabilityMeasure μ] {p : ℝ} (hp : 0 < p) :
    BddBelow ({x : ℝ | p ≤ ProbabilityTheory.cdf μ x} : Set ℝ) := by
  have h_eventually :
      ∀ᶠ x in atBot, ProbabilityTheory.cdf μ x < p :=
    (ProbabilityTheory.tendsto_cdf_atBot μ).eventually (Iio_mem_nhds hp)
  rcases Filter.eventually_atBot.mp h_eventually with ⟨a, ha⟩
  refine ⟨a, ?_⟩
  intro x hx
  by_contra hxa
  have hxlt : x < a := lt_of_not_ge hxa
  exact (not_lt_of_ge hx) (ha x hxlt.le)

/-- The lower quantile is monotone on the open unit interval `(0,1)`. -/
lemma monotoneOn_distLowerQuantile_Ioo (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    MonotoneOn (distLowerQuantile μ) (Set.Ioo 0 1) := by
  intro p hp q hq hpq
  exact csInf_le_csInf (upperLevelSet_bddBelow μ hp.1) (upperLevelSet_nonempty μ hq.2)
    (fun x hx => le_trans hpq hx)

/-- Distribution-level Value-at-Risk. -/
def distVaR (μ : Measure ℝ) [IsProbabilityMeasure μ] (p : Level) : ℝ :=
  distLowerQuantile μ (p : ℝ)

/-- Distribution-level Value-at-Risk is monotone on levels in `(0,1)`. -/
lemma monotoneOn_distVaR_Ioo (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    MonotoneOn (distVaR μ) {p : Level | 0 < (p : ℝ) ∧ (p : ℝ) < 1} := by
  intro p hp q hq hpq
  exact monotoneOn_distLowerQuantile_Ioo μ hp hq hpq

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
