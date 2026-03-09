import Formalization.RiskMeasure
import Mathlib.Analysis.Convex.Slope

/-!
# AES Bridge Lemmas

This file stores proof-facing bridge lemmas for the AES project.
They are intentionally narrower than the reusable risk-measure API:

- event-probability reductions derived from law invariance;
- profile wrappers for `ES` on indicator positions;
- convenience lemmas that connect the reusable `RiskMeasure` layer to the
  specific reduction pattern used in the AES proof.
-/

noncomputable section

open MeasureTheory
open Filter
open RiskMeasure

namespace AesSubmodularity

section RatioBridges

/-- On `(0,1]`, a concave profile with value `0` at the origin has a nonincreasing ratio
`φ(t) / t`. This is the slope monotonicity step used in the infinite-left AES argument. -/
theorem ratio_antitoneOn_of_concaveOn_zero {φ : ℝ → ℝ}
    (hconc : ConcaveOn ℝ (Set.Icc (0 : ℝ) 1) φ) (h0 : φ 0 = 0) :
    AntitoneOn (fun t : ℝ => φ t / t) (Set.Ioc (0 : ℝ) 1) := by
  intro s hs t ht hst
  have hneg := hconc.neg
  have hs_ne : s ≠ 0 := ne_of_gt hs.1
  have ht_ne : t ≠ 0 := ne_of_gt ht.1
  have key := hneg.secant_mono (show (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 by simp)
    (show s ∈ Set.Icc (0 : ℝ) 1 by exact ⟨le_of_lt hs.1, hs.2⟩)
    (show t ∈ Set.Icc (0 : ℝ) 1 by exact ⟨le_of_lt ht.1, ht.2⟩)
    hs_ne ht_ne hst
  have key' : (-φ s) / s ≤ (-φ t) / t := by
    simpa [h0] using key
  have key'' : -(φ s / s) ≤ -(φ t / t) := by
    simpa [neg_div] using key'
  linarith

/-- A ratio profile that is antitone on `(0,1]` cannot converge to `L` at the right-hand origin
while taking a strictly larger value at some positive point. -/
theorem not_tendsto_ratio_nhdsWithin_zero_of_antitoneOn_above {φ : ℝ → ℝ} {L t1 : ℝ}
    (hanti : AntitoneOn (fun t : ℝ => φ t / t) (Set.Ioc (0 : ℝ) 1))
    (ht1 : t1 ∈ Set.Ioc (0 : ℝ) 1)
    (hgt : L < φ t1 / t1)
    (hlim : Tendsto (fun t : ℝ => φ t / t) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds L)) :
    False := by
  let m : ℝ := (L + φ t1 / t1) / 2
  have hLm : L < m := by
    dsimp [m]
    linarith
  have hm1 : m < φ t1 / t1 := by
    dsimp [m]
    linarith
  have hnear : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0), φ t / t < m := by
    exact hlim (Iio_mem_nhds hLm)
  have hpos : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0), 0 < t := by
    exact self_mem_nhdsWithin
  have hltSet : Set.Iio t1 ∈ nhdsWithin (0 : ℝ) (Set.Ioi 0) := by
    exact
      (nhdsWithin_le_nhds : nhdsWithin (0 : ℝ) (Set.Ioi 0) ≤ nhds (0 : ℝ))
        (Iio_mem_nhds ht1.1)
  have hlt : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0), t < t1 := by
    have hmem : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0), t ∈ Set.Iio t1 := hltSet
    exact hmem.mono fun _ ht => ht
  have hcomb := hnear.and (hpos.and hlt)
  rcases Filter.Eventually.exists hcomb with ⟨t, ht, hpos_t, hlt_t⟩
  have htIoc : t ∈ Set.Ioc (0 : ℝ) 1 := ⟨hpos_t, le_trans (le_of_lt hlt_t) ht1.2⟩
  have hmono := hanti htIoc ht1 (le_of_lt hlt_t)
  linarith

/-- An antitone ratio profile on `(0,1]` cannot stay eventually below `L` near the origin while
taking a strictly larger value at some positive point. This is a weaker, more direct variant of
the limit-based contradiction used in the infinite-left AES argument. -/
theorem not_eventually_le_ratio_nhdsWithin_zero_of_antitoneOn_above {φ : ℝ → ℝ} {L t1 : ℝ}
    (hanti : AntitoneOn (fun t : ℝ => φ t / t) (Set.Ioc (0 : ℝ) 1))
    (ht1 : t1 ∈ Set.Ioc (0 : ℝ) 1)
    (hgt : L < φ t1 / t1)
    (hupper : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0), φ t / t ≤ L) :
    False := by
  have hpos : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0), 0 < t := by
    exact self_mem_nhdsWithin
  have hltSet : Set.Iio t1 ∈ nhdsWithin (0 : ℝ) (Set.Ioi 0) := by
    exact
      (nhdsWithin_le_nhds : nhdsWithin (0 : ℝ) (Set.Ioi 0) ≤ nhds (0 : ℝ))
        (Iio_mem_nhds ht1.1)
  have hlt : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0), t < t1 := by
    have hmem : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0), t ∈ Set.Iio t1 := hltSet
    exact hmem.mono fun _ ht => ht
  rcases Filter.Eventually.exists (hupper.and (hpos.and hlt)) with ⟨t, htL, ht0, htt1⟩
  have htIoc : t ∈ Set.Ioc (0 : ℝ) 1 := by
    exact ⟨ht0, le_trans (le_of_lt htt1) ht1.2⟩
  have hmono := hanti htIoc ht1 (le_of_lt htt1)
  linarith

/-- Along the dyadic sequence `t, t/2, t/4, ...`, the ratio `φ(t)/t` cannot decrease if `φ`
satisfies the midpoint inequality on `[0,1]` and vanishes at the origin. -/
theorem ratio_ge_at_dyadics_of_midpoint_zero {φ : ℝ → ℝ}
    (hmid :
      ∀ ⦃x y : ℝ⦄, x ∈ Set.Icc (0 : ℝ) 1 → y ∈ Set.Icc (0 : ℝ) 1 →
        φ (midpoint ℝ x y) ≥ midpoint ℝ (φ x) (φ y))
    (h0 : φ 0 = 0) {t : ℝ} (ht : t ∈ Set.Ioc (0 : ℝ) 1) :
    ∀ n : ℕ, φ (t * ((1 / 2 : ℝ) ^ n)) / (t * ((1 / 2 : ℝ) ^ n)) ≥ φ t / t := by
  intro n
  let u : ℕ → ℝ := fun m => t * ((1 / 2 : ℝ) ^ m)
  have hu_pos : ∀ m : ℕ, 0 < u m := by
    intro m
    dsimp [u]
    exact mul_pos ht.1 (pow_pos (by norm_num : (0 : ℝ) < 1 / 2) _)
  have hu_Icc : ∀ m : ℕ, u m ∈ Set.Icc (0 : ℝ) 1 := by
    intro m
    constructor
    · exact (hu_pos m).le
    · dsimp [u]
      have hpow_le : ((1 / 2 : ℝ) ^ m) ≤ 1 := by
        exact pow_le_one₀ (by norm_num) (by norm_num)
      have hpow_nonneg : 0 ≤ ((1 / 2 : ℝ) ^ m) := by
        exact pow_nonneg (by norm_num) m
      have hmul_le : t * ((1 / 2 : ℝ) ^ m) ≤ 1 * ((1 / 2 : ℝ) ^ m) := by
        exact mul_le_mul_of_nonneg_right ht.2 hpow_nonneg
      have hle_one : 1 * ((1 / 2 : ℝ) ^ m) ≤ 1 := by simpa using hpow_le
      exact le_trans hmul_le hle_one
  have hu_succ : ∀ m : ℕ, u (m + 1) = midpoint ℝ 0 (u m) := by
    intro m
    dsimp [u]
    rw [midpoint_eq_smul_add, invOf_eq_inv, smul_eq_mul]
    ring_nf
  have hstep : ∀ m : ℕ, φ (u (m + 1)) / u (m + 1) ≥ φ (u m) / u m := by
    intro m
    have hmid_m := hmid (show (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 by simp) (hu_Icc m)
    rw [← hu_succ m, midpoint_eq_smul_add, invOf_eq_inv, smul_eq_mul, h0, zero_add] at hmid_m
    have hu_ne : u m ≠ 0 := ne_of_gt (hu_pos m)
    have hu_succ_eq : u (m + 1) = u m / 2 := by
      rw [hu_succ m, midpoint_eq_smul_add, invOf_eq_inv, smul_eq_mul, zero_add]
      ring
    have hu_succ_pos : 0 < u (m + 1) := hu_pos (m + 1)
    have hdiv :
        (φ (u m) / 2) / (u (m + 1)) = φ (u m) / u m := by
      rw [hu_succ_eq]
      field_simp [hu_ne]
    calc
      φ (u m) / u m = (φ (u m) / 2) / (u (m + 1)) := hdiv.symm
      _ ≤ φ (u (m + 1)) / (u (m + 1)) := by
        have hmid_m' : φ (u m) / 2 ≤ φ (u (m + 1)) := by
          simpa [div_eq_mul_inv, mul_comm] using hmid_m
        exact div_le_div_of_nonneg_right hmid_m' hu_succ_pos.le
  have hmono : ∀ m : ℕ, φ (u m) / u m ≥ φ (u 0) / u 0 := by
    intro m
    induction m with
    | zero =>
        rfl
    | succ m ihm =>
        exact le_trans ihm (hstep m)
  simpa [u] using hmono n

/-- A midpoint-concave profile with value `0` at the origin cannot stay eventually below `L`
near the origin while taking a strictly larger ratio at some positive point. This avoids a full
`ConcaveOn` upgrade in the infinite-left AES argument. -/
theorem not_eventually_le_ratio_nhdsWithin_zero_of_midpoint_above {φ : ℝ → ℝ} {L t1 : ℝ}
    (hmid :
      ∀ ⦃x y : ℝ⦄, x ∈ Set.Icc (0 : ℝ) 1 → y ∈ Set.Icc (0 : ℝ) 1 →
        φ (midpoint ℝ x y) ≥ midpoint ℝ (φ x) (φ y))
    (h0 : φ 0 = 0) (ht1 : t1 ∈ Set.Ioc (0 : ℝ) 1)
    (hgt : L < φ t1 / t1)
    (hupper : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0), φ t / t ≤ L) :
    False := by
  let u : ℕ → ℝ := fun n => t1 * ((1 / 2 : ℝ) ^ n)
  have hu_nhds : Tendsto u atTop (nhds (0 : ℝ)) := by
    have hpow : Tendsto (fun n : ℕ => ((1 / 2 : ℝ) ^ n)) atTop (nhds (0 : ℝ)) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    simpa [u] using hpow.const_mul t1
  have hu_pos : ∀ᶠ n in atTop, u n ∈ Set.Ioi (0 : ℝ) := by
    refine Filter.Eventually.of_forall ?_
    intro n
    dsimp [u]
    exact mul_pos ht1.1 (pow_pos (by norm_num : (0 : ℝ) < 1 / 2) _)
  have hu_within : Tendsto u atTop (nhdsWithin (0 : ℝ) (Set.Ioi 0)) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within u hu_nhds hu_pos
  have hu_upper : ∀ᶠ n in atTop, φ (u n) / u n ≤ L := hu_within.eventually hupper
  have hu_lower : ∀ᶠ n in atTop, L < φ (u n) / u n := by
    refine Filter.Eventually.of_forall ?_
    intro n
    have hratio :=
      ratio_ge_at_dyadics_of_midpoint_zero hmid h0 ht1 n
    exact lt_of_lt_of_le hgt hratio
  rcases Filter.Eventually.exists (hu_upper.and hu_lower) with ⟨n, hle, hlt⟩
  linarith

/-- A function that equals `0` at the origin but stays uniformly above a positive level on
`(0,1]` cannot be continuous at `0`. This packages the contradiction pattern behind the
finite-penalty AES argument. -/
theorem not_continuousAt_zero_of_uniform_lowerBound_right {φ : ℝ → ℝ} {δ : ℝ}
    (h0 : φ 0 = 0) (hδ : 0 < δ)
    (hpos : ∀ ⦃t : ℝ⦄, 0 < t → t ≤ 1 → δ ≤ φ t) :
    ¬ ContinuousAt φ 0 := by
  intro hcont
  have hwithin : ContinuousWithinAt φ (Set.Ioi (0 : ℝ)) 0 := hcont.continuousWithinAt
  have hnear : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0), φ t < δ / 2 := by
    have : Set.Iio (δ / 2) ∈ nhds (φ 0) := by
      rw [h0]
      exact Iio_mem_nhds (by linarith)
    exact hwithin this
  have hsmall : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0), t < 1 := by
    have hset : Set.Iio (1 : ℝ) ∈ nhdsWithin (0 : ℝ) (Set.Ioi 0) := by
      exact
        (nhdsWithin_le_nhds : nhdsWithin (0 : ℝ) (Set.Ioi 0) ≤ nhds (0 : ℝ))
          (Iio_mem_nhds zero_lt_one)
    have hmem : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0), t ∈ Set.Iio (1 : ℝ) := hset
    exact hmem.mono fun _ ht => ht
  have hposf : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0), 0 < t := by
    exact self_mem_nhdsWithin
  rcases Filter.Eventually.exists (hnear.and (hsmall.and hposf)) with ⟨t, ht, ht1, ht0⟩
  have hδle : δ ≤ φ t := hpos ht0 (le_of_lt ht1)
  linarith

end RatioBridges

section LawReduction

variable {Ω C : Type*} [MeasurableSpace Ω]
variable (P : Measure Ω) [IsProbabilityMeasure P]

/-- By law invariance, a risk functional evaluated on `c 1_A` depends only on the probability of
`A`. -/
theorem lawInvariant_scaledIndicator_eq_of_measure_eq
    {ρ : RandomVariable P → C} (hρ : LawInvariant P ρ) (c : ℝ)
    {A B : Set Ω} (hA : MeasurableSet A) (hB : MeasurableSet B) (hAB : P A = P B) :
    ρ (scaledIndicatorRV P c A hA) = ρ (scaledIndicatorRV P c B hB) := by
  exact hρ.of_identDistrib (P := P)
    (identDistrib_scaledIndicator_of_measure_eq (P := P) c hA hB hAB)

end LawReduction

section ESProfiles

variable {Ω : Type*} [MeasurableSpace Ω]
variable (P : Measure Ω) [IsProbabilityMeasure P]

/-- Target closed form for the paper formula
`ES_p(c 1_A) = c * min (1, t / (1 - p))` on `p < 1`, with the endpoint value `c` at `p = 1`.

This is stored here as a proof-facing object before the full characterization theorem is proved. -/
def indicatorESClosedForm (c t : ℝ) (p : Level) : ℝ :=
  if (p : ℝ) < 1 then
    c * min 1 (t / (1 - (p : ℝ)))
  else
    c

/-- Closed-form `AES` envelope on an indicator position, written directly in terms of the
indicator-level `ES` formula. -/
def indicatorAESClosedForm (g : Level → ℝ) (c t : ℝ) : ℝ :=
  sSup (Set.range fun p : Level => indicatorESClosedForm c t p - g p)

omit [IsProbabilityMeasure P] in
private theorem scaledIndicatorLaw_apply_Iic (c : ℝ) {A : Set Ω} (x : ℝ) :
    scaledIndicatorLaw P c A (Set.Iic x) =
      (if c ≤ x then P A else 0) + (if 0 ≤ x then P Aᶜ else 0) := by
  rw [scaledIndicatorLaw, Measure.add_apply, Measure.smul_apply, Measure.smul_apply,
    Measure.dirac_apply' _ measurableSet_Iic, Measure.dirac_apply' _ measurableSet_Iic]
  by_cases hc : c ≤ x <;> by_cases h0 : 0 ≤ x <;> simp [Set.mem_Iic, hc, h0]

omit [IsProbabilityMeasure P] in
private theorem scaledIndicatorLaw_apply (c : ℝ) {A : Set Ω} {s : Set ℝ} (hs : MeasurableSet s) :
    scaledIndicatorLaw P c A s =
      s.indicator (fun _ => P A) c + s.indicator (fun _ => P Aᶜ) 0 := by
  rw [scaledIndicatorLaw, Measure.add_apply, Measure.smul_apply, Measure.smul_apply,
    Measure.dirac_apply' _ hs, Measure.dirac_apply' _ hs]
  by_cases hc : c ∈ s <;> by_cases h0 : (0 : ℝ) ∈ s <;> simp [hc, h0]

private theorem layeredIndicatorLaw_apply_Iic (low high : ℝ) {A D : Set Ω} (x : ℝ) :
    layeredIndicatorLaw P low high A D (Set.Iic x) =
      (if high ≤ x then P A else 0) +
        (if low ≤ x then P (D \ A) else 0) +
          (if 0 ≤ x then P Dᶜ else 0) := by
  rw [layeredIndicatorLaw, Measure.add_apply, Measure.add_apply, Measure.smul_apply,
    Measure.smul_apply, Measure.smul_apply, Measure.dirac_apply' _ measurableSet_Iic,
    Measure.dirac_apply' _ measurableSet_Iic, Measure.dirac_apply' _ measurableSet_Iic]
  by_cases hhigh : high ≤ x <;> by_cases hlow : low ≤ x <;> by_cases h0 : 0 ≤ x <;>
    simp [Set.mem_Iic, hhigh, hlow, h0, add_assoc]

private theorem cdf_layeredIndicatorLaw_of_lt_zero
    (low high : ℝ) (hlow : 0 ≤ low) (hlowhigh : low ≤ high) {A D : Set Ω}
    (hA : MeasurableSet A) (hD : MeasurableSet D) (hAD : A ⊆ D)
    {x : ℝ} (hx : x < 0) :
    ProbabilityTheory.cdf (layeredIndicatorLaw P low high A D) x = 0 := by
  haveI : IsProbabilityMeasure (layeredIndicatorLaw P low high A D) := by
    rw [← law_layeredIndicatorRV_eq_layeredIndicatorLaw (P := P) low high hA hD hAD]
    infer_instance
  rw [ProbabilityTheory.cdf_eq_real, measureReal_def,
    layeredIndicatorLaw_apply_Iic (P := P) low high x]
  have hhighx : ¬ high ≤ x := not_le.mpr (lt_of_lt_of_le hx (le_trans hlow hlowhigh))
  have hlowx : ¬ low ≤ x := not_le.mpr (lt_of_lt_of_le hx hlow)
  have h0x : ¬ 0 ≤ x := not_le.mpr hx
  simp [hhighx, hlowx, h0x]

private theorem cdf_layeredIndicatorLaw_of_nonneg_lt_low
    (low high : ℝ) (_hlow : 0 ≤ low) (hlowhigh : low ≤ high) {A D : Set Ω}
    (hA : MeasurableSet A) (hD : MeasurableSet D) (hAD : A ⊆ D)
    {x : ℝ} (hx0 : 0 ≤ x) (hxlow : x < low) :
    ProbabilityTheory.cdf (layeredIndicatorLaw P low high A D) x = P.real Dᶜ := by
  haveI : IsProbabilityMeasure (layeredIndicatorLaw P low high A D) := by
    rw [← law_layeredIndicatorRV_eq_layeredIndicatorLaw (P := P) low high hA hD hAD]
    infer_instance
  rw [ProbabilityTheory.cdf_eq_real, measureReal_def,
    layeredIndicatorLaw_apply_Iic (P := P) low high x]
  have hhighx : ¬ high ≤ x := not_le.mpr (lt_of_lt_of_le hxlow hlowhigh)
  have hlowx : ¬ low ≤ x := not_le.mpr hxlow
  simp [Measure.real, hhighx, hlowx, hx0]

private theorem cdf_layeredIndicatorLaw_of_low_le_lt_high
    (low high : ℝ) (hlow : 0 ≤ low) (hlowhigh : low ≤ high) {A D : Set Ω}
    (hA : MeasurableSet A) (hD : MeasurableSet D) (hAD : A ⊆ D)
    {x : ℝ} (hlowx : low ≤ x) (hxhigh : x < high) :
    ProbabilityTheory.cdf (layeredIndicatorLaw P low high A D) x = P.real Aᶜ := by
  haveI : IsProbabilityMeasure (layeredIndicatorLaw P low high A D) := by
    rw [← law_layeredIndicatorRV_eq_layeredIndicatorLaw (P := P) low high hA hD hAD]
    infer_instance
  have hAc_eq : Aᶜ = (D \ A) ∪ Dᶜ := by
    ext ω
    constructor
    · intro hωAc
      by_cases hωD : ω ∈ D
      · exact Or.inl ⟨hωD, hωAc⟩
      · exact Or.inr hωD
    · intro hω
      rcases hω with hω | hω
      · exact hω.2
      · intro hωA
        exact hω (hAD hωA)
  have hdisj_diff_compl : Disjoint (D \ A) Dᶜ := by
    refine Set.disjoint_left.2 ?_
    intro ω hωDA hωDc
    exact hωDc hωDA.1
  rw [ProbabilityTheory.cdf_eq_real, measureReal_def,
    layeredIndicatorLaw_apply_Iic (P := P) low high x]
  have hhighx : ¬ high ≤ x := not_le.mpr hxhigh
  have hx0 : 0 ≤ x := le_trans hlow hlowx
  have hsum : P (D \ A) + P Dᶜ = P Aᶜ := by
    rw [← measure_union hdisj_diff_compl hD.compl, hAc_eq]
  simp [Measure.real, hhighx, hlowx, hx0, hsum]

private theorem cdf_layeredIndicatorLaw_of_le_high
    (low high : ℝ) (hlow : 0 ≤ low) (hlowhigh : low ≤ high) {A D : Set Ω}
    (hA : MeasurableSet A) (hD : MeasurableSet D) (hAD : A ⊆ D)
    {x : ℝ} (hhighx : high ≤ x) :
    ProbabilityTheory.cdf (layeredIndicatorLaw P low high A D) x = 1 := by
  haveI : IsProbabilityMeasure (layeredIndicatorLaw P low high A D) := by
    rw [← law_layeredIndicatorRV_eq_layeredIndicatorLaw (P := P) low high hA hD hAD]
    infer_instance
  rw [ProbabilityTheory.cdf_eq_real, measureReal_def,
    layeredIndicatorLaw_apply_Iic (P := P) low high x]
  have hlowx : low ≤ x := le_trans hlowhigh hhighx
  have hx0 : 0 ≤ x := le_trans hlow hlowx
  have hdisj_A_diff : Disjoint A (D \ A) := by
    refine Set.disjoint_left.2 ?_
    intro ω hωA hωDA
    exact hωDA.2 hωA
  have hdisj_union_compl : Disjoint (A ∪ (D \ A)) Dᶜ := by
    refine Set.disjoint_left.2 ?_
    intro ω hω hωDc
    rcases hω with hωA | hωDA
    · exact hωDc (hAD hωA)
    · exact hωDc hωDA.1
  have hsum : P A + P (D \ A) + P Dᶜ = 1 := by
    calc
      P A + P (D \ A) + P Dᶜ = P (A ∪ (D \ A)) + P Dᶜ := by
        rw [measure_union hdisj_A_diff (hD.diff hA)]
      _ = P ((A ∪ (D \ A)) ∪ Dᶜ) := by
        rw [measure_union hdisj_union_compl hD.compl]
      _ = P Set.univ := by
        congr
        ext ω
        constructor
        · intro hω
          simp
        · intro hω
          by_cases hωD : ω ∈ D
          · by_cases hωA : ω ∈ A
            · exact Or.inl (Or.inl hωA)
            · exact Or.inl (Or.inr ⟨hωD, hωA⟩)
          · exact Or.inr hωD
      _ = 1 := by simp
  simp [hhighx, hlowx, hx0, hsum]

private theorem distLowerQuantile_layeredIndicator_eq_indicator
    (low high : ℝ) (hlow : 0 < low) (hlowhigh : low < high) {A D : Set Ω}
    (hA : MeasurableSet A) (hD : MeasurableSet D) (hAD : A ⊆ D) {q : ℝ}
    (hq : q ∈ Set.Ioc (0 : ℝ) 1) :
    distLowerQuantile (law P (layeredIndicatorRV P low high A D hA hD)) q =
      (Set.Ioc (P.real Dᶜ) 1).indicator (fun _ => low) q +
        (Set.Ioc (P.real Aᶜ) 1).indicator (fun _ => high - low) q := by
  haveI : IsProbabilityMeasure (layeredIndicatorLaw P low high A D) := by
    rw [← law_layeredIndicatorRV_eq_layeredIndicatorLaw (P := P) low high hA hD hAD]
    infer_instance
  have hlow_nonneg : 0 ≤ low := le_of_lt hlow
  have hlowhigh_le : low ≤ high := le_of_lt hlowhigh
  have hDc_le_Ac : P.real Dᶜ ≤ P.real Aᶜ := by
    have hmono : P Dᶜ ≤ P Aᶜ := measure_mono (by
      intro ω hωD
      intro hωA
      exact hωD (hAD hωA))
    exact ENNReal.toReal_mono (measure_ne_top _ _) hmono
  have hlayered :
      distLowerQuantile (layeredIndicatorLaw P low high A D) q =
        (Set.Ioc (P.real Dᶜ) 1).indicator (fun _ => low) q +
          (Set.Ioc (P.real Aᶜ) 1).indicator (fun _ => high - low) q := by
    by_cases hqD : q ≤ P.real Dᶜ
    · have hq_not_mem_D : q ∉ Set.Ioc (P.real Dᶜ) 1 := by
        simp [Set.mem_Ioc, hqD]
      have hq_not_mem_A : q ∉ Set.Ioc (P.real Aᶜ) 1 := by
        simp [Set.mem_Ioc, le_trans hqD hDc_le_Ac]
      rw [Set.indicator_of_notMem hq_not_mem_D, Set.indicator_of_notMem hq_not_mem_A]
      apply le_antisymm
      · apply csInf_le
        · exact upperLevelSet_bddBelow (layeredIndicatorLaw P low high A D) hq.1
        · have hcdf0 :
              ProbabilityTheory.cdf (layeredIndicatorLaw P low high A D) 0 = P.real Dᶜ :=
            cdf_layeredIndicatorLaw_of_nonneg_lt_low (P := P) low high hlow_nonneg hlowhigh_le
              hA hD hAD (show (0 : ℝ) ≤ 0 by simp) hlow
          simpa [hcdf0] using hqD
      · apply le_csInf
        · refine ⟨0, ?_⟩
          have hcdf0 :
              ProbabilityTheory.cdf (layeredIndicatorLaw P low high A D) 0 = P.real Dᶜ :=
            cdf_layeredIndicatorLaw_of_nonneg_lt_low (P := P) low high hlow_nonneg hlowhigh_le
              hA hD hAD (show (0 : ℝ) ≤ 0 by simp) hlow
          simpa [hcdf0] using hqD
        · intro x hx
          by_contra hx_nonneg
          have hxlt : x < 0 := by
            exact lt_of_not_ge (by simpa using hx_nonneg)
          have hcdfx :
              ProbabilityTheory.cdf (layeredIndicatorLaw P low high A D) x = 0 :=
            cdf_layeredIndicatorLaw_of_lt_zero (P := P) low high hlow_nonneg hlowhigh_le
              hA hD hAD hxlt
          have : q ≤ 0 := by simpa [hcdfx] using hx
          exact (not_le_of_gt hq.1) this
    · have hqD' : P.real Dᶜ < q := lt_of_not_ge hqD
      by_cases hqA : q ≤ P.real Aᶜ
      · have hq_mem_D : q ∈ Set.Ioc (P.real Dᶜ) 1 := ⟨hqD', hq.2⟩
        have hq_not_mem_A : q ∉ Set.Ioc (P.real Aᶜ) 1 := by
          simp [Set.mem_Ioc, hqA]
        rw [Set.indicator_of_mem hq_mem_D, Set.indicator_of_notMem hq_not_mem_A]
        apply le_antisymm
        · apply csInf_le
          · exact upperLevelSet_bddBelow (layeredIndicatorLaw P low high A D) hq.1
          · have hcdf_low :
                ProbabilityTheory.cdf (layeredIndicatorLaw P low high A D) low = P.real Aᶜ :=
              cdf_layeredIndicatorLaw_of_low_le_lt_high (P := P) low high hlow_nonneg hlowhigh_le
                hA hD hAD le_rfl hlowhigh
            simpa [hcdf_low] using hqA
        · apply le_csInf
          · refine ⟨low, ?_⟩
            have hcdf_low :
                ProbabilityTheory.cdf (layeredIndicatorLaw P low high A D) low = P.real Aᶜ :=
              cdf_layeredIndicatorLaw_of_low_le_lt_high (P := P) low high hlow_nonneg hlowhigh_le
                hA hD hAD le_rfl hlowhigh
            simpa [hcdf_low] using hqA
          · intro x hx
            by_contra hlow_le_x
            have hxlt_or : x < 0 ∨ 0 ≤ x ∧ x < low := by
              by_cases hx0 : x < 0
              · exact Or.inl hx0
              · have hxltlow : x < low := by
                  exact lt_of_not_ge (by simpa using hlow_le_x)
                exact Or.inr ⟨le_of_not_gt hx0, hxltlow⟩
            cases hxlt_or with
            | inl hxlt =>
                have hcdfx :
                    ProbabilityTheory.cdf (layeredIndicatorLaw P low high A D) x = 0 :=
                  cdf_layeredIndicatorLaw_of_lt_zero (P := P) low high hlow_nonneg hlowhigh_le
                    hA hD hAD hxlt
                have : q ≤ 0 := by simpa [hcdfx] using hx
                exact (not_le_of_gt hq.1) this
            | inr hxmid =>
                have hcdfx :
                    ProbabilityTheory.cdf (layeredIndicatorLaw P low high A D) x = P.real Dᶜ :=
                  cdf_layeredIndicatorLaw_of_nonneg_lt_low (P := P) low high hlow_nonneg
                    hlowhigh_le hA hD hAD hxmid.1 hxmid.2
                have : q ≤ P.real Dᶜ := by simpa [hcdfx] using hx
                linarith
      · have hqA' : P.real Aᶜ < q := lt_of_not_ge hqA
        have hq_mem_D : q ∈ Set.Ioc (P.real Dᶜ) 1 := ⟨lt_of_le_of_lt hDc_le_Ac hqA', hq.2⟩
        have hq_mem_A : q ∈ Set.Ioc (P.real Aᶜ) 1 := ⟨hqA', hq.2⟩
        rw [Set.indicator_of_mem hq_mem_D, Set.indicator_of_mem hq_mem_A]
        have hsum : low + (high - low) = high := by ring
        rw [hsum]
        apply le_antisymm
        · apply csInf_le
          · exact upperLevelSet_bddBelow (layeredIndicatorLaw P low high A D) hq.1
          · have hcdf_high :
                ProbabilityTheory.cdf (layeredIndicatorLaw P low high A D) high = 1 :=
              cdf_layeredIndicatorLaw_of_le_high (P := P) low high hlow_nonneg hlowhigh_le
                hA hD hAD le_rfl
            have : q ≤ 1 := hq.2
            simpa [hcdf_high] using this
        · apply le_csInf
          · refine ⟨high, ?_⟩
            have hcdf_high :
                ProbabilityTheory.cdf (layeredIndicatorLaw P low high A D) high = 1 :=
              cdf_layeredIndicatorLaw_of_le_high (P := P) low high hlow_nonneg hlowhigh_le
                hA hD hAD le_rfl
            have : q ≤ 1 := hq.2
            simpa [hcdf_high] using this
          · intro x hx
            by_contra hhigh_le_x
            have hxlt_or : x < 0 ∨ 0 ≤ x ∧ x < low ∨ low ≤ x ∧ x < high := by
              by_cases hx0 : x < 0
              · exact Or.inl hx0
              · have hx0' : 0 ≤ x := le_of_not_gt hx0
                by_cases hxl : x < low
                · exact Or.inr (Or.inl ⟨hx0', hxl⟩)
                · exact Or.inr (Or.inr ⟨le_of_not_gt hxl, lt_of_not_ge hhigh_le_x⟩)
            cases hxlt_or with
            | inl hxlt =>
                have hcdfx :
                    ProbabilityTheory.cdf (layeredIndicatorLaw P low high A D) x = 0 :=
                  cdf_layeredIndicatorLaw_of_lt_zero (P := P) low high hlow_nonneg hlowhigh_le
                    hA hD hAD hxlt
                have : q ≤ 0 := by simpa [hcdfx] using hx
                exact (not_le_of_gt hq.1) this
            | inr hrest =>
                cases hrest with
                | inl hxmid =>
                    have hcdfx :
                        ProbabilityTheory.cdf (layeredIndicatorLaw P low high A D) x = P.real Dᶜ :=
                      cdf_layeredIndicatorLaw_of_nonneg_lt_low (P := P) low high hlow_nonneg
                        hlowhigh_le hA hD hAD hxmid.1 hxmid.2
                    have : q ≤ P.real Dᶜ := by simpa [hcdfx] using hx
                    linarith [hDc_le_Ac, hqA']
                | inr hxh =>
                    have hcdfx :
                        ProbabilityTheory.cdf (layeredIndicatorLaw P low high A D) x = P.real Aᶜ :=
                      cdf_layeredIndicatorLaw_of_low_le_lt_high (P := P) low high hlow_nonneg
                        hlowhigh_le hA hD hAD hxh.1 hxh.2
                    have : q ≤ P.real Aᶜ := by simpa [hcdfx] using hx
                    linarith
  simpa [law_layeredIndicatorRV_eq_layeredIndicatorLaw (P := P) low high hA hD hAD] using hlayered

private theorem cdf_scaledIndicatorLaw_of_lt_zero (c : ℝ) (hc : 0 ≤ c) {A : Set Ω}
    (hA : MeasurableSet A) {x : ℝ} (hx : x < 0) :
    ProbabilityTheory.cdf (scaledIndicatorLaw P c A) x = 0 := by
  haveI : IsProbabilityMeasure (scaledIndicatorLaw P c A) := by
    rw [← law_scaledIndicatorRV_eq_scaledIndicatorLaw (P := P) (c := c) hA]
    infer_instance
  rw [ProbabilityTheory.cdf_eq_real, measureReal_def, scaledIndicatorLaw_apply_Iic (P := P) c x]
  have hcx : ¬ c ≤ x := not_le.mpr (lt_of_lt_of_le hx hc)
  have h0x : ¬ 0 ≤ x := not_le.mpr hx
  simp [hcx, h0x]

private theorem cdf_scaledIndicatorLaw_of_nonneg_lt (c : ℝ) {A : Set Ω}
    (hA : MeasurableSet A) {x : ℝ} (hx0 : 0 ≤ x) (hxc : x < c) :
    ProbabilityTheory.cdf (scaledIndicatorLaw P c A) x = P.real Aᶜ := by
  haveI : IsProbabilityMeasure (scaledIndicatorLaw P c A) := by
    rw [← law_scaledIndicatorRV_eq_scaledIndicatorLaw (P := P) (c := c) hA]
    infer_instance
  rw [ProbabilityTheory.cdf_eq_real, measureReal_def, scaledIndicatorLaw_apply_Iic (P := P) c x]
  have hcx : ¬ c ≤ x := not_le.mpr hxc
  simp [Measure.real, hcx, hx0]

private theorem cdf_scaledIndicatorLaw_of_le (c : ℝ) (hc : 0 ≤ c) {A : Set Ω}
    (hA : MeasurableSet A) {x : ℝ} (hcx : c ≤ x) :
    ProbabilityTheory.cdf (scaledIndicatorLaw P c A) x = 1 := by
  haveI : IsProbabilityMeasure (scaledIndicatorLaw P c A) := by
    rw [← law_scaledIndicatorRV_eq_scaledIndicatorLaw (P := P) (c := c) hA]
    infer_instance
  rw [ProbabilityTheory.cdf_eq_real, measureReal_def, scaledIndicatorLaw_apply_Iic (P := P) c x]
  have h0x : 0 ≤ x := hc.trans hcx
  simp [hcx, h0x, prob_add_prob_compl (μ := P) hA]

private theorem distLowerQuantile_scaledIndicator_eq_indicator (c : ℝ) (hc : 0 < c)
    {A : Set Ω} (hA : MeasurableSet A) (hA_pos : P A ≠ 0) {q : ℝ}
    (hq : q ∈ Set.Ioc (0 : ℝ) 1) :
    distLowerQuantile (law P (scaledIndicatorRV P c A hA)) q =
      (Set.Ioc (1 - P.real A) 1).indicator (fun _ => c) q := by
  haveI : IsProbabilityMeasure (scaledIndicatorLaw P c A) := by
    rw [← law_scaledIndicatorRV_eq_scaledIndicatorLaw (P := P) (c := c) hA]
    infer_instance
  have hscaled :
      distLowerQuantile (scaledIndicatorLaw P c A) q =
        (Set.Ioc (1 - P.real A) 1).indicator (fun _ => c) q := by
    have hc_nonneg : 0 ≤ c := le_of_lt hc
    have hA_real_ne : P.real A ≠ 0 := by
      intro h_real
      apply hA_pos
      exact (measureReal_eq_zero_iff (μ := P)).mp h_real
    have hA_real_pos : 0 < P.real A := lt_of_le_of_ne (by positivity) hA_real_ne.symm
    have hA_compl_real : P.real Aᶜ = 1 - P.real A := by
      linarith [probReal_add_probReal_compl (μ := P) hA]
    by_cases hqA : q ≤ 1 - P.real A
    · have hq_not_mem : q ∉ Set.Ioc (1 - P.real A) 1 := by
        simp [Set.mem_Ioc, hqA]
      rw [Set.indicator_of_notMem hq_not_mem]
      apply le_antisymm
      · apply csInf_le
        · exact upperLevelSet_bddBelow (scaledIndicatorLaw P c A) hq.1
        · have hcdf0 :
              ProbabilityTheory.cdf (scaledIndicatorLaw P c A) 0 = P.real Aᶜ :=
            cdf_scaledIndicatorLaw_of_nonneg_lt (P := P) c hA (show (0 : ℝ) ≤ 0 by simp) hc
          simpa [hcdf0, hA_compl_real] using hqA
      · apply le_csInf
        · refine ⟨0, ?_⟩
          have hcdf0 :
              ProbabilityTheory.cdf (scaledIndicatorLaw P c A) 0 = P.real Aᶜ :=
            cdf_scaledIndicatorLaw_of_nonneg_lt (P := P) c hA (show (0 : ℝ) ≤ 0 by simp) hc
          simpa [hcdf0, hA_compl_real] using hqA
        · intro x hx
          by_contra hx_nonneg
          have hxlt : x < 0 := lt_of_not_ge hx_nonneg
          have hcdfx :
              ProbabilityTheory.cdf (scaledIndicatorLaw P c A) x = 0 :=
            cdf_scaledIndicatorLaw_of_lt_zero (P := P) c hc_nonneg hA hxlt
          have : q ≤ 0 := by simpa [hcdfx] using hx
          exact (not_le_of_gt hq.1) this
    · have hqA' : 1 - P.real A < q := lt_of_not_ge hqA
      have hq_mem : q ∈ Set.Ioc (1 - P.real A) 1 := ⟨hqA', hq.2⟩
      rw [Set.indicator_of_mem hq_mem]
      apply le_antisymm
      · apply csInf_le
        · exact upperLevelSet_bddBelow (scaledIndicatorLaw P c A) hq.1
        · have hcdfc :
              ProbabilityTheory.cdf (scaledIndicatorLaw P c A) c = 1 :=
            cdf_scaledIndicatorLaw_of_le (P := P) c hc_nonneg hA le_rfl
          have : q ≤ 1 := hq.2
          simpa [hcdfc] using this
      · apply le_csInf
        · refine ⟨c, ?_⟩
          have hcdfc :
              ProbabilityTheory.cdf (scaledIndicatorLaw P c A) c = 1 :=
            cdf_scaledIndicatorLaw_of_le (P := P) c hc_nonneg hA le_rfl
          have : q ≤ 1 := hq.2
          simpa [hcdfc] using this
        · intro x hx
          by_contra hcx
          have hxlt_or : x < 0 ∨ 0 ≤ x ∧ x < c := by
            by_cases hx0 : x < 0
            · exact Or.inl hx0
            · exact Or.inr ⟨le_of_not_gt hx0, lt_of_not_ge hcx⟩
          cases hxlt_or with
          | inl hxlt =>
              have hcdfx :
                  ProbabilityTheory.cdf (scaledIndicatorLaw P c A) x = 0 :=
                cdf_scaledIndicatorLaw_of_lt_zero (P := P) c hc_nonneg hA hxlt
              have : q ≤ 0 := by simpa [hcdfx] using hx
              exact (not_le_of_gt hq.1) this
          | inr hxmid =>
              have hcdfx :
                  ProbabilityTheory.cdf (scaledIndicatorLaw P c A) x = P.real Aᶜ :=
                cdf_scaledIndicatorLaw_of_nonneg_lt (P := P) c hA hxmid.1 hxmid.2
              have : q ≤ P.real Aᶜ := by simpa [hcdfx] using hx
              linarith [hA_compl_real, hqA']
  simpa [law_scaledIndicatorRV_eq_scaledIndicatorLaw (P := P) (c := c) hA] using hscaled

private theorem distESIntegral_scaledIndicator_eq (p : Level) (c : ℝ) (hc : 0 < c)
    {A : Set Ω} (hA : MeasurableSet A) (hA_pos : P A ≠ 0) :
    distESIntegral (law P (scaledIndicatorRV P c A hA)) p = c * min (1 - (p : ℝ)) (P.real A) := by
  haveI : IsProbabilityMeasure (scaledIndicatorLaw P c A) := by
    rw [← law_scaledIndicatorRV_eq_scaledIndicatorLaw (P := P) (c := c) hA]
    infer_instance
  have hscaled :
      distESIntegral (scaledIndicatorLaw P c A) p = c * min (1 - (p : ℝ)) (P.real A) := by
    have hp_le : (p : ℝ) ≤ 1 := p.2.2
    have hp_nonneg : 0 ≤ (p : ℝ) := p.2.1
    have hA_real_pos : 0 < P.real A := by
      have hA_real_ne : P.real A ≠ 0 := by
        intro h_real
        apply hA_pos
        exact (measureReal_eq_zero_iff (μ := P)).mp h_real
      exact lt_of_le_of_ne (by positivity) hA_real_ne.symm
    have h_step :
        Set.EqOn (distLowerQuantile (scaledIndicatorLaw P c A))
          ((Set.Ioc (1 - P.real A) 1).indicator (fun _ => c)) (Set.Ioc (p : ℝ) 1) := by
      intro q hq
      have hq' : q ∈ Set.Ioc (0 : ℝ) 1 := ⟨lt_of_le_of_lt hp_nonneg hq.1, hq.2⟩
      simpa [law_scaledIndicatorRV_eq_scaledIndicatorLaw (P := P) (c := c) hA] using
        (distLowerQuantile_scaledIndicator_eq_indicator (P := P) c hc hA hA_pos hq')
    rw [distESIntegral, intervalIntegral.integral_of_le hp_le]
    rw [setIntegral_congr_fun measurableSet_Ioc h_step]
    by_cases hpA : 1 - P.real A ≤ (p : ℝ)
    · have hconst :
          Set.EqOn ((Set.Ioc (1 - P.real A) 1).indicator (fun _ => c)) (fun _ => c)
            (Set.Ioc (p : ℝ) 1) := by
          intro q hq
          have hq_mem : q ∈ Set.Ioc (1 - P.real A) 1 := ⟨lt_of_le_of_lt hpA hq.1, hq.2⟩
          simp [Set.indicator_of_mem hq_mem]
      rw [setIntegral_congr_fun measurableSet_Ioc hconst, setIntegral_const]
      have hvol : volume.real (Set.Ioc (p : ℝ) 1) = 1 - (p : ℝ) :=
        Real.volume_real_Ioc_of_le hp_le
      have hmin' : 1 - (p : ℝ) ≤ P.real A := by linarith
      rw [min_eq_left hmin']
      simp [hvol, smul_eq_mul, mul_comm]
    · have hpA' : (p : ℝ) < 1 - P.real A := lt_of_not_ge hpA
      rw [integral_indicator_const _ measurableSet_Ioc]
      rw [measureReal_restrict_apply measurableSet_Ioc]
      have h_inter :
          Set.Ioc (1 - P.real A) 1 ∩ Set.Ioc (p : ℝ) 1 = Set.Ioc (1 - P.real A) 1 := by
        ext q
        constructor
        · intro hq
          exact hq.1
        · intro hq
          exact ⟨hq, ⟨lt_trans hpA' hq.1, hq.2⟩⟩
      have hvol : volume.real (Set.Ioc (1 - P.real A) 1) = P.real A := by
        rw [Real.volume_real_Ioc_of_le]
        · ring
        · linarith
      have hmin' : P.real A < 1 - (p : ℝ) := by linarith
      rw [min_eq_right (le_of_lt hmin')]
      simp [h_inter, hvol, smul_eq_mul, mul_comm]
  simpa [law_scaledIndicatorRV_eq_scaledIndicatorLaw (P := P) (c := c) hA] using hscaled

/-- Closed form of `ES` on an indicator position `c 1_A` with positive payoff and non-null event. -/
theorem ES_scaledIndicatorRV_eq_indicatorESClosedForm (p : Level) (c : ℝ) (hc : 0 < c)
    {A : Set Ω} (hA : MeasurableSet A) (hA_pos : P A ≠ 0) :
    ES P p (scaledIndicatorRV P c A hA) = indicatorESClosedForm c (P.real A) p := by
  by_cases hp : (p : ℝ) < 1
  · have hmain :
        (1 - (p : ℝ))⁻¹ * distESIntegral (law P (scaledIndicatorRV P c A hA)) p =
          c * min 1 (P.real A / (1 - (p : ℝ))) := by
      rw [distESIntegral_scaledIndicator_eq (P := P) p c hc hA hA_pos]
      have hp_pos : 0 < 1 - (p : ℝ) := sub_pos.mpr hp
      have hp_ne : 1 - (p : ℝ) ≠ 0 := ne_of_gt hp_pos
      by_cases hmin : 1 - (p : ℝ) ≤ P.real A
      · rw [min_eq_left hmin, min_eq_left]
        · field_simp [hp_ne]
        · rw [one_le_div₀ hp_pos]
          linarith
      · have hlt : P.real A < 1 - (p : ℝ) := lt_of_not_ge hmin
        rw [min_eq_right (le_of_lt hlt), min_eq_right]
        · field_simp [hp_ne]
        · rw [div_le_one hp_pos]
          linarith
    simpa [ES, distES, indicatorESClosedForm, hp] using hmain
  · have hmain :
        distUpperQuantile (law P (scaledIndicatorRV P c A hA)) = c := by
      haveI : IsProbabilityMeasure (scaledIndicatorLaw P c A) := by
        rw [← law_scaledIndicatorRV_eq_scaledIndicatorLaw (P := P) (c := c) hA]
        infer_instance
      have hscaled : distUpperQuantile (scaledIndicatorLaw P c A) = c := by
        unfold distUpperQuantile
        rw [essSup_eq_sInf]
        let S : Set ℝ := {a : ℝ | scaledIndicatorLaw P c A {x : ℝ | a < x} = 0}
        have hc_mem : c ∈ S := by
          dsimp [S]
          rw [scaledIndicatorLaw_apply (P := P) (c := c) (A := A)
            (s := {x : ℝ | c < x}) measurableSet_Ioi]
          have hcc : c ∉ {x : ℝ | c < x} := by simp
          have h0c : (0 : ℝ) ∉ {x : ℝ | c < x} := by
            simp [not_lt.mpr (le_of_lt hc)]
          simp [hcc, h0c]
        have hsingleton : scaledIndicatorLaw P c A ({c} : Set ℝ) = P A := by
          rw [scaledIndicatorLaw_apply (P := P) (c := c) (A := A)
            (s := ({c} : Set ℝ)) (measurableSet_singleton c)]
          have hcc : c ∈ ({c} : Set ℝ) := by simp
          have h0c : (0 : ℝ) ∉ ({c} : Set ℝ) := by
            simpa using (ne_of_gt hc).symm
          simp [hcc, h0c]
        have h_lower : c ∈ lowerBounds S := by
          intro b hb
          by_contra hbc
          have hbc' : b < c := lt_of_not_ge hbc
          have hsubset : ({c} : Set ℝ) ⊆ {x : ℝ | b < x} := by
            intro x hx
            simp only [Set.mem_singleton_iff] at hx
            simp [hx, hbc']
          have hmono : scaledIndicatorLaw P c A ({c} : Set ℝ) ≤
              scaledIndicatorLaw P c A {x : ℝ | b < x} := measure_mono hsubset
          have : P A = 0 := by
            rw [hsingleton, hb] at hmono
            exact le_antisymm hmono bot_le
          exact hA_pos this
        refine le_antisymm ?_ ?_
        · exact csInf_le ⟨c, h_lower⟩ hc_mem
        · exact le_csInf ⟨c, hc_mem⟩ h_lower
      simpa [law_scaledIndicatorRV_eq_scaledIndicatorLaw (P := P) (c := c) hA] using hscaled
    simpa [ES, distES, indicatorESClosedForm, hp] using hmain

/-- Closed form of `AES` on an indicator position `c 1_A`, obtained by substituting the closed
form of `ES` into the `sup` defining `AES`. -/
theorem AES_scaledIndicatorRV_eq_indicatorAESClosedForm (g : Level → ℝ) (c : ℝ) (hc : 0 < c)
    {A : Set Ω} (hA : MeasurableSet A) (hA_pos : P A ≠ 0) :
    AES P g (scaledIndicatorRV P c A hA) = indicatorAESClosedForm g c (P.real A) := by
  unfold AES ESg distESg indicatorAESClosedForm
  congr 1
  ext y
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨z, by
      simpa [ES] using (ES_scaledIndicatorRV_eq_indicatorESClosedForm
        (P := P) z c hc hA hA_pos).symm⟩
  · rintro ⟨z, rfl⟩
    exact ⟨z, by
      simpa [ES] using ES_scaledIndicatorRV_eq_indicatorESClosedForm
        (P := P) z c hc hA hA_pos⟩

/-- Closed form of `ES` on the `L^\infty` indicator model. -/
theorem ESLinf_linfIndicator_eq_indicatorESClosedForm (p : Level) (c : ℝ) (hc : 0 < c)
    {A : Set Ω} (hA : MeasurableSet A) (hA_pos : P A ≠ 0) :
    ESLinf P p (linfIndicator P A hA c) = indicatorESClosedForm c (P.real A) p := by
  rw [ESLinf_linfIndicator_eq_scaledIndicatorRV (P := P) p c hA]
  exact ES_scaledIndicatorRV_eq_indicatorESClosedForm (P := P) p c hc hA hA_pos

/-- Closed form of `AES` on the `L^\infty` indicator model. -/
theorem AES_ofLinf_linfIndicator_eq_indicatorAESClosedForm
    (g : Level → ℝ) (c : ℝ) (hc : 0 < c)
    {A : Set Ω} (hA : MeasurableSet A) (hA_pos : P A ≠ 0) :
    AES P g (RandomVariable.ofLinf (μ := P) (linfIndicator P A hA c)) =
      indicatorAESClosedForm g c (P.real A) := by
  have hlaw :
      law P (RandomVariable.ofLinf (μ := P) (linfIndicator P A hA c)) =
        law P (scaledIndicatorRV P c A hA) := by
    unfold law
    exact Measure.map_congr (ofLinf_linfIndicator_ae_eq_scaledIndicatorRV (P := P) c hA)
  calc
    AES P g (RandomVariable.ofLinf (μ := P) (linfIndicator P A hA c)) =
        AES P g (scaledIndicatorRV P c A hA) :=
      AES_lawInvariant (P := P) g hlaw
    _ = indicatorAESClosedForm g c (P.real A) :=
      AES_scaledIndicatorRV_eq_indicatorAESClosedForm (P := P) g c hc hA hA_pos

/-- The `ES` test profile for `L^\infty` indicator positions. -/
def linfIndicatorESTestProfile (c : ℝ) (A : Set Ω) (hA : MeasurableSet A) : Level → ℝ :=
  fun p => ESLinf P p (linfIndicator P A hA c)

/-- The subtype-based indicator `ES` test profile. -/
def indicatorESTestProfile (c : ℝ) (A : Set Ω) (hA : MeasurableSet A) : Level → ℝ :=
  fun p => ES P p (scaledIndicatorRV P c A hA)

/-- The `L^\infty` and subtype-based indicator `ES` test profiles coincide. -/
theorem linfIndicatorESTestProfile_eq_indicatorESTestProfile (c : ℝ) {A : Set Ω}
    (hA : MeasurableSet A) :
    linfIndicatorESTestProfile P c A hA = indicatorESTestProfile P c A hA := by
  funext p
  exact ESLinf_linfIndicator_eq_scaledIndicatorRV (P := P) p c hA

/-- `ES` on `L^\infty` indicator positions depends only on the event probability. -/
theorem ESLinf_linfIndicator_eq_of_measure_eq (p : Level) (c : ℝ) {A B : Set Ω}
    (hA : MeasurableSet A) (hB : MeasurableSet B) (hAB : P A = P B) :
    ESLinf P p (linfIndicator P A hA c) = ESLinf P p (linfIndicator P B hB c) := by
  calc
    ESLinf P p (linfIndicator P A hA c) = ES P p (scaledIndicatorRV P c A hA) :=
      ESLinf_linfIndicator_eq_scaledIndicatorRV (P := P) p c hA
    _ = ES P p (scaledIndicatorRV P c B hB) := by
      exact lawInvariant_scaledIndicator_eq_of_measure_eq (P := P)
        (ρ := ES P p) (hρ := ES_lawInvariant (P := P) p) c hA hB hAB
    _ = ESLinf P p (linfIndicator P B hB c) := by
      symm
      exact ESLinf_linfIndicator_eq_scaledIndicatorRV (P := P) p c hB

/-- The `L^\infty` indicator `ES` test profile depends only on the event probability. -/
theorem linfIndicatorESTestProfile_eq_of_measure_eq (c : ℝ) {A B : Set Ω}
    (hA : MeasurableSet A) (hB : MeasurableSet B) (hAB : P A = P B) :
    linfIndicatorESTestProfile P c A hA = linfIndicatorESTestProfile P c B hB := by
  funext p
  exact ESLinf_linfIndicator_eq_of_measure_eq (P := P) p c hA hB hAB

end ESProfiles

section EventProfiles

variable {Ω : Type*} [MeasurableSpace Ω]
variable (P : Measure Ω) [IsProbabilityMeasure P]

/-- The event set function induced by testing a risk functional on scaled indicators. Nonmeasurable
sets are sent to `0`; all AES reductions only use the measurable branch. -/
def scaledIndicatorSetFunction (ρ : RandomVariable P → ℝ) (c : ℝ) : Set Ω → ℝ :=
  by
    classical
    exact fun A => if hA : MeasurableSet A then ρ (scaledIndicatorRV P c A hA) else 0

omit [IsProbabilityMeasure P] in
/-- On measurable events, the induced set function is computed by the expected indicator
position. -/
theorem scaledIndicatorSetFunction_apply (ρ : RandomVariable P → ℝ) (c : ℝ) {A : Set Ω}
    (hA : MeasurableSet A) :
    scaledIndicatorSetFunction P ρ c A = ρ (scaledIndicatorRV P c A hA) := by
  classical
  simp [scaledIndicatorSetFunction, hA]

omit [IsProbabilityMeasure P] in
/-- A submodular risk functional yields a submodular event functional on scaled indicators. -/
theorem measurableSetSubmodular_scaledIndicatorSetFunction
    {ρ : RandomVariable P → ℝ} (hρ : Submodular ρ) {c : ℝ} (hc : 0 ≤ c) :
    MeasurableSetSubmodular (scaledIndicatorSetFunction P ρ c) := by
  intro A B hA hB
  rw [scaledIndicatorSetFunction_apply (P := P) ρ c (hA := hA.inter hB),
    scaledIndicatorSetFunction_apply (P := P) ρ c (hA := hA.union hB),
    scaledIndicatorSetFunction_apply (P := P) ρ c (hA := hA),
    scaledIndicatorSetFunction_apply (P := P) ρ c (hA := hB)]
  have hsub := hρ (scaledIndicatorRV P c A hA) (scaledIndicatorRV P c B hB)
  rw [← scaledIndicatorRV_inf_eq_inter (P := P) hc hA hB,
    ← scaledIndicatorRV_sup_eq_union (P := P) hc hA hB] at hsub
  exact hsub

/-- Law invariance implies that the indicator-induced event functional depends only on event
probability. -/
theorem dependsOnlyOnProbability_scaledIndicatorSetFunction
    {ρ : RandomVariable P → ℝ} (hρ : LawInvariant P ρ) (c : ℝ) :
    DependsOnlyOnProbability P (scaledIndicatorSetFunction P ρ c) := by
  intro A B hA hB hAB
  rw [scaledIndicatorSetFunction_apply (P := P) ρ c hA,
    scaledIndicatorSetFunction_apply (P := P) ρ c hB]
  exact lawInvariant_scaledIndicator_eq_of_measure_eq (P := P)
    (ρ := ρ) hρ c hA hB hAB

/-- Combined AES-facing bridge: submodularity on random variables, together with law invariance,
induces decreasing increments for the one-dimensional indicator profile. -/
theorem decreasingIncrements_profileFromProbability_scaledIndicatorSetFunction
    {ρ : RandomVariable P → ℝ} (hsplit : HasFullEventSplitting P)
    (hρsub : Submodular ρ) (hρlaw : LawInvariant P ρ) {c : ℝ} (hc : 0 ≤ c) :
    DecreasingIncrements (profileFromProbability P hsplit (scaledIndicatorSetFunction P ρ c)) := by
  exact decreasingIncrements_of_measurableSetSubmodular_of_dependsOnlyOnProbability (P := P)
    hsplit
    (measurableSetSubmodular_scaledIndicatorSetFunction (P := P) hρsub hc)
    (dependsOnlyOnProbability_scaledIndicatorSetFunction (P := P) hρlaw c)

/-- The AES-specific indicator set function. -/
abbrev indicatorAESSetFunction (g : Level → ℝ) (c : ℝ) : Set Ω → ℝ :=
  scaledIndicatorSetFunction P (AES P g) c

/-- The one-dimensional profile extracted from AES on indicator positions. -/
noncomputable def indicatorAESProbabilityProfile
    (hsplit : HasFullEventSplitting P) (g : Level → ℝ) (c : ℝ) : ℝ → ℝ :=
  profileFromProbability P hsplit (indicatorAESSetFunction P g c)

/-- If `AES` is submodular, then its indicator probability profile has decreasing increments. -/
theorem decreasingIncrements_indicatorAESProbabilityProfile
    (hsplit : HasFullEventSplitting P) (g : Level → ℝ) {c : ℝ} (hc : 0 ≤ c)
    (hsub : Submodular (AES P g)) :
    DecreasingIncrements (indicatorAESProbabilityProfile P hsplit g c) := by
  simpa [indicatorAESProbabilityProfile, indicatorAESSetFunction] using
    (decreasingIncrements_profileFromProbability_scaledIndicatorSetFunction
      (P := P) (ρ := AES P g) hsplit hsub (AES_lawInvariant (P := P) g) hc)

/-- The indicator probability profile extracted from a submodular `AES` satisfies the midpoint
concavity inequality on `[0,1]`. This is the first concavity consequence used in the final
characterization argument. -/
theorem midpoint_ge_average_indicatorAESProbabilityProfile
    (hsplit : HasFullEventSplitting P) (g : Level → ℝ) {c : ℝ} (hc : 0 ≤ c)
    (hsub : Submodular (AES P g)) {x y : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) 1) (hy : y ∈ Set.Icc (0 : ℝ) 1) :
    indicatorAESProbabilityProfile P hsplit g c (midpoint ℝ x y) ≥
      midpoint ℝ (indicatorAESProbabilityProfile P hsplit g c x)
        (indicatorAESProbabilityProfile P hsplit g c y) := by
  exact midpoint_ge_average_of_decreasingIncrements
    (decreasingIncrements_indicatorAESProbabilityProfile (P := P) hsplit g hc hsub) hx hy

/-- On strictly positive masses, the chosen AES indicator profile agrees with the closed-form
envelope already computed for indicator positions. -/
theorem indicatorAESProbabilityProfile_eq_indicatorAESClosedForm
    (hsplit : HasFullEventSplitting P) (g : Level → ℝ) (c : ℝ) (hc : 0 < c)
    {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) :
    indicatorAESProbabilityProfile P hsplit g c t = indicatorAESClosedForm g c t := by
  let A : Set Ω := Classical.choose (exists_measurableSet_measureReal_eq
    (P := P) hsplit (le_of_lt ht0) ht1)
  have hA : MeasurableSet A :=
    (Classical.choose_spec (exists_measurableSet_measureReal_eq
      (P := P) hsplit (le_of_lt ht0) ht1)).1
  have hAreal : P.real A = t :=
    (Classical.choose_spec (exists_measurableSet_measureReal_eq
      (P := P) hsplit (le_of_lt ht0) ht1)).2
  have hA_pos : P A ≠ 0 := by
    intro hPA
    have hreal0 : P.real A = 0 := (measureReal_eq_zero_iff (μ := P)).mpr hPA
    linarith [hAreal, ht0]
  rw [indicatorAESProbabilityProfile, profileFromProbability_eq (P := P) hsplit
    (indicatorAESSetFunction P g c) (le_of_lt ht0) ht1]
  change scaledIndicatorSetFunction P (AES P g) c A = indicatorAESClosedForm g c t
  rw [scaledIndicatorSetFunction_apply (P := P) (ρ := AES P g) c hA]
  simpa [indicatorAESSetFunction, hAreal] using
    AES_scaledIndicatorRV_eq_indicatorAESClosedForm (P := P) g c hc hA hA_pos

/-- At the origin, the AES indicator probability profile vanishes under the normalized penalty
assumptions `g(0) = 0` and `g ≥ 0`. -/
theorem indicatorAESProbabilityProfile_zero_eq_zero
    (hsplit : HasFullEventSplitting P) (g : Level → ℝ) (c : ℝ)
    (hg0 : g 0 = 0) (hgnonneg : ∀ p : Level, 0 ≤ g p) :
    indicatorAESProbabilityProfile P hsplit g c 0 = 0 := by
  have hprofile :
      EventProfile P (indicatorAESSetFunction P g c)
        (indicatorAESProbabilityProfile P hsplit g c) :=
    EventProfile.of_dependsOnlyOnProbability (P := P) hsplit
      (dependsOnlyOnProbability_scaledIndicatorSetFunction (P := P) (ρ := AES P g)
        (AES_lawInvariant (P := P) g) c)
  have hempty :
      indicatorAESSetFunction P g c ∅ = indicatorAESProbabilityProfile P hsplit g c 0 := by
    simpa [indicatorAESProbabilityProfile, indicatorAESSetFunction, Measure.real] using
      (hprofile (A := ∅) MeasurableSet.empty)
  have happly :
      indicatorAESSetFunction P g c ∅ = AES P g (scaledIndicatorRV P c ∅ MeasurableSet.empty) := by
    simpa [indicatorAESSetFunction] using
      (scaledIndicatorSetFunction_apply (P := P) (ρ := AES P g) c (A := ∅) MeasurableSet.empty)
  rw [← hempty, happly, scaledIndicatorRV_empty_eq_zero]
  exact AES_zero_eq_zero (P := P) g hg0 hgnonneg

/-- The two-level test position used in the revised finite-penalty AES argument. -/
def finiteCounterexampleX (P : Measure Ω) (eps lam : ℝ) (A B C : Set Ω)
    (hA : MeasurableSet A) (hB : MeasurableSet B) (hC : MeasurableSet C) :
    RandomVariable P :=
  layeredIndicatorRV P eps lam A (A ∪ (B ∪ C)) hA (hA.union (hB.union hC))

/-- The pure-indicator test position used in the revised finite-penalty AES argument. -/
def finiteCounterexampleY (P : Measure Ω) (lam : ℝ) (A B : Set Ω)
    (hA : MeasurableSet A) (hB : MeasurableSet B) :
    RandomVariable P :=
  scaledIndicatorRV P lam (A ∪ B) (hA.union hB)

/-- The revised finite counterexample `X` has the expected three-point law. -/
theorem law_finiteCounterexampleX_eq_layeredIndicatorLaw
    (P : Measure Ω) [IsProbabilityMeasure P] (eps lam : ℝ) {A B C : Set Ω}
    (hA : MeasurableSet A) (hB : MeasurableSet B) (hC : MeasurableSet C) :
    law P (finiteCounterexampleX P eps lam A B C hA hB hC) =
      layeredIndicatorLaw P eps lam A (A ∪ (B ∪ C)) := by
  unfold finiteCounterexampleX
  exact law_layeredIndicatorRV_eq_layeredIndicatorLaw (P := P) eps lam hA
    (hA.union (hB.union hC)) (by intro ω hω; exact Or.inl hω)

/-- The revised finite counterexample `Y` is still a plain scaled indicator. -/
theorem law_finiteCounterexampleY_eq_scaledIndicatorLaw
    (P : Measure Ω) [IsProbabilityMeasure P] (lam : ℝ) {A B : Set Ω}
    (hA : MeasurableSet A) (hB : MeasurableSet B) :
    law P (finiteCounterexampleY P lam A B hA hB) =
      scaledIndicatorLaw P lam (A ∪ B) := by
  unfold finiteCounterexampleY
  exact law_scaledIndicatorRV_eq_scaledIndicatorLaw (P := P) lam (hA.union hB)

/-- The pointwise maximum of the finite-penalty test pair enlarges the high-payoff region from
`A` to `A ∪ B`. -/
theorem finiteCounterexample_sup
    (P : Measure Ω) {eps lam : ℝ} (heps : 0 ≤ eps) (hepslam : eps ≤ lam)
    {A B C : Set Ω} (hA : MeasurableSet A) (hB : MeasurableSet B) (hC : MeasurableSet C) :
    finiteCounterexampleX P eps lam A B C hA hB hC ⊔ finiteCounterexampleY P lam A B hA hB =
      layeredIndicatorRV P eps lam (A ∪ B) (A ∪ (B ∪ C))
        (hA.union hB) (hA.union (hB.union hC)) := by
  unfold finiteCounterexampleX finiteCounterexampleY
  symm
  refine layeredIndicatorRV_sup_eq_layeredIndicatorRV (P := P) heps hepslam
    (hA := hA) (hE := hA.union hB) (hD := hA.union (hB.union hC)) ?_ ?_
  · intro ω hω
    exact Or.inl hω
  · intro ω hω
    rcases hω with hω | hω
    · exact Or.inl hω
    · exact Or.inr (Or.inl hω)

/-- The pointwise minimum of the finite-penalty test pair cuts the support down from
`A ∪ B ∪ C` to `A ∪ B`, while keeping the high-payoff region equal to `A`. -/
theorem finiteCounterexample_inf
    (P : Measure Ω) {eps lam : ℝ} (heps : 0 ≤ eps) (hepslam : eps ≤ lam)
    {A B C : Set Ω} (hA : MeasurableSet A) (hB : MeasurableSet B) (hC : MeasurableSet C) :
    finiteCounterexampleX P eps lam A B C hA hB hC ⊓ finiteCounterexampleY P lam A B hA hB =
      layeredIndicatorRV P eps lam A (A ∪ B) hA (hA.union hB) := by
  unfold finiteCounterexampleX finiteCounterexampleY
  symm
  refine layeredIndicatorRV_inf_eq_layeredIndicatorRV (P := P) heps hepslam
    (hA := hA) (hE := hA.union hB) (hD := hA.union (hB.union hC)) ?_ ?_
  · intro ω hω
    exact Or.inl hω
  · intro ω hω
    rcases hω with hω | hω
    · exact Or.inl hω
    · exact Or.inr (Or.inl hω)

/-- The pointwise maximum in the revised finite counterexample again has a three-point law. -/
theorem law_finiteCounterexample_sup_eq_layeredIndicatorLaw
    (P : Measure Ω) [IsProbabilityMeasure P] {eps lam : ℝ} (heps : 0 ≤ eps)
    (hepslam : eps ≤ lam) {A B C : Set Ω}
    (hA : MeasurableSet A) (hB : MeasurableSet B) (hC : MeasurableSet C) :
    law P (finiteCounterexampleX P eps lam A B C hA hB hC ⊔
      finiteCounterexampleY P lam A B hA hB) =
      layeredIndicatorLaw P eps lam (A ∪ B) (A ∪ (B ∪ C)) := by
  rw [finiteCounterexample_sup (P := P) heps hepslam hA hB hC]
  exact law_layeredIndicatorRV_eq_layeredIndicatorLaw (P := P) eps lam (hA.union hB)
    (hA.union (hB.union hC)) (by
      intro ω hω
      rcases hω with hω | hω
      · exact Or.inl hω
      · exact Or.inr (Or.inl hω))

/-- The pointwise minimum in the revised finite counterexample also has an explicit three-point
law. -/
theorem law_finiteCounterexample_inf_eq_layeredIndicatorLaw
    (P : Measure Ω) [IsProbabilityMeasure P] {eps lam : ℝ} (heps : 0 ≤ eps)
    (hepslam : eps ≤ lam) {A B C : Set Ω}
    (hA : MeasurableSet A) (hB : MeasurableSet B) (hC : MeasurableSet C) :
    law P (finiteCounterexampleX P eps lam A B C hA hB hC ⊓
      finiteCounterexampleY P lam A B hA hB) =
      layeredIndicatorLaw P eps lam A (A ∪ B) := by
  rw [finiteCounterexample_inf (P := P) heps hepslam hA hB hC]
  exact law_layeredIndicatorRV_eq_layeredIndicatorLaw (P := P) eps lam hA (hA.union hB)
    (by intro ω hω; exact Or.inl hω)

/-- The real image of the zero set `{p : Level | g p = 0}`. This is the set whose supremum
appears in the infinite-left AES statement. -/
def zeroSetReal (g : Level → ℝ) : Set ℝ := {x : ℝ | ∃ p : Level, (p : ℝ) = x ∧ g p = 0}

/-- Fixed-level eventual largeness near the right endpoint `1`. This is the proof-friendly
version of the tail penalty condition used in the infinite-left AES argument. -/
def EventuallyLargeBeforeOne (g : Level → ℝ) (c : ℝ) : Prop :=
  ∃ bar : Level, (bar : ℝ) < 1 ∧ ∀ p : Level, (bar : ℝ) < (p : ℝ) → c < g p

/-- If `p₀` is the least upper bound of the zero set of `g`, then every level strictly above `p₀`
has strictly positive penalty, provided `g ≥ 0`. -/
theorem positive_of_gt_isLUB_zeroSetReal
    (g : Level → ℝ) {p0 : ℝ} (hsup : IsLUB (zeroSetReal g) p0)
    (hgnonneg : ∀ p : Level, 0 ≤ g p) {q : Level} (hp0q : p0 < (q : ℝ)) :
    0 < g q := by
  have hq_ne : g q ≠ 0 := by
    intro hq_zero
    have hq_mem : (q : ℝ) ∈ zeroSetReal g := ⟨q, rfl, hq_zero⟩
    have hupper : p0 ∈ upperBounds (zeroSetReal g) := hsup.1
    have hq_le : (q : ℝ) ≤ p0 := hupper hq_mem
    linarith
  exact lt_of_le_of_ne (hgnonneg q) (Ne.symm hq_ne)

/-- A tail witness `bar < 1` can always be enlarged to sit above a prescribed `q₀ < 1`, while
preserving the same eventual lower bound. -/
theorem exists_tailWitnessAbove_of_eventuallyLargeBeforeOne
    (g : Level → ℝ) {c : ℝ} {q0 : Level} (hq01 : (q0 : ℝ) < 1)
    (htail : EventuallyLargeBeforeOne g c) :
    ∃ bar : Level, (q0 : ℝ) < (bar : ℝ) ∧ (bar : ℝ) < 1 ∧
      ∀ p : Level, (bar : ℝ) < (p : ℝ) → c < g p := by
  rcases htail with ⟨b, hb1, hbLarge⟩
  let qmid : Level := ⟨((q0 : ℝ) + 1) / 2, by
    constructor
    · have hq0_nonneg : 0 ≤ (q0 : ℝ) := q0.2.1
      linarith
    · linarith⟩
  have hqmid1 : (qmid : ℝ) < 1 := by
    change (((q0 : ℝ) + 1) / 2) < 1
    linarith
  let bar : Level := ⟨max (b : ℝ) (qmid : ℝ), by
    constructor
    · exact le_trans b.2.1 (le_max_left _ _)
    · exact (max_lt_iff.mpr ⟨hb1, hqmid1⟩).le⟩
  refine ⟨bar, ?_, ?_, ?_⟩
  · change (q0 : ℝ) < max (b : ℝ) (qmid : ℝ)
    have hq0qmid : (q0 : ℝ) < (qmid : ℝ) := by
      change (q0 : ℝ) < ((q0 : ℝ) + 1) / 2
      linarith
    exact lt_of_lt_of_le hq0qmid (le_max_right _ _)
  · change max (b : ℝ) (qmid : ℝ) < 1
    exact max_lt_iff.mpr ⟨hb1, hqmid1⟩
  · intro p hp
    exact hbLarge p (lt_of_le_of_lt (le_max_left _ _) hp)

/-- If `g` is bounded above by `M` on `[0,1]`, then the indicator-level AES closed form enjoys a
uniform positive lower bound on `(0,1]` as soon as `c > M`. This is the quantitative ingredient
behind the `p₀ < 1` contradiction in the finite-penalty case. -/
theorem indicatorAESClosedForm_lowerBound_of_bddAbove
    (g : Level → ℝ) {c M : ℝ} (hc : 0 < c) {t : ℝ} (ht0 : 0 < t)
    (ht1 : t ≤ 1) (hgnonneg : ∀ p : Level, 0 ≤ g p) (hg : ∀ p : Level, g p ≤ M) :
    c - M ≤ indicatorAESClosedForm g c t := by
  let p : Level := ⟨1 - t / 2, by constructor <;> linarith⟩
  have hp_lt : ((p : Level) : ℝ) < 1 := by
    change 1 - t / 2 < 1
    linarith
  have hmin : min 1 (t / (1 - ((p : Level) : ℝ))) = 1 := by
    change min 1 (t / (1 - (1 - t / 2))) = 1
    have ht_ne : t ≠ 0 := ne_of_gt ht0
    have htwo : t / (t / 2) = 2 := by
      field_simp [ht_ne]
    have hden : 1 - (1 - t / 2) = t / 2 := by ring
    rw [hden, htwo]
    norm_num
  have hmem :
      indicatorESClosedForm c t p - g p ∈
        Set.range (fun q : Level => indicatorESClosedForm c t q - g q) := by
    exact ⟨p, rfl⟩
  have hsSup :
      indicatorESClosedForm c t p - g p ≤ indicatorAESClosedForm g c t := by
    unfold indicatorAESClosedForm
    exact le_csSup
      ⟨c, by
        rintro _ ⟨q, rfl⟩
        by_cases hq : (q : ℝ) < 1
        · have hmin_le : min 1 (t / (1 - (q : ℝ))) ≤ 1 := min_le_left _ _
          simp [indicatorESClosedForm, hq]
          nlinarith [hmin_le, hgnonneg q, hc]
        · simp [indicatorESClosedForm, hq]
          linarith [hgnonneg q]⟩
      hmem
  have hp_eval : indicatorESClosedForm c t p = c := by
    simp [indicatorESClosedForm, hp_lt, hmin]
  calc
    c - M ≤ c - g p := by linarith [hg p]
    _ = indicatorESClosedForm c t p - g p := by rw [hp_eval]
    _ ≤ indicatorAESClosedForm g c t := hsSup

/-- Under the same bounded-penalty assumption, the indicator-level AES closed form is strictly
positive on `(0,1]` whenever the payoff level dominates the penalty bound. -/
theorem indicatorAESClosedForm_pos_of_bddAbove
    (g : Level → ℝ) {c M : ℝ} (hc : 0 < c) (hcM : M < c) {t : ℝ} (ht0 : 0 < t)
    (ht1 : t ≤ 1) (hgnonneg : ∀ p : Level, 0 ≤ g p) (hg : ∀ p : Level, g p ≤ M) :
    0 < indicatorAESClosedForm g c t := by
  have hbound :=
    indicatorAESClosedForm_lowerBound_of_bddAbove (g := g) hc ht0 ht1 hgnonneg hg
  linarith

/-- Nonnegative penalties force the indicator-level AES closed form to stay below the payoff
level `c`. -/
theorem indicatorAESClosedForm_le_of_nonneg
    (g : Level → ℝ) {c t : ℝ} (hc : 0 < c) (hgnonneg : ∀ p : Level, 0 ≤ g p) :
    indicatorAESClosedForm g c t ≤ c := by
  unfold indicatorAESClosedForm
  refine csSup_le ?_ ?_
  · exact ⟨indicatorESClosedForm c t 0 - g 0, ⟨0, rfl⟩⟩
  · intro y hy
    rcases hy with ⟨q, rfl⟩
    by_cases hq : (q : ℝ) < 1
    · simp [indicatorESClosedForm, hq]
      have hmin_le : min 1 (t / (1 - (q : ℝ))) ≤ 1 := min_le_left _ _
      nlinarith [hmin_le, hgnonneg q, hc]
    · simp [indicatorESClosedForm, hq]
      linarith [hgnonneg q]

/-- The chosen AES indicator probability profile inherits the same strict positivity on `(0,1]`
once it is identified with the closed form. -/
theorem indicatorAESProbabilityProfile_pos_of_bddAbove
    (hsplit : HasFullEventSplitting P) (g : Level → ℝ) {c M : ℝ} (hc : 0 < c) (hcM : M < c)
    {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) (hgnonneg : ∀ p : Level, 0 ≤ g p)
    (hg : ∀ p : Level, g p ≤ M) :
    0 < indicatorAESProbabilityProfile P hsplit g c t := by
  rw [indicatorAESProbabilityProfile_eq_indicatorAESClosedForm (P := P) hsplit g c hc ht0 ht1]
  exact indicatorAESClosedForm_pos_of_bddAbove (g := g) hc hcM ht0 ht1 hgnonneg hg

/-- Under a finite penalty bound, the chosen AES indicator probability profile inherits the same
uniform lower bound as the closed form on positive masses. -/
theorem indicatorAESProbabilityProfile_lowerBound_of_bddAbove
    (hsplit : HasFullEventSplitting P) (g : Level → ℝ) {c M : ℝ} (hc : 0 < c)
    {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) (hgnonneg : ∀ p : Level, 0 ≤ g p)
    (hg : ∀ p : Level, g p ≤ M) :
    c - M ≤ indicatorAESProbabilityProfile P hsplit g c t := by
  rw [indicatorAESProbabilityProfile_eq_indicatorAESClosedForm (P := P) hsplit g c hc ht0 ht1]
  exact indicatorAESClosedForm_lowerBound_of_bddAbove (g := g) hc ht0 ht1 hgnonneg hg

/-- The chosen AES indicator probability profile inherits the same payoff upper bound on `(0,1]`
once it is identified with the closed form. -/
theorem indicatorAESProbabilityProfile_le_of_nonneg
    (hsplit : HasFullEventSplitting P) (g : Level → ℝ) {c t : ℝ} (hc : 0 < c)
    (ht0 : 0 < t) (ht1 : t ≤ 1) (hgnonneg : ∀ p : Level, 0 ≤ g p) :
    indicatorAESProbabilityProfile P hsplit g c t ≤ c := by
  rw [indicatorAESProbabilityProfile_eq_indicatorAESClosedForm (P := P) hsplit g c hc ht0 ht1]
  exact indicatorAESClosedForm_le_of_nonneg (g := g) hc hgnonneg

/-- Under a finite penalty bound, the AES indicator probability profile takes values in the compact
interval `[0, c]` on `(0,1]` provided `c` dominates that bound. This packages the local boundedness
data needed for a later Bernstein-Doetsch style concavity upgrade. -/
theorem indicatorAESProbabilityProfile_mem_Icc_of_bddAbove
    (hsplit : HasFullEventSplitting P) (g : Level → ℝ) {c M t : ℝ} (hc : 0 < c) (hcM : M < c)
    (ht0 : 0 < t) (ht1 : t ≤ 1) (hgnonneg : ∀ p : Level, 0 ≤ g p)
    (hg : ∀ p : Level, g p ≤ M) :
    indicatorAESProbabilityProfile P hsplit g c t ∈ Set.Icc (0 : ℝ) c := by
  constructor
  · exact le_of_lt <|
      indicatorAESProbabilityProfile_pos_of_bddAbove (P := P) hsplit g hc hcM ht0 ht1
        hgnonneg hg
  · exact indicatorAESProbabilityProfile_le_of_nonneg (P := P) hsplit g hc ht0 ht1 hgnonneg

/-- The same compact-interval bound, expressed as a bounded-above statement on the positive-mass
portion of the indicator probability profile. -/
theorem indicatorAESProbabilityProfile_bddAbove_on_Ioc
    (hsplit : HasFullEventSplitting P) (g : Level → ℝ) {c : ℝ} (hc : 0 < c)
    (hgnonneg : ∀ p : Level, 0 ≤ g p) :
    BddAbove (indicatorAESProbabilityProfile P hsplit g c '' Set.Ioc (0 : ℝ) 1) := by
  refine ⟨c, ?_⟩
  rintro y ⟨t, ht, rfl⟩
  exact indicatorAESProbabilityProfile_le_of_nonneg (P := P) hsplit g hc ht.1 ht.2 hgnonneg

/-- If the penalties are uniformly bounded above by `M < c`, then the positive-mass portion of the
indicator probability profile is also bounded below. -/
theorem indicatorAESProbabilityProfile_bddBelow_on_Ioc_of_bddAbove
    (hsplit : HasFullEventSplitting P) (g : Level → ℝ) {c M : ℝ} (hc : 0 < c) (hcM : M < c)
    (hgnonneg : ∀ p : Level, 0 ≤ g p) (hg : ∀ p : Level, g p ≤ M) :
    BddBelow (indicatorAESProbabilityProfile P hsplit g c '' Set.Ioc (0 : ℝ) 1) := by
  refine ⟨0, ?_⟩
  rintro y ⟨t, ht, rfl⟩
  exact le_of_lt <|
    indicatorAESProbabilityProfile_pos_of_bddAbove (P := P) hsplit g hc hcM ht.1 ht.2
      hgnonneg hg

/-- Lean-compilable finite-penalty bridge for the AES contradiction argument.

This packages the pieces that remain valid after removing the incorrect
`concave on [0,1] -> continuous at 0` step from the paper draft:
the indicator probability profile has decreasing increments, midpoint concavity,
and uniform two-sided bounds on positive masses. -/
theorem finitePenalty_indicatorAESProfile_bridge
    (hsplit : HasFullEventSplitting P) (g : Level → ℝ) {c M : ℝ}
    (hc : 0 < c) (hcM : M < c) (hsub : Submodular (AES P g))
    (hgnonneg : ∀ p : Level, 0 ≤ g p) (hg : ∀ p : Level, g p ≤ M) :
    DecreasingIncrements (indicatorAESProbabilityProfile P hsplit g c) ∧
      (∀ ⦃x y : ℝ⦄, x ∈ Set.Icc (0 : ℝ) 1 → y ∈ Set.Icc (0 : ℝ) 1 →
        indicatorAESProbabilityProfile P hsplit g c (midpoint ℝ x y) ≥
          midpoint ℝ (indicatorAESProbabilityProfile P hsplit g c x)
            (indicatorAESProbabilityProfile P hsplit g c y)) ∧
      BddAbove (indicatorAESProbabilityProfile P hsplit g c '' Set.Ioc (0 : ℝ) 1) ∧
      BddBelow (indicatorAESProbabilityProfile P hsplit g c '' Set.Ioc (0 : ℝ) 1) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact decreasingIncrements_indicatorAESProbabilityProfile (P := P) hsplit g
      (le_of_lt hc) hsub
  · intro x y hx hy
    exact midpoint_ge_average_indicatorAESProbabilityProfile (P := P) hsplit g
      (le_of_lt hc) hsub hx hy
  · exact indicatorAESProbabilityProfile_bddAbove_on_Ioc (P := P) hsplit g hc hgnonneg
  · exact indicatorAESProbabilityProfile_bddBelow_on_Ioc_of_bddAbove (P := P)
      hsplit g hc hcM hgnonneg hg

/-- Finite-penalty contradiction template: once one knows that the indicator AES profile is
continuous at the origin and vanishes there, the uniform lower bound on positive masses rules this
out. This isolates the exact point where the original finite-case proof must supply extra input. -/
theorem finitePenalty_indicatorAES_contradiction_of_continuousAt_zero
    (hsplit : HasFullEventSplitting P) (g : Level → ℝ) {c M : ℝ}
    (hc : 0 < c) (hcM : M < c) (hzero : indicatorAESProbabilityProfile P hsplit g c 0 = 0)
    (hcont : ContinuousAt (indicatorAESProbabilityProfile P hsplit g c) 0)
    (hgnonneg : ∀ p : Level, 0 ≤ g p) (hg : ∀ p : Level, g p ≤ M) :
    False := by
  have hδ : 0 < c - M := by linarith
  refine not_continuousAt_zero_of_uniform_lowerBound_right hzero hδ ?_ hcont
  intro t ht0 ht1
  exact indicatorAESProbabilityProfile_lowerBound_of_bddAbove (P := P) hsplit g hc ht0 ht1
    hgnonneg hg

/-- Finite-penalty contradiction template with the origin value discharged automatically by the
normalized-penalty assumptions. -/
theorem finitePenalty_indicatorAES_contradiction
    (hsplit : HasFullEventSplitting P) (g : Level → ℝ) {c M : ℝ}
    (hc : 0 < c) (hcM : M < c)
    (hg0 : g 0 = 0) (hcont : ContinuousAt (indicatorAESProbabilityProfile P hsplit g c) 0)
    (hgnonneg : ∀ p : Level, 0 ≤ g p) (hg : ∀ p : Level, g p ≤ M) :
    False := by
  refine finitePenalty_indicatorAES_contradiction_of_continuousAt_zero (P := P) hsplit g hc hcM ?_
    hcont hgnonneg hg
  exact indicatorAESProbabilityProfile_zero_eq_zero (P := P) hsplit g c hg0 hgnonneg

/-- Lean-friendly finite-penalty non-submodularity statement, conditional on continuity of the
indicator AES profile at the origin. This isolates the exact missing input in the original
finite-case proof. -/
theorem not_submodular_AES_of_finitePenalty_of_continuousAt_zero
    (hsplit : HasFullEventSplitting P) (g : Level → ℝ) {c M : ℝ}
    (hc : 0 < c) (hcM : M < c) (hg0 : g 0 = 0)
    (hcont : ContinuousAt (indicatorAESProbabilityProfile P hsplit g c) 0)
    (hgnonneg : ∀ p : Level, 0 ≤ g p) (hg : ∀ p : Level, g p ≤ M) :
    ¬ Submodular (AES P g) := by
  intro hsub
  exact finitePenalty_indicatorAES_contradiction (P := P) hsplit g hc hcM hg0 hcont hgnonneg hg

/-- If the penalty vanishes at a level `r`, then the indicator-level AES closed form dominates the
corresponding lower-bound line near the origin. This is the lower-bound half of the origin-slope
argument in the infinite-left AES proof. -/
theorem indicatorAESClosedForm_ratio_ge_of_zeroPenalty
    (g : Level → ℝ) {c : ℝ} (hc : 0 < c) (hgnonneg : ∀ p : Level, 0 ≤ g p) {r : Level}
    (hgr : g r = 0) {t : ℝ} (ht0 : 0 < t) (hrt : t < 1 - (r : ℝ)) :
    c / (1 - (r : ℝ)) ≤ indicatorAESClosedForm g c t / t := by
  have hr_lt : (r : ℝ) < 1 := by linarith
  have hden_pos : 0 < 1 - (r : ℝ) := sub_pos.mpr hr_lt
  have hrange :
      indicatorESClosedForm c t r - g r ∈
        Set.range (fun q : Level => indicatorESClosedForm c t q - g q) := by
    exact ⟨r, rfl⟩
  have hsSup :
      indicatorESClosedForm c t r - g r ≤ indicatorAESClosedForm g c t := by
    unfold indicatorAESClosedForm
    refine le_csSup ?_ hrange
    refine ⟨c, ?_⟩
    rintro _ ⟨q, rfl⟩
    by_cases hq : (q : ℝ) < 1
    · have hmin_le : min 1 (t / (1 - (q : ℝ))) ≤ 1 := min_le_left _ _
      have hmul_le : c * min 1 (t / (1 - (q : ℝ))) ≤ c := by
        nlinarith [hmin_le, hc]
      calc
        indicatorESClosedForm c t q - g q = c * min 1 (t / (1 - (q : ℝ))) - g q := by
          simp [indicatorESClosedForm, hq]
        _ ≤ c * min 1 (t / (1 - (q : ℝ))) := by
          linarith [hgnonneg q]
        _ ≤ c := hmul_le
    · simp [indicatorESClosedForm, hq]
      linarith [hgnonneg q]
  have hr_eval : indicatorESClosedForm c t r = c * (t / (1 - (r : ℝ))) := by
    have hratio_lt_one : t / (1 - (r : ℝ)) < 1 := by
      rw [div_lt_one hden_pos]
      simpa using hrt
    have hmin :
        min 1 (t / (1 - (r : ℝ))) = t / (1 - (r : ℝ)) :=
      min_eq_right (le_of_lt hratio_lt_one)
    simp [indicatorESClosedForm, hr_lt, hmin]
  have hcore : c * (t / (1 - (r : ℝ))) ≤ indicatorAESClosedForm g c t := by
    simpa [hr_eval, hgr] using hsSup
  have ht_ne : t ≠ 0 := ne_of_gt ht0
  have hden_ne : 1 - (r : ℝ) ≠ 0 := ne_of_gt hden_pos
  apply (le_div_iff₀ ht0).mpr
  calc
    c / (1 - (r : ℝ)) * t = c * (t / (1 - (r : ℝ))) := by
      field_simp [hden_ne]
    _ ≤ indicatorAESClosedForm g c t := hcore

/-- Transport the zero-penalty lower bound to the chosen AES indicator probability profile. -/
theorem indicatorAESProbabilityProfile_ratio_ge_of_zeroPenalty
    (hsplit : HasFullEventSplitting P) (g : Level → ℝ) {c : ℝ}
    (hc : 0 < c) (hgnonneg : ∀ p : Level, 0 ≤ g p) {r : Level}
    (hgr : g r = 0) {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) (hrt : t < 1 - (r : ℝ)) :
    c / (1 - (r : ℝ)) ≤ indicatorAESProbabilityProfile P hsplit g c t / t := by
  rw [indicatorAESProbabilityProfile_eq_indicatorAESClosedForm (P := P) hsplit g c hc ht0 ht1]
  exact indicatorAESClosedForm_ratio_ge_of_zeroPenalty (g := g) hc hgnonneg hgr ht0 hrt

/-- Evaluating the indicator-level AES closed form at the matching level `t = 1 - p` yields a
pointwise lower bound by `c - g(p)`. -/
theorem indicatorAESClosedForm_ratio_ge_at_level
    (g : Level → ℝ) {c : ℝ} (hc : 0 < c) (hgnonneg : ∀ p : Level, 0 ≤ g p) {p : Level}
    (hp : (p : ℝ) < 1) :
    (c - g p) / (1 - (p : ℝ)) ≤ indicatorAESClosedForm g c (1 - (p : ℝ)) / (1 - (p : ℝ)) := by
  have ht0 : 0 < 1 - (p : ℝ) := sub_pos.mpr hp
  have hrange :
      indicatorESClosedForm c (1 - (p : ℝ)) p - g p ∈
        Set.range (fun q : Level => indicatorESClosedForm c (1 - (p : ℝ)) q - g q) := by
    exact ⟨p, rfl⟩
  have hsSup :
      indicatorESClosedForm c (1 - (p : ℝ)) p - g p ≤
        indicatorAESClosedForm g c (1 - (p : ℝ)) := by
    unfold indicatorAESClosedForm
    refine le_csSup ?_ hrange
    refine ⟨c, ?_⟩
    rintro _ ⟨q, rfl⟩
    by_cases hq : (q : ℝ) < 1
    · have hmin_le : min 1 ((1 - (p : ℝ)) / (1 - (q : ℝ))) ≤ 1 := min_le_left _ _
      have hmul_le : c * min 1 ((1 - (p : ℝ)) / (1 - (q : ℝ))) ≤ c := by
        nlinarith [hmin_le, hc]
      calc
        indicatorESClosedForm c (1 - (p : ℝ)) q - g q =
            c * min 1 ((1 - (p : ℝ)) / (1 - (q : ℝ))) - g q := by
          simp [indicatorESClosedForm, hq]
        _ ≤ c * min 1 ((1 - (p : ℝ)) / (1 - (q : ℝ))) := by
          linarith [hgnonneg q]
        _ ≤ c := hmul_le
    · simp [indicatorESClosedForm, hq]
      linarith [hgnonneg q]
  have hp_eval : indicatorESClosedForm c (1 - (p : ℝ)) p = c := by
    have hmin : min 1 ((1 - (p : ℝ)) / (1 - (p : ℝ))) = (1 : ℝ) := by
      have hden_pos : 0 < 1 - (p : ℝ) := sub_pos.mpr hp
      have hden_ne : 1 - (p : ℝ) ≠ 0 := ne_of_gt hden_pos
      rw [div_self hden_ne, min_eq_left le_rfl]
    simp [indicatorESClosedForm, hp, hmin]
  have hcore : c - g p ≤ indicatorAESClosedForm g c (1 - (p : ℝ)) := by
    simpa [hp_eval] using hsSup
  have hinv_nonneg : 0 ≤ (1 - (p : ℝ))⁻¹ := by positivity
  simpa [div_eq_mul_inv] using mul_le_mul_of_nonneg_right hcore hinv_nonneg

/-- Transport the pointwise lower bound at `t = 1 - p` to the chosen AES indicator profile. -/
theorem indicatorAESProbabilityProfile_ratio_ge_at_level
    (hsplit : HasFullEventSplitting P) (g : Level → ℝ) {c : ℝ}
    (hc : 0 < c) (hgnonneg : ∀ p : Level, 0 ≤ g p) {p : Level}
    (hp : (p : ℝ) < 1) :
    (c - g p) / (1 - (p : ℝ)) ≤
      indicatorAESProbabilityProfile P hsplit g c (1 - (p : ℝ)) / (1 - (p : ℝ)) := by
  have ht0 : 0 < 1 - (p : ℝ) := sub_pos.mpr hp
  have hp_nonneg : 0 ≤ (p : ℝ) := p.2.1
  have ht1 : 1 - (p : ℝ) ≤ 1 := by
    linarith
  rw [indicatorAESProbabilityProfile_eq_indicatorAESClosedForm (P := P) hsplit g c hc ht0 ht1]
  exact indicatorAESClosedForm_ratio_ge_at_level (g := g) hc hgnonneg hp

/-- Small-`t` upper bound for the indicator-level AES closed form.

The interval `[0,1]` is split into three regions:
levels below `q₀`, an intermediate band up to `\bar p`, and the far-right tail where the penalty
already dominates the payoff level `c`. -/
theorem indicatorAESClosedForm_le_linear_of_cutoff
    (g : Level → ℝ) {c : ℝ} (hc : 0 < c) (hmono : _root_.Monotone g)
    (hgnonneg : ∀ p : Level, 0 ≤ g p) {q0 bar : Level}
    (hq0bar : (q0 : ℝ) < (bar : ℝ)) (hbar1 : (bar : ℝ) < 1)
    (hlarge : ∀ p : Level, (bar : ℝ) < (p : ℝ) → c < g p)
    {t : ℝ} (ht0 : 0 < t) (htbar : t < 1 - (bar : ℝ))
    (htgap :
      t * (c / (1 - (bar : ℝ)) - c / (1 - (q0 : ℝ))) ≤ g q0) :
    indicatorAESClosedForm g c t ≤ (c / (1 - (q0 : ℝ))) * t := by
  have hq0_lt1 : (q0 : ℝ) < 1 := lt_trans hq0bar hbar1
  have htarget_nonneg : 0 ≤ (c / (1 - (q0 : ℝ))) * t := by
    have hden_pos : 0 < 1 - (q0 : ℝ) := sub_pos.mpr hq0_lt1
    have hdiv_nonneg : 0 ≤ c / (1 - (q0 : ℝ)) := by
      exact div_nonneg (le_of_lt hc) (le_of_lt hden_pos)
    nlinarith [hdiv_nonneg, ht0]
  unfold indicatorAESClosedForm
  refine csSup_le ?_ ?_
  · exact ⟨indicatorESClosedForm c t q0 - g q0, ⟨q0, rfl⟩⟩
  · intro y hy
    rcases hy with ⟨q, rfl⟩
    by_cases hqbar : ((q : Level) : ℝ) ≤ (bar : ℝ)
    · have hq_lt1 : (q : ℝ) < 1 := lt_of_le_of_lt hqbar hbar1
      have htq : t < 1 - (q : ℝ) := by
        have hden : 1 - (bar : ℝ) ≤ 1 - (q : ℝ) := by linarith
        exact lt_of_lt_of_le htbar hden
      have hmin :
          min 1 (t / (1 - (q : ℝ))) = t / (1 - (q : ℝ)) := by
        have hratio_lt_one : t / (1 - (q : ℝ)) < 1 := by
          rw [div_lt_one (sub_pos.mpr hq_lt1)]
          exact htq
        exact min_eq_right (le_of_lt hratio_lt_one)
      have hbranch :
          indicatorESClosedForm c t q - g q = c * (t / (1 - (q : ℝ))) - g q := by
        simp [indicatorESClosedForm, hq_lt1, hmin]
      by_cases hqq0 : ((q : Level) : ℝ) ≤ (q0 : ℝ)
      · have hfrac : c / (1 - (q : ℝ)) ≤ c / (1 - (q0 : ℝ)) := by
          refine div_le_div_of_nonneg_left (le_of_lt hc) (sub_pos.mpr hq0_lt1) ?_
          linarith
        have hmul :
            c * (t / (1 - (q : ℝ))) ≤ (c / (1 - (q0 : ℝ))) * t := by
          have hmul' := mul_le_mul_of_nonneg_right hfrac (le_of_lt ht0)
          have hrew : c * (t / (1 - (q : ℝ))) = (c / (1 - (q : ℝ))) * t := by ring
          simpa [hrew] using hmul'
        calc
          indicatorESClosedForm c t q - g q = c * (t / (1 - (q : ℝ))) - g q := hbranch
          _ ≤ c * (t / (1 - (q : ℝ))) := by linarith [hgnonneg q]
          _ ≤ (c / (1 - (q0 : ℝ))) * t := hmul
      · have hq0q : (q0 : ℝ) < (q : ℝ) := lt_of_not_ge hqq0
        have hgq0q : g q0 ≤ g q := hmono (le_of_lt hq0q)
        have hfracbar : c / (1 - (q : ℝ)) ≤ c / (1 - (bar : ℝ)) := by
          refine div_le_div_of_nonneg_left (le_of_lt hc) (sub_pos.mpr hbar1) ?_
          linarith
        have hmulbar :
            c * (t / (1 - (q : ℝ))) ≤ (c / (1 - (bar : ℝ))) * t := by
          have hmul' := mul_le_mul_of_nonneg_right hfracbar (le_of_lt ht0)
          have hrew : c * (t / (1 - (q : ℝ))) = (c / (1 - (q : ℝ))) * t := by ring
          simpa [hrew] using hmul'
        calc
          indicatorESClosedForm c t q - g q = c * (t / (1 - (q : ℝ))) - g q := hbranch
          _ ≤ c * (t / (1 - (q : ℝ))) - g q0 := by linarith
          _ ≤ (c / (1 - (bar : ℝ))) * t - g q0 := by linarith
          _ ≤ (c / (1 - (q0 : ℝ))) * t := by linarith
    · have hqbar' : (bar : ℝ) < (q : ℝ) := lt_of_not_ge hqbar
      have htail : c < g q := hlarge q hqbar'
      by_cases hq_lt1 : (q : ℝ) < 1
      · have hmin_le : min 1 (t / (1 - (q : ℝ))) ≤ 1 := min_le_left _ _
        calc
          indicatorESClosedForm c t q - g q = c * min 1 (t / (1 - (q : ℝ))) - g q := by
            simp [indicatorESClosedForm, hq_lt1]
          _ ≤ c - g q := by nlinarith [hmin_le, hc]
          _ ≤ 0 := by linarith
          _ ≤ (c / (1 - (q0 : ℝ))) * t := htarget_nonneg
      · calc
          indicatorESClosedForm c t q - g q = c - g q := by simp [indicatorESClosedForm, hq_lt1]
          _ ≤ 0 := by linarith
          _ ≤ (c / (1 - (q0 : ℝ))) * t := htarget_nonneg

/-- Ratio upper bound corresponding to `indicatorAESClosedForm_le_linear_of_cutoff`. -/
theorem indicatorAESClosedForm_ratio_le_of_cutoff
    (g : Level → ℝ) {c : ℝ} (hc : 0 < c) (hmono : _root_.Monotone g)
    (hgnonneg : ∀ p : Level, 0 ≤ g p) {q0 bar : Level}
    (hq0bar : (q0 : ℝ) < (bar : ℝ)) (hbar1 : (bar : ℝ) < 1)
    (hlarge : ∀ p : Level, (bar : ℝ) < (p : ℝ) → c < g p)
    {t : ℝ} (ht0 : 0 < t) (htbar : t < 1 - (bar : ℝ))
    (htgap :
      t * (c / (1 - (bar : ℝ)) - c / (1 - (q0 : ℝ))) ≤ g q0) :
    indicatorAESClosedForm g c t / t ≤ c / (1 - (q0 : ℝ)) := by
  exact (div_le_iff₀ ht0).2 <|
    indicatorAESClosedForm_le_linear_of_cutoff (g := g) hc hmono hgnonneg hq0bar hbar1
      hlarge ht0 htbar htgap

/-- Eventual small-`t` upper bound for the indicator-level AES closed form. -/
theorem indicatorAESClosedForm_ratio_eventually_le_of_cutoff
    (g : Level → ℝ) {c : ℝ} (hc : 0 < c) (hmono : _root_.Monotone g)
    (hgnonneg : ∀ p : Level, 0 ≤ g p) {q0 bar : Level}
    (hq0bar : (q0 : ℝ) < (bar : ℝ)) (hbar1 : (bar : ℝ) < 1)
    (hq0pos : 0 < g q0) (hlarge : ∀ p : Level, (bar : ℝ) < (p : ℝ) → c < g p) :
    ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      indicatorAESClosedForm g c t / t ≤ c / (1 - (q0 : ℝ)) := by
  let D : ℝ := c / (1 - (bar : ℝ)) - c / (1 - (q0 : ℝ))
  have hDpos : 0 < D := by
    have hfrac_lt : c / (1 - (q0 : ℝ)) < c / (1 - (bar : ℝ)) := by
      refine div_lt_div_of_pos_left hc (sub_pos.mpr hbar1) ?_
      linarith
    dsimp [D]
    linarith
  let δ : ℝ := min (1 - (bar : ℝ)) (g q0 / D)
  have hδpos : 0 < δ := by
    refine lt_min ?_ ?_
    · linarith
    · exact div_pos hq0pos hDpos
  have hsmall : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0), t < δ := by
    have hset : Set.Iio δ ∈ nhdsWithin (0 : ℝ) (Set.Ioi 0) := by
      exact
        (nhdsWithin_le_nhds : nhdsWithin (0 : ℝ) (Set.Ioi 0) ≤ nhds (0 : ℝ))
          (Iio_mem_nhds hδpos)
    have hmem : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0), t ∈ Set.Iio δ := hset
    exact hmem.mono fun _ ht => ht
  have hpos : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0), 0 < t := by
    exact self_mem_nhdsWithin
  filter_upwards [hsmall, hpos] with t htδ ht0
  have htbar : t < 1 - (bar : ℝ) := lt_of_lt_of_le htδ (min_le_left _ _)
  have htle : t ≤ g q0 / D := le_of_lt <| lt_of_lt_of_le htδ (min_le_right _ _)
  have htgap : t * D ≤ g q0 := by
    exact (le_div_iff₀ hDpos).mp htle
  exact indicatorAESClosedForm_ratio_le_of_cutoff (g := g) hc hmono hgnonneg hq0bar hbar1
    hlarge ht0 htbar htgap

/-- Transport the eventual cutoff upper bound from the closed form to the chosen AES indicator
probability profile. -/
theorem indicatorAESProbabilityProfile_ratio_eventually_le_of_cutoff
    (hsplit : HasFullEventSplitting P) (g : Level → ℝ) {c : ℝ} (hc : 0 < c)
    (hmono : _root_.Monotone g) (hgnonneg : ∀ p : Level, 0 ≤ g p) {q0 bar : Level}
    (hq0bar : (q0 : ℝ) < (bar : ℝ)) (hbar1 : (bar : ℝ) < 1)
    (hq0pos : 0 < g q0) (hlarge : ∀ p : Level, (bar : ℝ) < (p : ℝ) → c < g p) :
    ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      indicatorAESProbabilityProfile P hsplit g c t / t ≤ c / (1 - (q0 : ℝ)) := by
  let D : ℝ := c / (1 - (bar : ℝ)) - c / (1 - (q0 : ℝ))
  let δ : ℝ := min (1 - (bar : ℝ)) (g q0 / D)
  have hDpos : 0 < D := by
    have hfrac_lt : c / (1 - (q0 : ℝ)) < c / (1 - (bar : ℝ)) := by
      refine div_lt_div_of_pos_left hc (sub_pos.mpr hbar1) ?_
      linarith
    dsimp [D]
    linarith
  have hδpos : 0 < δ := by
    refine lt_min ?_ ?_
    · linarith
    · exact div_pos hq0pos hDpos
  have hsmall : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0), t < δ := by
    have hset : Set.Iio δ ∈ nhdsWithin (0 : ℝ) (Set.Ioi 0) := by
      exact
        (nhdsWithin_le_nhds : nhdsWithin (0 : ℝ) (Set.Ioi 0) ≤ nhds (0 : ℝ))
          (Iio_mem_nhds hδpos)
    have hmem : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0), t ∈ Set.Iio δ := hset
    exact hmem.mono fun _ ht => ht
  have hpos : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0), 0 < t := by
    exact self_mem_nhdsWithin
  filter_upwards [hsmall, hpos] with t htδ ht0
  have htbar : t < 1 - (bar : ℝ) := lt_of_lt_of_le htδ (min_le_left _ _)
  have ht1 : t ≤ 1 := by
    have hbar_nonneg : 0 ≤ (bar : ℝ) := bar.2.1
    linarith
  rw [indicatorAESProbabilityProfile_eq_indicatorAESClosedForm (P := P) hsplit g c hc ht0 ht1]
  have htle : t ≤ g q0 / D := le_of_lt <| lt_of_lt_of_le htδ (min_le_right _ _)
  have htgap : t * D ≤ g q0 := by
    exact (le_div_iff₀ hDpos).mp htle
  exact indicatorAESClosedForm_ratio_le_of_cutoff (g := g) hc hmono hgnonneg hq0bar hbar1
    hlarge ht0 htbar htgap

/-- The paper's choice of a sufficiently large payoff level `λ` implies the strict pointwise ratio
gap needed for the infinite-left contradiction. -/
theorem point_ratio_strict_of_lambda_bound
    (g : Level → ℝ) {c : ℝ} {q0 p1 : Level}
    (hq0p1 : (q0 : ℝ) < (p1 : ℝ))
    (hp1 : (p1 : ℝ) < 1)
    (hc_large : g p1 * (1 - (q0 : ℝ)) / ((p1 : ℝ) - (q0 : ℝ)) < c) :
    c / (1 - (q0 : ℝ)) < (c - g p1) / (1 - (p1 : ℝ)) := by
  have hgap_pos : 0 < (p1 : ℝ) - (q0 : ℝ) := sub_pos.mpr hq0p1
  have hden_pos : 0 < 1 - (q0 : ℝ) := by
    exact sub_pos.mpr (lt_trans hq0p1 hp1)
  have hnum_pos : 0 < 1 - (p1 : ℝ) := sub_pos.mpr hp1
  have hmain :
      g p1 * (1 - (q0 : ℝ)) < c * ((p1 : ℝ) - (q0 : ℝ)) := by
    exact (div_lt_iff₀ hgap_pos).mp hc_large
  have htarget :
      c * (1 - (p1 : ℝ)) < (c - g p1) * (1 - (q0 : ℝ)) := by
    linarith
  exact (div_lt_div_iff₀ hden_pos hnum_pos).2 htarget

/-- Lean-valid contradiction template for the infinite-left AES argument: once one has
origin-slope control and concavity of the indicator profile, any strictly larger ratio at a
positive point is impossible. -/
theorem infiniteLeft_indicatorAES_contradiction_of_concave_originSlope
    (hsplit : HasFullEventSplitting P) (g : Level → ℝ) {c p0 : ℝ}
    (hc : 0 < c) (hp0 : p0 ∈ Set.Icc (0 : ℝ) 1) (hgnonneg : ∀ p : Level, 0 ≤ g p)
    (hconc :
      ConcaveOn ℝ (Set.Icc (0 : ℝ) 1) (indicatorAESProbabilityProfile P hsplit g c))
    (hzero : indicatorAESProbabilityProfile P hsplit g c 0 = 0)
    (hlim :
      Tendsto (fun t => indicatorAESProbabilityProfile P hsplit g c t / t)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (c / (1 - p0))))
    {p1 : Level} (hp0p1 : p0 < (p1 : ℝ)) (hp1 : (p1 : ℝ) < 1)
    (hpoint : c / (1 - p0) < (c - g p1) / (1 - (p1 : ℝ))) :
    False := by
  have hanti :
      AntitoneOn (fun t : ℝ => indicatorAESProbabilityProfile P hsplit g c t / t)
        (Set.Ioc (0 : ℝ) 1) :=
    ratio_antitoneOn_of_concaveOn_zero hconc hzero
  have ht1 : 1 - (p1 : ℝ) ∈ Set.Ioc (0 : ℝ) 1 := by
    constructor
    · linarith
    · linarith [hp0.1, hp1]
  have hratio :
      c / (1 - p0) <
        indicatorAESProbabilityProfile P hsplit g c (1 - (p1 : ℝ)) / (1 - (p1 : ℝ)) := by
    have hlower :=
      indicatorAESProbabilityProfile_ratio_ge_at_level (P := P) hsplit g hc hgnonneg hp1
    exact lt_of_lt_of_le hpoint hlower
  exact not_tendsto_ratio_nhdsWithin_zero_of_antitoneOn_above hanti ht1 hratio hlim

/-- A cutoff-based contradiction template for the infinite-left AES argument.

This avoids building the full origin-slope limit: it is enough to have an eventual upper bound
near the origin together with antitonicity of the ratio coming from concavity. -/
theorem infiniteLeft_indicatorAES_contradiction_of_concave_eventuallyUpper
    (hsplit : HasFullEventSplitting P) (g : Level → ℝ) {c q0 : ℝ}
    (hc : 0 < c) (hgnonneg : ∀ p : Level, 0 ≤ g p)
    (hconc :
      ConcaveOn ℝ (Set.Icc (0 : ℝ) 1) (indicatorAESProbabilityProfile P hsplit g c))
    (hzero : indicatorAESProbabilityProfile P hsplit g c 0 = 0)
    (hupper :
      ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0),
        indicatorAESProbabilityProfile P hsplit g c t / t ≤ c / (1 - q0))
    {p1 : Level} (hp1 : (p1 : ℝ) < 1)
    (hpoint : c / (1 - q0) < (c - g p1) / (1 - (p1 : ℝ))) :
    False := by
  have hanti :
      AntitoneOn (fun t : ℝ => indicatorAESProbabilityProfile P hsplit g c t / t)
        (Set.Ioc (0 : ℝ) 1) :=
    ratio_antitoneOn_of_concaveOn_zero hconc hzero
  have ht1 : 1 - (p1 : ℝ) ∈ Set.Ioc (0 : ℝ) 1 := by
    constructor
    · linarith
    · have hp1_nonneg : 0 ≤ (p1 : ℝ) := p1.2.1
      linarith
  have hratio :
      c / (1 - q0) <
        indicatorAESProbabilityProfile P hsplit g c (1 - (p1 : ℝ)) / (1 - (p1 : ℝ)) := by
    have hlower :=
      indicatorAESProbabilityProfile_ratio_ge_at_level (P := P) hsplit g hc hgnonneg hp1
    exact lt_of_lt_of_le hpoint hlower
  exact not_eventually_le_ratio_nhdsWithin_zero_of_antitoneOn_above hanti ht1 hratio hupper

/-- Infinite-left contradiction using only the midpoint inequality already derived from
submodularity, together with a cutoff-based eventual upper bound near the origin. -/
theorem infiniteLeft_indicatorAES_contradiction_of_midpoint_eventuallyUpper
    (hsplit : HasFullEventSplitting P) (g : Level → ℝ) {c q0 : ℝ}
    (hc : 0 < c) (hgnonneg : ∀ p : Level, 0 ≤ g p)
    (hmid :
      ∀ ⦃x y : ℝ⦄, x ∈ Set.Icc (0 : ℝ) 1 → y ∈ Set.Icc (0 : ℝ) 1 →
        indicatorAESProbabilityProfile P hsplit g c (midpoint ℝ x y) ≥
          midpoint ℝ (indicatorAESProbabilityProfile P hsplit g c x)
            (indicatorAESProbabilityProfile P hsplit g c y))
    (hzero : indicatorAESProbabilityProfile P hsplit g c 0 = 0)
    (hupper :
      ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0),
        indicatorAESProbabilityProfile P hsplit g c t / t ≤ c / (1 - q0))
    {p1 : Level} (hp1 : (p1 : ℝ) < 1)
    (hpoint : c / (1 - q0) < (c - g p1) / (1 - (p1 : ℝ))) :
    False := by
  have ht1 : 1 - (p1 : ℝ) ∈ Set.Ioc (0 : ℝ) 1 := by
    constructor
    · linarith
    · have hp1_nonneg : 0 ≤ (p1 : ℝ) := p1.2.1
      linarith
  have hratio :
      c / (1 - q0) <
        indicatorAESProbabilityProfile P hsplit g c (1 - (p1 : ℝ)) / (1 - (p1 : ℝ)) := by
    have hlower :=
      indicatorAESProbabilityProfile_ratio_ge_at_level (P := P) hsplit g hc hgnonneg hp1
    exact lt_of_lt_of_le hpoint hlower
  exact not_eventually_le_ratio_nhdsWithin_zero_of_midpoint_above hmid hzero ht1 hratio hupper

/-- AES-specific midpoint/cutoff contradiction package for the infinite-left case. -/
theorem infiniteLeft_indicatorAES_contradiction_of_submodular_cutoff
    (hsplit : HasFullEventSplitting P) (g : Level → ℝ) {c : ℝ}
    (hc : 0 < c) (hsub : Submodular (AES P g)) (hg0 : g 0 = 0)
    (hmono : _root_.Monotone g) (hgnonneg : ∀ p : Level, 0 ≤ g p)
    {q0 bar p1 : Level}
    (hq0bar : (q0 : ℝ) < (bar : ℝ)) (hbar1 : (bar : ℝ) < 1)
    (hq0pos : 0 < g q0) (hlarge : ∀ p : Level, (bar : ℝ) < (p : ℝ) → c < g p)
    (hp1 : (p1 : ℝ) < 1)
    (hpoint : c / (1 - (q0 : ℝ)) < (c - g p1) / (1 - (p1 : ℝ))) :
    False := by
  have hmid :
      ∀ ⦃x y : ℝ⦄, x ∈ Set.Icc (0 : ℝ) 1 → y ∈ Set.Icc (0 : ℝ) 1 →
        indicatorAESProbabilityProfile P hsplit g c (midpoint ℝ x y) ≥
          midpoint ℝ (indicatorAESProbabilityProfile P hsplit g c x)
            (indicatorAESProbabilityProfile P hsplit g c y) := by
    intro x y hx hy
    exact midpoint_ge_average_indicatorAESProbabilityProfile (P := P) hsplit g (le_of_lt hc) hsub
      hx hy
  have hzero := indicatorAESProbabilityProfile_zero_eq_zero (P := P) hsplit g c hg0 hgnonneg
  have hupper :=
    indicatorAESProbabilityProfile_ratio_eventually_le_of_cutoff (P := P) hsplit g hc hmono
      hgnonneg hq0bar hbar1 hq0pos hlarge
  exact infiniteLeft_indicatorAES_contradiction_of_midpoint_eventuallyUpper (P := P) hsplit g hc
    hgnonneg hmid hzero hupper hp1 hpoint

/-- A paper-style large-`λ` assumption implies the pointwise ratio gap required by the
cutoff contradiction theorem. -/
theorem infiniteLeft_indicatorAES_contradiction_of_submodular_cutoff_of_lambda
    (hsplit : HasFullEventSplitting P) (g : Level → ℝ) {c : ℝ}
    (hc : 0 < c) (hsub : Submodular (AES P g)) (hg0 : g 0 = 0)
    (hmono : _root_.Monotone g) (hgnonneg : ∀ p : Level, 0 ≤ g p)
    {q0 bar p1 : Level}
    (hq0p1 : (q0 : ℝ) < (p1 : ℝ)) (hq0bar : (q0 : ℝ) < (bar : ℝ)) (hbar1 : (bar : ℝ) < 1)
    (hq0pos : 0 < g q0) (hlarge : ∀ p : Level, (bar : ℝ) < (p : ℝ) → c < g p)
    (hp1 : (p1 : ℝ) < 1)
    (hc_large : g p1 * (1 - (q0 : ℝ)) / ((p1 : ℝ) - (q0 : ℝ)) < c) :
    False := by
  have hpoint :=
    point_ratio_strict_of_lambda_bound (g := g) hq0p1 hp1 hc_large
  exact infiniteLeft_indicatorAES_contradiction_of_submodular_cutoff (P := P) hsplit g hc hsub hg0
    hmono hgnonneg hq0bar hbar1 hq0pos hlarge hp1 hpoint

/-- Same contradiction, phrased with an existential tail witness instead of a named cutoff. -/
theorem infiniteLeft_indicatorAES_contradiction_of_submodular_eventuallyLarge
    (hsplit : HasFullEventSplitting P) (g : Level → ℝ) {c : ℝ}
    (hc : 0 < c) (hsub : Submodular (AES P g)) (hg0 : g 0 = 0)
    (hmono : _root_.Monotone g) (hgnonneg : ∀ p : Level, 0 ≤ g p)
    {q0 p1 : Level} (hq0p1 : (q0 : ℝ) < (p1 : ℝ))
    (hq0pos : 0 < g q0) (hp1 : (p1 : ℝ) < 1)
    (hc_large : g p1 * (1 - (q0 : ℝ)) / ((p1 : ℝ) - (q0 : ℝ)) < c)
    (htail : ∃ bar : Level, (q0 : ℝ) < (bar : ℝ) ∧ (bar : ℝ) < 1 ∧
      ∀ p : Level, (bar : ℝ) < (p : ℝ) → c < g p) :
    False := by
  rcases htail with ⟨bar, hq0bar, hbar1, hlarge⟩
  exact infiniteLeft_indicatorAES_contradiction_of_submodular_cutoff_of_lambda (P := P) hsplit
    g hc hsub hg0 hmono hgnonneg hq0p1 hq0bar hbar1 hq0pos hlarge hp1 hc_large

/-- Version of the previous contradiction theorem where the positivity of `g q₀` is discharged
from the statement that `p₀` is the supremum of the zero set of `g`. -/
theorem infiniteLeft_indicatorAES_contradiction_of_submodular_eventuallyLarge_of_isLUB
    (hsplit : HasFullEventSplitting P) (g : Level → ℝ) {c p0 : ℝ}
    (hc : 0 < c) (hsub : Submodular (AES P g)) (hg0 : g 0 = 0)
    (hmono : _root_.Monotone g) (hgnonneg : ∀ p : Level, 0 ≤ g p)
    (hsup : IsLUB (zeroSetReal g) p0)
    {q0 p1 : Level} (hp0q0 : p0 < (q0 : ℝ)) (hq0p1 : (q0 : ℝ) < (p1 : ℝ))
    (hp1 : (p1 : ℝ) < 1)
    (hc_large : g p1 * (1 - (q0 : ℝ)) / ((p1 : ℝ) - (q0 : ℝ)) < c)
    (htail : ∃ bar : Level, (q0 : ℝ) < (bar : ℝ) ∧ (bar : ℝ) < 1 ∧
      ∀ p : Level, (bar : ℝ) < (p : ℝ) → c < g p) :
    False := by
  have hq0pos := positive_of_gt_isLUB_zeroSetReal g hsup hgnonneg hp0q0
  exact infiniteLeft_indicatorAES_contradiction_of_submodular_eventuallyLarge (P := P) hsplit g
    hc hsub hg0 hmono hgnonneg hq0p1 hq0pos hp1 hc_large htail

/-- Same contradiction theorem, now stated with the more natural fixed-level tail assumption
`EventuallyLargeBeforeOne g c` instead of an explicit cutoff witness. -/
theorem infiniteLeft_indicatorAES_contradiction_of_submodular_leftLarge_of_isLUB
    (hsplit : HasFullEventSplitting P) (g : Level → ℝ) {c p0 : ℝ}
    (hc : 0 < c) (hsub : Submodular (AES P g)) (hg0 : g 0 = 0)
    (hmono : _root_.Monotone g) (hgnonneg : ∀ p : Level, 0 ≤ g p)
    (hsup : IsLUB (zeroSetReal g) p0) (htail : EventuallyLargeBeforeOne g c)
    {q0 p1 : Level} (hp0q0 : p0 < (q0 : ℝ)) (hq0p1 : (q0 : ℝ) < (p1 : ℝ))
    (hp1 : (p1 : ℝ) < 1)
    (hc_large : g p1 * (1 - (q0 : ℝ)) / ((p1 : ℝ) - (q0 : ℝ)) < c) :
    False := by
  have hq01 : (q0 : ℝ) < 1 := lt_trans hq0p1 hp1
  have htail' :=
    exists_tailWitnessAbove_of_eventuallyLargeBeforeOne g hq01 htail
  exact infiniteLeft_indicatorAES_contradiction_of_submodular_eventuallyLarge_of_isLUB (P := P)
    hsplit g hc hsub hg0 hmono hgnonneg hsup hp0q0 hq0p1 hp1 hc_large htail'

/-- Lean-friendly infinite-left non-submodularity statement for AES. This is the packaged form of
the contradiction bridge proved above. -/
theorem not_submodular_AES_of_leftLarge_of_isLUB
    (hsplit : HasFullEventSplitting P) (g : Level → ℝ) {c p0 : ℝ}
    (hc : 0 < c) (hg0 : g 0 = 0) (hmono : _root_.Monotone g)
    (hgnonneg : ∀ p : Level, 0 ≤ g p)
    (hsup : IsLUB (zeroSetReal g) p0) (htail : EventuallyLargeBeforeOne g c)
    {q0 p1 : Level} (hp0q0 : p0 < (q0 : ℝ)) (hq0p1 : (q0 : ℝ) < (p1 : ℝ))
    (hp1 : (p1 : ℝ) < 1)
    (hc_large : g p1 * (1 - (q0 : ℝ)) / ((p1 : ℝ) - (q0 : ℝ)) < c) :
    ¬ Submodular (AES P g) := by
  intro hsub
  exact infiniteLeft_indicatorAES_contradiction_of_submodular_leftLarge_of_isLUB (P := P)
    hsplit g hc hsub hg0 hmono hgnonneg hsup htail hp0q0 hq0p1 hp1 hc_large

/-- Real-valued penalties that become arbitrarily large near `1` cannot generate a submodular AES
once the zero set has a strict supremum below `1`.

This is the Lean-valid contradiction half of the paper's infinite-left corollary in the current
`g : Level → ℝ` model. The paper's final collapse to a single `ES_{p₀}` requires an
extended-valued penalty model, while the present theorem already rules out submodularity for
genuinely real-valued penalties with an arbitrarily large right tail. -/
theorem not_submodular_AES_of_forall_eventuallyLarge_of_isLUB
    (hsplit : HasFullEventSplitting P) (g : Level → ℝ) {p0 : ℝ}
    (hg0 : g 0 = 0) (hmono : _root_.Monotone g)
    (hgnonneg : ∀ p : Level, 0 ≤ g p)
    (hsup : IsLUB (zeroSetReal g) p0) (hp01 : p0 < 1)
    (htail : ∀ c : ℝ, EventuallyLargeBeforeOne g c) :
    ¬ Submodular (AES P g) := by
  have hp0_nonneg : 0 ≤ p0 := by
    have hzero_mem : (0 : ℝ) ∈ zeroSetReal g := ⟨0, by simp [hg0]⟩
    exact hsup.1 hzero_mem
  let q0 : Level := ⟨(p0 + 1) / 2, by
    constructor
    · linarith [show -1 ≤ p0 by linarith]
    · linarith⟩
  let p1 : Level := ⟨(((q0 : ℝ) + 1) / 2), by
    constructor
    · have hq0_nonneg : 0 ≤ (q0 : ℝ) := q0.2.1
      linarith
    · have hq01 : (q0 : ℝ) < 1 := by
        change (p0 + 1) / 2 < 1
        linarith
      linarith⟩
  have hp0q0 : p0 < (q0 : ℝ) := by
    change p0 < (p0 + 1) / 2
    linarith
  have hq01 : (q0 : ℝ) < 1 := by
    change (p0 + 1) / 2 < 1
    linarith
  have hq0p1 : (q0 : ℝ) < (p1 : ℝ) := by
    change (q0 : ℝ) < (((q0 : ℝ) + 1) / 2)
    linarith
  have hp11 : (p1 : ℝ) < 1 := by
    change (((q0 : ℝ) + 1) / 2) < 1
    linarith
  let c : ℝ := g p1 * (1 - (q0 : ℝ)) / ((p1 : ℝ) - (q0 : ℝ)) + 1
  have hc : 0 < c := by
    have hratio_nonneg : 0 ≤ g p1 * (1 - (q0 : ℝ)) / ((p1 : ℝ) - (q0 : ℝ)) := by
      refine div_nonneg ?_ ?_
      · exact mul_nonneg (hgnonneg p1) (by linarith)
      · linarith
    dsimp [c]
    linarith
  have hc_large : g p1 * (1 - (q0 : ℝ)) / ((p1 : ℝ) - (q0 : ℝ)) < c := by
    dsimp [c]
    linarith
  exact not_submodular_AES_of_leftLarge_of_isLUB (P := P) hsplit g hc hg0 hmono hgnonneg
    hsup (htail c) hp0q0 hq0p1 hp11 hc_large

/-- Infinite-left contradiction template with the origin value discharged automatically by
`g(0) = 0`. -/
theorem infiniteLeft_indicatorAES_contradiction
    (hsplit : HasFullEventSplitting P) (g : Level → ℝ) {c p0 : ℝ}
    (hc : 0 < c) (hp0 : p0 ∈ Set.Icc (0 : ℝ) 1) (hg0 : g 0 = 0)
    (hgnonneg : ∀ p : Level, 0 ≤ g p)
    (hconc :
      ConcaveOn ℝ (Set.Icc (0 : ℝ) 1) (indicatorAESProbabilityProfile P hsplit g c))
    (hlim :
      Tendsto (fun t => indicatorAESProbabilityProfile P hsplit g c t / t)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (c / (1 - p0))))
    {p1 : Level} (hp0p1 : p0 < (p1 : ℝ)) (hp1 : (p1 : ℝ) < 1)
    (hpoint : c / (1 - p0) < (c - g p1) / (1 - (p1 : ℝ))) :
    False := by
  refine infiniteLeft_indicatorAES_contradiction_of_concave_originSlope (P := P) hsplit g hc hp0
    hgnonneg hconc ?_ hlim hp0p1 hp1 hpoint
  exact indicatorAESProbabilityProfile_zero_eq_zero (P := P) hsplit g c hg0 hgnonneg

end EventProfiles

end AesSubmodularity
