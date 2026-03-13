import Formalization.AesSubmodularity.Bridge
import Formalization.RiskMeasure.AtomlessUniform
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.NonIntegrable
import Mathlib.MeasureTheory.Constructions.UnitInterval

/-!
# Finite Convex AES Folded Migration Layer

This module is the migration entry point for the finite-tail convex AES argument.

This module develops the folded-witness route for the finite-tail convex AES
argument, together with the support-line, transport, and contradiction tools
needed for the current verified theorem.
-/

noncomputable section

open MeasureTheory
open RiskMeasure
open scoped Topology unitInterval

namespace AesSubmodularity

section AffineSupportLine

/-- Affine line through `g(q)` with slope `a`, written on `Level`. -/
def affineSupportLine (g : Level → ℝ) (q : Level) (a : ℝ) : Level → ℝ := fun p =>
  g q + a * ((p : ℝ) - (q : ℝ))

@[simp] theorem affineSupportLine_apply_base (g : Level → ℝ) (q : Level) (a : ℝ) :
    affineSupportLine g q a q = g q := by
  simp [affineSupportLine]

@[simp] theorem affineSupportLine_apply_zero (g : Level → ℝ) (q : Level) (a : ℝ) :
    affineSupportLine g q a 0 = g q - a * (q : ℝ) := by
  simp [affineSupportLine]
  ring

@[simp] theorem affineSupportLine_apply_one (g : Level → ℝ) (q : Level) (a : ℝ) :
    affineSupportLine g q a 1 = g q + a * (1 - (q : ℝ)) := by
  simp [affineSupportLine]

@[simp] theorem affineSupportLine_apply_level (g : Level → ℝ) (q p : Level) (a : ℝ) :
    affineSupportLine g q a p = g q + a * ((p : ℝ) - (q : ℝ)) := by
  simp [affineSupportLine]

/-- An interior derivative gives a supporting affine line for a convex function on `[0,1]`. -/
theorem affineSupportLine_le_of_convexOn_hasDerivAt
    {f : ℝ → ℝ} {q : Level} {a : ℝ}
    (hconv : ConvexOn ℝ (Set.Icc (0 : ℝ) 1) f)
    (hq : (q : ℝ) ∈ Set.Ioo (0 : ℝ) 1)
    (hderiv : HasDerivAt f a (q : ℝ)) :
    ∀ p : Level, affineSupportLine (fun r : Level => f r) q a p ≤ f p := by
  intro p
  let x : ℝ := (q : ℝ)
  have hxmem : x ∈ Set.Icc (0 : ℝ) 1 := by
    exact ⟨le_of_lt hq.1, le_of_lt hq.2⟩
  rcases lt_trichotomy (p : ℝ) x with hpx | hpx | hxp
  · have hSlope : slope f (p : ℝ) x ≤ a := by
      simpa [x] using
        hconv.slope_le_of_hasDerivAt (x := (p : ℝ)) (y := x) p.2 hxmem hpx hderiv
    have hslope' : (f x - f p) / (x - (p : ℝ)) ≤ a := by
      simpa [slope_def_field] using hSlope
    have hden : 0 < x - (p : ℝ) := sub_pos.mpr hpx
    have hmul : f x - f p ≤ a * (x - (p : ℝ)) := (div_le_iff₀ hden).mp hslope'
    have hline : f x + a * ((p : ℝ) - x) ≤ f p := by
      linarith
    simpa [affineSupportLine, x] using hline
  · have hline : f x + a * ((p : ℝ) - x) = f p := by
      simp [hpx]
    simpa [affineSupportLine, x] using le_of_eq hline
  · have hSlope : a ≤ slope f x (p : ℝ) := by
      simpa [x] using
        hconv.le_slope_of_hasDerivAt (x := x) (y := (p : ℝ)) hxmem p.2 hxp hderiv
    have hslope' : a ≤ (f p - f x) / ((p : ℝ) - x) := by
      simpa [slope_def_field] using hSlope
    have hden : 0 < (p : ℝ) - x := sub_pos.mpr hxp
    have hmul : a * ((p : ℝ) - x) ≤ f p - f x := (le_div_iff₀ hden).mp hslope'
    have hline : f x + a * ((p : ℝ) - x) ≤ f p := by
      linarith
    simpa [affineSupportLine, x] using hline

/-- The left derivative at an interior point yields a supporting affine line on `[0,1]`. -/
theorem affineSupportLine_le_of_convexOn_leftDeriv
    {f : ℝ → ℝ} {q : Level}
    (hconv : ConvexOn ℝ (Set.Icc (0 : ℝ) 1) f)
    (hq : (q : ℝ) ∈ Set.Ioo (0 : ℝ) 1) :
    ∀ p : Level,
      affineSupportLine
          (fun r : Level => f r) q (derivWithin f (Set.Iio (q : ℝ)) (q : ℝ)) p ≤
        f p := by
  intro p
  have hqint : (q : ℝ) ∈ interior (Set.Icc (0 : ℝ) 1) := by
    simpa [interior_Icc] using hq
  rcases lt_trichotomy (p : ℝ) (q : ℝ) with hpq | hpq | hqp
  · have hslope :
        slope f (p : ℝ) (q : ℝ) ≤ derivWithin f (Set.Iio (q : ℝ)) (q : ℝ) :=
      hconv.slope_le_leftDeriv_of_mem_interior p.2 hqint hpq
    have hslope' :
        (f (q : ℝ) - f p) / ((q : ℝ) - (p : ℝ)) ≤
          derivWithin f (Set.Iio (q : ℝ)) (q : ℝ) := by
      simpa [slope_def_field] using hslope
    have hden : 0 < (q : ℝ) - (p : ℝ) := sub_pos.mpr hpq
    have hmul :
        f (q : ℝ) - f p ≤ derivWithin f (Set.Iio (q : ℝ)) (q : ℝ) * ((q : ℝ) - (p : ℝ)) :=
      (div_le_iff₀ hden).mp hslope'
    have hline :
        f (q : ℝ) -
            derivWithin f (Set.Iio (q : ℝ)) (q : ℝ) * ((q : ℝ) - (p : ℝ)) ≤
          f p := by
      linarith
    have hrewrite :
        f (q : ℝ) +
            derivWithin f (Set.Iio (q : ℝ)) (q : ℝ) * ((p : ℝ) - (q : ℝ)) =
          f (q : ℝ) -
            derivWithin f (Set.Iio (q : ℝ)) (q : ℝ) * ((q : ℝ) - (p : ℝ)) := by
      ring
    rw [affineSupportLine, hrewrite]
    exact hline
  · have hpq' : p = q := Subtype.ext hpq
    subst hpq'
    simp [affineSupportLine]
  · have hldrdr :
        derivWithin f (Set.Iio (q : ℝ)) (q : ℝ) ≤ derivWithin f (Set.Ioi (q : ℝ)) (q : ℝ) :=
      hconv.leftDeriv_le_rightDeriv_of_mem_interior hqint
    have hright :
        derivWithin f (Set.Ioi (q : ℝ)) (q : ℝ) ≤ slope f (q : ℝ) (p : ℝ) :=
      hconv.rightDeriv_le_slope_of_mem_interior hqint p.2 hqp
    have hslope :
        derivWithin f (Set.Iio (q : ℝ)) (q : ℝ) ≤ slope f (q : ℝ) (p : ℝ) :=
      hldrdr.trans hright
    have hslope' :
        derivWithin f (Set.Iio (q : ℝ)) (q : ℝ) ≤
          (f p - f (q : ℝ)) / ((p : ℝ) - (q : ℝ)) := by
      simpa [slope_def_field] using hslope
    have hden : 0 < (p : ℝ) - (q : ℝ) := sub_pos.mpr hqp
    have hmul :
        derivWithin f (Set.Iio (q : ℝ)) (q : ℝ) * ((p : ℝ) - (q : ℝ)) ≤ f p - f (q : ℝ) :=
      (le_div_iff₀ hden).mp hslope'
    have hline :
        f (q : ℝ) +
            derivWithin f (Set.Iio (q : ℝ)) (q : ℝ) * ((p : ℝ) - (q : ℝ)) ≤
          f p := by
      linarith
    simpa [affineSupportLine] using hline

/-- If a convex function vanishes at `0` and is positive at an interior point, then the
left derivative at that point is strictly positive. -/
theorem leftDeriv_pos_of_convexOn_pos_before_one_at
    {f : ℝ → ℝ} (hconv : ConvexOn ℝ (Set.Icc (0 : ℝ) 1) f)
    (h0 : f 0 = 0) {q : Level} (hq : (q : ℝ) ∈ Set.Ioo (0 : ℝ) 1) (hqpos : 0 < f q) :
    0 < derivWithin f (Set.Iio (q : ℝ)) (q : ℝ) := by
  have hqint : (q : ℝ) ∈ interior (Set.Icc (0 : ℝ) 1) := by
    simpa [interior_Icc] using hq
  have hslope :
      slope f 0 (q : ℝ) ≤ derivWithin f (Set.Iio (q : ℝ)) (q : ℝ) :=
    hconv.slope_le_leftDeriv_of_mem_interior (by simp) hqint hq.1
  have hslopepos : 0 < slope f 0 (q : ℝ) := by
    rw [slope_def_field, h0]
    have hnum : 0 < f q - 0 := by simpa using hqpos
    have hden : 0 < (q : ℝ) - 0 := sub_pos.mpr hq.1
    exact div_pos hnum hden
  exact lt_of_lt_of_le hslopepos hslope

/-- If a convex function vanishes at `0` and is positive at an interior point where it is
differentiable, then its derivative there is strictly positive. -/
theorem deriv_pos_of_convexOn_pos_before_one_at
    {f : ℝ → ℝ} (hconv : ConvexOn ℝ (Set.Icc (0 : ℝ) 1) f)
    (h0 : f 0 = 0) {q : Level} (hq : (q : ℝ) ∈ Set.Ioo (0 : ℝ) 1)
    (hdiff : DifferentiableAt ℝ f q) (hqpos : 0 < f q) :
    0 < deriv f q := by
  have hslope : slope f 0 (q : ℝ) ≤ deriv f q := by
    simpa using hconv.slope_le_deriv (by simp) q.2 hq.1 hdiff
  have hslopepos : 0 < slope f 0 (q : ℝ) := by
    rw [slope_def_field, h0]
    have hnum : 0 < f q - 0 := by simpa using hqpos
    have hden : 0 < (q : ℝ) - 0 := sub_pos.mpr hq.1
    exact div_pos hnum hden
  exact lt_of_lt_of_le hslopepos hslope

end AffineSupportLine

section FrontHalfGrowth

/-- If `m' ≥ m / (1 - x)` on `(x0, 1)`, then the auxiliary function
`x ↦ (1 - x) * m x` is monotone on `[x0, 1]`.

This is the core analytic step behind the contradiction argument used to produce a
good folded witness point: a positive value at `x0` then propagates into a
`const / (1 - x)` lower bound near `1`. -/
theorem monotoneOn_one_sub_mul_of_deriv_ge_div
    {x0 : ℝ} (hx0 : x0 < 1) {m : ℝ → ℝ}
    (hmcont : ContinuousOn m (Set.Icc x0 1))
    (hmdiff : DifferentiableOn ℝ m (Set.Ioo x0 1))
    (hineq : ∀ x ∈ Set.Ioo x0 1, m x / (1 - x) ≤ deriv m x) :
    MonotoneOn (fun x => (1 - x) * m x) (Set.Icc x0 1) := by
  have hx0ne : x0 ≠ 1 := ne_of_lt hx0
  refine monotoneOn_of_deriv_nonneg (D := Set.Icc x0 1) (convex_Icc x0 (1 : ℝ)) ?_ ?_ ?_
  · exact (continuousOn_const.sub continuousOn_id).mul hmcont
  · intro x hx
    have hx' : x ∈ Set.Ioo x0 1 := by
      simpa [interior_Icc, hx0ne] using hx
    have hmdiffAt : DifferentiableAt ℝ m x :=
      (hmdiff x hx').differentiableAt (IsOpen.mem_nhds isOpen_Ioo hx')
    have h1mx : HasDerivAt (fun y : ℝ => 1 - y) (-1) x := by
      simpa using (hasDerivAt_id x).const_sub (1 : ℝ)
    exact (h1mx.mul hmdiffAt.hasDerivAt).differentiableAt.differentiableWithinAt
  · intro x hx
    have hx' : x ∈ Set.Ioo x0 1 := by
      simpa [interior_Icc, hx0ne] using hx
    have hmdiffAt : DifferentiableAt ℝ m x :=
      (hmdiff x hx').differentiableAt (IsOpen.mem_nhds isOpen_Ioo hx')
    have h1mx : HasDerivAt (fun y : ℝ => 1 - y) (-1) x := by
      simpa using (hasDerivAt_id x).const_sub (1 : ℝ)
    have haux :
        HasDerivAt (fun y : ℝ => (1 - y) * m y) ((-1) * m x + (1 - x) * deriv m x) x := by
      simpa using h1mx.mul hmdiffAt.hasDerivAt
    have hmul : m x ≤ (1 - x) * deriv m x := by
      have hone : 0 < 1 - x := sub_pos.mpr hx'.2
      have hmul' : m x ≤ deriv m x * (1 - x) := (div_le_iff₀ hone).mp (hineq x hx')
      simpa [mul_comm] using hmul'
    rw [haux.deriv]
    linarith

/-- Under the same differential inequality, positivity at `x0` yields the explicit lower bound
`m x ≥ ((1 - x0) * m x0) / (1 - x)` for every `x ∈ [x0, 1)`. -/
theorem lower_bound_div_one_sub_of_deriv_ge_div
    {x0 : ℝ} (hx0 : x0 < 1) {m : ℝ → ℝ}
    (hmcont : ContinuousOn m (Set.Icc x0 1))
    (hmdiff : DifferentiableOn ℝ m (Set.Ioo x0 1))
    (hineq : ∀ x ∈ Set.Ioo x0 1, m x / (1 - x) ≤ deriv m x)
    {x : ℝ} (hx : x ∈ Set.Ico x0 1) :
    ((1 - x0) * m x0) / (1 - x) ≤ m x := by
  have hmono :=
    monotoneOn_one_sub_mul_of_deriv_ge_div (x0 := x0) hx0 hmcont hmdiff hineq
  have hle :
      (1 - x0) * m x0 ≤ (1 - x) * m x := by
    exact hmono ⟨le_rfl, le_of_lt hx0⟩ ⟨hx.1, le_of_lt hx.2⟩ hx.1
  have hden : 0 < 1 - x := sub_pos.mpr hx.2
  exact (div_le_iff₀ hden).2 (by simpa [mul_comm] using hle)

/-- A function on `(x0, 1)` that dominates a positive multiple of `(1 - x)⁻¹`
cannot be interval-integrable on `x0..1`. -/
theorem not_intervalIntegrable_of_lower_bound_inv_one_sub
    {x0 K : ℝ} (hx0 : x0 < 1) (hK : 0 < K) {m : ℝ → ℝ}
    (hnonneg : ∀ x ∈ Set.Icc x0 1, 0 ≤ m x)
    (hbound : ∀ x ∈ Set.Ico x0 1, K * (1 - x)⁻¹ ≤ m x) :
    ¬ IntervalIntegrable m volume x0 1 := by
  have hsub_inv :
      ¬ IntervalIntegrable (fun x : ℝ => (x - 1)⁻¹) volume x0 1 := by
    rw [intervalIntegrable_sub_inv_iff]
    have hmem : (1 : ℝ) ∈ Set.uIcc x0 1 := by
      rw [Set.uIcc_of_le (le_of_lt hx0)]
      simp [le_of_lt hx0]
    simp [hx0.ne, hmem]
  have hone_sub_inv :
      ¬ IntervalIntegrable (fun x : ℝ => (1 - x)⁻¹) volume x0 1 := by
    intro h
    apply hsub_inv
    have hneg : IntervalIntegrable (fun x : ℝ => (-1 : ℝ) * ((1 - x)⁻¹)) volume x0 1 :=
      h.const_mul (-1 : ℝ)
    convert hneg using 1
    ext x
    calc
      (x - 1)⁻¹ = (-(1 - x))⁻¹ := by congr; ring
      _ = -((1 - x)⁻¹) := by rw [inv_neg]
      _ = (-1 : ℝ) * ((1 - x)⁻¹) := by ring
  have hscaled_inv :
      ¬ IntervalIntegrable (fun x : ℝ => K * (1 - x)⁻¹) volume x0 1 := by
    intro h
    apply hone_sub_inv
    have h' : IntervalIntegrable (fun x : ℝ => K⁻¹ * (K * (1 - x)⁻¹)) volume x0 1 :=
      h.const_mul K⁻¹
    simpa [mul_assoc, hK.ne'] using h'
  intro hm
  have hcomp :
      IntervalIntegrable (fun x : ℝ => K * (1 - x)⁻¹) volume x0 1 := by
    refine hm.mono_fun' ?_ ?_
    · have hmeas : Measurable (fun x : ℝ => K * (1 - x)⁻¹) := by
        fun_prop
      exact hmeas.aestronglyMeasurable
    · refine (ae_restrict_mem measurableSet_uIoc).mono ?_
      intro x hx
      have hx' : x ∈ Set.Ioc x0 1 := by
        simpa [Set.uIoc_of_le (le_of_lt hx0)] using hx
      by_cases hx1 : x = 1
      · subst hx1
        have hnonneg1 : 0 ≤ m 1 := hnonneg 1 (by simp [le_of_lt hx0])
        simpa using hnonneg1
      · have hxlt : x < 1 := lt_of_le_of_ne hx'.2 hx1
        have hxIco : x ∈ Set.Ico x0 1 := ⟨le_of_lt hx'.1, hxlt⟩
        have hnonnegCmp : 0 ≤ K * (1 - x)⁻¹ := by
          have hden : 0 ≤ (1 - x)⁻¹ := inv_nonneg.mpr (sub_nonneg.mpr hxlt.le)
          exact mul_nonneg hK.le hden
        change ‖K * (1 - x)⁻¹‖ ≤ m x
        rw [Real.norm_of_nonneg hnonnegCmp]
        exact hbound x hxIco
  exact hscaled_inv hcomp

/-- A differential inequality of the form `m' ≥ m / (1 - x)` together with positivity at
`x0` forces non-integrability on `x0..1`. -/
theorem not_intervalIntegrable_of_deriv_ge_div_of_pos
    {x0 : ℝ} (hx0 : x0 < 1) {m : ℝ → ℝ}
    (hmcont : ContinuousOn m (Set.Icc x0 1))
    (hmdiff : DifferentiableOn ℝ m (Set.Ioo x0 1))
    (hineq : ∀ x ∈ Set.Ioo x0 1, m x / (1 - x) ≤ deriv m x)
    (hnonneg : ∀ x ∈ Set.Icc x0 1, 0 ≤ m x)
    (hx0pos : 0 < m x0) :
    ¬ IntervalIntegrable m volume x0 1 := by
  have hK : 0 < (1 - x0) * m x0 := by
    exact mul_pos (sub_pos.mpr hx0) hx0pos
  apply not_intervalIntegrable_of_lower_bound_inv_one_sub (x0 := x0) (K := (1 - x0) * m x0)
    hx0 hK hnonneg
  intro x hx
  have hlow :=
    lower_bound_div_one_sub_of_deriv_ge_div (x0 := x0) hx0 hmcont hmdiff hineq hx
  simpa [div_eq_mul_inv, mul_assoc] using hlow

/-- An interval-integrable function that is positive at `x0` must violate the barrier
inequality `m' ≥ m / (1 - x)` at some interior point. This packages the contradiction step
used to extract the folded witness base point. -/
theorem exists_lt_deriv_barrier_of_intervalIntegrable
    {x0 : ℝ} (hx0 : x0 < 1) {m : ℝ → ℝ}
    (hmcont : ContinuousOn m (Set.Icc x0 1))
    (hmdiff : DifferentiableOn ℝ m (Set.Ioo x0 1))
    (hint : IntervalIntegrable m volume x0 1)
    (hnonneg : ∀ x ∈ Set.Icc x0 1, 0 ≤ m x)
    (hx0pos : 0 < m x0) :
    ∃ q ∈ Set.Ioo x0 1, deriv m q < m q / (1 - q) := by
  by_contra hq
  push_neg at hq
  exact
    (not_intervalIntegrable_of_deriv_ge_div_of_pos (x0 := x0) hx0 hmcont hmdiff hq
      hnonneg hx0pos) hint

/-- A Volterra-type interval barrier inequality forces the same harmonic lower bound that appears
in the smooth differential argument. This is the analytic bridge needed to replace Taylor
expansions by integral remainders in the convex front half. -/
theorem lower_bound_div_one_sub_of_interval_barrier
    {x0 y : ℝ} (hx0y : x0 < y) (hy1 : y < 1) {g : ℝ → ℝ}
    (hInt : IntervalIntegrable (fun t : ℝ => g t / (1 - t)) volume x0 y)
    (hbarrier : ∀ z ∈ Set.Icc x0 y, g x0 + ∫ t in x0..z, g t / (1 - t) ≤ g z)
    (hx0pos : 0 < g x0) :
    ((1 - x0) * g x0) / (1 - y) ≤ g y := by
  let n : ℝ → ℝ := fun z => g x0 + ∫ t in x0..z, g t / (1 - t)
  have hACint :
      AbsolutelyContinuousOnInterval (fun z : ℝ => ∫ t in x0..z, g t / (1 - t)) x0 y := by
    exact hInt.absolutelyContinuousOnInterval_intervalIntegral (c := x0)
      (by
        rw [Set.uIcc_of_le hx0y.le]
        exact ⟨le_rfl, hx0y.le⟩)
  have hACconst : AbsolutelyContinuousOnInterval (fun _ : ℝ => g x0) x0 y := by
    exact (LipschitzWith.const (g x0)).lipschitzOnWith.absolutelyContinuousOnInterval
  have hACn : AbsolutelyContinuousOnInterval n x0 y := by
    simpa [n] using hACconst.add hACint
  have hLip1mz : LipschitzWith 1 (fun z : ℝ => 1 - z) := by
    refine LipschitzWith.mk_one ?_
    intro u v
    simp [Real.dist_eq, sub_eq_add_neg, sub_sub, abs_sub_comm]
  have hAC1mz : AbsolutelyContinuousOnInterval (fun z : ℝ => 1 - z) x0 y := by
    exact hLip1mz.lipschitzOnWith.absolutelyContinuousOnInterval
  have hmulEq :
      ∫ z in x0..y, (-n z + g z) = (1 - y) * n y - (1 - x0) * n x0 := by
    calc
      ∫ z in x0..y, (-n z + g z)
          = ∫ z in x0..y, deriv (fun z : ℝ => 1 - z) z * n z +
              (1 - z) * deriv n z := by
              apply intervalIntegral.integral_congr_ae
              filter_upwards [hInt.ae_hasDerivAt_integral] with z hz hzmem
              have hzIcc : z ∈ Set.uIcc x0 y := by
                simpa [Set.uIoc_of_le hx0y.le, Set.uIcc_of_le hx0y.le] using
                  Set.Ioc_subset_Icc_self (by simpa [Set.uIoc_of_le hx0y.le] using hzmem)
              have hz1 : z ≠ 1 := by
                have hzy : z ≤ y := by
                  have hzIoc : z ∈ Set.Ioc x0 y := by simpa [Set.uIoc_of_le hx0y.le] using hzmem
                  exact hzIoc.2
                linarith
              have hderivInt :
                  deriv n z = g z / (1 - z) := by
                have hconst : HasDerivAt (fun _ : ℝ => g x0) 0 z := hasDerivAt_const z (g x0)
                have hintDeriv :
                    HasDerivAt (fun x : ℝ => ∫ t in x0..x, g t / (1 - t)) (g z / (1 - z)) z :=
                  hz hzIcc x0 (by
                    rw [Set.uIcc_of_le hx0y.le]
                    exact ⟨le_rfl, hx0y.le⟩)
                have hsum' : HasDerivAt n (g z / (1 - z)) z := by
                  dsimp [n]
                  simpa using hintDeriv.const_add (g x0)
                exact hsum'.deriv
              have hderivLin : deriv (fun z : ℝ => 1 - z) z = -1 := by
                simpa using ((hasDerivAt_id z).const_sub (1 : ℝ)).deriv
              rw [hderivLin, hderivInt]
              have hcancel : (1 - z) * (g z / (1 - z)) = g z := by
                field_simp [sub_ne_zero.mpr (Ne.symm hz1)]
              rw [hcancel]
              ring
      _ = (1 - y) * n y - (1 - x0) * n x0 := by
          simpa using hAC1mz.integral_deriv_mul_eq_sub hACn
  have hnonneg :
      0 ≤ ∫ z in x0..y, (-n z + g z) := by
    apply intervalIntegral.integral_nonneg_of_ae_restrict hx0y.le
    exact (MeasureTheory.ae_restrict_iff' measurableSet_Icc).2 <|
      Filter.Eventually.of_forall fun z hzIcc => by
        have hzdom := hbarrier z hzIcc
        change 0 ≤ -n z + g z
        linarith
  have hx0n : n x0 = g x0 := by
    simp [n]
  have hyn : n y ≤ g y := by
    exact hbarrier y ⟨hx0y.le, le_rfl⟩
  have hprod :
      (1 - x0) * g x0 ≤ (1 - y) * n y := by
    rw [hmulEq, hx0n] at hnonneg
    linarith
  have hyden : 0 < 1 - y := sub_pos.mpr hy1
  have hdiv : ((1 - x0) * g x0) / (1 - y) ≤ n y := by
    have hprod' : (1 - x0) * g x0 ≤ n y * (1 - y) := by
      simpa [mul_comm] using hprod
    exact (div_le_iff₀ hyden).2 hprod'
  exact hdiv.trans hyn

/-- Closed-form evaluation of the harmonic interval integral appearing in the bare-convex front
half. -/
theorem intervalIntegral_const_div_one_sub_eq_log
    {a b c : ℝ} (hab : a < b) (hb1 : b < 1) :
    ∫ x in a..b, c / (1 - x) = c * Real.log ((1 - a) / (1 - b)) := by
  have ha1 : a < 1 := lt_trans hab hb1
  have hba : 0 < 1 - b := sub_pos.mpr hb1
  have haa : 0 < 1 - a := sub_pos.mpr ha1
  calc
    ∫ x in a..b, c / (1 - x)
        = ∫ x in a..b, c * ((1 - x)⁻¹) := by simp [div_eq_mul_inv]
    _ = c * ∫ x in a..b, (1 - x)⁻¹ := by
          rw [intervalIntegral.integral_const_mul]
    _ = c * ∫ u in 1 - b..1 - a, u⁻¹ := by
          rw [intervalIntegral.integral_comp_sub_left]
    _ = c * Real.log ((1 - a) / (1 - b)) := by
          rw [integral_inv_of_pos hba haa]

end FrontHalfGrowth

section C2FrontHalf

/-- A `C²`-style version of the convex front half: if `f` is convex on `[0,1]`, vanishes at `0`,
is positive at the interior point `x0`, and `deriv f` is regular enough, then there exists a later
point where the barrier inequality needed by the folded contradiction fails. -/
theorem exists_lt_secondDeriv_barrier_of_convexOn
    {f : ℝ → ℝ} {x0 : ℝ} (hx0 : x0 ∈ Set.Ioo (0 : ℝ) 1)
    (hconv : ConvexOn ℝ (Set.Icc (0 : ℝ) 1) f) (h0 : f 0 = 0)
    (hfd : ∀ x ∈ Set.Icc (0 : ℝ) 1, DifferentiableAt ℝ f x)
    (hderivCont : ContinuousOn (deriv f) (Set.Icc x0 1))
    (hderivDiff : DifferentiableOn ℝ (deriv f) (Set.Ioo x0 1))
    (hx0pos : 0 < f x0) :
    ∃ q ∈ Set.Ioo x0 1, deriv (deriv f) q < deriv f q / (1 - q) := by
  let x0L : Level := ⟨x0, ⟨le_of_lt hx0.1, le_of_lt hx0.2⟩⟩
  have hx0Lmem : (x0L : ℝ) ∈ Set.Ioo (0 : ℝ) 1 := by
    simpa [x0L] using hx0
  have hx0Ldiff : DifferentiableAt ℝ f x0L := by
    exact hfd x0L x0L.2
  have hderivx0pos : 0 < deriv f x0 := by
    simpa [x0L] using
      deriv_pos_of_convexOn_pos_before_one_at hconv h0 hx0Lmem hx0Ldiff hx0pos
  have hmonoDeriv :
      MonotoneOn (deriv f) (Set.uIcc x0 1) := by
    have hmonoAll : MonotoneOn (deriv f) (Set.Icc (0 : ℝ) 1) := hconv.monotoneOn_deriv hfd
    simpa [Set.uIcc_of_le (le_of_lt hx0.2)] using
      (fun ⦃x hx y hy⦄ hxy => hmonoAll
        ⟨le_trans hx0.1.le hx.1, hx.2⟩
        ⟨le_trans hx0.1.le hy.1, hy.2⟩ hxy)
  have hmonoDerivIcc : MonotoneOn (deriv f) (Set.Icc x0 1) := by
    simpa [Set.uIcc_of_le (le_of_lt hx0.2)] using hmonoDeriv
  have hint : IntervalIntegrable (deriv f) volume x0 1 := hmonoDeriv.intervalIntegrable
  have hnonneg : ∀ x ∈ Set.Icc x0 1, 0 ≤ deriv f x := by
    intro x hx
    have hmono := hmonoDerivIcc ⟨le_rfl, le_of_lt hx0.2⟩ hx hx.1
    exact le_trans hderivx0pos.le hmono
  exact
    exists_lt_deriv_barrier_of_intervalIntegrable (x0 := x0) hx0.2 hderivCont hderivDiff hint
      hnonneg hderivx0pos

/-- The previous theorem packaged with the affine tangent line data used later in the folded
construction. -/
theorem exists_good_affineSupportLine_point_of_convexOn
    {f : ℝ → ℝ} {x0 : ℝ} (hx0 : x0 ∈ Set.Ioo (0 : ℝ) 1)
    (hconv : ConvexOn ℝ (Set.Icc (0 : ℝ) 1) f) (h0 : f 0 = 0)
    (hfd : ∀ x ∈ Set.Icc (0 : ℝ) 1, DifferentiableAt ℝ f x)
    (hderivCont : ContinuousOn (deriv f) (Set.Icc x0 1))
    (hderivDiff : DifferentiableOn ℝ (deriv f) (Set.Ioo x0 1))
    (hx0pos : 0 < f x0) :
    ∃ q : Level,
      x0 < (q : ℝ) ∧
      (q : ℝ) < 1 ∧
      0 < deriv f q ∧
      deriv (deriv f) q < deriv f q / (1 - q) ∧
      ∀ p : Level, affineSupportLine (fun r : Level => f r) q (deriv f q) p ≤ f p := by
  let x0L : Level := ⟨x0, ⟨le_of_lt hx0.1, le_of_lt hx0.2⟩⟩
  have hx0Lmem : (x0L : ℝ) ∈ Set.Ioo (0 : ℝ) 1 := by
    simpa [x0L] using hx0
  have hx0Ldiff : DifferentiableAt ℝ f x0L := by
    exact hfd x0L x0L.2
  have hderivx0pos : 0 < deriv f x0 := by
    simpa [x0L] using
      deriv_pos_of_convexOn_pos_before_one_at hconv h0 hx0Lmem hx0Ldiff hx0pos
  have hmonoDeriv :
      MonotoneOn (deriv f) (Set.uIcc x0 1) := by
    have hmonoAll : MonotoneOn (deriv f) (Set.Icc (0 : ℝ) 1) := hconv.monotoneOn_deriv hfd
    simpa [Set.uIcc_of_le (le_of_lt hx0.2)] using
      (fun ⦃x hx y hy⦄ hxy => hmonoAll
        ⟨le_trans hx0.1.le hx.1, hx.2⟩
        ⟨le_trans hx0.1.le hy.1, hy.2⟩ hxy)
  have hmonoDerivIcc : MonotoneOn (deriv f) (Set.Icc x0 1) := by
    simpa [Set.uIcc_of_le (le_of_lt hx0.2)] using hmonoDeriv
  obtain ⟨q, hq, hbarrier⟩ :=
    exists_lt_secondDeriv_barrier_of_convexOn hx0 hconv h0 hfd hderivCont hderivDiff hx0pos
  let qL : Level := ⟨q, ⟨le_of_lt (lt_trans hx0.1 hq.1), le_of_lt hq.2⟩⟩
  have hqLmem : (qL : ℝ) ∈ Set.Ioo (0 : ℝ) 1 := by
    exact ⟨lt_trans hx0.1 hq.1, hq.2⟩
  have hqLdiff : DifferentiableAt ℝ f qL := by
    exact hfd qL qL.2
  have hderivqpos : 0 < deriv f q := by
    have hmono := hmonoDerivIcc ⟨le_rfl, le_of_lt hx0.2⟩ ⟨hq.1.le, hq.2.le⟩ hq.1.le
    exact lt_of_lt_of_le hderivx0pos hmono
  refine ⟨qL, hq.1, hq.2, ?_, ?_, ?_⟩
  · simpa [qL] using hderivqpos
  · simpa [qL] using hbarrier
  · intro p
    exact affineSupportLine_le_of_convexOn_hasDerivAt hconv hqLmem hqLdiff.hasDerivAt p

end C2FrontHalf

section C2Gap

theorem exists_levelGap_of_lt_secondDeriv_barrier
    {f : ℝ → ℝ} {q : Level}
    (hcd : ContDiff ℝ 2 f)
    (hq0 : 0 < (q : ℝ)) (hq : (q : ℝ) < 1)
    (ha : 0 < deriv f q)
    (hbarrier : deriv (deriv f) q < deriv f q / (1 - q)) :
    ∃ p : Level,
      (p : ℝ) < (q : ℝ) ∧
      f p <
        affineSupportLine (fun r : Level => f r) q (deriv f q) p +
          deriv f q * ((q : ℝ) - (p : ℝ)) ^ 2 / (2 * (1 - (p : ℝ))) := by
  let a : ℝ := deriv f q
  let d : ℝ := iteratedDeriv 2 f q
  let s : ℝ := (max d 0 + a / (1 - (q : ℝ))) / 2
  have hqden : 0 < 1 - (q : ℝ) := by linarith
  have hd_eq : d = deriv (deriv f) q := by
    simp [d, iteratedDeriv_succ]
  have hd_lt_top : d < a / (1 - (q : ℝ)) := by
    simpa [a, hd_eq] using hbarrier
  have hs_pos : 0 < s := by
    have htop_pos : 0 < a / (1 - (q : ℝ)) := by
      exact div_pos ha hqden
    have hmax_nonneg : 0 ≤ max d 0 := le_max_right _ _
    dsimp [s]
    linarith
  have hd_lt_s : d < s := by
    have hmax_left : d ≤ max d 0 := le_max_left _ _
    dsimp [s]
    linarith
  have hs_lt_top : s < a / (1 - (q : ℝ)) := by
    have htop_pos : 0 < a / (1 - (q : ℝ)) := by
      exact div_pos ha hqden
    have hmax_lt : max d 0 < a / (1 - (q : ℝ)) := by
      refine max_lt hd_lt_top ?_
      exact htop_pos
    dsimp [s]
    linarith
  have hcont2 : Continuous (iteratedDeriv 2 f) := ContDiff.continuous_iteratedDeriv' 2 hcd
  have hpre :
      {x : ℝ | iteratedDeriv 2 f x < s} ∈ nhds (q : ℝ) := by
    have hsnhds : Set.Iio s ∈ nhds (iteratedDeriv 2 f q) := Iio_mem_nhds hd_lt_s
    simpa [Set.preimage, Function.comp] using
      (hcont2.continuousAt.preimage_mem_nhds hsnhds)
  obtain ⟨δ, hδpos, hδsub⟩ := Metric.mem_nhds_iff.mp hpre
  have hgap_to_coeff : 0 < a / s - (1 - (q : ℝ)) := by
    have hmul : s * (1 - (q : ℝ)) < a := (lt_div_iff₀ hqden).1 hs_lt_top
    have hmul' : (1 - (q : ℝ)) * s < a := by simpa [mul_comm] using hmul
    have haux : 1 - (q : ℝ) < a / s := (lt_div_iff₀ hs_pos).2 hmul'
    linarith
  let ε : ℝ := (a / s - (1 - (q : ℝ))) / 2
  have hεpos : 0 < ε := by
    dsimp [ε]
    linarith [hgap_to_coeff]
  let t : ℝ := min (δ / 2) (min ((q : ℝ) / 2) ε)
  have ht_pos : 0 < t := by
    dsimp [t]
    refine lt_min ?_ (lt_min ?_ hεpos)
    · linarith
    · linarith
  have ht_lt_δ : t < δ := by
    dsimp [t]
    have : t ≤ δ / 2 := min_le_left _ _
    linarith
  have ht_lt_q : t < (q : ℝ) := by
    dsimp [t]
    have : t ≤ (q : ℝ) / 2 := (min_le_right _ _).trans (min_le_left _ _)
    linarith
  have ht_le_ε : t ≤ ε := by
    dsimp [t]
    exact (min_le_right _ _).trans (min_le_right _ _)
  let p : Level := ⟨(q : ℝ) - t, by
    constructor
    · linarith
    · linarith [q.2.2]⟩
  have hp_lt_q : (p : ℝ) < (q : ℝ) := by
    dsimp [p]
    linarith
  have hp_lt_one : (p : ℝ) < 1 := lt_trans hp_lt_q hq
  have hpden : 0 < 1 - (p : ℝ) := by linarith
  have hs_lt_coeff : s < a / (1 - (p : ℝ)) := by
    have ht_lt_bound : t < a / s - (1 - (q : ℝ)) := by
      have hε_lt : ε < a / s - (1 - (q : ℝ)) := by
        dsimp [ε]
        linarith
      exact lt_of_le_of_lt ht_le_ε hε_lt
    have htmp : 1 - (q : ℝ) + t < a / s := by
      linarith
    have hmul : s * (1 - (q : ℝ) + t) < s * (a / s) := by
      exact mul_lt_mul_of_pos_left htmp hs_pos
    have hmul' : s * (1 - (p : ℝ)) < a := by
      have hsas : s * (a / s) = a := by
        field_simp [hs_pos.ne']
      rw [show 1 - (p : ℝ) = 1 - (q : ℝ) + t by
        dsimp [p]
        ring]
      simpa [hsas] using hmul
    exact (lt_div_iff₀ hpden).2 hmul'
  let hfun : ℝ → ℝ := fun z => f ((q : ℝ) - z)
  have hhcd : ContDiff ℝ 2 hfun := by
    dsimp [hfun]
    fun_prop
  have htmem : t ∈ Set.Icc (0 : ℝ) t := ⟨le_rfl.trans ht_pos.le, le_rfl⟩
  obtain ⟨ξ, hξ, hTaylor⟩ :=
    taylor_mean_remainder_lagrange_iteratedDeriv
      (x₀ := (0 : ℝ)) (x := t) (n := 1) ht_pos hhcd.contDiffOn
  have h0mem : (0 : ℝ) ∈ Set.Icc (0 : ℝ) t := ⟨le_rfl, ht_pos.le⟩
  have hiter1 :
      iteratedDerivWithin 1 hfun (Set.Icc (0 : ℝ) t) 0 = -a := by
    rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc ht_pos) (hhcd.of_le (by norm_num)).contDiffAt
      h0mem]
    simpa [hfun, a] using (deriv_comp_const_sub (f := f) (a := (q : ℝ)) (x := (0 : ℝ)))
  have hTaylorPoly :
      taylorWithinEval hfun 1 (Set.Icc (0 : ℝ) t) 0 t = f q - a * t := by
    rw [taylorWithinEval_succ, taylor_within_zero_eval, hiter1]
    simp [hfun, a]
    ring
  have hderivWithin0 : derivWithin hfun (Set.Icc (0 : ℝ) t) 0 = -a := by
    simpa using hiter1
  have hiter2 :
      iteratedDeriv 2 hfun ξ = iteratedDeriv 2 f ((q : ℝ) - ξ) := by
    let hcomp := iteratedDeriv_comp_const_sub (n := 2) (f := f) (s := (q : ℝ))
    have := congrArg (fun g => g ξ) hcomp
    simpa [hfun] using this
  have hξ_ball : (q : ℝ) - ξ ∈ Metric.ball (q : ℝ) δ := by
    rw [Metric.mem_ball, Real.dist_eq]
    have hξ_nonneg : 0 ≤ ξ := le_of_lt hξ.1
    have habs : |(q : ℝ) - ξ - q| = ξ := by
      have : (q : ℝ) - ξ - q = -ξ := by ring
      rw [this, abs_neg, abs_of_nonneg hξ_nonneg]
    rw [habs]
    exact lt_trans hξ.2 ht_lt_δ
  have hiter2_lt : iteratedDeriv 2 f ((q : ℝ) - ξ) < s := hδsub hξ_ball
  have hp_raw :
      f ((q : ℝ) - t) < f q - a * t + s * t ^ 2 / 2 := by
    have hTaylor' :
        f ((q : ℝ) - t) - (f q - a * t) =
          iteratedDeriv 2 f ((q : ℝ) - ξ) * t ^ 2 / 2 := by
      simpa [hfun, hderivWithin0, hiter2, a, mul_comm] using hTaylor
    have ht_sq_nonneg : 0 ≤ t ^ 2 / 2 := by positivity
    have hmul :
        iteratedDeriv 2 f ((q : ℝ) - ξ) * (t ^ 2 / 2) < s * (t ^ 2 / 2) :=
      mul_lt_mul_of_pos_right hiter2_lt (by positivity)
    have hmul' :
        iteratedDeriv 2 f ((q : ℝ) - ξ) * t ^ 2 / 2 < s * t ^ 2 / 2 := by
      simpa [mul_assoc, div_eq_mul_inv] using hmul
    linarith
  have hp_line :
      f p < affineSupportLine (fun r : Level => f r) q a p + s * ((q : ℝ) - (p : ℝ)) ^ 2 / 2 := by
    have hlinep : affineSupportLine (fun r : Level => f r) q a p = f q - a * t := by
      dsimp [p, affineSupportLine, a]
      ring
    have hpowp : ((q : ℝ) - (p : ℝ)) ^ 2 = t ^ 2 := by
      dsimp [p]
      ring
    simpa [p, hlinep, hpowp] using hp_raw
  have hcorr :
      affineSupportLine (fun r : Level => f r) q a p + s * ((q : ℝ) - (p : ℝ)) ^ 2 / 2 <
        affineSupportLine (fun r : Level => f r) q a p +
          a * ((q : ℝ) - (p : ℝ)) ^ 2 / (2 * (1 - (p : ℝ))) := by
    have hfactor :
        s * (((q : ℝ) - (p : ℝ)) ^ 2 / 2) <
          (a / (1 - (p : ℝ))) * (((q : ℝ) - (p : ℝ)) ^ 2 / 2) := by
      have hpos_factor : 0 < ((q : ℝ) - (p : ℝ)) ^ 2 / 2 := by
        have hqp : 0 < (q : ℝ) - (p : ℝ) := by linarith
        positivity
      exact mul_lt_mul_of_pos_right hs_lt_coeff hpos_factor
    have hrewrite_left :
        s * ((q : ℝ) - (p : ℝ)) ^ 2 / 2 = s * (((q : ℝ) - (p : ℝ)) ^ 2 / 2) := by ring
    have hrewrite_right :
        a * ((q : ℝ) - (p : ℝ)) ^ 2 / (2 * (1 - (p : ℝ))) =
          (a / (1 - (p : ℝ))) * (((q : ℝ) - (p : ℝ)) ^ 2 / 2) := by
      field_simp [hpden.ne']
    rw [hrewrite_left, hrewrite_right]
    linarith
  refine ⟨p, hp_lt_q, ?_⟩
  exact lt_trans hp_line hcorr

end C2Gap

section IntegralGap

theorem sub_affineSupportLine_eq_intervalIntegral_sub
    {f m : ℝ → ℝ} {q p : Level} {a : ℝ}
    (hmint : IntervalIntegrable m volume p q)
    (hrep : f q - f p = ∫ t in (p : ℝ)..q, m t) :
    f p - affineSupportLine (fun r : Level => f r) q a p =
      ∫ x in (p : ℝ)..(q : ℝ), (a - m x) := by
  have hconstInt : IntervalIntegrable (fun _ : ℝ => a) volume p q := intervalIntegrable_const
  have hlinep : affineSupportLine (fun r : Level => f r) q a p = f q - a * ((q : ℝ) - (p : ℝ)) := by
    simp [affineSupportLine]
    ring
  have hp_eq : f p = f q - ∫ t in (p : ℝ)..q, m t := by
    linarith
  calc
    f p - affineSupportLine (fun r : Level => f r) q a p
        = (f q - ∫ t in (p : ℝ)..q, m t) - (f q - a * ((q : ℝ) - (p : ℝ))) := by
            rw [hp_eq, hlinep]
    _ = a * ((q : ℝ) - (p : ℝ)) - ∫ t in (p : ℝ)..q, m t := by
          ring
    _ = (∫ x in (p : ℝ)..(q : ℝ), a) - ∫ x in (p : ℝ)..(q : ℝ), m x := by
          rw [intervalIntegral.integral_const]
          simp [sub_eq_add_neg, smul_eq_mul]
          ring_nf
    _ = ∫ x in (p : ℝ)..(q : ℝ), (a - m x) := by
          simpa using (intervalIntegral.integral_sub hconstInt hmint).symm

theorem intervalIntegral_mul_sub_right_eq_sq
    {p q s : ℝ} :
    ∫ x in p..q, s * (q - x) = s * (q - p) ^ 2 / 2 := by
  rw [intervalIntegral.integral_const_mul]
  have hIntId : IntervalIntegrable (fun x : ℝ => x) volume p q := by
    simpa using continuous_id.intervalIntegrable p q
  rw [intervalIntegral.integral_sub intervalIntegrable_const hIntId]
  rw [intervalIntegral.integral_const, integral_id]
  simp [smul_eq_mul]
  ring

theorem leftDeriv_intervalIntegrable_and_sub_eq_of_convexOn_subinterval
    {f : ℝ → ℝ} {p q : Level}
    (hconv : ConvexOn ℝ (Set.Icc (0 : ℝ) 1) f)
    (hp0 : 0 < (p : ℝ)) (hpq : (p : ℝ) < (q : ℝ)) (hq : (q : ℝ) < 1) :
    IntervalIntegrable (fun x : ℝ => derivWithin f (Set.Iio x) x) volume p q ∧
      f q - f p = ∫ t in (p : ℝ)..q, derivWithin f (Set.Iio t) t := by
  have hsubset :
      Set.uIcc (p : ℝ) (q : ℝ) ⊆ interior (Set.Icc (0 : ℝ) 1) := by
    intro x hx
    have hxIcc : x ∈ Set.Icc (p : ℝ) (q : ℝ) := by
      simpa [Set.uIcc_of_le hpq.le] using hx
    have hxIoo : x ∈ Set.Ioo (0 : ℝ) 1 := by
      exact ⟨lt_of_lt_of_le hp0 hxIcc.1, lt_of_le_of_lt hxIcc.2 hq⟩
    simpa [interior_Icc] using hxIoo
  obtain ⟨K, hK⟩ :=
    LocallyLipschitzOn.exists_lipschitzOnWith_of_compact
      (s := Set.uIcc (p : ℝ) (q : ℝ)) isCompact_uIcc
      ((hconv.locallyLipschitzOn_interior).mono hsubset)
  have hAC : AbsolutelyContinuousOnInterval f p q := hK.absolutelyContinuousOnInterval
  have hEqAE :
      (fun x : ℝ => deriv f x) =ᵐ[volume.restrict (Set.uIoc (p : ℝ) (q : ℝ))]
        (fun x : ℝ => derivWithin f (Set.Iio x) x) := by
    refine (ae_restrict_iff' measurableSet_uIoc).2 ?_
    filter_upwards [hAC.ae_differentiableAt] with x hxdiff
    intro hxmem
    have hxIoc : x ∈ Set.Ioc (p : ℝ) (q : ℝ) := by
      simpa [Set.uIoc, hpq.le] using hxmem
    have hxIcc : x ∈ Set.uIcc (p : ℝ) (q : ℝ) := by
      simpa [Set.uIcc_of_le hpq.le] using ⟨hxIoc.1.le, hxIoc.2⟩
    have hdx : DifferentiableAt ℝ f x := hxdiff hxIcc
    exact (hdx.derivWithin (uniqueDiffWithinAt_Iio x)).symm
  have hInt :
      IntervalIntegrable (fun x : ℝ => derivWithin f (Set.Iio x) x) volume p q :=
    hAC.intervalIntegrable_deriv.congr_ae hEqAE
  refine ⟨hInt, ?_⟩
  rw [← hAC.integral_deriv_eq_sub]
  exact intervalIntegral.integral_congr_ae ((ae_restrict_iff' measurableSet_uIoc).1 hEqAE)

/-- On every strict subinterval of `(0,1)`, the left derivative of a convex function is almost
everywhere differentiable. This isolates the regularity input needed to choose a good folded
witness point without assuming global `C²` smoothness. -/
theorem ae_differentiableAt_leftDeriv_of_convexOn_subinterval
    {f : ℝ → ℝ} {p q : Level}
    (hconv : ConvexOn ℝ (Set.Icc (0 : ℝ) 1) f)
    (hp0 : 0 < (p : ℝ)) (hpq : (p : ℝ) < (q : ℝ)) (hq : (q : ℝ) < 1) :
    ∀ᵐ x ∂volume.restrict (Set.Ioo (p : ℝ) (q : ℝ)),
      DifferentiableAt ℝ (fun y : ℝ => derivWithin f (Set.Iio y) y) x := by
  let m : ℝ → ℝ := fun y : ℝ => derivWithin f (Set.Iio y) y
  have hmono : MonotoneOn m (Set.Ioo (p : ℝ) (q : ℝ)) := by
    have hmonoAll : MonotoneOn m (Set.Ioo (0 : ℝ) 1) := by
      simpa [m] using hconv.monotoneOn_leftDeriv
    intro x hx y hy hxy
    exact hmonoAll
      ⟨lt_of_lt_of_le hp0 (le_of_lt hx.1), lt_trans hx.2 hq⟩
      ⟨lt_of_lt_of_le hp0 (le_of_lt hy.1), lt_trans hy.2 hq⟩ hxy
  have hs : MeasurableSet (Set.Ioo (p : ℝ) (q : ℝ)) := by measurability
  filter_upwards [hmono.ae_differentiableWithinAt hs, ae_restrict_mem hs] with x hx hxmem
  have hIoo : Set.Ioo (p : ℝ) (q : ℝ) ∈ 𝓝 x := Ioo_mem_nhds hxmem.1 hxmem.2
  exact hx.differentiableAt hIoo

/-- If the left derivative of a convex function never violates the barrier inequality at
differentiability points inside `(x0,y)`, then it satisfies the corresponding Volterra interval
barrier on `x0..y`. This is the non-`C²` replacement for the smooth differential contradiction. -/
theorem leftDeriv_interval_barrier_of_convexOn_no_goodPoint
    {f : ℝ → ℝ} {x0 y : Level}
    (hconv : ConvexOn ℝ (Set.Icc (0 : ℝ) 1) f)
    (hx0 : 0 < (x0 : ℝ)) (hxy : (x0 : ℝ) < (y : ℝ)) (hy : (y : ℝ) < 1)
    (hno :
      ∀ x ∈ Set.Ioo (x0 : ℝ) (y : ℝ),
        DifferentiableAt ℝ (fun z : ℝ => derivWithin f (Set.Iio z) z) x →
          derivWithin f (Set.Iio x) x / (1 - x) ≤
            deriv (fun z : ℝ => derivWithin f (Set.Iio z) z) x) :
    derivWithin f (Set.Iio (x0 : ℝ)) (x0 : ℝ) +
        ∫ t in (x0 : ℝ)..(y : ℝ), derivWithin f (Set.Iio t) t / (1 - t)
      ≤ derivWithin f (Set.Iio (y : ℝ)) (y : ℝ) := by
  let m : ℝ → ℝ := fun z : ℝ => derivWithin f (Set.Iio z) z
  have hmInt : IntervalIntegrable m volume x0 y :=
    (leftDeriv_intervalIntegrable_and_sub_eq_of_convexOn_subinterval
      (f := f) (p := x0) (q := y) hconv hx0 hxy hy).1
  have hmInvCont : ContinuousOn (fun z : ℝ => (1 - z)⁻¹) (Set.uIcc (x0 : ℝ) (y : ℝ)) := by
    intro z hz
    have hzy : z < 1 := by
      have hzIcc : z ∈ Set.Icc (x0 : ℝ) (y : ℝ) := by
        simpa [Set.uIcc_of_le hxy.le] using hz
      exact lt_of_le_of_lt hzIcc.2 hy
    have hz1 : 1 - z ≠ 0 := sub_ne_zero.mpr (by linarith)
    simpa using ((continuous_const.sub continuous_id).continuousAt.inv₀ hz1).continuousWithinAt
  have hmFracInt :
      IntervalIntegrable (fun z : ℝ => m z / (1 - z)) volume x0 y := by
    simpa [m, div_eq_mul_inv, mul_comm] using hmInt.continuousOn_mul hmInvCont
  have hmonoIcc : MonotoneOn m (Set.uIcc (x0 : ℝ) (y : ℝ)) := by
    have hmonoAll : MonotoneOn m (Set.Ioo (0 : ℝ) 1) := by
      simpa [m] using hconv.monotoneOn_leftDeriv
    intro a ha b hb hab
    have ha' : a ∈ Set.Ioo (0 : ℝ) 1 := by
      have haIcc : a ∈ Set.Icc (x0 : ℝ) (y : ℝ) := by
        simpa [Set.uIcc_of_le hxy.le] using ha
      exact ⟨lt_of_lt_of_le hx0 haIcc.1, lt_of_le_of_lt haIcc.2 hy⟩
    have hb' : b ∈ Set.Ioo (0 : ℝ) 1 := by
      have hbIcc : b ∈ Set.Icc (x0 : ℝ) (y : ℝ) := by
        simpa [Set.uIcc_of_le hxy.le] using hb
      exact ⟨lt_of_lt_of_le hx0 hbIcc.1, lt_of_le_of_lt hbIcc.2 hy⟩
    exact hmonoAll ha' hb' hab
  have hmDerivInt : IntervalIntegrable (deriv m) volume x0 y :=
    hmonoIcc.intervalIntegrable_deriv
  have hAEDiff :
      ∀ᵐ x ∂volume, x ∈ Set.Ioo (x0 : ℝ) (y : ℝ) →
        DifferentiableAt ℝ m x := by
    exact (ae_restrict_iff' (by measurability)).1
      (ae_differentiableAt_leftDeriv_of_convexOn_subinterval
        (f := f) (p := x0) (q := y) hconv hx0 hxy hy)
  have hnotx0 : ∀ᵐ x ∂volume, x ≠ (x0 : ℝ) := by
    simp [ae_iff, measure_singleton]
  have hnoty : ∀ᵐ x ∂volume, x ≠ (y : ℝ) := by
    simp [ae_iff, measure_singleton]
  have hAEbar :
      (fun z : ℝ => m z / (1 - z)) ≤ᵐ[volume.restrict (Set.Icc (x0 : ℝ) (y : ℝ))] fun z => deriv m z := by
    rw [Filter.EventuallyLE, MeasureTheory.ae_restrict_iff' measurableSet_Icc]
    filter_upwards [hAEDiff, hnotx0, hnoty] with z hzdiff hz0 hzy hzmem
    have hzIoo : z ∈ Set.Ioo (x0 : ℝ) (y : ℝ) := by
      exact ⟨lt_of_le_of_ne hzmem.1 hz0.symm, lt_of_le_of_ne hzmem.2 hzy⟩
    exact hno z hzIoo (hzdiff hzIoo)
  have hLower :
      ∫ z in (x0 : ℝ)..(y : ℝ), m z / (1 - z)
        ≤ ∫ z in (x0 : ℝ)..(y : ℝ), deriv m z := by
    exact intervalIntegral.integral_mono_ae_restrict hxy.le hmFracInt hmDerivInt hAEbar
  have hUpperMem :
      ∫ z in (x0 : ℝ)..(y : ℝ), deriv m z ∈ Set.uIcc 0 (m y - m x0) :=
    hmonoIcc.intervalIntegral_deriv_mem_uIcc
  have hUpper :
      ∫ z in (x0 : ℝ)..(y : ℝ), deriv m z ≤ m y - m x0 := by
    have hmonoVal : m x0 ≤ m y := hmonoIcc (by simp) (by simp) hxy.le
    rw [Set.uIcc_of_le (sub_nonneg.mpr hmonoVal)] at hUpperMem
    exact hUpperMem.2
  dsimp [m] at hLower hUpper
  linarith

/-- Under the global no-good-point hypothesis, the left derivative of a convex function obeys the
same harmonic lower bound as in the smooth front-half argument. -/
theorem leftDeriv_lower_bound_div_one_sub_of_convexOn_no_goodPoint
    {f : ℝ → ℝ} {x0 y : Level}
    (hconv : ConvexOn ℝ (Set.Icc (0 : ℝ) 1) f)
    (hx0 : 0 < (x0 : ℝ)) (hxy : (x0 : ℝ) < (y : ℝ)) (hy : (y : ℝ) < 1)
    (hx0mpos : 0 < derivWithin f (Set.Iio (x0 : ℝ)) (x0 : ℝ))
    (hno :
      ∀ x ∈ Set.Ioo (x0 : ℝ) 1,
        DifferentiableAt ℝ (fun z : ℝ => derivWithin f (Set.Iio z) z) x →
          derivWithin f (Set.Iio x) x / (1 - x) ≤
            deriv (fun z : ℝ => derivWithin f (Set.Iio z) z) x) :
    ((1 - (x0 : ℝ)) * derivWithin f (Set.Iio (x0 : ℝ)) (x0 : ℝ)) / (1 - (y : ℝ))
      ≤ derivWithin f (Set.Iio (y : ℝ)) (y : ℝ) := by
  let m : ℝ → ℝ := fun z : ℝ => derivWithin f (Set.Iio z) z
  have hmInt : IntervalIntegrable (fun z : ℝ => m z / (1 - z)) volume x0 y := by
    have hmBase :
        IntervalIntegrable m volume x0 y :=
      (leftDeriv_intervalIntegrable_and_sub_eq_of_convexOn_subinterval
        (f := f) (p := x0) (q := y) hconv hx0 hxy hy).1
    have hmInvCont : ContinuousOn (fun z : ℝ => (1 - z)⁻¹) (Set.uIcc (x0 : ℝ) (y : ℝ)) := by
      intro z hz
      have hzIcc : z ∈ Set.Icc (x0 : ℝ) (y : ℝ) := by
        simpa [Set.uIcc_of_le hxy.le] using hz
      have hz1 : 1 - z ≠ 0 := sub_ne_zero.mpr (by
        have : z < 1 := lt_of_le_of_lt hzIcc.2 hy
        linarith)
      simpa using ((continuous_const.sub continuous_id).continuousAt.inv₀ hz1).continuousWithinAt
    simpa [m, div_eq_mul_inv, mul_comm] using hmBase.continuousOn_mul hmInvCont
  have hbarrier :
      ∀ z ∈ Set.Icc (x0 : ℝ) (y : ℝ),
        m x0 + ∫ t in (x0 : ℝ)..z, m t / (1 - t) ≤ m z := by
    intro z hz
    by_cases hzEq : z = (x0 : ℝ)
    · subst hzEq
      simp
    · have hzx0 : (x0 : ℝ) < z := lt_of_le_of_ne hz.1 (by
          intro h
          exact hzEq h.symm)
      exact leftDeriv_interval_barrier_of_convexOn_no_goodPoint
        (f := f) (x0 := x0) (y := ⟨z, ⟨le_trans hx0.le hz.1, le_of_lt (lt_of_le_of_lt hz.2 hy)⟩⟩)
        hconv hx0 hzx0 (lt_of_le_of_lt hz.2 hy)
        (fun x hx hd => hno x ⟨hx.1, lt_trans hx.2 (lt_of_le_of_lt hz.2 hy)⟩ hd)
  simpa [m] using
    lower_bound_div_one_sub_of_interval_barrier
      (x0 := (x0 : ℝ)) (y := (y : ℝ)) hxy hy hmInt hbarrier hx0mpos

theorem exists_levelGap_of_integral_remainder_barrier
    {f m : ℝ → ℝ} {q : Level} {d : ℝ}
    (hq0 : 0 < (q : ℝ)) (hq : (q : ℝ) < 1)
    (ha : 0 < m q)
    (hmd : HasDerivAt m d q)
    (hmint : ∀ x ∈ Set.Ioo (0 : ℝ) (q : ℝ), IntervalIntegrable m volume x q)
    (hrep : ∀ x ∈ Set.Ioo (0 : ℝ) (q : ℝ), f q - f x = ∫ t in x..q, m t)
    (hbarrier : d < m q / (1 - q)) :
    ∃ p : Level,
      (p : ℝ) < (q : ℝ) ∧
      f p <
        affineSupportLine (fun r : Level => f r) q (m q) p +
          m q * ((q : ℝ) - (p : ℝ)) ^ 2 / (2 * (1 - (p : ℝ))) := by
  let a : ℝ := m q
  let s : ℝ := (max d 0 + a / (1 - (q : ℝ))) / 2
  have hqden : 0 < 1 - (q : ℝ) := by
    linarith
  have htop_pos : 0 < a / (1 - (q : ℝ)) := by
    exact div_pos (by simpa [a] using ha) hqden
  have hs_pos : 0 < s := by
    have hmax_nonneg : 0 ≤ max d 0 := le_max_right _ _
    dsimp [s]
    linarith
  have hs_gt : d < s := by
    have hmax_left : d ≤ max d 0 := le_max_left _ _
    dsimp [s]
    linarith
  have hs_lt_top : s < a / (1 - (q : ℝ)) := by
    have hmax_lt : max d 0 < a / (1 - (q : ℝ)) := by
      refine max_lt hbarrier ?_
      exact htop_pos
    dsimp [s]
    linarith
  have hslope_tendsto : Filter.Tendsto (slope m q) (𝓝[<] (q : ℝ)) (𝓝 d) := by
    simpa using hmd.tendsto_slope.mono_left (nhdsLT_le_nhdsNE (q : ℝ))
  have hslope_event :
      {x : ℝ | slope m q x < s} ∈ 𝓝[<] (q : ℝ) := by
    exact hslope_tendsto (Iio_mem_nhds hs_gt)
  obtain ⟨δ, hδpos, hδsub⟩ := Metric.mem_nhdsWithin_iff.mp hslope_event
  have hgap_to_coeff : 0 < a / s - (1 - (q : ℝ)) := by
    have hmul : s * (1 - (q : ℝ)) < a := (lt_div_iff₀ hqden).1 hs_lt_top
    have hmul' : (1 - (q : ℝ)) * s < a := by
      simpa [mul_comm] using hmul
    have haux : 1 - (q : ℝ) < a / s := (lt_div_iff₀ hs_pos).2 hmul'
    linarith
  let ε : ℝ := (a / s - (1 - (q : ℝ))) / 2
  have hεpos : 0 < ε := by
    dsimp [ε]
    linarith [hgap_to_coeff]
  let t : ℝ := min (δ / 2) (min ((q : ℝ) / 2) ε)
  have ht_pos : 0 < t := by
    dsimp [t]
    refine lt_min ?_ (lt_min ?_ hεpos)
    · linarith
    · linarith
  have ht_lt_δ : t < δ := by
    dsimp [t]
    have : t ≤ δ / 2 := min_le_left _ _
    linarith
  have ht_lt_q : t < (q : ℝ) := by
    dsimp [t]
    have : t ≤ (q : ℝ) / 2 := (min_le_right _ _).trans (min_le_left _ _)
    linarith
  have ht_le_ε : t ≤ ε := by
    dsimp [t]
    exact (min_le_right _ _).trans (min_le_right _ _)
  let p : Level := ⟨(q : ℝ) - t, by
    constructor
    · linarith
    · linarith [q.2.2]⟩
  have hp_lt_q : (p : ℝ) < (q : ℝ) := by
    dsimp [p]
    linarith
  have hpden : 0 < 1 - (p : ℝ) := by
    linarith [hq, hp_lt_q]
  have hs_lt_coeff : s < a / (1 - (p : ℝ)) := by
    have ht_lt_bound : t < a / s - (1 - (q : ℝ)) := by
      have hε_lt : ε < a / s - (1 - (q : ℝ)) := by
        dsimp [ε]
        linarith
      exact lt_of_le_of_lt ht_le_ε hε_lt
    have htmp : 1 - (q : ℝ) + t < a / s := by
      linarith
    have hmul : s * (1 - (q : ℝ) + t) < s * (a / s) := by
      exact mul_lt_mul_of_pos_left htmp hs_pos
    have hmul' : s * (1 - (p : ℝ)) < a := by
      have hsas : s * (a / s) = a := by
        field_simp [hs_pos.ne']
      rw [show 1 - (p : ℝ) = 1 - (q : ℝ) + t by
        dsimp [p]
        ring]
      simpa [hsas] using hmul
    exact (lt_div_iff₀ hpden).2 hmul'
  have hp_pos : 0 < (p : ℝ) := by
    dsimp [p]
    linarith
  have hpmem : (p : ℝ) ∈ Set.Ioo (0 : ℝ) (q : ℝ) := by
    exact ⟨hp_pos, hp_lt_q⟩
  have hbound :
      ∀ x ∈ Set.Icc (p : ℝ) (q : ℝ), a - m x ≤ s * ((q : ℝ) - x) := by
    intro x hx
    by_cases hxq : x = (q : ℝ)
    · subst hxq
      simp [a]
    · have hxlt : x < (q : ℝ) := lt_of_le_of_ne hx.2 hxq
      have hxdist : dist x (q : ℝ) < δ := by
        rw [Real.dist_eq]
        have hxnonpos : x - (q : ℝ) ≤ 0 := sub_nonpos.mpr hx.2
        rw [abs_of_nonpos hxnonpos]
        have : (q : ℝ) - x ≤ t := by
          have : x ≥ (p : ℝ) := hx.1
          dsimp [p] at this
          linarith
        linarith
      have hslope_lt : slope m q x < s := by
        have hball : x ∈ Metric.ball (q : ℝ) δ := by
          simpa [Metric.mem_ball, dist_comm] using hxdist
        exact hδsub ⟨hball, hxlt⟩
      have hslope_lt' : (m x - a) / (x - (q : ℝ)) < s := by
        simpa [a, slope_def_field] using hslope_lt
      have hdenneg : x - (q : ℝ) < 0 := sub_neg.mpr hxlt
      have hmul : s * (x - (q : ℝ)) < m x - a := by
        exact (div_lt_iff_of_neg hdenneg).mp hslope_lt'
      have : a - m x < s * ((q : ℝ) - x) := by
        linarith
      exact this.le
  have hmintp : IntervalIntegrable m volume p q := hmint p hpmem
  have hrep_p : f q - f p = ∫ t in (p : ℝ)..q, m t := hrep p hpmem
  have hint_diff : IntervalIntegrable (fun x : ℝ => a - m x) volume p q := by
    exact (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => a) volume p q).sub hmintp
  have hint_lin : IntervalIntegrable (fun x : ℝ => s * ((q : ℝ) - x)) volume p q := by
    simpa using (continuous_const.mul (continuous_const.sub continuous_id)).intervalIntegrable p q
  have hmonoInt :
      ∫ x in (p : ℝ)..(q : ℝ), (a - m x) ≤ ∫ x in (p : ℝ)..(q : ℝ), s * ((q : ℝ) - x) := by
    exact intervalIntegral.integral_mono_on hp_lt_q.le hint_diff hint_lin hbound
  have herror :
      f p - affineSupportLine (fun r : Level => f r) q a p =
        ∫ x in (p : ℝ)..(q : ℝ), (a - m x) := by
    exact sub_affineSupportLine_eq_intervalIntegral_sub (q := q) (p := p) (a := a) hmintp hrep_p
  have hlinEval :
      ∫ x in (p : ℝ)..(q : ℝ), s * ((q : ℝ) - x) =
        s * ((q : ℝ) - (p : ℝ)) ^ 2 / 2 := by
    exact intervalIntegral_mul_sub_right_eq_sq (p := (p : ℝ)) (q := (q : ℝ)) (s := s)
  have hp_line :
      f p ≤ affineSupportLine (fun r : Level => f r) q a p + s * ((q : ℝ) - (p : ℝ)) ^ 2 / 2 := by
    rw [← herror] at hmonoInt
    rw [hlinEval] at hmonoInt
    linarith
  have hcorr :
      affineSupportLine (fun r : Level => f r) q a p + s * ((q : ℝ) - (p : ℝ)) ^ 2 / 2 <
        affineSupportLine (fun r : Level => f r) q a p +
          a * ((q : ℝ) - (p : ℝ)) ^ 2 / (2 * (1 - (p : ℝ))) := by
    have hfactor :
        s * (((q : ℝ) - (p : ℝ)) ^ 2 / 2) <
          (a / (1 - (p : ℝ))) * (((q : ℝ) - (p : ℝ)) ^ 2 / 2) := by
      have hpos_factor : 0 < ((q : ℝ) - (p : ℝ)) ^ 2 / 2 := by
        have hqp : 0 < (q : ℝ) - (p : ℝ) := by
          linarith
        positivity
      exact mul_lt_mul_of_pos_right hs_lt_coeff hpos_factor
    have hrewrite_left :
        s * ((q : ℝ) - (p : ℝ)) ^ 2 / 2 = s * (((q : ℝ) - (p : ℝ)) ^ 2 / 2) := by
      ring
    have hrewrite_right :
        a * ((q : ℝ) - (p : ℝ)) ^ 2 / (2 * (1 - (p : ℝ))) =
          (a / (1 - (p : ℝ))) * (((q : ℝ) - (p : ℝ)) ^ 2 / 2) := by
      field_simp [hpden.ne']
    rw [hrewrite_left, hrewrite_right]
    linarith
  refine ⟨p, hp_lt_q, ?_⟩
  exact lt_of_le_of_lt hp_line hcorr

theorem exists_levelGap_of_convexOn_leftDeriv_barrier
    {f : ℝ → ℝ} {q : Level} {d : ℝ}
    (hconv : ConvexOn ℝ (Set.Icc (0 : ℝ) 1) f)
    (hq0 : 0 < (q : ℝ)) (hq : (q : ℝ) < 1)
    (ha : 0 < derivWithin f (Set.Iio (q : ℝ)) (q : ℝ))
    (hmd : HasDerivAt (fun x : ℝ => derivWithin f (Set.Iio x) x) d q)
    (hbarrier : d < derivWithin f (Set.Iio (q : ℝ)) (q : ℝ) / (1 - q)) :
    ∃ p : Level,
      (p : ℝ) < (q : ℝ) ∧
      f p <
        affineSupportLine
            (fun r : Level => f r) q (derivWithin f (Set.Iio (q : ℝ)) (q : ℝ)) p +
          derivWithin f (Set.Iio (q : ℝ)) (q : ℝ) *
            ((q : ℝ) - (p : ℝ)) ^ 2 / (2 * (1 - (p : ℝ))) := by
  refine exists_levelGap_of_integral_remainder_barrier
    (f := f)
    (m := fun x : ℝ => derivWithin f (Set.Iio x) x)
    (q := q) (d := d) hq0 hq ha hmd ?_ ?_ hbarrier
  · intro x hx
    let xL : Level := ⟨x, ⟨le_of_lt hx.1, le_trans hx.2.le q.2.2⟩⟩
    simpa [xL] using
      (leftDeriv_intervalIntegrable_and_sub_eq_of_convexOn_subinterval
        (f := f) (p := xL) (q := q) hconv hx.1 hx.2 hq).1
  · intro x hx
    let xL : Level := ⟨x, ⟨le_of_lt hx.1, le_trans hx.2.le q.2.2⟩⟩
    simpa [xL] using
      (leftDeriv_intervalIntegrable_and_sub_eq_of_convexOn_subinterval
        (f := f) (p := xL) (q := q) hconv hx.1 hx.2 hq).2

end IntegralGap

section BareConvexFrontHalf

/-- Bare convexity plus positivity at one interior point already produces a good point for the
folded contradiction: a differentiability point of the left-derivative where the barrier fails. -/
theorem exists_good_leftDeriv_real_point_of_convexOn
    {f : ℝ → ℝ} {x0 : Level}
    (hx0 : (x0 : ℝ) ∈ Set.Ioo (0 : ℝ) 1)
    (hconv : ConvexOn ℝ (Set.Icc (0 : ℝ) 1) f)
    (h0 : f 0 = 0)
    (hx0pos : 0 < f x0) :
    ∃ q ∈ Set.Ioo (x0 : ℝ) 1,
      DifferentiableAt ℝ (fun x : ℝ => derivWithin f (Set.Iio x) x) q ∧
      deriv (fun x : ℝ => derivWithin f (Set.Iio x) x) q <
        derivWithin f (Set.Iio q) q / (1 - q) := by
  let m : ℝ → ℝ := fun x : ℝ => derivWithin f (Set.Iio x) x
  have hm0pos : 0 < m x0 := by
    simpa [m] using leftDeriv_pos_of_convexOn_pos_before_one_at hconv h0 hx0 hx0pos
  let c : ℝ := (1 - (x0 : ℝ)) * m x0
  have hcpos : 0 < c := by
    dsimp [c]
    have hx01 : 0 < 1 - (x0 : ℝ) := sub_pos.mpr hx0.2
    positivity
  by_contra hno
  push_neg at hno
  have hlogNat :
      Filter.Tendsto (fun n : ℕ => Real.log (n : ℝ)) Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨N, hNlog, hNgt⟩ :=
    ((hlogNat.eventually_gt_atTop ((f 1 - f x0) / c)).and
      (Filter.eventually_gt_atTop (1 : ℕ))).exists
  let y : Level := ⟨1 - (1 - (x0 : ℝ)) / (N : ℝ), by
    have hNpos : (0 : ℝ) < N := by exact_mod_cast (lt_trans Nat.zero_lt_one hNgt)
    have hNone : (1 : ℝ) < N := by exact_mod_cast hNgt
    have hfrac_lt : (1 - (x0 : ℝ)) / (N : ℝ) < 1 - (x0 : ℝ) := by
      exact div_lt_self (sub_pos.mpr hx0.2) hNone
    have hyx0 : (x0 : ℝ) < 1 - (1 - (x0 : ℝ)) / (N : ℝ) := by
      have hsub := sub_lt_sub_left hfrac_lt 1
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hsub
    constructor
    · exact le_of_lt (lt_trans hx0.1 hyx0)
    · have hfrac_nonneg : 0 ≤ (1 - (x0 : ℝ)) / (N : ℝ) := by
        exact div_nonneg (sub_nonneg.mpr hx0.2.le) hNpos.le
      linarith⟩
  have hy : (y : ℝ) ∈ Set.Ioo (x0 : ℝ) 1 := by
    have hNpos : (0 : ℝ) < N := by exact_mod_cast (lt_trans Nat.zero_lt_one hNgt)
    have hNone : (1 : ℝ) < N := by exact_mod_cast hNgt
    have hfrac_lt : (1 - (x0 : ℝ)) / (N : ℝ) < 1 - (x0 : ℝ) := by
      exact div_lt_self (sub_pos.mpr hx0.2) hNone
    have hyx0 : (x0 : ℝ) < 1 - (1 - (x0 : ℝ)) / (N : ℝ) := by
      have hsub := sub_lt_sub_left hfrac_lt 1
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hsub
    constructor
    · exact hyx0
    · have hfrac_pos : 0 < (1 - (x0 : ℝ)) / (N : ℝ) := by
        exact div_pos (sub_pos.mpr hx0.2) hNpos
      linarith
  have hpoint :
      ∀ z ∈ Set.Icc (x0 : ℝ) (y : ℝ), c / (1 - z) ≤ m z := by
    intro z hz
    by_cases hzEq : z = (x0 : ℝ)
    · subst hzEq
      have hx01 : (1 - (x0 : ℝ)) ≠ 0 := sub_ne_zero.mpr (by linarith [hx0.2])
      have hcEq : c / (1 - (x0 : ℝ)) = m x0 := by
        dsimp [c]
        field_simp [hx01]
      simpa [hcEq]
    · have hzx0 : (x0 : ℝ) < z := lt_of_le_of_ne hz.1 (by
          intro h
          exact hzEq h.symm)
      let zL : Level := ⟨z, ⟨le_trans hx0.1.le hz.1, le_of_lt (lt_of_le_of_lt hz.2 hy.2)⟩⟩
      have hz1 : z < 1 := lt_of_le_of_lt hz.2 hy.2
      simpa [c, m, zL] using
        leftDeriv_lower_bound_div_one_sub_of_convexOn_no_goodPoint
          (f := f) (x0 := x0) (y := zL) hconv hx0.1 hzx0 hz1 hm0pos hno
  have hmInt :
      IntervalIntegrable m volume x0 y :=
    (leftDeriv_intervalIntegrable_and_sub_eq_of_convexOn_subinterval
      (f := f) (p := x0) (q := y) hconv hx0.1 hy.1 hy.2).1
  have hInvCont :
      ContinuousOn (fun z : ℝ => c / (1 - z)) (Set.uIcc (x0 : ℝ) (y : ℝ)) := by
    intro z hz
    have hzIcc : z ∈ Set.Icc (x0 : ℝ) (y : ℝ) := by
      simpa [Set.uIcc_of_le hy.1.le] using hz
    have hz1 : 1 - z ≠ 0 := sub_ne_zero.mpr (by
      have : z < 1 := lt_of_le_of_lt hzIcc.2 hy.2
      linarith)
    exact continuousWithinAt_const.div
      ((continuous_const.sub continuous_id).continuousAt.continuousWithinAt) hz1
  have hInvInt :
      IntervalIntegrable (fun z : ℝ => c / (1 - z)) volume x0 y :=
    hInvCont.intervalIntegrable
  have hIntegralLower :
      ∫ z in (x0 : ℝ)..(y : ℝ), c / (1 - z) ≤ ∫ z in (x0 : ℝ)..(y : ℝ), m z := by
    exact intervalIntegral.integral_mono_on hy.1.le hInvInt hmInt hpoint
  have hIntEq :
      ∫ z in (x0 : ℝ)..(y : ℝ), m z = f y - f x0 := by
    simpa [m] using
      (leftDeriv_intervalIntegrable_and_sub_eq_of_convexOn_subinterval
        (f := f) (p := x0) (q := y) hconv hx0.1 hy.1 hy.2).2.symm
  have hmmono : MonotoneOn m (Set.Ioo (0 : ℝ) 1) := by
    simpa [m] using hconv.monotoneOn_leftDeriv
  have hy01 : (y : ℝ) ∈ Set.Ioo (0 : ℝ) 1 := ⟨lt_trans hx0.1 hy.1, hy.2⟩
  have hm_y_pos : 0 < m y := by
    have hxy0 : m ((x0 : ℝ)) ≤ m ((y : ℝ)) := by
      exact hmmono hx0 hy01 (le_of_lt hy.1)
    exact lt_of_lt_of_le hm0pos hxy0
  have hyline :
      f y + m y * (1 - (y : ℝ)) ≤ f 1 := by
    have hline1 :
        affineSupportLine
            (fun r : Level => f r)
            y
            (derivWithin f (Set.Iio (y : ℝ)) (y : ℝ))
            1 ≤
          f 1 := by
      exact affineSupportLine_le_of_convexOn_leftDeriv (f := f) (q := y) hconv hy01 1
    simpa [m, affineSupportLine] using hline1
  have hfy_le : f y ≤ f 1 := by
    have hnonneg : 0 ≤ m y * (1 - (y : ℝ)) := by
      have hmy_nonneg : 0 ≤ m y := le_of_lt hm_y_pos
      have hy_nonneg : 0 ≤ 1 - (y : ℝ) := by linarith [hy.2]
      exact mul_nonneg hmy_nonneg hy_nonneg
    linarith
  have hIntegralUpper :
      ∫ z in (x0 : ℝ)..(y : ℝ), m z ≤ f 1 - f x0 := by
    rw [hIntEq]
    linarith
  have hcy :
      ∫ z in (x0 : ℝ)..(y : ℝ), c / (1 - z) = c * Real.log (N : ℝ) := by
    have hyDen :
        1 - (y : ℝ) = (1 - (x0 : ℝ)) / (N : ℝ) := by
      dsimp [y]
      field_simp [show (N : ℝ) ≠ 0 by positivity]
      ring
    calc
      ∫ z in (x0 : ℝ)..(y : ℝ), c / (1 - z)
          = c * Real.log ((1 - (x0 : ℝ)) / (1 - (y : ℝ))) := by
              simpa using intervalIntegral_const_div_one_sub_eq_log
                (a := (x0 : ℝ)) (b := (y : ℝ)) (c := c) hy.1 hy.2
      _ = c * Real.log (N : ℝ) := by
            rw [hyDen]
            have hx01 : (1 - (x0 : ℝ)) ≠ 0 := sub_ne_zero.mpr (by linarith [hx0.2])
            field_simp [hx01, show (N : ℝ) ≠ 0 by positivity]
  have hBig : f 1 - f x0 < c * Real.log (N : ℝ) := by
    have hmul := mul_lt_mul_of_pos_left hNlog hcpos
    have hleft : c * ((f 1 - f x0) / c) = f 1 - f x0 := by
      field_simp [hcpos.ne']
    rw [hleft] at hmul
    exact hmul
  rw [hcy] at hIntegralLower
  exact not_lt_of_ge ((le_trans hIntegralLower hIntegralUpper)) hBig

/-- The previous existence theorem repackaged with the supporting-line data needed by the folded
witness construction. -/
theorem exists_good_affineSupportLine_point_of_convexOn_leftDeriv
    {f : ℝ → ℝ} {x0 : Level}
    (hx0 : (x0 : ℝ) ∈ Set.Ioo (0 : ℝ) 1)
    (hconv : ConvexOn ℝ (Set.Icc (0 : ℝ) 1) f)
    (h0 : f 0 = 0)
    (hx0pos : 0 < f x0) :
    ∃ q : Level,
      (x0 : ℝ) < (q : ℝ) ∧
      (q : ℝ) < 1 ∧
      0 < derivWithin f (Set.Iio (q : ℝ)) (q : ℝ) ∧
      DifferentiableAt ℝ (fun x : ℝ => derivWithin f (Set.Iio x) x) q ∧
      deriv (fun x : ℝ => derivWithin f (Set.Iio x) x) q <
        derivWithin f (Set.Iio (q : ℝ)) (q : ℝ) / (1 - q) ∧
      ∀ p : Level,
        affineSupportLine
            (fun r : Level => f r) q (derivWithin f (Set.Iio (q : ℝ)) (q : ℝ)) p ≤
          f p := by
  obtain ⟨q, hq, hdiff, hbarrier⟩ :=
    exists_good_leftDeriv_real_point_of_convexOn (x0 := x0) hx0 hconv h0 hx0pos
  let qL : Level := ⟨q, ⟨le_of_lt (lt_trans hx0.1 hq.1), le_of_lt hq.2⟩⟩
  have hqL : (qL : ℝ) ∈ Set.Ioo (0 : ℝ) 1 := ⟨lt_trans hx0.1 hq.1, hq.2⟩
  have hqpos : 0 < f qL := by
    have hxline :=
      affineSupportLine_le_of_convexOn_leftDeriv (f := f) (q := x0) hconv hx0 qL
    have hm0pos :
        0 < derivWithin f (Set.Iio (x0 : ℝ)) (x0 : ℝ) := by
      exact leftDeriv_pos_of_convexOn_pos_before_one_at hconv h0 hx0 hx0pos
    have hline' :
        f x0 + derivWithin f (Set.Iio (x0 : ℝ)) (x0 : ℝ) * ((qL : ℝ) - (x0 : ℝ)) ≤ f qL := by
      simpa [affineSupportLine] using hxline
    have hstrict :
        0 < f x0 + derivWithin f (Set.Iio (x0 : ℝ)) (x0 : ℝ) * ((qL : ℝ) - (x0 : ℝ)) := by
      have : 0 < derivWithin f (Set.Iio (x0 : ℝ)) (x0 : ℝ) * ((qL : ℝ) - (x0 : ℝ)) := by
        have : 0 < (qL : ℝ) - (x0 : ℝ) := sub_pos.mpr hq.1
        positivity
      linarith
    linarith
  refine ⟨qL, hq.1, hq.2, ?_, ?_, ?_, ?_⟩
  · simpa [qL] using leftDeriv_pos_of_convexOn_pos_before_one_at hconv h0 hqL hqpos
  · simpa [qL] using hdiff
  · simpa [qL] using hbarrier
  · intro p
    exact affineSupportLine_le_of_convexOn_leftDeriv hconv hqL p

end BareConvexFrontHalf

section FoldedUniformLaw

open unitInterval

/-- The real-valued fold map used in the uniform witness construction. -/
def foldMapReal (q : I) : I → ℝ := fun u =>
  if u ≤ q then (q : ℝ) - u else u

@[simp] theorem foldMapReal_of_le {q u : I} (huq : u ≤ q) :
    foldMapReal q u = (q : ℝ) - u := by
  simp [foldMapReal, huq]

@[simp] theorem foldMapReal_of_not_le {q u : I} (huq : ¬ u ≤ q) :
    foldMapReal q u = u := by
  simp [foldMapReal, huq]

theorem foldMapReal_mem_I (q u : I) : foldMapReal q u ∈ Set.Icc (0 : ℝ) 1 := by
  by_cases huq : u ≤ q
  · rw [foldMapReal_of_le huq]
    constructor
    · exact sub_nonneg.mpr huq
    · linarith [q.2.2, u.2.1]
  · rw [foldMapReal_of_not_le huq]
    exact u.2

@[fun_prop]
theorem measurable_foldMapReal (q : I) : Measurable (foldMapReal q) := by
  classical
  refine Measurable.ite measurableSet_Iic ?_ measurable_subtype_coe
  exact measurable_const.sub measurable_subtype_coe

/-- Fold the lower segment `[0,q]` by reflection and keep the upper segment fixed.

We use the closed branch `u ≤ q` instead of `u < q`; this differs from the manuscript map only at
the single point `u = q`, which is measure-zero under the uniform law. The closed version makes the
interval preimage formulas cleaner in Lean. -/
def foldMap (q : I) : I → I := fun u => ⟨foldMapReal q u, foldMapReal_mem_I q u⟩

@[simp] theorem foldMap_of_le {q u : I} (huq : u ≤ q) :
    ((foldMap q u : I) : ℝ) = (q : ℝ) - u := by
  simp [foldMap, foldMapReal, huq]

@[simp] theorem foldMap_of_not_le {q u : I} (huq : ¬ u ≤ q) :
    ((foldMap q u : I) : ℝ) = u := by
  simp [foldMap, foldMapReal, huq]

@[fun_prop]
theorem measurable_foldMap (q : I) : Measurable (foldMap q) := by
  exact Measurable.subtype_mk (measurable_foldMapReal q)

/-- The reflected left endpoint `q - x`, packaged again as a point of the unit interval. -/
def reflectAt (q x : I) (hxq : x ≤ q) : I :=
  ⟨(q : ℝ) - x, by
    constructor
    · exact sub_nonneg.mpr hxq
    · linarith [q.2.2, x.2.1]⟩

@[simp] theorem coe_reflectAt {q x : I} (hxq : x ≤ q) :
    ((reflectAt q x hxq : I) : ℝ) = (q : ℝ) - x := rfl

/-- For `x ≤ q`, the lower-tail preimage of the folded map is exactly the reflected interval
`[q - x, q]`. -/
theorem preimage_foldMap_Iic_of_le {q x : I} (hxq : x ≤ q) :
    foldMap q ⁻¹' Set.Iic x = Set.Icc (reflectAt q x hxq) q := by
  ext u
  constructor
  · intro hu
    change ((foldMap q u : I) : ℝ) ≤ (x : ℝ) at hu
    by_cases huq : u ≤ q
    · refine ⟨?_, huq⟩
      rw [foldMap_of_le huq] at hu
      change (q : ℝ) - x ≤ (u : ℝ)
      linarith
    · exfalso
      exact huq ((show u ≤ x from by simpa [foldMap, foldMapReal, huq] using hu).trans hxq)
  · rintro ⟨hleft, huq⟩
    change ((foldMap q u : I) : ℝ) ≤ (x : ℝ)
    rw [foldMap_of_le huq]
    change (((reflectAt q x hxq : I) : ℝ) ≤ (u : ℝ)) at hleft
    rw [coe_reflectAt hxq] at hleft
    linarith

/-- Once `x` is above the fold point, the lower-tail preimage is the usual lower interval. -/
theorem preimage_foldMap_Iic_of_ge {q x : I} (hqx : q ≤ x) :
    foldMap q ⁻¹' Set.Iic x = Set.Iic x := by
  ext u
  constructor
  · intro hu
    change ((foldMap q u : I) : ℝ) ≤ (x : ℝ) at hu
    by_cases huq : u ≤ q
    · exact huq.trans hqx
    · simpa [foldMap, foldMapReal, huq] using hu
  · intro hu
    by_cases huq : u ≤ q
    · change ((foldMap q u : I) : ℝ) ≤ (x : ℝ)
      rw [foldMap_of_le huq]
      have hqu : (q : ℝ) - (u : ℝ) ≤ (q : ℝ) := by
        linarith [u.2.1]
      exact hqu.trans hqx
    · simpa [foldMap, foldMapReal, huq] using hu

/-- The folded map preserves the lower-tail volumes of the unit-interval law. -/
theorem volume_preimage_foldMap_Iic (q x : I) :
    (volume : Measure I) (foldMap q ⁻¹' Set.Iic x) = volume (Set.Iic x) := by
  by_cases hxq : x ≤ q
  · rw [preimage_foldMap_Iic_of_le hxq, unitInterval.volume_Icc, unitInterval.volume_Iic]
    congr 1
    rw [coe_reflectAt hxq]
    ring
  · rw [preimage_foldMap_Iic_of_ge (le_of_not_ge hxq)]

/-- The folded map leaves the canonical unit-interval probability measure invariant. -/
theorem map_foldMap_volume_eq (q : I) :
    Measure.map (foldMap q) (volume : Measure I) = volume := by
  refine Measure.ext_of_Iic _ _ fun x => ?_
  rw [Measure.map_apply (measurable_foldMap q) measurableSet_Iic]
  exact volume_preimage_foldMap_Iic q x

/-- The real-valued folded coordinate has the same law as the standard uniform coordinate on
`[0,1]`. -/
theorem law_foldMap_eq_uniform (q : I) :
    Measure.map (fun u : I => ((foldMap q u : I) : ℝ)) (volume : Measure I) =
      Measure.map (Subtype.val : I → ℝ) (volume : Measure I) := by
  calc
    Measure.map (fun u : I => ((foldMap q u : I) : ℝ)) (volume : Measure I) =
        Measure.map (Subtype.val : I → ℝ) (Measure.map (foldMap q) (volume : Measure I)) := by
          simpa using
            (Measure.map_map (μ := (volume : Measure I)) (f := foldMap q)
              (g := (Subtype.val : I → ℝ)) measurable_subtype_coe (measurable_foldMap q)).symm
    _ = Measure.map (Subtype.val : I → ℝ) (volume : Measure I) := by
          rw [map_foldMap_volume_eq]

end FoldedUniformLaw

section UniformLawFormulas

open unitInterval

/-- The standard uniform law on `[0,1]`, viewed as a probability measure on `ℝ`. -/
def uniform01Law : Measure ℝ :=
  Measure.map (Subtype.val : I → ℝ) (volume : Measure I)

instance : IsProbabilityMeasure uniform01Law :=
  Measure.isProbabilityMeasure_map measurable_subtype_coe.aemeasurable

theorem cdf_uniform01_of_mem (x : I) :
    ProbabilityTheory.cdf uniform01Law x = x := by
  rw [uniform01Law, ProbabilityTheory.unitInterval.cdf_eq_real (μ := (volume : Measure I)) x]
  rw [show Set.Icc (0 : I) x = Set.Iic x by
    ext u
    simp]
  rw [Measure.real, unitInterval.volume_Iic]
  simp [x.2.1]

theorem cdf_uniform01_of_mem_Icc {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    ProbabilityTheory.cdf uniform01Law x = x := by
  let xI : I := ⟨x, hx⟩
  simpa [xI] using cdf_uniform01_of_mem xI

theorem cdf_uniform01_of_lt_zero {x : ℝ} (hx : x < 0) :
    ProbabilityTheory.cdf uniform01Law x = 0 := by
  have hmono := ProbabilityTheory.monotone_cdf uniform01Law
  have hle : ProbabilityTheory.cdf uniform01Law x ≤ ProbabilityTheory.cdf uniform01Law 0 :=
    hmono hx.le
  have hzero : ProbabilityTheory.cdf uniform01Law 0 = 0 := by
    simpa using cdf_uniform01_of_mem (0 : I)
  exact le_antisymm (hle.trans_eq hzero) (ProbabilityTheory.cdf_nonneg uniform01Law x)

theorem cdf_uniform01_of_one_le {x : ℝ} (hx : 1 ≤ x) :
    ProbabilityTheory.cdf uniform01Law x = 1 := by
  have hmono := ProbabilityTheory.monotone_cdf uniform01Law
  have hge : ProbabilityTheory.cdf uniform01Law 1 ≤ ProbabilityTheory.cdf uniform01Law x :=
    hmono hx
  have hone : ProbabilityTheory.cdf uniform01Law 1 = 1 := by
    simpa using cdf_uniform01_of_mem (1 : I)
  exact le_antisymm (ProbabilityTheory.cdf_le_one uniform01Law x) (hone ▸ hge)

theorem distLowerQuantile_uniform01_eq {q : ℝ} (hq : q ∈ Set.Ioc (0 : ℝ) 1) :
    distLowerQuantile uniform01Law q = q := by
  let S : Set ℝ := {x : ℝ | q ≤ ProbabilityTheory.cdf uniform01Law x}
  change sInf S = q
  have hqIcc : q ∈ Set.Icc (0 : ℝ) 1 := ⟨hq.1.le, hq.2⟩
  have hcdfq : ProbabilityTheory.cdf uniform01Law q = q := cdf_uniform01_of_mem_Icc hqIcc
  apply le_antisymm
  · refine csInf_le (upperLevelSet_bddBelow uniform01Law hq.1) ?_
    simpa [S, hcdfq]
  · refine le_csInf ?_ ?_
    · exact ⟨q, by simpa [S, hcdfq]⟩
    · intro x hxS
      by_contra hxlt
      have hxq : q ≤ ProbabilityTheory.cdf uniform01Law x := by simpa [S] using hxS
      by_cases hx0 : x < 0
      · have hcdfx : ProbabilityTheory.cdf uniform01Law x = 0 := cdf_uniform01_of_lt_zero hx0
        have : q ≤ 0 := by simpa [hcdfx] using hxq
        exact (not_le_of_gt hq.1) this
      · have hx0' : 0 ≤ x := not_lt.mp hx0
        have hx1 : x ≤ 1 := by linarith [hxlt, hq.2]
        have hcdfx : ProbabilityTheory.cdf uniform01Law x = x :=
          cdf_uniform01_of_mem_Icc ⟨hx0', hx1⟩
        have : q ≤ x := by simpa [hcdfx] using hxq
        linarith

theorem distESIntegral_uniform01_eq (p : Level) :
    distESIntegral uniform01Law p = (1 - (p : ℝ) ^ 2) / 2 := by
  rw [distESIntegral]
  calc
    ∫ q in (p : ℝ)..1, distLowerQuantile uniform01Law q =
        ∫ q in (p : ℝ)..1, q := by
          refine intervalIntegral.integral_congr_ae ?_
          filter_upwards [] with q
          intro hq
          have hp1 : (p : ℝ) ≤ 1 := p.2.2
          have hqIocp : q ∈ Set.Ioc (p : ℝ) 1 := by
            simpa [Set.uIoc, hp1] using hq
          have hqIoc01 : q ∈ Set.Ioc (0 : ℝ) 1 := by
            exact ⟨lt_of_le_of_lt p.2.1 hqIocp.1, hqIocp.2⟩
          exact distLowerQuantile_uniform01_eq hqIoc01
    _ = (1 ^ 2 - (p : ℝ) ^ 2) / 2 := by
          rw [integral_id]
    _ = (1 - (p : ℝ) ^ 2) / 2 := by ring

theorem distES_uniform01_eq_of_lt_one (p : Level) (hp : (p : ℝ) < 1) :
    distES uniform01Law p = (1 + (p : ℝ)) / 2 := by
  have hne : 1 - (p : ℝ) ≠ 0 := by
    linarith
  rw [distES, dif_pos hp, distESIntegral_uniform01_eq]
  field_simp [hne]
  ring

end UniformLawFormulas

section AffinePushforward

instance instIsProbabilityMeasure_map_affine (μ : Measure ℝ) [IsProbabilityMeasure μ] (m c : ℝ) :
    IsProbabilityMeasure (Measure.map (fun y : ℝ => m * y + c) μ) :=
  Measure.isProbabilityMeasure_map (by fun_prop)

theorem preimage_affine_Iic {m c x : ℝ} (hm : 0 < m) :
    (fun y : ℝ => m * y + c) ⁻¹' Set.Iic x = Set.Iic ((x - c) / m) := by
  ext y
  constructor <;> intro hy
  · change m * y + c ≤ x at hy
    have hmy : m * y ≤ x - c := by linarith
    exact (le_div_iff₀ hm).2 (by simpa [mul_comm] using hmy)
  · have : y * m ≤ x - c := by
      have hy' : y ≤ (x - c) / m := hy
      exact (le_div_iff₀ hm).1 hy'
    have hmy : m * y ≤ x - c := by simpa [mul_comm] using this
    change m * y + c ≤ x
    linarith

theorem cdf_map_affine {μ : Measure ℝ} [IsProbabilityMeasure μ] {m c x : ℝ} (hm : 0 < m) :
    ProbabilityTheory.cdf (Measure.map (fun y : ℝ => m * y + c) μ) x =
      ProbabilityTheory.cdf μ ((x - c) / m) := by
  haveI : IsProbabilityMeasure (Measure.map (fun y : ℝ => m * y + c) μ) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  rw [ProbabilityTheory.cdf_eq_real (μ := Measure.map (fun y : ℝ => m * y + c) μ),
    measureReal_def, Measure.map_apply (by fun_prop) measurableSet_Iic, preimage_affine_Iic hm,
    ProbabilityTheory.cdf_eq_real (μ := μ), measureReal_def]

theorem distLowerQuantile_map_affine_eq {μ : Measure ℝ} [IsProbabilityMeasure μ] {m c u : ℝ}
    (hm : 0 < m) (hu : u ∈ Set.Ioo (0 : ℝ) 1) :
    distLowerQuantile (Measure.map (fun y : ℝ => m * y + c) μ) u =
      m * distLowerQuantile μ u + c := by
  let f : ℝ → ℝ := fun y => m * y + c
  let S : Set ℝ := {x : ℝ | u ≤ ProbabilityTheory.cdf μ x}
  have hS :
      {x : ℝ | u ≤ ProbabilityTheory.cdf (Measure.map f μ) x} = f '' S := by
    ext x
    constructor
    · intro hx
      refine ⟨(x - c) / m, ?_, ?_⟩
      · have hcdfx :
            ProbabilityTheory.cdf (Measure.map f μ) x =
              ProbabilityTheory.cdf μ ((x - c) / m) := by
          simpa [f] using cdf_map_affine (μ := μ) (m := m) (c := c) (x := x) hm
        simpa [S, hcdfx] using hx
      · have hxrepr : f ((x - c) / m) = x := by
          dsimp [f]
          field_simp [hm.ne']
          ring
        exact hxrepr
    · rintro ⟨y, hyS, rfl⟩
      have hyrepr : (f y - c) / m = y := by
        dsimp [f]
        field_simp [hm.ne']
        ring
      have hycdf : ProbabilityTheory.cdf (Measure.map f μ) (f y) = ProbabilityTheory.cdf μ y := by
        rw [show ProbabilityTheory.cdf (Measure.map f μ) (f y) =
            ProbabilityTheory.cdf μ ((f y - c) / m) by
              simpa [f] using cdf_map_affine (μ := μ) (m := m) (c := c) (x := f y) hm, hyrepr]
      simpa [S, hycdf] using hyS
  have hmon : _root_.Monotone f := by
    intro a b hab
    dsimp [f]
    simpa [add_comm, add_left_comm, add_assoc] using
      add_le_add_right (mul_le_mul_of_nonneg_left hab hm.le) c
  have hcont : Continuous f := by
    fun_prop
  change sInf {x : ℝ | u ≤ ProbabilityTheory.cdf (Measure.map f μ) x} = f (sInf S)
  rw [hS]
  exact
    (Monotone.map_csInf_of_continuousAt (Cf := hcont.continuousAt) hmon
      (upperLevelSet_nonempty μ hu.2) (upperLevelSet_bddBelow μ hu.1)).symm

theorem distESIntegral_map_affine_eq {μ : Measure ℝ} [IsProbabilityMeasure μ] {m c : ℝ}
    (hm : 0 < m) (p : Level) :
    distESIntegral (Measure.map (fun y : ℝ => m * y + c) μ) p =
      ∫ u in (p : ℝ)..1, (m * distLowerQuantile μ u + c) := by
  rw [distESIntegral]
  have hIooEqIoc : Set.Ioo (p : ℝ) (1 : ℝ) =ᵐ[volume] Set.Ioc (p : ℝ) (1 : ℝ) := Ioo_ae_eq_Ioc
  have hEqIoo :
      ∀ᵐ u ∂ volume.restrict (Set.Ioo (p : ℝ) (1 : ℝ)),
        distLowerQuantile (Measure.map (fun y : ℝ => m * y + c) μ) u =
          m * distLowerQuantile μ u + c := by
    rw [ae_restrict_iff' measurableSet_Ioo]
    filter_upwards [] with u hu
    have huIoo : u ∈ Set.Ioo (p : ℝ) 1 := by
      simpa [Set.Ioo] using hu
    have huIoo01 : u ∈ Set.Ioo (0 : ℝ) 1 := by
      exact ⟨lt_of_le_of_lt p.2.1 huIoo.1, huIoo.2⟩
    simpa using distLowerQuantile_map_affine_eq (μ := μ) (m := m) (c := c) hm huIoo01
  have hEqIoc :
      ∀ᵐ u ∂ volume.restrict (Set.Ioc (p : ℝ) (1 : ℝ)),
        distLowerQuantile (Measure.map (fun y : ℝ => m * y + c) μ) u =
          m * distLowerQuantile μ u + c := by
    exact ae_restrict_of_ae_eq_of_ae_restrict (s := Set.Ioo (p : ℝ) (1 : ℝ))
      (t := Set.Ioc (p : ℝ) (1 : ℝ)) hIooEqIoc hEqIoo
  refine intervalIntegral.integral_congr_ae_restrict ?_
  show ∀ᵐ u ∂ volume.restrict (Set.uIoc (p : ℝ) 1),
    distLowerQuantile (Measure.map (fun y : ℝ => m * y + c) μ) u =
      m * distLowerQuantile μ u + c
  simpa [Set.uIoc, p.2.2] using hEqIoc

theorem distESIntegral_map_affine_linear_eq {μ : Measure ℝ} [IsProbabilityMeasure μ] {m c : ℝ}
    (hm : 0 < m) (p : Level)
    (hfi : IntervalIntegrable (distLowerQuantile μ) volume (p : ℝ) 1) :
    distESIntegral (Measure.map (fun y : ℝ => m * y + c) μ) p =
      m * distESIntegral μ p + (1 - (p : ℝ)) * c := by
  have hconst : IntervalIntegrable (fun _ : ℝ => c) volume (p : ℝ) 1 := by
    simpa using
      (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => c) volume (p : ℝ) 1)
  rw [distESIntegral_map_affine_eq (μ := μ) (m := m) (c := c) hm p, distESIntegral,
    intervalIntegral.integral_add (hfi.const_mul m) hconst, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const]
  simpa [smul_eq_mul, sub_eq_add_neg, add_comm, add_left_comm, add_assoc, add_mul, mul_add]

theorem distES_map_affine_eq_of_lt_one_of_intervalIntegrable
    {μ : Measure ℝ} [IsProbabilityMeasure μ] {m c : ℝ}
    (hm : 0 < m) (p : Level) (hp : (p : ℝ) < 1)
    (hfi : IntervalIntegrable (distLowerQuantile μ) volume (p : ℝ) 1) :
    distES (Measure.map (fun y : ℝ => m * y + c) μ) p = m * distES μ p + c := by
  have hne : 1 - (p : ℝ) ≠ 0 := by
    linarith
  rw [distES, dif_pos hp, distESIntegral_map_affine_linear_eq (μ := μ) (m := m) (c := c) hm p hfi,
    distES, dif_pos hp]
  field_simp [hne]

end AffinePushforward

section AffineUniformLawFormulas

open unitInterval

/-- Positive-slope affine image of the standard uniform law on `[0,1]`. -/
def affineUniformLaw (m c : ℝ) : Measure ℝ :=
  Measure.map (fun u : I => m * (u : ℝ) + c) (volume : Measure I)

instance affineUniformLaw.instIsProbabilityMeasure (m c : ℝ) :
    IsProbabilityMeasure (affineUniformLaw m c) :=
  Measure.isProbabilityMeasure_map (by fun_prop)

/-- Rescaled coordinate `(x - c) / m`, viewed as a point of `[0,1]`. -/
def affineUniformLevel {m c x : ℝ} (hm : 0 < m) (hx : x ∈ Set.Icc c (c + m)) : I :=
  ⟨(x - c) / m, by
    constructor
    · exact div_nonneg (sub_nonneg.mpr hx.1) hm.le
    · have hx' : x - c ≤ m := by linarith [hx.2]
      exact (div_le_iff₀ hm).2 (by simpa using hx')⟩

@[simp] theorem coe_affineUniformLevel {m c x : ℝ} (hm : 0 < m)
    (hx : x ∈ Set.Icc c (c + m)) :
    ((affineUniformLevel hm hx : I) : ℝ) = (x - c) / m := rfl

theorem preimage_affineUniform_Iic {m c x : ℝ} (hm : 0 < m) (hx : x ∈ Set.Icc c (c + m)) :
    (fun u : I => m * (u : ℝ) + c) ⁻¹' Set.Iic x = Set.Iic (affineUniformLevel hm hx) := by
  ext u
  constructor
  · intro hu
    change m * (u : ℝ) + c ≤ x at hu
    change (u : ℝ) ≤ (x - c) / m
    rw [le_div_iff₀ hm, mul_comm]
    linarith
  · intro hu
    change (u : ℝ) ≤ (x - c) / m at hu
    change m * (u : ℝ) + c ≤ x
    have hu' : (u : ℝ) * m ≤ x - c := by
      simpa [mul_comm] using (le_div_iff₀ hm).1 hu
    linarith

theorem cdf_affineUniform_of_mem_Icc {m c x : ℝ} (hm : 0 < m)
    (hx : x ∈ Set.Icc c (c + m)) :
    ProbabilityTheory.cdf (affineUniformLaw m c) x = (x - c) / m := by
  haveI : IsProbabilityMeasure (affineUniformLaw m c) :=
    affineUniformLaw.instIsProbabilityMeasure m c
  rw [ProbabilityTheory.cdf_eq_real (μ := affineUniformLaw m c), affineUniformLaw, measureReal_def,
    Measure.map_apply (by fun_prop) measurableSet_Iic, preimage_affineUniform_Iic hm hx,
    unitInterval.volume_Iic]
  exact ENNReal.toReal_ofReal (div_nonneg (sub_nonneg.mpr hx.1) hm.le)

theorem cdf_affineUniform_of_lt {m c x : ℝ} (hm : 0 < m) (hx : x < c) :
    ProbabilityTheory.cdf (affineUniformLaw m c) x = 0 := by
  have hmono := ProbabilityTheory.monotone_cdf (affineUniformLaw m c)
  have hle :
      ProbabilityTheory.cdf (affineUniformLaw m c) x ≤
        ProbabilityTheory.cdf (affineUniformLaw m c) c := hmono hx.le
  have hc :
      ProbabilityTheory.cdf (affineUniformLaw m c) c = 0 := by
    rw [cdf_affineUniform_of_mem_Icc hm ⟨le_rfl, by nlinarith [hm]⟩]
    ring
  exact le_antisymm (hle.trans_eq hc) (ProbabilityTheory.cdf_nonneg _ _)

theorem cdf_affineUniform_of_ge {m c x : ℝ} (hm : 0 < m) (hx : c + m ≤ x) :
    ProbabilityTheory.cdf (affineUniformLaw m c) x = 1 := by
  have hmono := ProbabilityTheory.monotone_cdf (affineUniformLaw m c)
  have hge :
      ProbabilityTheory.cdf (affineUniformLaw m c) (c + m) ≤
        ProbabilityTheory.cdf (affineUniformLaw m c) x := hmono hx
  have hc :
      ProbabilityTheory.cdf (affineUniformLaw m c) (c + m) = 1 := by
    rw [cdf_affineUniform_of_mem_Icc hm ⟨by linarith [hm], le_rfl⟩]
    field_simp [hm.ne']
    ring
  exact le_antisymm (ProbabilityTheory.cdf_le_one _ _) (hc ▸ hge)

theorem distLowerQuantile_affineUniform_eq {m c q : ℝ} (hm : 0 < m) (hq : q ∈ Set.Ioc (0 : ℝ) 1) :
    distLowerQuantile (affineUniformLaw m c) q = m * q + c := by
  let S : Set ℝ := {x : ℝ | q ≤ ProbabilityTheory.cdf (affineUniformLaw m c) x}
  change sInf S = m * q + c
  have hmqcIcc : m * q + c ∈ Set.Icc c (c + m) := by
    constructor <;> nlinarith [hm, hq.1, hq.2]
  have hcdfq :
      ProbabilityTheory.cdf (affineUniformLaw m c) (m * q + c) = q := by
    rw [cdf_affineUniform_of_mem_Icc hm hmqcIcc]
    field_simp [hm.ne']
    ring
  apply le_antisymm
  · refine csInf_le (upperLevelSet_bddBelow (affineUniformLaw m c) hq.1) ?_
    simpa [S, hcdfq]
  · refine le_csInf ?_ ?_
    · exact ⟨m * q + c, by simpa [S, hcdfq]⟩
    · intro x hxS
      by_contra hxlt
      have hxq : q ≤ ProbabilityTheory.cdf (affineUniformLaw m c) x := by simpa [S] using hxS
      by_cases hxc : x < c
      · have hcdfx : ProbabilityTheory.cdf (affineUniformLaw m c) x = 0 :=
          cdf_affineUniform_of_lt hm hxc
        have : q ≤ 0 := by simpa [hcdfx] using hxq
        exact (not_le_of_gt hq.1) this
      · have hxc' : c ≤ x := not_lt.mp hxc
        have hxm : x ≤ c + m := by
          nlinarith [hxlt, hm, hq.2]
        have hcdfx :
            ProbabilityTheory.cdf (affineUniformLaw m c) x = (x - c) / m :=
          cdf_affineUniform_of_mem_Icc hm ⟨hxc', hxm⟩
        have : m * q + c ≤ x := by
          have hxq' : q ≤ (x - c) / m := by simpa [hcdfx] using hxq
          have hxq'' : q * m ≤ x - c := by
            simpa [mul_comm] using (le_div_iff₀ hm).1 hxq'
          linarith
        linarith

theorem distESIntegral_affineUniform_eq (m c : ℝ) (hm : 0 < m) (p : Level) :
    distESIntegral (affineUniformLaw m c) p =
      ∫ q in (p : ℝ)..1, (m * q + c) := by
  rw [distESIntegral]
  refine intervalIntegral.integral_congr_ae ?_
  filter_upwards [] with q
  intro hq
  have hp1 : (p : ℝ) ≤ 1 := p.2.2
  have hqIocp : q ∈ Set.Ioc (p : ℝ) 1 := by
    simpa [Set.uIoc, hp1] using hq
  have hqIoc01 : q ∈ Set.Ioc (0 : ℝ) 1 := by
    exact ⟨lt_of_le_of_lt p.2.1 hqIocp.1, hqIocp.2⟩
  exact distLowerQuantile_affineUniform_eq hm hqIoc01

theorem distESIntegral_affineUniform_closed (m c : ℝ) (hm : 0 < m) (p : Level) :
    distESIntegral (affineUniformLaw m c) p =
      m * ((1 - (p : ℝ) ^ 2) / 2) + (1 - (p : ℝ)) * c := by
  have hf_id : IntervalIntegrable (fun q : ℝ => q) volume (p : ℝ) 1 := by
    exact Continuous.intervalIntegrable continuous_id _ _
  have hf : IntervalIntegrable (fun q : ℝ => m * q) volume (p : ℝ) 1 := by
    simpa using hf_id.const_mul m
  have hg : IntervalIntegrable (fun _ : ℝ => c) volume (p : ℝ) 1 := by
    simpa using
      (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => c) volume (p : ℝ) 1)
  rw [distESIntegral_affineUniform_eq m c hm p, intervalIntegral.integral_add hf hg,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const, integral_id]
  simpa [smul_eq_mul, sub_eq_add_neg, add_comm, add_left_comm, add_assoc, add_mul, mul_add]

theorem distES_affineUniform_eq_of_lt_one (m c : ℝ) (hm : 0 < m) (p : Level)
    (hp : (p : ℝ) < 1) :
    distES (affineUniformLaw m c) p = m * ((1 + (p : ℝ)) / 2) + c := by
  have hne : 1 - (p : ℝ) ≠ 0 := by
    linarith
  have hf_id : IntervalIntegrable (fun q : ℝ => q) volume (p : ℝ) 1 := by
    exact Continuous.intervalIntegrable continuous_id _ _
  have hf : IntervalIntegrable (fun q : ℝ => m * q) volume (p : ℝ) 1 := by
    simpa using hf_id.const_mul m
  have hg : IntervalIntegrable (fun _ : ℝ => c) volume (p : ℝ) 1 := by
    simpa using (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => c) volume (p : ℝ) 1)
  rw [distES, dif_pos hp, distESIntegral_affineUniform_eq m c hm p,
    intervalIntegral.integral_add hf hg, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const, integral_id]
  field_simp [hne]
  simp [smul_eq_mul]
  ring

end AffineUniformLawFormulas

section FoldedAffineLaw

open unitInterval

/-- The folded witness with positive affine scaling. -/
def foldedAffineLaw (q : I) (m c : ℝ) : Measure ℝ :=
  Measure.map (fun u : I => m * ((foldMap q u : I) : ℝ) + c) (volume : Measure I)

instance foldedAffineLaw.instIsProbabilityMeasure (q : I) (m c : ℝ) :
    IsProbabilityMeasure (foldedAffineLaw q m c) :=
  Measure.isProbabilityMeasure_map (by fun_prop)

/-- Folding the unit coordinate before an affine positive rescaling does not change the law. -/
theorem foldedAffineLaw_eq_affineUniformLaw (q : I) (m c : ℝ) :
    foldedAffineLaw q m c = affineUniformLaw m c := by
  calc
    foldedAffineLaw q m c =
        Measure.map (fun x : ℝ => m * x + c)
          (Measure.map (fun u : I => ((foldMap q u : I) : ℝ)) (volume : Measure I)) := by
            simpa [foldedAffineLaw] using
              (Measure.map_map (μ := (volume : Measure I))
                (f := fun u : I => ((foldMap q u : I) : ℝ))
                (g := fun x : ℝ => m * x + c) (by fun_prop) (by fun_prop)).symm
    _ = Measure.map (fun x : ℝ => m * x + c) uniform01Law := by
          rw [law_foldMap_eq_uniform, uniform01Law]
    _ = affineUniformLaw m c := by
          simpa [uniform01Law, affineUniformLaw] using
            (Measure.map_map (μ := (volume : Measure I))
              (f := (Subtype.val : I → ℝ))
              (g := fun x : ℝ => m * x + c) (by fun_prop) measurable_subtype_coe)

theorem distLowerQuantile_foldedAffine_eq (q : I) {m c u : ℝ} (hm : 0 < m)
    (hu : u ∈ Set.Ioc (0 : ℝ) 1) :
    distLowerQuantile (foldedAffineLaw q m c) u = m * u + c := by
  simpa [foldedAffineLaw_eq_affineUniformLaw] using
    (distLowerQuantile_affineUniform_eq (m := m) (c := c) hm hu)

theorem distESIntegral_foldedAffine_eq (q : I) (m c : ℝ) (hm : 0 < m) (p : Level) :
    distESIntegral (foldedAffineLaw q m c) p =
      ∫ u in (p : ℝ)..1, (m * u + c) := by
  simpa [foldedAffineLaw_eq_affineUniformLaw] using
    (distESIntegral_affineUniform_eq (m := m) (c := c) hm p)

theorem distES_foldedAffine_eq_of_lt_one (q : I) (m c : ℝ) (hm : 0 < m) (p : Level)
    (hp : (p : ℝ) < 1) :
    distES (foldedAffineLaw q m c) p = m * ((1 + (p : ℝ)) / 2) + c := by
  simpa [foldedAffineLaw_eq_affineUniformLaw] using
    (distES_affineUniform_eq_of_lt_one (m := m) (c := c) hm p hp)

end FoldedAffineLaw

section FoldedSupInfLaw

open unitInterval

/-- The pointwise maximum of the unfolded and folded unit coordinates. -/
def supCoord (q : I) : I → ℝ := fun u => max (u : ℝ) ((foldMap q u : I) : ℝ)

/-- The pointwise minimum of the unfolded and folded unit coordinates. -/
def infCoord (q : I) : I → ℝ := fun u => min (u : ℝ) ((foldMap q u : I) : ℝ)

@[fun_prop]
theorem measurable_supCoord (q : I) : Measurable (supCoord q) := by
  unfold supCoord
  fun_prop

@[fun_prop]
theorem measurable_infCoord (q : I) : Measurable (infCoord q) := by
  unfold infCoord
  fun_prop

@[simp] theorem supCoord_of_le {q u : I} (huq : u ≤ q) :
    supCoord q u = max (u : ℝ) ((q : ℝ) - u) := by
  simp [supCoord, foldMap_of_le, huq]

@[simp] theorem supCoord_of_not_le {q u : I} (huq : ¬ u ≤ q) :
    supCoord q u = u := by
  simp [supCoord, foldMap_of_not_le, huq]

@[simp] theorem infCoord_of_le {q u : I} (huq : u ≤ q) :
    infCoord q u = min (u : ℝ) ((q : ℝ) - u) := by
  simp [infCoord, foldMap_of_le, huq]

@[simp] theorem infCoord_of_not_le {q u : I} (huq : ¬ u ≤ q) :
    infCoord q u = u := by
  simp [infCoord, foldMap_of_not_le, huq]

/-- The law of the folded supremum witness on the unit interval. -/
def foldedSupLaw (q : I) : Measure ℝ :=
  Measure.map (supCoord q) (volume : Measure I)

/-- The law of the folded infimum witness on the unit interval. -/
def foldedInfLaw (q : I) : Measure ℝ :=
  Measure.map (infCoord q) (volume : Measure I)

instance foldedSupLaw.instIsProbabilityMeasure (q : I) :
    IsProbabilityMeasure (foldedSupLaw q) :=
  Measure.isProbabilityMeasure_map (measurable_supCoord q).aemeasurable

instance foldedInfLaw.instIsProbabilityMeasure (q : I) :
    IsProbabilityMeasure (foldedInfLaw q) :=
  Measure.isProbabilityMeasure_map (measurable_infCoord q).aemeasurable

/-- Below the fold point `q`, the lower-tail preimage of the supremum coordinate is the symmetric
interval `[q - x, x]`. When `x < q / 2`, this interval is automatically empty. -/
theorem preimage_supCoord_Iic_of_le {q x : I} (hxq : x ≤ q) :
    supCoord q ⁻¹' Set.Iic x = Set.Icc (reflectAt q x hxq) x := by
  ext u
  constructor
  · intro hu
    change max (u : ℝ) (((foldMap q u : I) : ℝ)) ≤ (x : ℝ) at hu
    have hux : (u : ℝ) ≤ x := le_trans (le_max_left _ _) hu
    have huq : u ≤ q := by
      exact hux.trans hxq
    refine ⟨?_, hux⟩
    change (q : ℝ) - x ≤ (u : ℝ)
    have hfold : ((foldMap q u : I) : ℝ) ≤ (x : ℝ) := le_trans (le_max_right _ _) hu
    rw [foldMap_of_le huq] at hfold
    linarith
  · rintro ⟨hleft, hright⟩
    change max (u : ℝ) (((foldMap q u : I) : ℝ)) ≤ (x : ℝ)
    have huq : u ≤ q := hright.trans hxq
    rw [foldMap_of_le huq]
    change ((reflectAt q x hxq : I) : ℝ) ≤ (u : ℝ) at hleft
    rw [coe_reflectAt hxq] at hleft
    have hfold : (q : ℝ) - (u : ℝ) ≤ (x : ℝ) := by linarith
    exact max_le hright hfold

/-- Once the threshold is above the fold point, the supremum coordinate has the usual lower-tail
preimage. -/
theorem preimage_supCoord_Iic_of_ge {q x : I} (hqx : q ≤ x) :
    supCoord q ⁻¹' Set.Iic x = Set.Iic x := by
  ext u
  constructor
  · intro hu
    change max (u : ℝ) (((foldMap q u : I) : ℝ)) ≤ (x : ℝ) at hu
    exact le_trans (le_max_left _ _) hu
  · intro hu
    change max (u : ℝ) (((foldMap q u : I) : ℝ)) ≤ (x : ℝ)
    by_cases huq : u ≤ q
    · rw [foldMap_of_le huq]
      have hfold : (q : ℝ) - (u : ℝ) ≤ (x : ℝ) := by
        have hqx' : (q : ℝ) ≤ (x : ℝ) := hqx
        linarith [u.2.1, hqx']
      exact max_le hu hfold
    · rw [foldMap_of_not_le huq]
      exact max_le_iff.mpr ⟨hu, hu⟩

/-- Above the fold point, the infimum coordinate has the same lower-tail preimage as the original
uniform coordinate. -/
theorem preimage_infCoord_Iic_of_ge {q x : I} (hqx : q ≤ x) :
    infCoord q ⁻¹' Set.Iic x = Set.Iic x := by
  ext u
  constructor
  · intro hu
    change min (u : ℝ) (((foldMap q u : I) : ℝ)) ≤ (x : ℝ) at hu
    by_cases huq : u ≤ q
    · exact huq.trans hqx
    · have : (u : ℝ) ≤ x := by
        simpa [infCoord, foldMap_of_not_le huq] using hu
      exact this
  · intro hu
    change min (u : ℝ) (((foldMap q u : I) : ℝ)) ≤ (x : ℝ)
    by_cases huq : u ≤ q
    · rw [foldMap_of_le huq]
      have hfold : (q : ℝ) - (u : ℝ) ≤ (x : ℝ) := by
        have hqx' : (q : ℝ) ≤ (x : ℝ) := hqx
        linarith [u.2.1, hqx']
      exact min_le_iff.mpr (Or.inl hu)
    · rw [foldMap_of_not_le huq]
      exact min_le_iff.mpr (Or.inl hu)

theorem cdf_foldedSupLaw_of_mem_Icc {q : I} {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) q) :
    ProbabilityTheory.cdf (foldedSupLaw q) x = max 0 (2 * x - q) := by
  let xI : I := ⟨x, ⟨hx.1, hx.2.trans q.2.2⟩⟩
  have hxIq : xI ≤ q := hx.2
  rw [ProbabilityTheory.cdf_eq_real (μ := foldedSupLaw q), foldedSupLaw, measureReal_def,
    Measure.map_apply (measurable_supCoord q) measurableSet_Iic,
    preimage_supCoord_Iic_of_le (q := q) (x := xI) hxIq, unitInterval.volume_Icc]
  rw [ENNReal.toReal_ofReal']
  have hring : (xI : ℝ) - ((q : ℝ) - xI) = 2 * x - q := by
    ring
  simpa [coe_reflectAt hxIq, hring, max_comm]

theorem cdf_foldedSupLaw_of_lt_zero {q : I} {x : ℝ} (hx : x < 0) :
    ProbabilityTheory.cdf (foldedSupLaw q) x = 0 := by
  have hmono := ProbabilityTheory.monotone_cdf (foldedSupLaw q)
  have hle : ProbabilityTheory.cdf (foldedSupLaw q) x ≤ ProbabilityTheory.cdf (foldedSupLaw q) 0 :=
    hmono hx.le
  have hzero : ProbabilityTheory.cdf (foldedSupLaw q) 0 = 0 := by
    have h0Icc : (0 : ℝ) ∈ Set.Icc (0 : ℝ) q := ⟨le_rfl, q.2.1⟩
    rw [cdf_foldedSupLaw_of_mem_Icc (q := q) h0Icc]
    simp [q.2.1]
  exact le_antisymm (hle.trans_eq hzero) (ProbabilityTheory.cdf_nonneg _ _)

theorem cdf_foldedSupLaw_of_mem_Icc_ge {q : I} {x : ℝ} (hx : x ∈ Set.Icc (q : ℝ) (1 : ℝ)) :
    ProbabilityTheory.cdf (foldedSupLaw q) x = x := by
  let xI : I := ⟨x, ⟨q.2.1.trans hx.1, hx.2⟩⟩
  have hqx : q ≤ xI := hx.1
  rw [ProbabilityTheory.cdf_eq_real (μ := foldedSupLaw q), foldedSupLaw, measureReal_def,
    Measure.map_apply (measurable_supCoord q) measurableSet_Iic,
    preimage_supCoord_Iic_of_ge (q := q) (x := xI) hqx, unitInterval.volume_Iic]
  exact ENNReal.toReal_ofReal xI.2.1

theorem cdf_foldedInfLaw_of_mem_Icc_ge {q : I} {x : ℝ} (hx : x ∈ Set.Icc (q : ℝ) (1 : ℝ)) :
    ProbabilityTheory.cdf (foldedInfLaw q) x = x := by
  let xI : I := ⟨x, ⟨q.2.1.trans hx.1, hx.2⟩⟩
  have hqx : q ≤ xI := hx.1
  rw [ProbabilityTheory.cdf_eq_real (μ := foldedInfLaw q), foldedInfLaw, measureReal_def,
    Measure.map_apply (measurable_infCoord q) measurableSet_Iic,
    preimage_infCoord_Iic_of_ge (q := q) (x := xI) hqx, unitInterval.volume_Iic]
  exact ENNReal.toReal_ofReal xI.2.1

theorem cdf_foldedInfLaw_of_lt_zero {q : I} {x : ℝ} (hx : x < 0) :
    ProbabilityTheory.cdf (foldedInfLaw q) x = 0 := by
  have hmono := ProbabilityTheory.monotone_cdf (foldedInfLaw q)
  have hle : ProbabilityTheory.cdf (foldedInfLaw q) x ≤ ProbabilityTheory.cdf (foldedInfLaw q) 0 :=
    hmono hx.le
  have hzero : ProbabilityTheory.cdf (foldedInfLaw q) 0 = 0 := by
    have hmeas : foldedInfLaw q (Set.Iic 0) = 0 := by
      rw [foldedInfLaw, Measure.map_apply (measurable_infCoord q) measurableSet_Iic]
      have hsubset : infCoord q ⁻¹' Set.Iic 0 ⊆ ({0, q} : Set I) := by
        intro u hu
        change min (u : ℝ) (((foldMap q u : I) : ℝ)) ≤ 0 at hu
        have hnonneg : 0 ≤ min (u : ℝ) (((foldMap q u : I) : ℝ)) := by
          exact le_min u.2.1 (foldMap q u).2.1
        have hmin0 : min (u : ℝ) (((foldMap q u : I) : ℝ)) = 0 := le_antisymm hu hnonneg
        by_cases hul : (u : ℝ) ≤ (((foldMap q u : I) : ℝ))
        · have hu0 : (u : ℝ) = 0 := by
            rw [min_eq_left hul] at hmin0
            exact hmin0
          have : u = (0 : I) := Subtype.ext hu0
          simp [this]
        · have hfold0 : (((foldMap q u : I) : ℝ)) = 0 := by
            have hulf : (((foldMap q u : I) : ℝ)) ≤ (u : ℝ) := le_of_not_ge hul
            rw [min_eq_right hulf] at hmin0
            exact hmin0
          have huq : u ≤ q := by
            by_contra huq
            rw [foldMap_of_not_le huq] at hfold0
            have : (u : ℝ) ≠ 0 := by
              intro hu0
              have hu_eq_zero : u = (0 : I) := Subtype.ext hu0
              apply huq
              simpa [hu_eq_zero] using q.2.1
            exact this hfold0
          have hu_eq_q : u = q := by
            apply Subtype.ext
            rw [foldMap_of_le huq] at hfold0
            linarith
          simp [hu_eq_q]
      have hfinite : ({0, q} : Set I).Finite := by simp
      exact measure_mono_null hsubset (hfinite.measure_zero (volume : Measure I))
    rw [ProbabilityTheory.cdf_eq_real (μ := foldedInfLaw q), measureReal_def, hmeas]
    simp
  exact le_antisymm (hle.trans_eq hzero) (ProbabilityTheory.cdf_nonneg _ _)

theorem preimage_infCoord_Iic_of_le_half {q x : I} (hx2q : 2 * (x : ℝ) ≤ q) :
    infCoord q ⁻¹' Set.Iic x =
      Set.Icc (0 : I) x ∪
        Set.Icc (reflectAt q x (show x ≤ q from by
          have hxq' : (x : ℝ) ≤ q := by linarith [x.2.1]
          exact hxq')) q := by
  have hxq : x ≤ q := by
    have hxq' : (x : ℝ) ≤ q := by linarith [x.2.1]
    exact hxq'
  ext u
  constructor
  · intro hu
    change min (u : ℝ) (((foldMap q u : I) : ℝ)) ≤ (x : ℝ) at hu
    by_cases huq : u ≤ q
    · rw [foldMap_of_le huq] at hu
      by_cases hux : (u : ℝ) ≤ x
      · exact Or.inl ⟨u.2.1, hux⟩
      · have hxu : (x : ℝ) < u := lt_of_not_ge hux
        have hfold : (q : ℝ) - (u : ℝ) ≤ (x : ℝ) := by
          rcases min_le_iff.mp hu with hu' | hfold
          · exact False.elim (hux hu')
          · exact hfold
        have hleft : ((reflectAt q x hxq : I) : ℝ) ≤ (u : ℝ) := by
          rw [coe_reflectAt hxq]
          linarith
        exact Or.inr ⟨hleft, huq⟩
    · exfalso
      have : (u : ℝ) ≤ x := by simpa [infCoord, foldMap_of_not_le huq] using hu
      exact huq (this.trans hxq)
  · intro hu
    change min (u : ℝ) (((foldMap q u : I) : ℝ)) ≤ (x : ℝ)
    rcases hu with hu | hu
    · exact min_le_iff.mpr (Or.inl hu.2)
    · have huq : u ≤ q := hu.2
      rw [foldMap_of_le huq]
      have hfold : (q : ℝ) - (u : ℝ) ≤ (x : ℝ) := by
        have hu' : ((reflectAt q x hxq : I) : ℝ) ≤ (u : ℝ) := hu.1
        rw [coe_reflectAt hxq] at hu'
        linarith
      exact min_le_iff.mpr (Or.inr hfold)

theorem preimage_infCoord_Iic_of_half_le {q x : I} (hqx2 : q ≤ 2 * (x : ℝ)) (hxq : x ≤ q) :
    infCoord q ⁻¹' Set.Iic x = Set.Icc (0 : I) q := by
  ext u
  constructor
  · intro hu
    change min (u : ℝ) (((foldMap q u : I) : ℝ)) ≤ (x : ℝ) at hu
    by_cases huq : u ≤ q
    · exact ⟨u.2.1, huq⟩
    · exfalso
      have : (u : ℝ) ≤ x := by simpa [infCoord, foldMap_of_not_le huq] using hu
      exact huq (this.trans hxq)
  · intro hu
    change min (u : ℝ) (((foldMap q u : I) : ℝ)) ≤ (x : ℝ)
    have huq : u ≤ q := hu.2
    rw [foldMap_of_le huq]
    have hqdiv2 : (q : ℝ) / 2 ≤ (x : ℝ) := by linarith
    have hminle : min (u : ℝ) ((q : ℝ) - (u : ℝ)) ≤ (q : ℝ) / 2 := by
      by_cases hul : (u : ℝ) ≤ (q : ℝ) - (u : ℝ)
      · rw [min_eq_left hul]
        linarith
      · rw [min_eq_right (le_of_not_ge hul)]
        linarith
    exact hminle.trans hqdiv2

theorem cdf_foldedInfLaw_of_mem_Icc_half {q : I} {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) ((q : ℝ) / 2)) :
    ProbabilityTheory.cdf (foldedInfLaw q) x = 2 * x := by
  have hx1 : x ≤ 1 := by
    have hq2 : (q : ℝ) / 2 ≤ 1 := by nlinarith [q.2.2]
    exact le_trans hx.2 hq2
  let xI : I := ⟨x, ⟨hx.1, hx1⟩⟩
  have hx2q : 2 * (xI : ℝ) ≤ q := by
    linarith [hx.2]
  have hxq : xI ≤ q := by
    have : (xI : ℝ) ≤ q := by linarith [hx2q, xI.2.1]
    exact this
  rw [ProbabilityTheory.cdf_eq_real (μ := foldedInfLaw q), foldedInfLaw, measureReal_def,
    Measure.map_apply (measurable_infCoord q) measurableSet_Iic,
    preimage_infCoord_Iic_of_le_half (q := q) (x := xI) hx2q]
  let A : Set I := Set.Icc (0 : I) xI
  let B : Set I := Set.Icc (reflectAt q xI hxq) q
  have hinter :
      A ∩ B = Set.Icc (reflectAt q xI hxq) xI := by
    ext u
    constructor
    · intro hu
      exact ⟨hu.2.1, hu.1.2⟩
    · intro hu
      exact ⟨⟨u.2.1, hu.2⟩, ⟨hu.1, hu.2.trans hxq⟩⟩
  have hzeroInter : (volume : Measure I) (A ∩ B) = 0 := by
    rw [hinter, unitInterval.volume_Icc, ENNReal.ofReal_eq_zero]
    rw [coe_reflectAt hxq]
    linarith [hx2q]
  have hunion :
      (volume : Measure I) (A ∪ B) = (volume : Measure I) A + (volume : Measure I) B := by
    have hunion' :=
      measure_union_add_inter (μ := (volume : Measure I)) A measurableSet_Icc (t := B)
    rw [hzeroInter, add_zero] at hunion'
    exact hunion'
  have hA : 0 ≤ (xI : ℝ) - (0 : ℝ) := sub_nonneg.mpr xI.2.1
  have hB : 0 ≤ (q : ℝ) - ((reflectAt q xI hxq : I) : ℝ) := by
    rw [coe_reflectAt hxq]
    linarith [xI.2.1]
  have hx0 : 0 ≤ x := hx.1
  rw [hunion, unitInterval.volume_Icc, unitInterval.volume_Icc,
    ENNReal.toReal_add ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top]
  simp [hA, hB, coe_reflectAt hxq, xI]
  rw [ENNReal.toReal_ofReal hx0]
  ring

theorem cdf_foldedInfLaw_of_mem_Icc_mid {q : I} {x : ℝ}
    (hx : x ∈ Set.Icc ((q : ℝ) / 2) (q : ℝ)) :
    ProbabilityTheory.cdf (foldedInfLaw q) x = q := by
  let xI : I := ⟨x, ⟨by linarith [q.2.1, hx.1], hx.2.trans q.2.2⟩⟩
  have hqx2 : q ≤ 2 * (xI : ℝ) := by
    linarith [hx.1]
  have hxq : xI ≤ q := by
    exact hx.2
  rw [ProbabilityTheory.cdf_eq_real (μ := foldedInfLaw q), foldedInfLaw, measureReal_def,
    Measure.map_apply (measurable_infCoord q) measurableSet_Iic,
    preimage_infCoord_Iic_of_half_le (q := q) (x := xI) hqx2 hxq, unitInterval.volume_Icc]
  simpa using ENNReal.toReal_ofReal q.2.1

theorem distLowerQuantile_foldedSup_eq_of_lt_q {q u : ℝ} (hq : q ∈ Set.Ioc (0 : ℝ) 1)
    (hu : u ∈ Set.Ioc (0 : ℝ) q) :
    distLowerQuantile (foldedSupLaw ⟨q, ⟨hq.1.le, hq.2⟩⟩) u = (u + q) / 2 := by
  let qI : I := ⟨q, ⟨hq.1.le, hq.2⟩⟩
  let S : Set ℝ := {x : ℝ | u ≤ ProbabilityTheory.cdf (foldedSupLaw qI) x}
  change sInf S = (u + q) / 2
  have huIcc : (u + q) / 2 ∈ Set.Icc (0 : ℝ) q := by
    constructor
    · linarith [hu.1, hq.1]
    · linarith [hu.2]
  have hcdf_mid : ProbabilityTheory.cdf (foldedSupLaw qI) ((u + q) / 2) = u := by
    rw [cdf_foldedSupLaw_of_mem_Icc (q := qI) huIcc]
    have : 2 * ((u + q) / 2) - q = u := by ring
    rw [this]
    exact max_eq_right hu.1.le
  apply le_antisymm
  · refine csInf_le (upperLevelSet_bddBelow (foldedSupLaw qI) hu.1) ?_
    simpa [S, hcdf_mid]
  · refine le_csInf ?_ ?_
    · exact ⟨(u + q) / 2, by simpa [S, hcdf_mid]⟩
    · intro x hxS
      by_contra hxlt
      have hxlt' : x < (u + q) / 2 := lt_of_not_ge hxlt
      have hxu : u ≤ ProbabilityTheory.cdf (foldedSupLaw qI) x := by simpa [S] using hxS
      by_cases hx0 : x < 0
      · have hcdfx : ProbabilityTheory.cdf (foldedSupLaw qI) x = 0 :=
          cdf_foldedSupLaw_of_lt_zero (q := qI) hx0
        have : u ≤ 0 := by simpa [hcdfx] using hxu
        exact (not_le_of_gt hu.1) this
      · have hx0' : 0 ≤ x := not_lt.mp hx0
        have hmidleq : (u + q) / 2 ≤ q := by linarith [hu.2]
        have hxq : x ≤ q := hxlt'.le.trans hmidleq
        have hcdfx : ProbabilityTheory.cdf (foldedSupLaw qI) x = max 0 (2 * x - q) :=
          cdf_foldedSupLaw_of_mem_Icc (q := qI) ⟨hx0', hxq⟩
        have hmaxlt : max (0 : ℝ) (2 * x - q) < u := by
          refine max_lt_iff.mpr ?_
          constructor
          · exact hu.1
          · linarith
        have : ProbabilityTheory.cdf (foldedSupLaw qI) x < u := by simpa [hcdfx] using hmaxlt
        exact (not_lt_of_ge hxu) this

theorem distLowerQuantile_foldedSup_eq_of_gt_q {q u : ℝ} (hq : q ∈ Set.Ioc (0 : ℝ) 1)
    (hu : u ∈ Set.Ioc q 1) :
    distLowerQuantile (foldedSupLaw ⟨q, ⟨hq.1.le, hq.2⟩⟩) u = u := by
  let qI : I := ⟨q, ⟨hq.1.le, hq.2⟩⟩
  let S : Set ℝ := {x : ℝ | u ≤ ProbabilityTheory.cdf (foldedSupLaw qI) x}
  change sInf S = u
  have huIcc : u ∈ Set.Icc q (1 : ℝ) := ⟨hu.1.le, hu.2⟩
  have hcdf_u : ProbabilityTheory.cdf (foldedSupLaw qI) u = u :=
    cdf_foldedSupLaw_of_mem_Icc_ge (q := qI) huIcc
  have hcdf_q : ProbabilityTheory.cdf (foldedSupLaw qI) q = q := by
    exact cdf_foldedSupLaw_of_mem_Icc_ge (q := qI) ⟨le_rfl, hq.2⟩
  apply le_antisymm
  · refine csInf_le (upperLevelSet_bddBelow (foldedSupLaw qI) (lt_trans hq.1 hu.1)) ?_
    simpa [S, hcdf_u]
  · refine le_csInf ?_ ?_
    · exact ⟨u, by simpa [S, hcdf_u]⟩
    · intro x hxS
      by_contra hxlt
      have hxu : u ≤ ProbabilityTheory.cdf (foldedSupLaw qI) x := by simpa [S] using hxS
      by_cases hx0 : x < 0
      · have hcdfx : ProbabilityTheory.cdf (foldedSupLaw qI) x = 0 :=
          cdf_foldedSupLaw_of_lt_zero (q := qI) hx0
        have : u ≤ 0 := by simpa [hcdfx] using hxu
        exact (not_le_of_gt (lt_trans hq.1 hu.1)) this
      · have hx0' : 0 ≤ x := not_lt.mp hx0
        by_cases hxq : x < q
        · have hmon := ProbabilityTheory.monotone_cdf (foldedSupLaw qI)
          have hcdfx_le : ProbabilityTheory.cdf (foldedSupLaw qI) x ≤ q := by
            simpa [hcdf_q] using hmon hxq.le
          have : u ≤ q := le_trans hxu hcdfx_le
          exact (not_le_of_gt hu.1) this
        · have hqle : q ≤ x := not_lt.mp hxq
          have hx1 : x ≤ 1 := by linarith [hxlt, hu.2]
          have hcdfx : ProbabilityTheory.cdf (foldedSupLaw qI) x = x :=
            cdf_foldedSupLaw_of_mem_Icc_ge (q := qI) ⟨hqle, hx1⟩
          have : u ≤ x := by simpa [hcdfx] using hxu
          linarith

theorem distLowerQuantile_foldedInf_eq_of_gt_q {q u : ℝ} (hq : q ∈ Set.Ioc (0 : ℝ) 1)
    (hu : u ∈ Set.Ioc q 1) :
    distLowerQuantile (foldedInfLaw ⟨q, ⟨hq.1.le, hq.2⟩⟩) u = u := by
  let qI : I := ⟨q, ⟨hq.1.le, hq.2⟩⟩
  let S : Set ℝ := {x : ℝ | u ≤ ProbabilityTheory.cdf (foldedInfLaw qI) x}
  change sInf S = u
  have huIcc : u ∈ Set.Icc q (1 : ℝ) := ⟨hu.1.le, hu.2⟩
  have hcdf_u : ProbabilityTheory.cdf (foldedInfLaw qI) u = u :=
    cdf_foldedInfLaw_of_mem_Icc_ge (q := qI) huIcc
  have hcdf_q : ProbabilityTheory.cdf (foldedInfLaw qI) q = q := by
    exact cdf_foldedInfLaw_of_mem_Icc_ge (q := qI) ⟨le_rfl, hq.2⟩
  apply le_antisymm
  · refine csInf_le (upperLevelSet_bddBelow (foldedInfLaw qI) (lt_trans hq.1 hu.1)) ?_
    simpa [S, hcdf_u]
  · refine le_csInf ?_ ?_
    · exact ⟨u, by simpa [S, hcdf_u]⟩
    · intro x hxS
      by_contra hxlt
      have hxu : u ≤ ProbabilityTheory.cdf (foldedInfLaw qI) x := by simpa [S] using hxS
      by_cases hx0 : x < 0
      · have hcdfx : ProbabilityTheory.cdf (foldedInfLaw qI) x = 0 :=
          cdf_foldedInfLaw_of_lt_zero (q := qI) hx0
        have : u ≤ 0 := by simpa [hcdfx] using hxu
        exact (not_le_of_gt (lt_trans hq.1 hu.1)) this
      · by_cases hxq : x < q
        · have hmon := ProbabilityTheory.monotone_cdf (foldedInfLaw qI)
          have hcdfx_le : ProbabilityTheory.cdf (foldedInfLaw qI) x ≤ q := by
            simpa [hcdf_q] using hmon hxq.le
          have : u ≤ q := le_trans hxu hcdfx_le
          exact (not_le_of_gt hu.1) this
        · have hqle : q ≤ x := not_lt.mp hxq
          have hx1 : x ≤ 1 := by linarith [hxlt, hu.2]
          have hcdfx : ProbabilityTheory.cdf (foldedInfLaw qI) x = x :=
            cdf_foldedInfLaw_of_mem_Icc_ge (q := qI) ⟨hqle, hx1⟩
          have : u ≤ x := by simpa [hcdfx] using hxu
          linarith

theorem distLowerQuantile_foldedInf_eq_of_lt_q {q u : ℝ} (hq : q ∈ Set.Ioc (0 : ℝ) 1)
    (hu : u ∈ Set.Ioc (0 : ℝ) q) :
    distLowerQuantile (foldedInfLaw ⟨q, ⟨hq.1.le, hq.2⟩⟩) u = u / 2 := by
  let qI : I := ⟨q, ⟨hq.1.le, hq.2⟩⟩
  let S : Set ℝ := {x : ℝ | u ≤ ProbabilityTheory.cdf (foldedInfLaw qI) x}
  change sInf S = u / 2
  have huHalf : u / 2 ∈ Set.Icc (0 : ℝ) (q / 2) := by
    constructor
    · linarith [hu.1]
    · linarith [hu.2]
  have hcdf_half : ProbabilityTheory.cdf (foldedInfLaw qI) (u / 2) = u := by
    rw [cdf_foldedInfLaw_of_mem_Icc_half (q := qI) huHalf]
    ring
  apply le_antisymm
  · refine csInf_le (upperLevelSet_bddBelow (foldedInfLaw qI) hu.1) ?_
    simpa [S, hcdf_half]
  · refine le_csInf ?_ ?_
    · exact ⟨u / 2, by simpa [S, hcdf_half]⟩
    · intro x hxS
      by_contra hxlt
      have hxu : u ≤ ProbabilityTheory.cdf (foldedInfLaw qI) x := by simpa [S] using hxS
      by_cases hx0 : x < 0
      · have hcdfx : ProbabilityTheory.cdf (foldedInfLaw qI) x = 0 :=
          cdf_foldedInfLaw_of_lt_zero (q := qI) hx0
        have : u ≤ 0 := by simpa [hcdfx] using hxu
        exact (not_le_of_gt hu.1) this
      · have hx0' : 0 ≤ x := not_lt.mp hx0
        by_cases hxh : x ≤ q / 2
        · have hcdfx : ProbabilityTheory.cdf (foldedInfLaw qI) x = 2 * x :=
            cdf_foldedInfLaw_of_mem_Icc_half (q := qI) ⟨hx0', hxh⟩
          have : ProbabilityTheory.cdf (foldedInfLaw qI) x < u := by
            simpa [hcdfx] using (show 2 * x < u by linarith)
          exact (not_lt_of_ge hxu) this
        · have hxltq2 : x < q / 2 := by
            linarith [hxlt, hu.2]
          exact False.elim (hxh hxltq2.le)

theorem distESIntegral_foldedSup_eq_split_of_lt_q {q : ℝ} (hq : q ∈ Set.Ioc (0 : ℝ) 1)
    (p : Level) (hp : (p : ℝ) < q) :
    distESIntegral (foldedSupLaw ⟨q, ⟨hq.1.le, hq.2⟩⟩) p =
      (∫ u in (p : ℝ)..q, (u + q) / 2) + ∫ u in q..1, u := by
  let qI : I := ⟨q, ⟨hq.1.le, hq.2⟩⟩
  let f : ℝ → ℝ := fun u => if u ≤ q then (u + q) / 2 else u
  have hqle : (p : ℝ) ≤ q := hp.le
  have hfull :
      ∫ u in (p : ℝ)..1, distLowerQuantile (foldedSupLaw qI) u =
        ∫ u in (p : ℝ)..1, f u := by
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [] with u hu
    have huIoc : u ∈ Set.Ioc (p : ℝ) 1 := by
      simpa [Set.uIoc, p.2.2] using hu
    by_cases huq : u ≤ q
    · have huIoc0q : u ∈ Set.Ioc (0 : ℝ) q := by
        exact ⟨lt_of_le_of_lt p.2.1 huIoc.1, huq⟩
      rw [distLowerQuantile_foldedSup_eq_of_lt_q (hq := hq) huIoc0q]
      simp [f, huq]
    · have huIocq1 : u ∈ Set.Ioc q 1 := ⟨lt_of_not_ge huq, huIoc.2⟩
      rw [distLowerQuantile_foldedSup_eq_of_gt_q (hq := hq) huIocq1]
      simp [f, huq]
  have hleft_simple : IntervalIntegrable (fun u : ℝ => (u + q) / 2) volume (p : ℝ) q := by
    simpa using (((continuous_id.add continuous_const).div_const (2 : ℝ)).intervalIntegrable
      (p : ℝ) q)
  have hright_simple : IntervalIntegrable (fun u : ℝ => u) volume q 1 := by
    exact Continuous.intervalIntegrable continuous_id q 1
  have hf_pq : IntervalIntegrable f volume (p : ℝ) q := by
    refine hleft_simple.congr ?_
    intro u hu
    have huIoc : u ∈ Set.Ioc (p : ℝ) q := by
      simpa [Set.uIoc, hqle] using hu
    simp [f, huIoc.2]
  have hf_q1 : IntervalIntegrable f volume q 1 := by
    refine hright_simple.congr ?_
    intro u hu
    have huIoc : u ∈ Set.Ioc q 1 := by
      simpa [Set.uIoc, hq.2] using hu
    simp [f, not_le_of_gt huIoc.1]
  have hleft :
      ∫ u in (p : ℝ)..q, f u = ∫ u in (p : ℝ)..q, (u + q) / 2 := by
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [] with u hu
    have huIoc : u ∈ Set.Ioc (p : ℝ) q := by
      simpa [Set.uIoc, hqle] using hu
    simp [f, huIoc.2]
  have hright :
      ∫ u in q..1, f u = ∫ u in q..1, u := by
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [] with u hu
    have huIoc : u ∈ Set.Ioc q 1 := by
      simpa [Set.uIoc, hq.2] using hu
    simp [f, not_le_of_gt huIoc.1]
  let A : ℝ := ∫ u in (p : ℝ)..1, f u
  let B : ℝ := ∫ u in (p : ℝ)..q, f u
  let C : ℝ := ∫ u in q..1, f u
  let B' : ℝ := ∫ u in (p : ℝ)..q, (u + q) / 2
  let C' : ℝ := ∫ u in q..1, u
  have hsplit' : A = B + C := by
    dsimp [A, B, C]
    rw [← intervalIntegral.integral_add_adjacent_intervals hf_pq hf_q1]
  have hsum' : B + C = B' + C' := by
    dsimp [B, C, B', C']
    simpa using congrArg₂ (fun x y : ℝ => x + y) hleft hright
  calc
    distESIntegral (foldedSupLaw qI) p = ∫ u in (p : ℝ)..1, f u := by
      rw [distESIntegral, hfull]
    _ = A := by rfl
    _ = B + C := hsplit'
    _ = B' + C' := hsum'
    _ = (∫ u in (p : ℝ)..q, (u + q) / 2) + ∫ u in q..1, u := by rfl

theorem distESIntegral_foldedSup_eq_of_ge_q {q : ℝ} (hq : q ∈ Set.Ioc (0 : ℝ) 1)
    (p : Level) (hqp : q ≤ (p : ℝ)) :
    distESIntegral (foldedSupLaw ⟨q, ⟨hq.1.le, hq.2⟩⟩) p =
      ∫ u in (p : ℝ)..1, u := by
  let qI : I := ⟨q, ⟨hq.1.le, hq.2⟩⟩
  rw [distESIntegral]
  refine intervalIntegral.integral_congr_ae ?_
  filter_upwards [] with u hu
  have huIoc : u ∈ Set.Ioc (p : ℝ) 1 := by
    simpa [Set.uIoc, p.2.2] using hu
  have huq : u ∈ Set.Ioc q 1 := by
    exact ⟨lt_of_le_of_lt hqp huIoc.1, huIoc.2⟩
  simpa using distLowerQuantile_foldedSup_eq_of_gt_q (hq := hq) huq

theorem distESIntegral_foldedInf_eq_of_ge_q {q : ℝ} (hq : q ∈ Set.Ioc (0 : ℝ) 1)
    (p : Level) (hqp : q ≤ (p : ℝ)) :
    distESIntegral (foldedInfLaw ⟨q, ⟨hq.1.le, hq.2⟩⟩) p =
      ∫ u in (p : ℝ)..1, u := by
  let qI : I := ⟨q, ⟨hq.1.le, hq.2⟩⟩
  rw [distESIntegral]
  refine intervalIntegral.integral_congr_ae ?_
  filter_upwards [] with u hu
  have huIoc : u ∈ Set.Ioc (p : ℝ) 1 := by
    simpa [Set.uIoc, p.2.2] using hu
  have huq : u ∈ Set.Ioc q 1 := by
    exact ⟨lt_of_le_of_lt hqp huIoc.1, huIoc.2⟩
  simpa using distLowerQuantile_foldedInf_eq_of_gt_q (hq := hq) huq

theorem distESIntegral_foldedInf_eq_split_of_lt_q {q : ℝ} (hq : q ∈ Set.Ioc (0 : ℝ) 1)
    (p : Level) (hp : (p : ℝ) < q) :
    distESIntegral (foldedInfLaw ⟨q, ⟨hq.1.le, hq.2⟩⟩) p =
      (∫ u in (p : ℝ)..q, u / 2) + ∫ u in q..1, u := by
  let qI : I := ⟨q, ⟨hq.1.le, hq.2⟩⟩
  have hqle : (p : ℝ) ≤ q := hp.le
  have hleft_simple : IntervalIntegrable (fun u : ℝ => u / 2) volume (p : ℝ) q := by
    simpa using ((continuous_id.div_const (2 : ℝ)).intervalIntegrable (p : ℝ) q)
  have hright_simple : IntervalIntegrable (fun u : ℝ => u) volume q 1 := by
    exact Continuous.intervalIntegrable continuous_id q 1
  have hleft :
      ∫ u in (p : ℝ)..q, distLowerQuantile (foldedInfLaw qI) u =
        ∫ u in (p : ℝ)..q, u / 2 := by
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [] with u hu
    have huIoc : u ∈ Set.Ioc (p : ℝ) q := by
      simpa [Set.uIoc, hqle] using hu
    have huIoc0q : u ∈ Set.Ioc (0 : ℝ) q := by
      exact ⟨lt_of_le_of_lt p.2.1 huIoc.1, huIoc.2⟩
    exact distLowerQuantile_foldedInf_eq_of_lt_q (hq := hq) huIoc0q
  have hright :
      ∫ u in q..1, distLowerQuantile (foldedInfLaw qI) u =
        ∫ u in q..1, u := by
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [] with u hu
    have huIoc : u ∈ Set.Ioc q 1 := by
      simpa [Set.uIoc, hq.2] using hu
    exact distLowerQuantile_foldedInf_eq_of_gt_q (hq := hq) huIoc
  have hfi_pq :
      IntervalIntegrable (distLowerQuantile (foldedInfLaw qI)) volume (p : ℝ) q := by
    refine hleft_simple.congr ?_
    intro u hu
    have huIoc : u ∈ Set.Ioc (p : ℝ) q := by
      simpa [Set.uIoc, hqle] using hu
    symm
    exact distLowerQuantile_foldedInf_eq_of_lt_q (hq := hq)
      ⟨lt_of_le_of_lt p.2.1 huIoc.1, huIoc.2⟩
  have hfi_q1 :
      IntervalIntegrable (distLowerQuantile (foldedInfLaw qI)) volume q 1 := by
    refine hright_simple.congr ?_
    intro u hu
    have huIoc : u ∈ Set.Ioc q 1 := by
      simpa [Set.uIoc, hq.2] using hu
    symm
    exact distLowerQuantile_foldedInf_eq_of_gt_q (hq := hq) huIoc
  calc
    distESIntegral (foldedInfLaw qI) p =
        (∫ u in (p : ℝ)..q, distLowerQuantile (foldedInfLaw qI) u) +
          ∫ u in q..1, distLowerQuantile (foldedInfLaw qI) u := by
            rw [distESIntegral, ← intervalIntegral.integral_add_adjacent_intervals hfi_pq hfi_q1]
    _ = (∫ u in (p : ℝ)..q, u / 2) + ∫ u in q..1, u := by rw [hleft, hright]

theorem distESIntegral_affineUniform_one_zero_eq (p : Level) :
    distESIntegral (affineUniformLaw 1 0) p = (1 - (p : ℝ) ^ 2) / 2 := by
  have hbase : distESIntegral (affineUniformLaw 1 0) p = ∫ u in (p : ℝ)..1, u := by
    simpa using (distESIntegral_affineUniform_eq (m := 1) (c := 0) (by norm_num) p)
  rw [hbase, integral_id]
  ring

theorem distESIntegral_foldedInf_eq_sub_sq_of_lt_q {q : ℝ} (hq : q ∈ Set.Ioc (0 : ℝ) 1)
    (p : Level) (hp : (p : ℝ) < q) :
    distESIntegral (foldedInfLaw ⟨q, ⟨hq.1.le, hq.2⟩⟩) p =
      distESIntegral (affineUniformLaw 1 0) p - (q ^ 2 - (p : ℝ) ^ 2) / 4 := by
  let Δ : ℝ := (q ^ 2 - (p : ℝ) ^ 2) / 4
  let I₁ : ℝ := ∫ u in (p : ℝ)..q, u
  let I₂ : ℝ := ∫ u in q..1, u
  let I₃ : ℝ := ∫ u in (p : ℝ)..1, u
  have hid_pq : IntervalIntegrable (fun u : ℝ => u) volume (p : ℝ) q := by
    exact Continuous.intervalIntegrable continuous_id _ _
  have hid_q1 : IntervalIntegrable (fun u : ℝ => u) volume q 1 := by
    exact Continuous.intervalIntegrable continuous_id _ _
  have hleft_formula :
      ∫ u in (p : ℝ)..q, u / 2 = Δ := by
    dsimp [Δ]
    rw [intervalIntegral.integral_div, integral_id]
    ring
  have hbase :
      distESIntegral (affineUniformLaw 1 0) p = I₃ := by
    dsimp [I₃]
    simpa using (distESIntegral_affineUniform_eq (m := 1) (c := 0) (by norm_num) p)
  have hI₁ : I₁ = (q ^ 2 - (p : ℝ) ^ 2) / 2 := by
    dsimp [I₁]
    rw [integral_id]
  have hsplit_u : I₁ + I₂ = I₃ := by
    dsimp [I₁, I₂, I₃]
    rw [intervalIntegral.integral_add_adjacent_intervals hid_pq hid_q1]
  calc
    distESIntegral (foldedInfLaw ⟨q, ⟨hq.1.le, hq.2⟩⟩) p =
        (∫ u in (p : ℝ)..q, u / 2) + ∫ u in q..1, u := by
          exact distESIntegral_foldedInf_eq_split_of_lt_q hq p hp
    _ = Δ + I₂ := by
          dsimp [I₂]
          rw [hleft_formula]
    _ = I₃ - Δ := by
          rw [← hsplit_u, hI₁]
          dsimp [Δ]
          ring
    _ = distESIntegral (affineUniformLaw 1 0) p - Δ := by
          simpa using congrArg (fun x : ℝ => x - Δ) hbase.symm
    _ = distESIntegral (affineUniformLaw 1 0) p - (q ^ 2 - (p : ℝ) ^ 2) / 4 := by
          rfl

theorem distESIntegral_foldedSup_eq_add_sq_of_lt_q {q : ℝ} (hq : q ∈ Set.Ioc (0 : ℝ) 1)
    (p : Level) (hp : (p : ℝ) < q) :
    distESIntegral (foldedSupLaw ⟨q, ⟨hq.1.le, hq.2⟩⟩) p =
      distESIntegral (affineUniformLaw 1 0) p + (q - (p : ℝ)) ^ 2 / 4 := by
  let Δ : ℝ := (q - (p : ℝ)) ^ 2 / 4
  let I₁ : ℝ := ∫ u in (p : ℝ)..q, u
  let I₂ : ℝ := ∫ u in q..1, u
  let I₃ : ℝ := ∫ u in (p : ℝ)..1, u
  have hid_pq : IntervalIntegrable (fun u : ℝ => u) volume (p : ℝ) q := by
    exact Continuous.intervalIntegrable continuous_id _ _
  have hconst_pq : IntervalIntegrable (fun _ : ℝ => q) volume (p : ℝ) q := by
    simpa using
      (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => q) volume (p : ℝ) q)
  have hid_q1 : IntervalIntegrable (fun u : ℝ => u) volume q 1 := by
    exact Continuous.intervalIntegrable continuous_id _ _
  have hleft_formula :
      ∫ u in (p : ℝ)..q, (u + q) / 2 = I₁ + Δ := by
    have hI₁ : I₁ = (q ^ 2 - (p : ℝ) ^ 2) / 2 := by
      dsimp [I₁]
      rw [integral_id]
    calc
      ∫ u in (p : ℝ)..q, (u + q) / 2
          = ((q ^ 2 - (p : ℝ) ^ 2) / 2 + (q - (p : ℝ)) • q) / 2 := by
              rw [intervalIntegral.integral_div, intervalIntegral.integral_add hid_pq hconst_pq,
                intervalIntegral.integral_const, integral_id]
      _ = I₁ + Δ := by
            rw [hI₁]
            dsimp [Δ]
            ring
  have hbase :
      distESIntegral (affineUniformLaw 1 0) p = I₃ := by
    dsimp [I₃]
    simpa using (distESIntegral_affineUniform_eq (m := 1) (c := 0) (by norm_num) p)
  have hsumΔ : (I₁ + Δ) + I₂ = (I₁ + I₂) + Δ := by
    ring
  have hsplit_u : I₁ + I₂ = I₃ := by
    dsimp [I₁, I₂, I₃]
    rw [intervalIntegral.integral_add_adjacent_intervals hid_pq hid_q1]
  calc
    distESIntegral (foldedSupLaw ⟨q, ⟨hq.1.le, hq.2⟩⟩) p =
        (∫ u in (p : ℝ)..q, (u + q) / 2) + ∫ u in q..1, u := by
          exact distESIntegral_foldedSup_eq_split_of_lt_q hq p hp
    _ = (I₁ + Δ) + I₂ := by
          dsimp [I₂]
          rw [hleft_formula]
    _ = (I₁ + I₂) + Δ := hsumΔ
    _ = I₃ + Δ := by rw [hsplit_u]
    _ = distESIntegral (affineUniformLaw 1 0) p + Δ := by
          simpa using congrArg (fun x : ℝ => x + Δ) hbase.symm
    _ = distESIntegral (affineUniformLaw 1 0) p + (q - (p : ℝ)) ^ 2 / 4 := by
          rfl

theorem distES_foldedSup_eq_of_lt_q {q : ℝ} (hq : q ∈ Set.Ioc (0 : ℝ) 1)
    (p : Level) (hp : (p : ℝ) < q) :
    distES (foldedSupLaw ⟨q, ⟨hq.1.le, hq.2⟩⟩) p =
      (1 + (p : ℝ)) / 2 + (q - (p : ℝ)) ^ 2 / (4 * (1 - (p : ℝ))) := by
  have hp1 : (p : ℝ) < 1 := lt_of_lt_of_le hp hq.2
  have hne : 1 - (p : ℝ) ≠ 0 := by
    linarith
  rw [distES, dif_pos hp1, distESIntegral_foldedSup_eq_add_sq_of_lt_q hq p hp,
    distESIntegral_affineUniform_one_zero_eq]
  field_simp [hne]
  ring

theorem distES_foldedInf_eq_of_lt_q {q : ℝ} (hq : q ∈ Set.Ioc (0 : ℝ) 1)
    (p : Level) (hp : (p : ℝ) < q) :
    distES (foldedInfLaw ⟨q, ⟨hq.1.le, hq.2⟩⟩) p =
      (1 + (p : ℝ)) / 2 - (q ^ 2 - (p : ℝ) ^ 2) / (4 * (1 - (p : ℝ))) := by
  have hp1 : (p : ℝ) < 1 := lt_of_lt_of_le hp hq.2
  have hne : 1 - (p : ℝ) ≠ 0 := by
    linarith
  rw [distES, dif_pos hp1, distESIntegral_foldedInf_eq_sub_sq_of_lt_q hq p hp,
    distESIntegral_affineUniform_one_zero_eq]
  field_simp [hne]
  ring

theorem distES_foldedSup_eq_of_ge_q {q : ℝ} (hq : q ∈ Set.Ioc (0 : ℝ) 1)
    (p : Level) (hqp : q ≤ (p : ℝ)) (hp : (p : ℝ) < 1) :
    distES (foldedSupLaw ⟨q, ⟨hq.1.le, hq.2⟩⟩) p = (1 + (p : ℝ)) / 2 := by
  rw [distES, dif_pos hp, distESIntegral_foldedSup_eq_of_ge_q hq p hqp, integral_id]
  have hne : 1 - (p : ℝ) ≠ 0 := by
    linarith
  field_simp [hne]
  ring

theorem distES_foldedInf_eq_of_ge_q {q : ℝ} (hq : q ∈ Set.Ioc (0 : ℝ) 1)
    (p : Level) (hqp : q ≤ (p : ℝ)) (hp : (p : ℝ) < 1) :
    distES (foldedInfLaw ⟨q, ⟨hq.1.le, hq.2⟩⟩) p = (1 + (p : ℝ)) / 2 := by
  rw [distES, dif_pos hp, distESIntegral_foldedInf_eq_of_ge_q hq p hqp, integral_id]
  have hne : 1 - (p : ℝ) ≠ 0 := by
    linarith
  field_simp [hne]
  ring

end FoldedSupInfLaw

section AffineFoldedSupInfLaw

open unitInterval

/-- Positive affine image of the folded supremum law. -/
def affineFoldedSupLaw (q : I) (m c : ℝ) : Measure ℝ :=
  Measure.map (fun x : ℝ => m * x + c) (foldedSupLaw q)

/-- Positive affine image of the folded infimum law. -/
def affineFoldedInfLaw (q : I) (m c : ℝ) : Measure ℝ :=
  Measure.map (fun x : ℝ => m * x + c) (foldedInfLaw q)

instance affineFoldedSupLaw.instIsProbabilityMeasure (q : I) (m c : ℝ) :
    IsProbabilityMeasure (affineFoldedSupLaw q m c) :=
  Measure.isProbabilityMeasure_map (by fun_prop)

instance affineFoldedInfLaw.instIsProbabilityMeasure (q : I) (m c : ℝ) :
    IsProbabilityMeasure (affineFoldedInfLaw q m c) :=
  Measure.isProbabilityMeasure_map (by fun_prop)

theorem intervalIntegrable_distLowerQuantile_foldedSup_of_lt_q
    {q : ℝ} (hq : q ∈ Set.Ioc (0 : ℝ) 1) (p : Level) (hp : (p : ℝ) < q) :
    IntervalIntegrable
      (distLowerQuantile (foldedSupLaw ⟨q, ⟨hq.1.le, hq.2⟩⟩))
      volume (p : ℝ) 1 := by
  let qI : I := ⟨q, ⟨hq.1.le, hq.2⟩⟩
  have hfi_pq :
      IntervalIntegrable (distLowerQuantile (foldedSupLaw qI)) volume (p : ℝ) q := by
    have hcont : Continuous (fun u : ℝ => (u + q) / 2) := by
      fun_prop
    refine (hcont.intervalIntegrable _ _).congr ?_
    intro u hu
    have huIoc : u ∈ Set.Ioc (p : ℝ) q := by
      simpa [Set.uIoc, hp.le] using hu
    symm
    exact distLowerQuantile_foldedSup_eq_of_lt_q (hq := hq)
      ⟨lt_of_le_of_lt p.2.1 huIoc.1, huIoc.2⟩
  have hfi_q1 :
      IntervalIntegrable (distLowerQuantile (foldedSupLaw qI)) volume q 1 := by
    refine (Continuous.intervalIntegrable continuous_id _ _).congr ?_
    intro u hu
    have huIoc : u ∈ Set.Ioc q 1 := by
      simpa [Set.uIoc, hq.2] using hu
    symm
    exact distLowerQuantile_foldedSup_eq_of_gt_q (hq := hq) huIoc
  exact IntervalIntegrable.trans (b := q) hfi_pq hfi_q1

theorem intervalIntegrable_distLowerQuantile_foldedSup_of_ge_q
    {q : ℝ} (hq : q ∈ Set.Ioc (0 : ℝ) 1) (p : Level) (hqp : q ≤ (p : ℝ)) :
    IntervalIntegrable
      (distLowerQuantile (foldedSupLaw ⟨q, ⟨hq.1.le, hq.2⟩⟩))
      volume (p : ℝ) 1 := by
  refine (Continuous.intervalIntegrable continuous_id _ _).congr ?_
  intro u hu
  have huIoc : u ∈ Set.Ioc (p : ℝ) 1 := by
    simpa [Set.uIoc, p.2.2] using hu
  have huq : u ∈ Set.Ioc q 1 := by
    exact ⟨lt_of_le_of_lt hqp huIoc.1, huIoc.2⟩
  symm
  exact distLowerQuantile_foldedSup_eq_of_gt_q (hq := hq) huq

theorem intervalIntegrable_distLowerQuantile_foldedInf_of_ge_q
    {q : ℝ} (hq : q ∈ Set.Ioc (0 : ℝ) 1) (p : Level) (hqp : q ≤ (p : ℝ)) :
    IntervalIntegrable
      (distLowerQuantile (foldedInfLaw ⟨q, ⟨hq.1.le, hq.2⟩⟩))
      volume (p : ℝ) 1 := by
  refine (Continuous.intervalIntegrable continuous_id _ _).congr ?_
  intro u hu
  have huIoc : u ∈ Set.Ioc (p : ℝ) 1 := by
    simpa [Set.uIoc, p.2.2] using hu
  have huq : u ∈ Set.Ioc q 1 := by
    exact ⟨lt_of_le_of_lt hqp huIoc.1, huIoc.2⟩
  symm
  exact distLowerQuantile_foldedInf_eq_of_gt_q (hq := hq) huq

theorem intervalIntegrable_distLowerQuantile_foldedInf_of_lt_q
    {q : ℝ} (hq : q ∈ Set.Ioc (0 : ℝ) 1) (p : Level) (hp : (p : ℝ) < q) :
    IntervalIntegrable
      (distLowerQuantile (foldedInfLaw ⟨q, ⟨hq.1.le, hq.2⟩⟩))
      volume (p : ℝ) 1 := by
  let qI : I := ⟨q, ⟨hq.1.le, hq.2⟩⟩
  have hfi_pq :
      IntervalIntegrable (distLowerQuantile (foldedInfLaw qI)) volume (p : ℝ) q := by
    have hcont : Continuous (fun u : ℝ => u / 2) := by
      fun_prop
    refine (hcont.intervalIntegrable _ _).congr ?_
    intro u hu
    have huIoc : u ∈ Set.Ioc (p : ℝ) q := by
      simpa [Set.uIoc, hp.le] using hu
    symm
    exact distLowerQuantile_foldedInf_eq_of_lt_q (hq := hq)
      ⟨lt_of_le_of_lt p.2.1 huIoc.1, huIoc.2⟩
  have hfi_q1 :
      IntervalIntegrable (distLowerQuantile (foldedInfLaw qI)) volume q 1 := by
    refine (Continuous.intervalIntegrable continuous_id _ _).congr ?_
    intro u hu
    have huIoc : u ∈ Set.Ioc q 1 := by
      simpa [Set.uIoc, hq.2] using hu
    symm
    exact distLowerQuantile_foldedInf_eq_of_gt_q (hq := hq) huIoc
  exact IntervalIntegrable.trans (b := q) hfi_pq hfi_q1

theorem distES_affineFoldedSup_eq_of_lt_q
    {q : ℝ} (hq : q ∈ Set.Ioc (0 : ℝ) 1)
    (m c : ℝ) (hm : 0 < m) (p : Level) (hp : (p : ℝ) < q) :
    distES (affineFoldedSupLaw ⟨q, ⟨hq.1.le, hq.2⟩⟩ m c) p =
      m * ((1 + (p : ℝ)) / 2 + (q - (p : ℝ)) ^ 2 / (4 * (1 - (p : ℝ)))) + c := by
  let qI : I := ⟨q, ⟨hq.1.le, hq.2⟩⟩
  have hp1 : (p : ℝ) < 1 := lt_of_lt_of_le hp hq.2
  have hfi :
      IntervalIntegrable (distLowerQuantile (foldedSupLaw qI)) volume (p : ℝ) 1 :=
    intervalIntegrable_distLowerQuantile_foldedSup_of_lt_q hq p hp
  calc
    distES (affineFoldedSupLaw qI m c) p = m * distES (foldedSupLaw qI) p + c := by
      simpa [affineFoldedSupLaw] using
        (distES_map_affine_eq_of_lt_one_of_intervalIntegrable
          (μ := foldedSupLaw qI) (m := m) (c := c) hm p hp1 hfi)
    _ = m * ((1 + (p : ℝ)) / 2 + (q - (p : ℝ)) ^ 2 / (4 * (1 - (p : ℝ)))) + c := by
          rw [distES_foldedSup_eq_of_lt_q hq p hp]

theorem distES_affineFoldedSup_eq_of_ge_q
    {q : ℝ} (hq : q ∈ Set.Ioc (0 : ℝ) 1)
    (m c : ℝ) (hm : 0 < m) (p : Level) (hqp : q ≤ (p : ℝ)) (hp : (p : ℝ) < 1) :
    distES (affineFoldedSupLaw ⟨q, ⟨hq.1.le, hq.2⟩⟩ m c) p =
      m * ((1 + (p : ℝ)) / 2) + c := by
  let qI : I := ⟨q, ⟨hq.1.le, hq.2⟩⟩
  have hfi :
      IntervalIntegrable (distLowerQuantile (foldedSupLaw qI)) volume (p : ℝ) 1 :=
    intervalIntegrable_distLowerQuantile_foldedSup_of_ge_q hq p hqp
  calc
    distES (affineFoldedSupLaw qI m c) p = m * distES (foldedSupLaw qI) p + c := by
      simpa [affineFoldedSupLaw] using
        (distES_map_affine_eq_of_lt_one_of_intervalIntegrable
          (μ := foldedSupLaw qI) (m := m) (c := c) hm p hp hfi)
    _ = m * ((1 + (p : ℝ)) / 2) + c := by
          rw [distES_foldedSup_eq_of_ge_q hq p hqp hp]

theorem distES_affineFoldedInf_eq_of_ge_q
    {q : ℝ} (hq : q ∈ Set.Ioc (0 : ℝ) 1)
    (m c : ℝ) (hm : 0 < m) (p : Level) (hqp : q ≤ (p : ℝ)) (hp : (p : ℝ) < 1) :
    distES (affineFoldedInfLaw ⟨q, ⟨hq.1.le, hq.2⟩⟩ m c) p =
      m * ((1 + (p : ℝ)) / 2) + c := by
  let qI : I := ⟨q, ⟨hq.1.le, hq.2⟩⟩
  have hfi :
      IntervalIntegrable (distLowerQuantile (foldedInfLaw qI)) volume (p : ℝ) 1 :=
    intervalIntegrable_distLowerQuantile_foldedInf_of_ge_q hq p hqp
  calc
    distES (affineFoldedInfLaw qI m c) p = m * distES (foldedInfLaw qI) p + c := by
      simpa [affineFoldedInfLaw] using
        (distES_map_affine_eq_of_lt_one_of_intervalIntegrable
          (μ := foldedInfLaw qI) (m := m) (c := c) hm p hp hfi)
    _ = m * ((1 + (p : ℝ)) / 2) + c := by
          rw [distES_foldedInf_eq_of_ge_q hq p hqp hp]

theorem distES_affineFoldedInf_eq_of_lt_q
    {q : ℝ} (hq : q ∈ Set.Ioc (0 : ℝ) 1)
    (m c : ℝ) (hm : 0 < m) (p : Level) (hp : (p : ℝ) < q) :
    distES (affineFoldedInfLaw ⟨q, ⟨hq.1.le, hq.2⟩⟩ m c) p =
      m * ((1 + (p : ℝ)) / 2 - (q ^ 2 - (p : ℝ) ^ 2) / (4 * (1 - (p : ℝ)))) + c := by
  let qI : I := ⟨q, ⟨hq.1.le, hq.2⟩⟩
  have hp1 : (p : ℝ) < 1 := lt_of_lt_of_le hp hq.2
  have hfi :
      IntervalIntegrable (distLowerQuantile (foldedInfLaw qI)) volume (p : ℝ) 1 :=
    intervalIntegrable_distLowerQuantile_foldedInf_of_lt_q hq p hp
  calc
    distES (affineFoldedInfLaw qI m c) p = m * distES (foldedInfLaw qI) p + c := by
      simpa [affineFoldedInfLaw] using
        (distES_map_affine_eq_of_lt_one_of_intervalIntegrable
          (μ := foldedInfLaw qI) (m := m) (c := c) hm p hp1 hfi)
    _ = m * ((1 + (p : ℝ)) / 2 - (q ^ 2 - (p : ℝ) ^ 2) / (4 * (1 - (p : ℝ)))) + c := by
          rw [distES_foldedInf_eq_of_lt_q hq p hp]

theorem distES_tangentWitness_eq_of_lt_one
    {a b : ℝ} (ha : 0 < a) (p : Level) (hp : (p : ℝ) < 1) :
    distES (affineUniformLaw (2 * a) (b - a)) p = a * (p : ℝ) + b := by
  have h2a : 0 < 2 * a := by nlinarith
  rw [distES_affineUniform_eq_of_lt_one (m := 2 * a) (c := b - a) h2a p hp]
  ring

theorem distES_foldedTangentSup_eq_of_lt_q
    {q a b : ℝ} (hq : q ∈ Set.Ioc (0 : ℝ) 1) (ha : 0 < a)
    (p : Level) (hp : (p : ℝ) < q) :
    distES (affineFoldedSupLaw ⟨q, ⟨hq.1.le, hq.2⟩⟩ (2 * a) (b - a)) p =
      a * (p : ℝ) + b + a * (q - (p : ℝ)) ^ 2 / (2 * (1 - (p : ℝ))) := by
  have h2a : 0 < 2 * a := by nlinarith
  have hp1 : (p : ℝ) < 1 := lt_of_lt_of_le hp hq.2
  have hne : 1 - (p : ℝ) ≠ 0 := by
    linarith
  rw [distES_affineFoldedSup_eq_of_lt_q hq (2 * a) (b - a) h2a p hp]
  field_simp [hne]
  ring

theorem distES_foldedTangentSup_eq_of_ge_q
    {q a b : ℝ} (hq : q ∈ Set.Ioc (0 : ℝ) 1) (ha : 0 < a)
    (p : Level) (hqp : q ≤ (p : ℝ)) (hp : (p : ℝ) < 1) :
    distES (affineFoldedSupLaw ⟨q, ⟨hq.1.le, hq.2⟩⟩ (2 * a) (b - a)) p =
      a * (p : ℝ) + b := by
  have h2a : 0 < 2 * a := by nlinarith
  rw [distES_affineFoldedSup_eq_of_ge_q hq (2 * a) (b - a) h2a p hqp hp]
  ring

theorem distES_foldedTangentInf_eq_of_ge_q
    {q a b : ℝ} (hq : q ∈ Set.Ioc (0 : ℝ) 1) (ha : 0 < a)
    (p : Level) (hqp : q ≤ (p : ℝ)) (hp : (p : ℝ) < 1) :
    distES (affineFoldedInfLaw ⟨q, ⟨hq.1.le, hq.2⟩⟩ (2 * a) (b - a)) p =
      a * (p : ℝ) + b := by
  have h2a : 0 < 2 * a := by nlinarith
  rw [distES_affineFoldedInf_eq_of_ge_q hq (2 * a) (b - a) h2a p hqp hp]
  ring

theorem distES_foldedTangentInf_eq_of_lt_q
    {q a b : ℝ} (hq : q ∈ Set.Ioc (0 : ℝ) 1) (ha : 0 < a)
    (p : Level) (hp : (p : ℝ) < q) :
    distES (affineFoldedInfLaw ⟨q, ⟨hq.1.le, hq.2⟩⟩ (2 * a) (b - a)) p =
      a * (p : ℝ) + b - a * (q ^ 2 - (p : ℝ) ^ 2) / (2 * (1 - (p : ℝ))) := by
  have h2a : 0 < 2 * a := by nlinarith
  have hp1 : (p : ℝ) < 1 := lt_of_lt_of_le hp hq.2
  have hne : 1 - (p : ℝ) ≠ 0 := by
    linarith
  rw [distES_affineFoldedInf_eq_of_lt_q hq (2 * a) (b - a) h2a p hp]
  field_simp [hne]
  ring

end AffineFoldedSupInfLaw

section DistributionAESWitness

open unitInterval

@[simp] theorem affineSupportLine_eq_linear (g : Level → ℝ) (q p : Level) (a : ℝ) :
    affineSupportLine g q a p = a * (p : ℝ) + (g q - a * (q : ℝ)) := by
  rw [affineSupportLine]
  ring

theorem distUpperQuantile_le_of_ae_le_const (μ : Measure ℝ) [IsProbabilityMeasure μ] {c : ℝ}
    (hμ : ∀ᵐ x ∂μ, x ≤ c) :
    distUpperQuantile μ ≤ c := by
  unfold distUpperQuantile
  rw [essSup_eq_sInf]
  let S : Set ℝ := {a : ℝ | μ (Set.Ioi a) = 0}
  refine csInf_le ?_ ?_
  · change BddBelow S
    refine ⟨distLowerQuantile μ (1 / 2 : ℝ), ?_⟩
    intro b hb
    have hbIoi : μ (Set.Ioi b) = 0 := by
      simpa [S] using hb
    have hbIic : μ (Set.Iic b) = 1 := by
      rw [← prob_compl_eq_zero_iff (μ := μ) (s := Set.Iic b) measurableSet_Iic, Set.compl_Iic]
      simpa using hbIoi
    have hbmem : (1 / 2 : ℝ) ≤ ProbabilityTheory.cdf μ b := by
      rw [ProbabilityTheory.cdf_eq_real]
      have hhalf : (1 / 2 : ℝ) ≤ 1 := by norm_num
      simpa [Measure.real_def, hbIic] using hhalf
    unfold distLowerQuantile
    exact csInf_le (upperLevelSet_bddBelow μ (by norm_num : (0 : ℝ) < 1 / 2)) hbmem
  · change μ (Set.Ioi c) = 0
    simpa [ae_iff, not_le] using hμ

theorem distES_affineUniform_le_at_one (m c : ℝ) (hm : 0 ≤ m) :
    distES (affineUniformLaw m c) 1 ≤ m + c := by
  simp [distES]
  refine distUpperQuantile_le_of_ae_le_const (μ := affineUniformLaw m c) ?_
  rw [affineUniformLaw]
  exact
    (ae_map_iff (by fun_prop : AEMeasurable (fun u : I => m * (u : ℝ) + c) (volume : Measure I))
      (measurableSet_le measurable_id measurable_const)).2 <|
      Filter.Eventually.of_forall fun u => by
        have hu1 : (u : ℝ) ≤ 1 := u.2.2
        have hmul : m * (u : ℝ) ≤ m * (1 : ℝ) := mul_le_mul_of_nonneg_left hu1 hm
        simpa using add_le_add_right hmul c

theorem distES_foldedAffine_le_at_one (q : I) (m c : ℝ) (hm : 0 ≤ m) :
    distES (foldedAffineLaw q m c) 1 ≤ m + c := by
  simpa [foldedAffineLaw_eq_affineUniformLaw q m c] using
    (distES_affineUniform_le_at_one m c hm)

theorem distES_affineFoldedSup_le_at_one (q : I) (m c : ℝ) (hm : 0 ≤ m) :
    distES (affineFoldedSupLaw q m c) 1 ≤ m + c := by
  simp [distES]
  have hmap :
      affineFoldedSupLaw q m c =
        Measure.map (fun u : I => m * supCoord q u + c) (volume : Measure I) := by
    simpa [affineFoldedSupLaw, foldedSupLaw, Function.comp] using
      (Measure.map_map (μ := (volume : Measure I)) (f := supCoord q)
        (g := fun x : ℝ => m * x + c) (by fun_prop) (measurable_supCoord q))
  have hae :
      ∀ᵐ x ∂ Measure.map (fun u : I => m * supCoord q u + c) (volume : Measure I), x ≤ m + c :=
    (ae_map_iff (by fun_prop : AEMeasurable (fun u : I => m * supCoord q u + c) (volume : Measure I))
      (measurableSet_le measurable_id measurable_const)).2 <|
      Filter.Eventually.of_forall fun u => by
        have hu1 : supCoord q u ≤ 1 := by
          dsimp [supCoord]
          exact max_le_iff.mpr ⟨u.2.2, (foldMap q u).2.2⟩
        have hmul : m * supCoord q u ≤ m * (1 : ℝ) := mul_le_mul_of_nonneg_left hu1 hm
        simpa using add_le_add_right hmul c
  haveI :
      IsProbabilityMeasure (Measure.map (fun u : I => m * supCoord q u + c) (volume : Measure I)) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  simpa [distES, hmap] using
    (distUpperQuantile_le_of_ae_le_const
      (μ := Measure.map (fun u : I => m * supCoord q u + c) (volume : Measure I)) hae)

theorem distES_affineFoldedInf_le_at_one (q : I) (m c : ℝ) (hm : 0 ≤ m) :
    distES (affineFoldedInfLaw q m c) 1 ≤ m + c := by
  simp [distES]
  have hmap :
      affineFoldedInfLaw q m c =
        Measure.map (fun u : I => m * infCoord q u + c) (volume : Measure I) := by
    simpa [affineFoldedInfLaw, foldedInfLaw, Function.comp] using
      (Measure.map_map (μ := (volume : Measure I)) (f := infCoord q)
        (g := fun x : ℝ => m * x + c) (by fun_prop) (measurable_infCoord q))
  have hae :
      ∀ᵐ x ∂ Measure.map (fun u : I => m * infCoord q u + c) (volume : Measure I), x ≤ m + c :=
    (ae_map_iff (by fun_prop : AEMeasurable (fun u : I => m * infCoord q u + c) (volume : Measure I))
      (measurableSet_le measurable_id measurable_const)).2 <|
      Filter.Eventually.of_forall fun u => by
        have hu1 : infCoord q u ≤ 1 := by
          dsimp [infCoord]
          exact le_trans (min_le_left _ _) u.2.2
        have hmul : m * infCoord q u ≤ m * (1 : ℝ) := mul_le_mul_of_nonneg_left hu1 hm
        simpa using add_le_add_right hmul c
  haveI :
      IsProbabilityMeasure (Measure.map (fun u : I => m * infCoord q u + c) (volume : Measure I)) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  simpa [distES, hmap] using
    (distUpperQuantile_le_of_ae_le_const
      (μ := Measure.map (fun u : I => m * infCoord q u + c) (volume : Measure I)) hae)

theorem distAES_tangentWitness_le_zero_of_affineSupportLine
    {g : Level → ℝ} {q : Level} {a : ℝ} (ha : 0 < a)
    (hline : ∀ p : Level, affineSupportLine g q a p ≤ g p) :
    distAES (affineUniformLaw (2 * a) (g q - a * (q : ℝ) - a)) g ≤ 0 := by
  let b : ℝ := g q - a * (q : ℝ)
  unfold distAES distESg
  refine csSup_le ?_ ?_
  · exact Set.range_nonempty _
  · rintro _ ⟨p, rfl⟩
    by_cases hp : (p : ℝ) < 1
    · have hES :
          distES (affineUniformLaw (2 * a) (b - a)) p = a * (p : ℝ) + b :=
        distES_tangentWitness_eq_of_lt_one (ha := ha) (b := b) p hp
      have hES' :
          distES (affineUniformLaw (2 * a) (g q - a * (q : ℝ) - a)) p = a * (p : ℝ) + b := by
        simpa [b] using hES
      have hlinep := hline p
      have hlinep' : a * (p : ℝ) + b ≤ g p := by
        dsimp [b]
        have hlinep'' : g q + a * ((p : ℝ) - (q : ℝ)) ≤ g p := by
          simpa [affineSupportLine] using hlinep
        linarith
      have hterm : distES (affineUniformLaw (2 * a) (g q - a * (q : ℝ) - a)) p ≤ g p := by
        rw [hES']
        exact hlinep'
      linarith
    · have hp1 : p = 1 := by
        apply Subtype.ext
        have hpge : (1 : ℝ) ≤ p := by linarith
        exact le_antisymm p.2.2 hpge
      subst hp1
      have hend :
          distES (affineUniformLaw (2 * a) (g q - a * (q : ℝ) - a)) (1 : Level) ≤
            affineSupportLine g q a 1 := by
        have hraw :
            distES (affineUniformLaw (2 * a) (g q - a * (q : ℝ) - a)) (1 : Level) ≤
              (2 * a) + (g q - a * (q : ℝ) - a) :=
          distES_affineUniform_le_at_one (2 * a) (g q - a * (q : ℝ) - a) (by nlinarith [ha])
        have : (2 * a) + (g q - a * (q : ℝ) - a) = affineSupportLine g q a 1 := by
          simp [affineSupportLine]
          ring
        exact hraw.trans_eq this
      exact sub_nonpos.mpr (le_trans hend (hline 1))

theorem distAES_foldedTangentWitness_le_zero_of_affineSupportLine
    {g : Level → ℝ} {q : Level} {a : ℝ} (ha : 0 < a)
    (hline : ∀ p : Level, affineSupportLine g q a p ≤ g p) :
    distAES (foldedAffineLaw q (2 * a) (g q - a * (q : ℝ) - a)) g ≤ 0 := by
  simpa [foldedAffineLaw_eq_affineUniformLaw q (2 * a) (g q - a * (q : ℝ) - a)] using
    (distAES_tangentWitness_le_zero_of_affineSupportLine (g := g) (q := q) (a := a) ha hline)

theorem distAES_foldedTangentInf_ge_zero
    {g : Level → ℝ} {q : Level} {a : ℝ} (hq0 : 0 < (q : ℝ)) (hq : (q : ℝ) < 1) (ha : 0 < a)
    (hgnonneg : ∀ p : Level, 0 ≤ g p) :
    0 ≤ distAES (affineFoldedInfLaw q (2 * a) (g q - a * (q : ℝ) - a)) g := by
  let b : ℝ := g q - a * (q : ℝ)
  have hqIoc : (q : ℝ) ∈ Set.Ioc (0 : ℝ) 1 := ⟨hq0, hq.le⟩
  unfold distAES distESg
  refine le_csSup ?_ ?_
  · refine ⟨a + g q, ?_⟩
    rintro _ ⟨p, rfl⟩
    have hgp : 0 ≤ g p := hgnonneg p
    by_cases hp1 : (p : ℝ) < 1
    · by_cases hpq : (p : ℝ) < q
      · have hES :
            distES (affineFoldedInfLaw q (2 * a) (b - a)) p =
              a * (p : ℝ) + b - a * (q ^ 2 - (p : ℝ) ^ 2) / (2 * (1 - (p : ℝ))) :=
          distES_foldedTangentInf_eq_of_lt_q (q := (q : ℝ)) (hq := hqIoc) (ha := ha) p hpq
        have hES' :
            distES (affineFoldedInfLaw q (2 * a) (g q - a * (q : ℝ) - a)) p =
              a * (p : ℝ) + b - a * (q ^ 2 - (p : ℝ) ^ 2) / (2 * (1 - (p : ℝ))) := by
          simpa [b] using hES
        have hsub :
            0 ≤ a * (q ^ 2 - (p : ℝ) ^ 2) / (2 * (1 - (p : ℝ))) := by
          have hpqabs : 0 ≤ q ^ 2 - (p : ℝ) ^ 2 := by
            nlinarith [hpq.le, q.2.1, p.2.1]
          have hpden : 0 < 2 * (1 - (p : ℝ)) := by
            nlinarith
          exact div_nonneg (mul_nonneg ha.le hpqabs) hpden.le
        have hpp : (p : ℝ) ≤ 1 := p.2.2
        have hterm :
            distES (affineFoldedInfLaw q (2 * a) (g q - a * (q : ℝ) - a)) p ≤ a + g q := by
          rw [hES']
          have hbase : a * (p : ℝ) + b ≤ a + g q := by
            dsimp [b]
            have hpa : a * (p : ℝ) ≤ a := by
              nlinarith [ha, p.2.2]
            have hqa : -(a * (q : ℝ)) ≤ 0 := by
              nlinarith [ha, q.2.1]
            linarith
          linarith
        linarith
      · have hqp : q ≤ (p : ℝ) := not_lt.mp hpq
        have hES :
            distES (affineFoldedInfLaw q (2 * a) (b - a)) p = a * (p : ℝ) + b :=
          distES_foldedTangentInf_eq_of_ge_q (q := (q : ℝ)) (hq := hqIoc) (ha := ha) p hqp hp1
        have hES' :
            distES (affineFoldedInfLaw q (2 * a) (g q - a * (q : ℝ) - a)) p =
              a * (p : ℝ) + b := by
          simpa [b] using hES
        have hpp : (p : ℝ) ≤ 1 := p.2.2
        have hterm :
            distES (affineFoldedInfLaw q (2 * a) (g q - a * (q : ℝ) - a)) p ≤ a + g q := by
          rw [hES']
          have hbase : a * (p : ℝ) + b ≤ a + g q := by
            dsimp [b]
            have hpa : a * (p : ℝ) ≤ a := by
              nlinarith [ha, p.2.2]
            have hqa : -(a * (q : ℝ)) ≤ 0 := by
              nlinarith [ha, q.2.1]
            linarith
          linarith
        linarith
    · have hp1eq : p = 1 := by
        apply Subtype.ext
        have hpge : (1 : ℝ) ≤ p := by linarith
        exact le_antisymm p.2.2 hpge
      subst hp1eq
      have hend :
          distES (affineFoldedInfLaw q (2 * a) (g q - a * (q : ℝ) - a)) (1 : Level) ≤ a + g q := by
        have hraw :
            distES (affineFoldedInfLaw q (2 * a) (g q - a * (q : ℝ) - a)) (1 : Level) ≤
              (2 * a) + (g q - a * (q : ℝ) - a) :=
          distES_affineFoldedInf_le_at_one (q := q) (m := 2 * a) (c := g q - a * (q : ℝ) - a)
            (show 0 ≤ 2 * a by nlinarith [ha])
        have : (2 * a) + (g q - a * (q : ℝ) - a) ≤ a + g q := by
          have hq0' : 0 ≤ (q : ℝ) := q.2.1
          nlinarith
        exact hraw.trans this
      linarith
  · refine ⟨q, ?_⟩
    have hqle : (q : ℝ) ≤ q := le_rfl
    have hqval :
        distES (affineFoldedInfLaw q (2 * a) (b - a)) q =
          a * (q : ℝ) + b := by
      exact distES_foldedTangentInf_eq_of_ge_q (q := (q : ℝ)) (hq := hqIoc) (ha := ha) q hqle hq
    have hqval' :
        distES (affineFoldedInfLaw q (2 * a) (g q - a * (q : ℝ) - a)) q =
          a * (q : ℝ) + b := by
      simpa [b] using hqval
    have hterm :
        distES (affineFoldedInfLaw q (2 * a) (g q - a * (q : ℝ) - a)) q - g q = 0 := by
      rw [hqval']
      simp [b]
    linarith

theorem distAES_foldedTangentSup_pos_of_levelGap
    {g : Level → ℝ} {q p : Level} {a : ℝ}
    (hq0 : 0 < (q : ℝ)) (hq : (q : ℝ) < 1) (ha : 0 < a)
    (hgnonneg : ∀ r : Level, 0 ≤ g r)
    (hpq : (p : ℝ) < (q : ℝ))
    (hgap :
      g p < affineSupportLine g q a p +
        a * ((q : ℝ) - (p : ℝ)) ^ 2 / (2 * (1 - (p : ℝ)))) :
    0 < distAES (affineFoldedSupLaw q (2 * a) (g q - a * (q : ℝ) - a)) g := by
  let b : ℝ := g q - a * (q : ℝ)
  have hqIoc : (q : ℝ) ∈ Set.Ioc (0 : ℝ) 1 := ⟨hq0, hq.le⟩
  have hBdd :
      BddAbove
        (Set.range fun r : Level =>
          distES (affineFoldedSupLaw q (2 * a) (g q - a * (q : ℝ) - a)) r - g r) := by
    refine ⟨(3 * a) / 2 + b, ?_⟩
    rintro _ ⟨r, rfl⟩
    have hgr : 0 ≤ g r := hgnonneg r
    by_cases hr1 : (r : ℝ) < 1
    · by_cases hrq : (r : ℝ) < (q : ℝ)
      · have hES :
            distES (affineFoldedSupLaw q (2 * a) (g q - a * (q : ℝ) - a)) r =
              a * (r : ℝ) + b + a * ((q : ℝ) - (r : ℝ)) ^ 2 / (2 * (1 - (r : ℝ))) := by
          simpa [b] using
            (distES_foldedTangentSup_eq_of_lt_q (q := (q : ℝ)) (hq := hqIoc) (ha := ha) r hrq)
        have hcorr :
            a * ((q : ℝ) - (r : ℝ)) ^ 2 / (2 * (1 - (r : ℝ))) ≤ a / 2 := by
          have hsquare : ((q : ℝ) - (r : ℝ)) ^ 2 ≤ 1 - (r : ℝ) := by
            have hqr_nonneg : 0 ≤ (q : ℝ) - (r : ℝ) := by linarith
            have hqr_le_one : (q : ℝ) - (r : ℝ) ≤ 1 := by nlinarith [q.2.2, r.2.1]
            have hsq_le : ((q : ℝ) - (r : ℝ)) ^ 2 ≤ (q : ℝ) - (r : ℝ) := by
              nlinarith
            have hq_le_one : (q : ℝ) - (r : ℝ) ≤ 1 - (r : ℝ) := by
              nlinarith [q.2.2]
            exact hsq_le.trans hq_le_one
          have hden_pos : 0 < 2 * (1 - (r : ℝ)) := by
            nlinarith
          apply (div_le_iff₀ hden_pos).2
          nlinarith [hsquare, ha]
        have hbase : a * (r : ℝ) + b ≤ a + b := by
          nlinarith [ha, r.2.2]
        change distES (affineFoldedSupLaw q (2 * a) (g q - a * (q : ℝ) - a)) r - g r ≤
          (3 * a) / 2 + b
        rw [hES]
        linarith
      · have hqr : (q : ℝ) ≤ (r : ℝ) := not_lt.mp hrq
        have hES :
            distES (affineFoldedSupLaw q (2 * a) (g q - a * (q : ℝ) - a)) r =
              a * (r : ℝ) + b := by
          simpa [b] using
            (distES_foldedTangentSup_eq_of_ge_q (q := (q : ℝ)) (hq := hqIoc) (ha := ha) r hqr hr1)
        have hbase : a * (r : ℝ) + b ≤ a + b := by
          nlinarith [ha, r.2.2]
        change distES (affineFoldedSupLaw q (2 * a) (g q - a * (q : ℝ) - a)) r - g r ≤
          (3 * a) / 2 + b
        rw [hES]
        linarith
    · have hr1eq : r = 1 := by
        apply Subtype.ext
        have hrge : (1 : ℝ) ≤ r := by linarith
        exact le_antisymm r.2.2 hrge
      subst hr1eq
      have hend :
          distES (affineFoldedSupLaw q (2 * a) (g q - a * (q : ℝ) - a)) (1 : Level) ≤ a + b := by
        have hraw :
            distES (affineFoldedSupLaw q (2 * a) (g q - a * (q : ℝ) - a)) (1 : Level) ≤
              (2 * a) + (g q - a * (q : ℝ) - a) :=
          distES_affineFoldedSup_le_at_one
            (q := q) (m := 2 * a) (c := g q - a * (q : ℝ) - a)
            (show 0 ≤ 2 * a by nlinarith [ha])
        have hrewrite : (2 * a) + (g q - a * (q : ℝ) - a) = a + b := by
          simp [b]
          ring
        exact hraw.trans_eq hrewrite
      linarith
  have hwitness :
      distES (affineFoldedSupLaw q (2 * a) (g q - a * (q : ℝ) - a)) p - g p ≤
        distAES (affineFoldedSupLaw q (2 * a) (g q - a * (q : ℝ) - a)) g := by
    unfold distAES distESg
    exact le_csSup hBdd ⟨p, rfl⟩
  have hESp :
      distES (affineFoldedSupLaw q (2 * a) (g q - a * (q : ℝ) - a)) p =
        affineSupportLine g q a p +
          a * ((q : ℝ) - (p : ℝ)) ^ 2 / (2 * (1 - (p : ℝ))) := by
    have hraw :
        distES (affineFoldedSupLaw q (2 * a) (g q - a * (q : ℝ) - a)) p =
          a * (p : ℝ) + b + a * ((q : ℝ) - (p : ℝ)) ^ 2 / (2 * (1 - (p : ℝ))) := by
      simpa [b] using
        (distES_foldedTangentSup_eq_of_lt_q (q := (q : ℝ)) (hq := hqIoc) (ha := ha) p hpq)
    rw [hraw, affineSupportLine_eq_linear]
  have hpos :
      0 <
        distES (affineFoldedSupLaw q (2 * a) (g q - a * (q : ℝ) - a)) p - g p := by
    rw [hESp]
    linarith
  exact lt_of_lt_of_le hpos hwitness

end DistributionAESWitness

section Contradiction

variable {Ω : Type*} [MeasurableSpace Ω]
variable (P : Measure Ω)

/-- A strict witness gap on a concrete pair contradicts submodularity. -/
theorem not_submodular_of_witness_bounds {ρ : RandomVariable P → ℝ} {X Y : RandomVariable P}
    {xUpper yUpper infLower supLower : ℝ}
    (hX : ρ X ≤ xUpper) (hY : ρ Y ≤ yUpper)
    (hInf : infLower ≤ ρ (X ⊓ Y)) (hSup : supLower ≤ ρ (X ⊔ Y))
    (hgap : xUpper + yUpper < infLower + supLower) :
    ¬ Submodular ρ := by
  intro hsub
  have hsubXY := hsub X Y
  linarith

variable [IsProbabilityMeasure P]

/-- AES-specific contradiction wrapper phrased directly in terms of witness bounds. -/
theorem not_submodular_AES_of_witness_bounds
    {g : Level → ℝ} {X Y : RandomVariable P}
    {xUpper yUpper infLower supLower : ℝ}
    (hX : AES P g X ≤ xUpper) (hY : AES P g Y ≤ yUpper)
    (hInf : infLower ≤ AES P g (X ⊓ Y)) (hSup : supLower ≤ AES P g (X ⊔ Y))
    (hgap : xUpper + yUpper < infLower + supLower) :
    ¬ Submodular (AES P g) := by
  exact not_submodular_of_witness_bounds (P := P) hX hY hInf hSup hgap

end Contradiction

section StandardUnitIntervalWitness

open unitInterval

/-- The affine tangent witness `X(u) = 2 a u + g(q) - a q - a` on the standard unit interval
probability space. -/
def tangentWitnessXRV (q : I) (a : ℝ) (g : Level → ℝ) :
    RandomVariable (volume : Measure I) :=
  ⟨fun u : I => (2 * a) * (u : ℝ) + (g q - a * (q : ℝ) - a), by fun_prop⟩

/-- The folded affine tangent witness `Y`. -/
def tangentWitnessYRV (q : I) (a : ℝ) (g : Level → ℝ) :
    RandomVariable (volume : Measure I) :=
  ⟨fun u : I => (2 * a) * (((foldMap q u : I) : ℝ)) + (g q - a * (q : ℝ) - a), by fun_prop⟩

/-- The pointwise maximum witness written directly through `supCoord`. -/
def tangentWitnessSupRV (q : I) (a : ℝ) (g : Level → ℝ) :
    RandomVariable (volume : Measure I) :=
  ⟨fun u : I => (2 * a) * supCoord q u + (g q - a * (q : ℝ) - a), by fun_prop⟩

/-- The pointwise minimum witness written directly through `infCoord`. -/
def tangentWitnessInfRV (q : I) (a : ℝ) (g : Level → ℝ) :
    RandomVariable (volume : Measure I) :=
  ⟨fun u : I => (2 * a) * infCoord q u + (g q - a * (q : ℝ) - a), by fun_prop⟩

@[simp] theorem law_tangentWitnessXRV (q : I) (a : ℝ) (g : Level → ℝ) :
    law (volume : Measure I) (tangentWitnessXRV q a g) =
      affineUniformLaw (2 * a) (g q - a * (q : ℝ) - a) := by
  rfl

@[simp] theorem law_tangentWitnessYRV (q : I) (a : ℝ) (g : Level → ℝ) :
    law (volume : Measure I) (tangentWitnessYRV q a g) =
      foldedAffineLaw q (2 * a) (g q - a * (q : ℝ) - a) := by
  rfl

@[simp] theorem law_tangentWitnessSupRV (q : I) (a : ℝ) (g : Level → ℝ) :
    law (volume : Measure I) (tangentWitnessSupRV q a g) =
      affineFoldedSupLaw q (2 * a) (g q - a * (q : ℝ) - a) := by
  simpa [law, tangentWitnessSupRV, affineFoldedSupLaw, foldedSupLaw, Function.comp] using
    (Measure.map_map (μ := (volume : Measure I)) (f := supCoord q)
      (g := fun x : ℝ => (2 * a) * x + (g q - a * (q : ℝ) - a))
      (by fun_prop) (measurable_supCoord q)).symm

@[simp] theorem law_tangentWitnessInfRV (q : I) (a : ℝ) (g : Level → ℝ) :
    law (volume : Measure I) (tangentWitnessInfRV q a g) =
      affineFoldedInfLaw q (2 * a) (g q - a * (q : ℝ) - a) := by
  simpa [law, tangentWitnessInfRV, affineFoldedInfLaw, foldedInfLaw, Function.comp] using
    (Measure.map_map (μ := (volume : Measure I)) (f := infCoord q)
      (g := fun x : ℝ => (2 * a) * x + (g q - a * (q : ℝ) - a))
      (by fun_prop) (measurable_infCoord q)).symm

theorem tangentWitness_sup_eq (q : I) {a : ℝ} (ha : 0 < a) (g : Level → ℝ) :
    tangentWitnessXRV q a g ⊔ tangentWitnessYRV q a g = tangentWitnessSupRV q a g := by
  ext u
  have h2a : 0 ≤ 2 * a := by nlinarith [ha]
  change max ((2 * a) * (u : ℝ) + (g q - a * (q : ℝ) - a))
      ((2 * a) * (((foldMap q u : I) : ℝ)) + (g q - a * (q : ℝ) - a)) =
    (2 * a) * supCoord q u + (g q - a * (q : ℝ) - a)
  rw [max_add_add_right, ← mul_max_of_nonneg (u : ℝ) (((foldMap q u : I) : ℝ)) h2a]
  rfl

theorem tangentWitness_inf_eq (q : I) {a : ℝ} (ha : 0 < a) (g : Level → ℝ) :
    tangentWitnessXRV q a g ⊓ tangentWitnessYRV q a g = tangentWitnessInfRV q a g := by
  ext u
  have h2a : 0 ≤ 2 * a := by nlinarith [ha]
  change min ((2 * a) * (u : ℝ) + (g q - a * (q : ℝ) - a))
      ((2 * a) * (((foldMap q u : I) : ℝ)) + (g q - a * (q : ℝ) - a)) =
    (2 * a) * infCoord q u + (g q - a * (q : ℝ) - a)
  rw [min_add_add_right, ← mul_min_of_nonneg (u : ℝ) (((foldMap q u : I) : ℝ)) h2a]
  rfl

/-- On the standard unit interval probability space, the folded tangent witness already contradicts
submodularity once a supporting line and one strict folded-sup gap are available. -/
theorem not_submodular_AES_standardUnitInterval_of_foldedTangentWitness
    {g : Level → ℝ} {q p : Level} {a : ℝ}
    (hq0 : 0 < (q : ℝ)) (hq : (q : ℝ) < 1) (ha : 0 < a)
    (hgnonneg : ∀ r : Level, 0 ≤ g r)
    (hline : ∀ r : Level, affineSupportLine g q a r ≤ g r)
    (hpq : (p : ℝ) < (q : ℝ))
    (hgap :
      g p < affineSupportLine g q a p +
        a * ((q : ℝ) - (p : ℝ)) ^ 2 / (2 * (1 - (p : ℝ)))) :
    ¬ Submodular (AES (volume : Measure I) g) := by
  let X : RandomVariable (volume : Measure I) := tangentWitnessXRV q a g
  let Y : RandomVariable (volume : Measure I) := tangentWitnessYRV q a g
  have hX : AES (volume : Measure I) g X ≤ 0 := by
    simpa [X, AES, ESg, law, tangentWitnessXRV] using
      (distAES_tangentWitness_le_zero_of_affineSupportLine (g := g) (q := q) (a := a) ha hline)
  have hY : AES (volume : Measure I) g Y ≤ 0 := by
    simpa [Y, AES, ESg, law, tangentWitnessYRV] using
      (distAES_foldedTangentWitness_le_zero_of_affineSupportLine
        (g := g) (q := q) (a := a) ha hline)
  have hInf : 0 ≤ AES (volume : Measure I) g (X ⊓ Y) := by
    have hEqInf : X ⊓ Y = tangentWitnessInfRV q a g := by
      change tangentWitnessXRV q a g ⊓ tangentWitnessYRV q a g = tangentWitnessInfRV q a g
      exact tangentWitness_inf_eq (q := q) (a := a) ha g
    rw [hEqInf]
    change 0 ≤ distAES (law (volume : Measure I) (tangentWitnessInfRV q a g)) g
    simpa [law_tangentWitnessInfRV (q := q) (a := a) (g := g)] using
      (distAES_foldedTangentInf_ge_zero (g := g) (q := q) (a := a) hq0 hq ha hgnonneg)
  have hSupPos : 0 < AES (volume : Measure I) g (X ⊔ Y) := by
    have hEqSup : X ⊔ Y = tangentWitnessSupRV q a g := by
      change tangentWitnessXRV q a g ⊔ tangentWitnessYRV q a g = tangentWitnessSupRV q a g
      exact tangentWitness_sup_eq (q := q) (a := a) ha g
    rw [hEqSup]
    change 0 < distAES (law (volume : Measure I) (tangentWitnessSupRV q a g)) g
    simpa [law_tangentWitnessSupRV (q := q) (a := a) (g := g)] using
      (distAES_foldedTangentSup_pos_of_levelGap
        (g := g) (q := q) (p := p) (a := a) hq0 hq ha hgnonneg hpq hgap)
  exact not_submodular_AES_of_witness_bounds
    (P := (volume : Measure I)) (g := g) (X := X) (Y := Y)
    (xUpper := 0) (yUpper := 0) (infLower := 0)
    (supLower := AES (volume : Measure I) g (X ⊔ Y))
    hX hY hInf le_rfl (by linarith)

end StandardUnitIntervalWitness

section UniformCoordinateWitness

open unitInterval

variable {Ω : Type*} [MeasurableSpace Ω]
variable (P : Measure Ω) [IsProbabilityMeasure P]

/-- Tangent witness driven by a measurable uniform coordinate `U : Ω → I`. -/
def tangentWitnessXOfCoord (U : Ω → I) (hU : Measurable U)
    (q : I) (a : ℝ) (g : Level → ℝ) : RandomVariable P :=
  ⟨fun ω => (2 * a) * ((U ω : I) : ℝ) + (g q - a * (q : ℝ) - a), by
    have hmeas :
        Measurable fun ω => (2 * a) * ((U ω : I) : ℝ) + (g q - a * (q : ℝ) - a) := by
      fun_prop
    exact hmeas.aemeasurable⟩

/-- Folded tangent witness driven by a measurable uniform coordinate `U : Ω → I`. -/
def tangentWitnessYOfCoord (U : Ω → I) (hU : Measurable U)
    (q : I) (a : ℝ) (g : Level → ℝ) : RandomVariable P :=
  ⟨fun ω => (2 * a) * (((foldMap q (U ω) : I) : ℝ)) + (g q - a * (q : ℝ) - a), by
    have hmeas :
        Measurable fun ω =>
          (2 * a) * (((foldMap q (U ω) : I) : ℝ)) + (g q - a * (q : ℝ) - a) := by
      fun_prop
    exact hmeas.aemeasurable⟩

/-- Pointwise maximum witness written through `supCoord` and an ambient uniform coordinate. -/
def tangentWitnessSupOfCoord (U : Ω → I) (hU : Measurable U)
    (q : I) (a : ℝ) (g : Level → ℝ) : RandomVariable P :=
  ⟨fun ω => (2 * a) * supCoord q (U ω) + (g q - a * (q : ℝ) - a), by
    have hmeas :
        Measurable fun ω => (2 * a) * supCoord q (U ω) + (g q - a * (q : ℝ) - a) := by
      fun_prop
    exact hmeas.aemeasurable⟩

/-- Pointwise minimum witness written through `infCoord` and an ambient uniform coordinate. -/
def tangentWitnessInfOfCoord (U : Ω → I) (hU : Measurable U)
    (q : I) (a : ℝ) (g : Level → ℝ) : RandomVariable P :=
  ⟨fun ω => (2 * a) * infCoord q (U ω) + (g q - a * (q : ℝ) - a), by
    have hmeas :
        Measurable fun ω => (2 * a) * infCoord q (U ω) + (g q - a * (q : ℝ) - a) := by
      fun_prop
    exact hmeas.aemeasurable⟩

@[simp] theorem law_tangentWitnessXOfCoord
    (U : Ω → I) (hU : Measurable U) (hlawU : Measure.map U P = (volume : Measure I))
    (q : I) (a : ℝ) (g : Level → ℝ) :
    law P (tangentWitnessXOfCoord P U hU q a g) =
      affineUniformLaw (2 * a) (g q - a * (q : ℝ) - a) := by
  calc
    law P (tangentWitnessXOfCoord P U hU q a g)
        = Measure.map (fun u : I => (2 * a) * (u : ℝ) + (g q - a * (q : ℝ) - a))
            (Measure.map U P) := by
            simpa [law, tangentWitnessXOfCoord, Function.comp] using
              (Measure.map_map (μ := P) (f := U)
                (g := fun u : I => (2 * a) * (u : ℝ) + (g q - a * (q : ℝ) - a))
                (by fun_prop) hU).symm
    _ = Measure.map (fun u : I => (2 * a) * (u : ℝ) + (g q - a * (q : ℝ) - a))
          (volume : Measure I) := by rw [hlawU]
    _ = affineUniformLaw (2 * a) (g q - a * (q : ℝ) - a) := by
          rfl

@[simp] theorem law_tangentWitnessYOfCoord
    (U : Ω → I) (hU : Measurable U) (hlawU : Measure.map U P = (volume : Measure I))
    (q : I) (a : ℝ) (g : Level → ℝ) :
    law P (tangentWitnessYOfCoord P U hU q a g) =
      foldedAffineLaw q (2 * a) (g q - a * (q : ℝ) - a) := by
  calc
    law P (tangentWitnessYOfCoord P U hU q a g)
        = Measure.map
            (fun u : I => (2 * a) * (((foldMap q u : I) : ℝ)) + (g q - a * (q : ℝ) - a))
            (Measure.map U P) := by
            simpa [law, tangentWitnessYOfCoord, Function.comp] using
              (Measure.map_map (μ := P) (f := U)
                (g := fun u : I =>
                  (2 * a) * (((foldMap q u : I) : ℝ)) + (g q - a * (q : ℝ) - a))
                (by fun_prop) hU).symm
    _ = Measure.map
          (fun u : I => (2 * a) * (((foldMap q u : I) : ℝ)) + (g q - a * (q : ℝ) - a))
          (volume : Measure I) := by rw [hlawU]
    _ = foldedAffineLaw q (2 * a) (g q - a * (q : ℝ) - a) := by
          rfl

@[simp] theorem law_tangentWitnessSupOfCoord
    (U : Ω → I) (hU : Measurable U) (hlawU : Measure.map U P = (volume : Measure I))
    (q : I) (a : ℝ) (g : Level → ℝ) :
    law P (tangentWitnessSupOfCoord P U hU q a g) =
      affineFoldedSupLaw q (2 * a) (g q - a * (q : ℝ) - a) := by
  calc
    law P (tangentWitnessSupOfCoord P U hU q a g)
        = Measure.map (fun u : I => (2 * a) * supCoord q u + (g q - a * (q : ℝ) - a))
            (Measure.map U P) := by
            simpa [law, tangentWitnessSupOfCoord, Function.comp] using
              (Measure.map_map (μ := P) (f := U)
                (g := fun u : I => (2 * a) * supCoord q u + (g q - a * (q : ℝ) - a))
                (by fun_prop) hU).symm
    _ = Measure.map (fun u : I => (2 * a) * supCoord q u + (g q - a * (q : ℝ) - a))
          (volume : Measure I) := by rw [hlawU]
    _ = affineFoldedSupLaw q (2 * a) (g q - a * (q : ℝ) - a) := by
          simpa [affineFoldedSupLaw, foldedSupLaw, Function.comp] using
            (Measure.map_map (μ := (volume : Measure I)) (f := supCoord q)
              (g := fun x : ℝ => (2 * a) * x + (g q - a * (q : ℝ) - a))
              (by fun_prop) (measurable_supCoord q)).symm

@[simp] theorem law_tangentWitnessInfOfCoord
    (U : Ω → I) (hU : Measurable U) (hlawU : Measure.map U P = (volume : Measure I))
    (q : I) (a : ℝ) (g : Level → ℝ) :
    law P (tangentWitnessInfOfCoord P U hU q a g) =
      affineFoldedInfLaw q (2 * a) (g q - a * (q : ℝ) - a) := by
  calc
    law P (tangentWitnessInfOfCoord P U hU q a g)
        = Measure.map (fun u : I => (2 * a) * infCoord q u + (g q - a * (q : ℝ) - a))
            (Measure.map U P) := by
            simpa [law, tangentWitnessInfOfCoord, Function.comp] using
              (Measure.map_map (μ := P) (f := U)
                (g := fun u : I => (2 * a) * infCoord q u + (g q - a * (q : ℝ) - a))
                (by fun_prop) hU).symm
    _ = Measure.map (fun u : I => (2 * a) * infCoord q u + (g q - a * (q : ℝ) - a))
          (volume : Measure I) := by rw [hlawU]
    _ = affineFoldedInfLaw q (2 * a) (g q - a * (q : ℝ) - a) := by
          simpa [affineFoldedInfLaw, foldedInfLaw, Function.comp] using
            (Measure.map_map (μ := (volume : Measure I)) (f := infCoord q)
              (g := fun x : ℝ => (2 * a) * x + (g q - a * (q : ℝ) - a))
              (by fun_prop) (measurable_infCoord q)).symm

theorem tangentWitness_sup_eq_ofCoord
    (U : Ω → I) (hU : Measurable U) (q : I) {a : ℝ} (ha : 0 < a) (g : Level → ℝ) :
    tangentWitnessXOfCoord P U hU q a g ⊔ tangentWitnessYOfCoord P U hU q a g =
      tangentWitnessSupOfCoord P U hU q a g := by
  ext ω
  have h2a : 0 ≤ 2 * a := by nlinarith [ha]
  change
      max ((2 * a) * (((U ω : I) : ℝ)) + (g q - a * (q : ℝ) - a))
        ((2 * a) * (((foldMap q (U ω) : I) : ℝ)) + (g q - a * (q : ℝ) - a)) =
      (2 * a) * supCoord q (U ω) + (g q - a * (q : ℝ) - a)
  rw [max_add_add_right, ← mul_max_of_nonneg (((U ω : I) : ℝ))
    (((foldMap q (U ω) : I) : ℝ)) h2a]
  rfl

theorem tangentWitness_inf_eq_ofCoord
    (U : Ω → I) (hU : Measurable U) (q : I) {a : ℝ} (ha : 0 < a) (g : Level → ℝ) :
    tangentWitnessXOfCoord P U hU q a g ⊓ tangentWitnessYOfCoord P U hU q a g =
      tangentWitnessInfOfCoord P U hU q a g := by
  ext ω
  have h2a : 0 ≤ 2 * a := by nlinarith [ha]
  change
      min ((2 * a) * (((U ω : I) : ℝ)) + (g q - a * (q : ℝ) - a))
        ((2 * a) * (((foldMap q (U ω) : I) : ℝ)) + (g q - a * (q : ℝ) - a)) =
      (2 * a) * infCoord q (U ω) + (g q - a * (q : ℝ) - a)
  rw [min_add_add_right, ← mul_min_of_nonneg (((U ω : I) : ℝ))
    (((foldMap q (U ω) : I) : ℝ)) h2a]
  rfl

/-- Any probability space carrying a measurable standard-uniform coordinate inherits the folded
tangent contradiction. This is the law-transport interface needed before constructing such a
coordinate on strongly atomless spaces. -/
theorem not_submodular_AES_of_foldedTangentWitness_of_uniformCoord
    (U : Ω → I) (hU : Measurable U) (hlawU : Measure.map U P = (volume : Measure I))
    {g : Level → ℝ} {q p : Level} {a : ℝ}
    (hq0 : 0 < (q : ℝ)) (hq : (q : ℝ) < 1) (ha : 0 < a)
    (hgnonneg : ∀ r : Level, 0 ≤ g r)
    (hline : ∀ r : Level, affineSupportLine g q a r ≤ g r)
    (hpq : (p : ℝ) < (q : ℝ))
    (hgap :
      g p < affineSupportLine g q a p +
        a * ((q : ℝ) - (p : ℝ)) ^ 2 / (2 * (1 - (p : ℝ)))) :
    ¬ Submodular (AES P g) := by
  let X : RandomVariable P := tangentWitnessXOfCoord P U hU q a g
  let Y : RandomVariable P := tangentWitnessYOfCoord P U hU q a g
  have hX : AES P g X ≤ 0 := by
    change distAES (law P (tangentWitnessXOfCoord P U hU q a g)) g ≤ 0
    simpa [law_tangentWitnessXOfCoord (P := P) (U := U) (hU := hU) (hlawU := hlawU)
      (q := q) (a := a) (g := g)] using
      (distAES_tangentWitness_le_zero_of_affineSupportLine (g := g) (q := q) (a := a) ha hline)
  have hY : AES P g Y ≤ 0 := by
    change distAES (law P (tangentWitnessYOfCoord P U hU q a g)) g ≤ 0
    simpa [law_tangentWitnessYOfCoord (P := P) (U := U) (hU := hU) (hlawU := hlawU)
      (q := q) (a := a) (g := g)] using
      (distAES_foldedTangentWitness_le_zero_of_affineSupportLine
        (g := g) (q := q) (a := a) ha hline)
  have hInf : 0 ≤ AES P g (X ⊓ Y) := by
    have hEqInf : X ⊓ Y = tangentWitnessInfOfCoord P U hU q a g := by
      change
        tangentWitnessXOfCoord P U hU q a g ⊓ tangentWitnessYOfCoord P U hU q a g =
          tangentWitnessInfOfCoord P U hU q a g
      exact tangentWitness_inf_eq_ofCoord (P := P) (U := U) (hU := hU) (q := q) (a := a) ha g
    rw [hEqInf]
    change 0 ≤ distAES (law P (tangentWitnessInfOfCoord P U hU q a g)) g
    simpa [law_tangentWitnessInfOfCoord (P := P) (U := U) (hU := hU) (hlawU := hlawU)
      (q := q) (a := a) (g := g)] using
      (distAES_foldedTangentInf_ge_zero (g := g) (q := q) (a := a) hq0 hq ha hgnonneg)
  have hSupPos : 0 < AES P g (X ⊔ Y) := by
    have hEqSup : X ⊔ Y = tangentWitnessSupOfCoord P U hU q a g := by
      change
        tangentWitnessXOfCoord P U hU q a g ⊔ tangentWitnessYOfCoord P U hU q a g =
          tangentWitnessSupOfCoord P U hU q a g
      exact tangentWitness_sup_eq_ofCoord (P := P) (U := U) (hU := hU) (q := q) (a := a) ha g
    rw [hEqSup]
    change 0 < distAES (law P (tangentWitnessSupOfCoord P U hU q a g)) g
    simpa [law_tangentWitnessSupOfCoord (P := P) (U := U) (hU := hU) (hlawU := hlawU)
      (q := q) (a := a) (g := g)] using
      (distAES_foldedTangentSup_pos_of_levelGap
        (g := g) (q := q) (p := p) (a := a) hq0 hq ha hgnonneg hpq hgap)
  exact not_submodular_AES_of_witness_bounds
    (P := P) (g := g) (X := X) (Y := Y)
    (xUpper := 0) (yUpper := 0) (infLower := 0)
    (supLower := AES P g (X ⊔ Y))
    hX hY hInf le_rfl (by linarith)

/-- The folded tangent contradiction can also be driven by a real-valued uniform coordinate whose
law is `volume.restrict (Icc 0 1)`. This keeps the transport layer on `ℝ` until the final
conversion to `unitInterval`. -/
theorem not_submodular_AES_of_foldedTangentWitness_of_realUniformCoord
    (U : Ω → ℝ) (hU : Measurable U) (hlawU : Measure.map U P = uniformMeasure)
    {g : Level → ℝ} {q p : Level} {a : ℝ}
    (hq0 : 0 < (q : ℝ)) (hq : (q : ℝ) < 1) (ha : 0 < a)
    (hgnonneg : ∀ r : Level, 0 ≤ g r)
    (hline : ∀ r : Level, affineSupportLine g q a r ≤ g r)
    (hpq : (p : ℝ) < (q : ℝ))
    (hgap :
      g p < affineSupportLine g q a p +
        a * ((q : ℝ) - (p : ℝ)) ^ 2 / (2 * (1 - (p : ℝ)))) :
    ¬ Submodular (AES P g) := by
  let U' : Ω → I := fun ω => Set.projIcc (0 : ℝ) 1 zero_le_one (U ω)
  have hU' : Measurable U' := by
    change Measurable (Set.projIcc (0 : ℝ) 1 zero_le_one ∘ U)
    exact continuous_projIcc.measurable.comp hU
  have hlawU' : Measure.map U' P = (volume : Measure I) := by
    calc
      Measure.map U' P
          = Measure.map (Set.projIcc (0 : ℝ) 1 zero_le_one) (Measure.map U P) := by
              simpa [U', Function.comp] using
                (Measure.map_map (μ := P) (f := U)
                  (g := Set.projIcc (0 : ℝ) 1 zero_le_one) (continuous_projIcc.measurable)
                  hU).symm
      _ = Measure.map (Set.projIcc (0 : ℝ) 1 zero_le_one) uniformMeasure := by rw [hlawU]
      _ = (volume : Measure I) := map_projIcc_uniformMeasure
  exact not_submodular_AES_of_foldedTangentWitness_of_uniformCoord
    (P := P) (U := U') hU' hlawU' hq0 hq ha hgnonneg hline hpq hgap

/-- Exact event splitting suffices to realize a standard-uniform coordinate, so the folded tangent
contradiction extends from the canonical `[0,1]` model to any such probability space. -/
theorem not_submodular_AES_of_foldedTangentWitness_of_fullEventSplitting
    (hsplit : HasFullEventSplitting P)
    {g : Level → ℝ} {q p : Level} {a : ℝ}
    (hq0 : 0 < (q : ℝ)) (hq : (q : ℝ) < 1) (ha : 0 < a)
    (hgnonneg : ∀ r : Level, 0 ≤ g r)
    (hline : ∀ r : Level, affineSupportLine g q a r ≤ g r)
    (hpq : (p : ℝ) < (q : ℝ))
    (hgap :
      g p < affineSupportLine g q a p +
        a * ((q : ℝ) - (p : ℝ)) ^ 2 / (2 * (1 - (p : ℝ)))) :
    ¬ Submodular (AES P g) := by
  obtain ⟨U, hU, hlawU⟩ := exists_realUniformCoord_of_fullEventSplitting (P := P) hsplit
  exact not_submodular_AES_of_foldedTangentWitness_of_realUniformCoord
    (P := P) U hU hlawU hq0 hq ha hgnonneg hline hpq hgap

/-- The folded tangent contradiction therefore applies on every strongly atomless probability
space. -/
theorem not_submodular_AES_of_foldedTangentWitness_of_stronglyAtomless
    (hatom : StronglyAtomless P)
    {g : Level → ℝ} {q p : Level} {a : ℝ}
    (hq0 : 0 < (q : ℝ)) (hq : (q : ℝ) < 1) (ha : 0 < a)
    (hgnonneg : ∀ r : Level, 0 ≤ g r)
    (hline : ∀ r : Level, affineSupportLine g q a r ≤ g r)
    (hpq : (p : ℝ) < (q : ℝ))
    (hgap :
      g p < affineSupportLine g q a p +
        a * ((q : ℝ) - (p : ℝ)) ^ 2 / (2 * (1 - (p : ℝ)))) :
    ¬ Submodular (AES P g) := by
  exact not_submodular_AES_of_foldedTangentWitness_of_fullEventSplitting
    (P := P) hatom.2 hq0 hq ha hgnonneg hline hpq hgap

end UniformCoordinateWitness

section FinalAssembly

variable {Ω : Type*} [MeasurableSpace Ω]
variable (P : Measure Ω) [IsProbabilityMeasure P]

/-- A non-`C²` folded contradiction theorem: once a convex penalty admits an interior point `q`
where the left derivative is positive, differentiable as a function of the base point, and violates
the barrier inequality, the folded tangent witness already yields non-submodularity on every
strongly atomless probability space. -/
theorem not_submodular_AES_of_convexOn_leftDeriv_barrier_of_stronglyAtomless
    (hatom : StronglyAtomless P)
    {f : ℝ → ℝ} {q : Level} {d : ℝ}
    (hconv : ConvexOn ℝ (Set.Icc (0 : ℝ) 1) f)
    (h0 : f 0 = 0)
    (hnonneg : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 ≤ f x)
    (hq0 : 0 < (q : ℝ)) (hq : (q : ℝ) < 1)
    (hqpos : 0 < f q)
    (hmd : HasDerivAt (fun x : ℝ => derivWithin f (Set.Iio x) x) d q)
    (hbarrier : d < derivWithin f (Set.Iio (q : ℝ)) (q : ℝ) / (1 - q)) :
    ¬ Submodular (AES P (fun p : Level => f p)) := by
  have hqmem : (q : ℝ) ∈ Set.Ioo (0 : ℝ) 1 := ⟨hq0, hq⟩
  have ha : 0 < derivWithin f (Set.Iio (q : ℝ)) (q : ℝ) := by
    exact leftDeriv_pos_of_convexOn_pos_before_one_at hconv h0 hqmem hqpos
  have hline :
      ∀ p : Level,
        affineSupportLine
            (fun r : Level => f r) q (derivWithin f (Set.Iio (q : ℝ)) (q : ℝ)) p ≤
          f p :=
    affineSupportLine_le_of_convexOn_leftDeriv hconv hqmem
  have hgnonneg : ∀ r : Level, 0 ≤ f r := by
    intro r
    exact hnonneg r r.2
  obtain ⟨p, hpq, hgap⟩ :=
    exists_levelGap_of_convexOn_leftDeriv_barrier hconv hq0 hq ha hmd hbarrier
  exact not_submodular_AES_of_foldedTangentWitness_of_stronglyAtomless
    (P := P) hatom hq0 hq ha hgnonneg hline hpq hgap

/-- Bare convexity already suffices for the folded contradiction on every strongly atomless
probability space. This theorem matches the front-half logic of the tex proof without assuming
`C²` regularity. -/
theorem not_submodular_AES_of_convexOn_of_stronglyAtomless
    (hatom : StronglyAtomless P)
    {f : ℝ → ℝ} {x0 : Level}
    (hx0 : (x0 : ℝ) ∈ Set.Ioo (0 : ℝ) 1)
    (hconv : ConvexOn ℝ (Set.Icc (0 : ℝ) 1) f)
    (h0 : f 0 = 0)
    (hnonneg : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 ≤ f x)
    (hx0pos : 0 < f x0) :
    ¬ Submodular (AES P (fun p : Level => f p)) := by
  obtain ⟨q, hx0q, hq, hqderivPos, hqd, hqbarrier, hline⟩ :=
    exists_good_affineSupportLine_point_of_convexOn_leftDeriv
      (x0 := x0) hx0 hconv h0 hx0pos
  have hx0derivPos :
      0 < derivWithin f (Set.Iio (x0 : ℝ)) (x0 : ℝ) := by
    exact leftDeriv_pos_of_convexOn_pos_before_one_at hconv h0 hx0 hx0pos
  have hqpos : 0 < f q := by
    have hx0line :=
      affineSupportLine_le_of_convexOn_leftDeriv (f := f) (q := x0) hconv hx0 q
    have hstrict :
        0 <
          f x0 +
            derivWithin f (Set.Iio (x0 : ℝ)) (x0 : ℝ) * ((q : ℝ) - (x0 : ℝ)) := by
      have hdelta : 0 < (q : ℝ) - (x0 : ℝ) := sub_pos.mpr hx0q
      have hterm :
          0 <
            derivWithin f (Set.Iio (x0 : ℝ)) (x0 : ℝ) * ((q : ℝ) - (x0 : ℝ)) := by
        positivity
      linarith
    have hupper : f x0 + derivWithin f (Set.Iio (x0 : ℝ)) (x0 : ℝ) * ((q : ℝ) - (x0 : ℝ)) ≤ f q := by
      simpa [affineSupportLine] using hx0line
    linarith
  exact not_submodular_AES_of_convexOn_leftDeriv_barrier_of_stronglyAtomless
    (P := P) (q := q)
    (d := deriv (fun x : ℝ => derivWithin f (Set.Iio x) x) q)
    hatom hconv h0 hnonneg (lt_trans hx0.1 hx0q) hq
    hqpos
    (by simpa using hqd.hasDerivAt)
    (by simpa using hqbarrier)

/-- A `C^2` convex penalty with positive mass away from `0` yields the folded tangent
contradiction on every strongly atomless probability space. This is the first end-to-end
formalization of the revised tex proof. -/
theorem not_submodular_AES_of_convexOn_contDiff_two_of_stronglyAtomless
    (hatom : StronglyAtomless P)
    {f : ℝ → ℝ} {x0 : ℝ}
    (hx0 : x0 ∈ Set.Ioo (0 : ℝ) 1)
    (hconv : ConvexOn ℝ (Set.Icc (0 : ℝ) 1) f)
    (h0 : f 0 = 0)
    (hnonneg : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 ≤ f x)
    (hcd : ContDiff ℝ 2 f)
    (hx0pos : 0 < f x0) :
    ¬ Submodular (AES P (fun p : Level => f p)) := by
  have hfd : ∀ x ∈ Set.Icc (0 : ℝ) 1, DifferentiableAt ℝ f x := by
    intro x hx
    exact (hcd.differentiable (by norm_num)) x
  have hderivCont : ContinuousOn (deriv f) (Set.Icc x0 1) := by
    exact (hcd.continuous_deriv (by norm_num)).continuousOn
  have hderivDiff : DifferentiableOn ℝ (deriv f) (Set.Ioo x0 1) := by
    exact hcd.differentiable_deriv_two.differentiableOn
  obtain ⟨q, hx0q, hq, ha, hbarrier, hline⟩ :=
    exists_good_affineSupportLine_point_of_convexOn
      hx0 hconv h0 hfd hderivCont hderivDiff hx0pos
  have hq0 : 0 < (q : ℝ) := lt_trans hx0.1 hx0q
  have hgnonneg : ∀ r : Level, 0 ≤ f r := by
    intro r
    exact hnonneg r r.2
  obtain ⟨p, hpq, hgap⟩ :=
    exists_levelGap_of_lt_secondDeriv_barrier hcd hq0 hq ha hbarrier
  exact not_submodular_AES_of_foldedTangentWitness_of_stronglyAtomless
    (P := P) hatom hq0 hq ha hgnonneg hline hpq hgap

end FinalAssembly

end AesSubmodularity
