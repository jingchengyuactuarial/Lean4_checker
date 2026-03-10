import Formalization.AesSubmodularity.Bridge
import Mathlib.Analysis.Convex.Deriv

/-!
# Finite Convex AES Counterexample Skeleton

This file isolates the finite convex construction from the manuscript, separately from the
infinite-left corollary line.

The first milestone here is constructive rather than asymptotic: we package the explicit
test positions together with a bounds-to-contradiction theorem for `AES`. The later wrapper
from convex finite-valued penalties to these explicit bounds can be added on top of this file.
-/

noncomputable section

open MeasureTheory
open RiskMeasure

namespace AesSubmodularity

section Levels

/-- The level `1 - 3h` appearing in the finite convex construction. -/
def finiteLevel0 (h : ℝ) (hh : 0 < h) (h3 : 3 * h < 1) : Level :=
  ⟨1 - 3 * h, by
    constructor <;> linarith⟩

/-- The level `1 - 2h` appearing in the finite convex construction. -/
def finiteLevel1 (h : ℝ) (hh : 0 < h) (h3 : 3 * h < 1) : Level :=
  ⟨1 - 2 * h, by
    constructor <;> linarith⟩

/-- The level `1 - h` appearing in the finite convex construction. -/
def finiteLevel2 (h : ℝ) (hh : 0 < h) (h3 : 3 * h < 1) : Level :=
  ⟨1 - h, by
    constructor <;> linarith⟩

@[simp] theorem coe_finiteLevel0 (h : ℝ) (hh : 0 < h) (h3 : 3 * h < 1) :
    ((finiteLevel0 h hh h3 : Level) : ℝ) = 1 - 3 * h :=
  rfl

@[simp] theorem coe_finiteLevel1 (h : ℝ) (hh : 0 < h) (h3 : 3 * h < 1) :
    ((finiteLevel1 h hh h3 : Level) : ℝ) = 1 - 2 * h :=
  rfl

@[simp] theorem coe_finiteLevel2 (h : ℝ) (hh : 0 < h) (h3 : 3 * h < 1) :
    ((finiteLevel2 h hh h3 : Level) : ℝ) = 1 - h :=
  rfl

end Levels

section SupportLine

/-- The affine support line `ℓ(p) = g(p₁) + r (p - p₁)` used in the finite convex proof. -/
def finiteSupportLine (g : Level → ℝ) (h r : ℝ) (hh : 0 < h) (h3 : 3 * h < 1) :
    Level → ℝ := fun p =>
  g (finiteLevel1 h hh h3) + r * ((p : ℝ) - (finiteLevel1 h hh h3 : ℝ))

@[simp] theorem finiteSupportLine_apply_p1 (g : Level → ℝ) (h r : ℝ) (hh : 0 < h)
    (h3 : 3 * h < 1) :
    finiteSupportLine g h r hh h3 (finiteLevel1 h hh h3) = g (finiteLevel1 h hh h3) := by
  simp [finiteSupportLine]

@[simp] theorem finiteSupportLine_apply_p0 (g : Level → ℝ) (h r : ℝ) (hh : 0 < h)
    (h3 : 3 * h < 1) :
    finiteSupportLine g h r hh h3 (finiteLevel0 h hh h3) =
      g (finiteLevel1 h hh h3) - r * h := by
  simp [finiteSupportLine]
  ring_nf

@[simp] theorem finiteSupportLine_apply_p2 (g : Level → ℝ) (h r : ℝ) (hh : 0 < h)
    (h3 : 3 * h < 1) :
    finiteSupportLine g h r hh h3 (finiteLevel2 h hh h3) =
      g (finiteLevel1 h hh h3) + r * h := by
  unfold finiteSupportLine
  have hdiff :
      (((finiteLevel2 h hh h3 : Level) : ℝ) - ((finiteLevel1 h hh h3 : Level) : ℝ)) = h := by
    simp
    ring
  rw [hdiff]

@[simp] theorem finiteSupportLine_apply_zero (g : Level → ℝ) (h r : ℝ) (hh : 0 < h)
    (h3 : 3 * h < 1) :
    finiteSupportLine g h r hh h3 0 =
      g (finiteLevel1 h hh h3) - r * (1 - 2 * h) := by
  simp [finiteSupportLine]
  ring

@[simp] theorem finiteSupportLine_apply_one (g : Level → ℝ) (h r : ℝ) (hh : 0 < h)
    (h3 : 3 * h < 1) :
    finiteSupportLine g h r hh h3 1 =
      g (finiteLevel1 h hh h3) + 2 * r * h := by
  simp [finiteSupportLine]
  ring_nf

end SupportLine

section WitnessPreparation

theorem finiteSupportLine_le_of_convexOn_hasDerivAt
    {f : ℝ → ℝ} {h r : ℝ} (hh : 0 < h) (h3 : 3 * h < 1)
    (hconv : ConvexOn ℝ (Set.Icc (0 : ℝ) 1) f)
    (hderiv : HasDerivAt f r (1 - 2 * h)) :
    ∀ p : Level, finiteSupportLine (fun q : Level => f q) h r hh h3 p ≤ f p := by
  intro p
  let q : ℝ := 1 - 2 * h
  have hqmem : q ∈ Set.Icc (0 : ℝ) 1 := by
    dsimp [q]
    constructor <;> linarith
  rcases lt_trichotomy (p : ℝ) q with hpq | hpq | hqp
  · have hSlope : slope f (p : ℝ) q ≤ r := by
      simpa [q] using
        hconv.slope_le_of_hasDerivAt (x := (p : ℝ)) (y := q) p.2 hqmem hpq hderiv
    have hslope' : (f q - f p) / (q - (p : ℝ)) ≤ r := by
      simpa [slope_def_field] using hSlope
    have hden : 0 < q - (p : ℝ) := sub_pos.mpr hpq
    have hmul : f q - f p ≤ r * (q - (p : ℝ)) := (div_le_iff₀ hden).mp hslope'
    have hline : f q + r * ((p : ℝ) - q) ≤ f p := by
      linarith
    simpa [finiteSupportLine, q] using hline
  · have hline : f q + r * ((p : ℝ) - q) = f p := by
      simp [hpq]
    simpa [finiteSupportLine, q] using le_of_eq hline
  · have hSlope : r ≤ slope f q (p : ℝ) := by
      simpa [q] using
        hconv.le_slope_of_hasDerivAt (x := q) (y := (p : ℝ)) hqmem p.2 hqp hderiv
    have hslope' : r ≤ (f p - f q) / ((p : ℝ) - q) := by
      simpa [slope_def_field] using hSlope
    have hden : 0 < (p : ℝ) - q := sub_pos.mpr hqp
    have hmul : r * ((p : ℝ) - q) ≤ f p - f q := (le_div_iff₀ hden).mp hslope'
    have hline : f q + r * ((p : ℝ) - q) ≤ f p := by
      linarith
    simpa [finiteSupportLine, q] using hline

theorem exists_M_for_finiteConvex
    {g : Level → ℝ} {h r u a b : ℝ} (hh : 0 < h) (h3 : 3 * h < 1) :
    ∃ M : ℝ,
      a < M ∧
        (-(1 - 3 * h) * M - h * (a + b)) - finiteSupportLine g h r hh h3 0 <
          -(3 * u / 4) - g (finiteLevel1 h hh h3) := by
  let p1 : Level := finiteLevel1 h hh h3
  let B : ℝ :=
    (3 * u / 4 + g p1 - h * (a + b) - finiteSupportLine g h r hh h3 0) / (1 - 3 * h)
  let M : ℝ := max a B + 1
  refine ⟨M, ?_, ?_⟩
  · dsimp [M]
    linarith [le_max_left a B]
  · have hden : 0 < 1 - 3 * h := by linarith
    have hBlt : B < M := by
      dsimp [M]
      have hBle : B ≤ max a B := le_max_right a B
      linarith
    have hmul :
        3 * u / 4 + g p1 - h * (a + b) - finiteSupportLine g h r hh h3 0 <
          M * (1 - 3 * h) := by
      exact (div_lt_iff₀ hden).mp hBlt
    have hgoal :
        (-(1 - 3 * h) * M - h * (a + b)) - finiteSupportLine g h r hh h3 0 <
          -(3 * u / 4) - g p1 := by
      linarith
    simpa [p1, M] using hgoal

end WitnessPreparation

section Positions

variable {Ω : Type*} [MeasurableSpace Ω]
variable (P : Measure Ω)

private theorem measure_union_three_eq_sum {A B C : Set Ω}
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C)
    (hB : MeasurableSet B) (hC : MeasurableSet C) :
    P (A ∪ B ∪ C) = P A + P B + P C := by
  calc
    P ((A ∪ B) ∪ C) = P (A ∪ B) + P C := by
      refine measure_union ?_ hC
      refine Set.disjoint_left.2 ?_
      intro ω hωAB hωC
      rcases hωAB with hωA | hωB
      · exact Set.disjoint_left.mp hAC hωA hωC
      · exact Set.disjoint_left.mp hBC hωB hωC
    _ = P A + P B + P C := by
      rw [measure_union hAB hB, add_assoc]

private theorem measure_union_four_eq_sum {A B C D : Set Ω}
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hAD : Disjoint A D)
    (hBC : Disjoint B C) (hBD : Disjoint B D) (hCD : Disjoint C D)
    (hB : MeasurableSet B) (hC : MeasurableSet C) (hD : MeasurableSet D) :
    P (A ∪ B ∪ C ∪ D) = P A + P B + P C + P D := by
  calc
    P ((A ∪ B ∪ C) ∪ D) = P (A ∪ B ∪ C) + P D := by
      refine measure_union ?_ hD
      refine Set.disjoint_left.2 ?_
      intro ω hωABC hωD
      rcases hωABC with hωAB | hωC
      · rcases hωAB with hωA | hωB
        · exact Set.disjoint_left.mp hAD hωA hωD
        · exact Set.disjoint_left.mp hBD hωB hωD
      · exact Set.disjoint_left.mp hCD hωC hωD
    _ = P A + P B + P C + P D := by
      rw [measure_union_three_eq_sum (P := P) hAB hAC hBC hB hC, add_assoc]

omit [MeasurableSpace Ω] in
private theorem scaledIndicator_union_eq_add_of_disjoint (c : ℝ) {A B : Set Ω}
    (hAB : Disjoint A B) :
    scaledIndicator c (A ∪ B) = fun ω => scaledIndicator c A ω + scaledIndicator c B ω := by
  funext ω
  by_cases hωA : ω ∈ A
  · have hωB : ω ∉ B := by
      intro hωB
      exact Set.disjoint_left.mp hAB hωA hωB
    simp [scaledIndicator, eventIndicator, hωA, hωB]
  · by_cases hωB : ω ∈ B
    · simp [scaledIndicator, eventIndicator, hωA, hωB]
    · simp [scaledIndicator, eventIndicator, hωA, hωB]

/-- A three-layer simple law with an additional `0`-valued complement atom. This is the finite
convex law shape needed for `X`, `Y`, `X ⊔ Y`, and `X ⊓ Y`. -/
def finiteThreeIndicatorLaw (x0 x1 x2 : ℝ) (E0 E1 E2 : Set Ω) : Measure ℝ :=
  P E0 • Measure.dirac x0 +
    (P E1 • Measure.dirac x1 +
      (P E2 • Measure.dirac x2 + P (E0 ∪ E1 ∪ E2)ᶜ • Measure.dirac 0))

/-- The `X` test position from the finite convex manuscript construction. -/
def finiteConvexX (M a b : ℝ) (E0 E1 E2 : Set Ω)
    (hE0 : MeasurableSet E0) (hE1 : MeasurableSet E1) (hE2 : MeasurableSet E2) :
    RandomVariable P :=
  scaledIndicatorRV P (-M) E0 hE0 +
    scaledIndicatorRV P (-a) E1 hE1 +
    scaledIndicatorRV P (-b) E2 hE2

/-- The `Y` test position from the finite convex manuscript construction. -/
def finiteConvexY (M a b : ℝ) (E0 E1 E2 : Set Ω)
    (hE0 : MeasurableSet E0) (hE1 : MeasurableSet E1) (hE2 : MeasurableSet E2) :
    RandomVariable P :=
  scaledIndicatorRV P (-M) E0 hE0 +
    scaledIndicatorRV P (-b) E1 hE1 +
    scaledIndicatorRV P (-a) E2 hE2

/-- The explicit `X ⊔ Y` position from the finite convex manuscript construction. -/
def finiteConvexSup (M b : ℝ) (E0 E1 E2 : Set Ω)
    (hE0 : MeasurableSet E0) (hE12 : MeasurableSet (E1 ∪ E2)) :
    RandomVariable P :=
  scaledIndicatorRV P (-M) E0 hE0 + scaledIndicatorRV P (-b) (E1 ∪ E2) hE12

/-- The explicit `X ⊓ Y` position from the finite convex manuscript construction. -/
def finiteConvexInf (M a : ℝ) (E0 E1 E2 : Set Ω)
    (hE0 : MeasurableSet E0) (hE12 : MeasurableSet (E1 ∪ E2)) :
    RandomVariable P :=
  scaledIndicatorRV P (-M) E0 hE0 + scaledIndicatorRV P (-a) (E1 ∪ E2) hE12

@[simp] theorem finiteConvexX_apply (M a b : ℝ) (E0 E1 E2 : Set Ω)
    (hE0 : MeasurableSet E0) (hE1 : MeasurableSet E1) (hE2 : MeasurableSet E2) (ω : Ω) :
    (finiteConvexX P M a b E0 E1 E2 hE0 hE1 hE2 : Ω → ℝ) ω =
      scaledIndicator (-M) E0 ω + scaledIndicator (-a) E1 ω + scaledIndicator (-b) E2 ω :=
  rfl

@[simp] theorem finiteConvexY_apply (M a b : ℝ) (E0 E1 E2 : Set Ω)
    (hE0 : MeasurableSet E0) (hE1 : MeasurableSet E1) (hE2 : MeasurableSet E2) (ω : Ω) :
    (finiteConvexY P M a b E0 E1 E2 hE0 hE1 hE2 : Ω → ℝ) ω =
      scaledIndicator (-M) E0 ω + scaledIndicator (-b) E1 ω + scaledIndicator (-a) E2 ω :=
  rfl

@[simp] theorem finiteConvexSup_apply (M b : ℝ) (E0 E1 E2 : Set Ω)
    (hE0 : MeasurableSet E0) (hE12 : MeasurableSet (E1 ∪ E2)) (ω : Ω) :
    (finiteConvexSup P M b E0 E1 E2 hE0 hE12 : Ω → ℝ) ω =
      scaledIndicator (-M) E0 ω + scaledIndicator (-b) (E1 ∪ E2) ω :=
  rfl

@[simp] theorem finiteConvexInf_apply (M a : ℝ) (E0 E1 E2 : Set Ω)
    (hE0 : MeasurableSet E0) (hE12 : MeasurableSet (E1 ∪ E2)) (ω : Ω) :
    (finiteConvexInf P M a E0 E1 E2 hE0 hE12 : Ω → ℝ) ω =
      scaledIndicator (-M) E0 ω + scaledIndicator (-a) (E1 ∪ E2) ω :=
  rfl

theorem finiteConvexX_sup_finiteConvexY_eq_finiteConvexSup
    {M a b : ℝ} {E0 E1 E2 : Set Ω}
    (hE0 : MeasurableSet E0) (hE1 : MeasurableSet E1) (hE2 : MeasurableSet E2)
    (h01 : Disjoint E0 E1) (h02 : Disjoint E0 E2) (h12 : Disjoint E1 E2) (hba : b ≤ a) :
    finiteConvexX P M a b E0 E1 E2 hE0 hE1 hE2 ⊔
        finiteConvexY P M a b E0 E1 E2 hE0 hE1 hE2 =
      finiteConvexSup P M b E0 E1 E2 hE0 (hE1.union hE2) := by
  ext ω
  by_cases hω0 : ω ∈ E0
  · have hω1 : ω ∉ E1 := by
      intro hω1
      exact Set.disjoint_left.mp h01 hω0 hω1
    have hω2 : ω ∉ E2 := by
      intro hω2
      exact Set.disjoint_left.mp h02 hω0 hω2
    change max
        ((finiteConvexX P M a b E0 E1 E2 hE0 hE1 hE2 : Ω → ℝ) ω)
        ((finiteConvexY P M a b E0 E1 E2 hE0 hE1 hE2 : Ω → ℝ) ω) =
      (finiteConvexSup P M b E0 E1 E2 hE0 (hE1.union hE2) : Ω → ℝ) ω
    simp [finiteConvexX_apply, finiteConvexY_apply, finiteConvexSup_apply,
      scaledIndicator_eq_indicator_const, hω0, hω1, hω2]
  · by_cases hω1 : ω ∈ E1
    · have hω2 : ω ∉ E2 := by
        intro hω2
        exact Set.disjoint_left.mp h12 hω1 hω2
      change max
          ((finiteConvexX P M a b E0 E1 E2 hE0 hE1 hE2 : Ω → ℝ) ω)
          ((finiteConvexY P M a b E0 E1 E2 hE0 hE1 hE2 : Ω → ℝ) ω) =
        (finiteConvexSup P M b E0 E1 E2 hE0 (hE1.union hE2) : Ω → ℝ) ω
      simp [finiteConvexX_apply, finiteConvexY_apply, finiteConvexSup_apply,
        scaledIndicator_eq_indicator_const, hω0, hω1, hω2]
      exact hba
    · by_cases hω2 : ω ∈ E2
      · have hω12 : ω ∈ E1 ∪ E2 := Or.inr hω2
        change max
            ((finiteConvexX P M a b E0 E1 E2 hE0 hE1 hE2 : Ω → ℝ) ω)
            ((finiteConvexY P M a b E0 E1 E2 hE0 hE1 hE2 : Ω → ℝ) ω) =
          (finiteConvexSup P M b E0 E1 E2 hE0 (hE1.union hE2) : Ω → ℝ) ω
        simp [finiteConvexX_apply, finiteConvexY_apply, finiteConvexSup_apply,
          scaledIndicator_eq_indicator_const, hω0, hω1, hω2, hω12]
        exact hba
      · have hω12 : ω ∉ E1 ∪ E2 := by
          simp [hω1, hω2]
        have hX0 :
            ((finiteConvexX P M a b E0 E1 E2 hE0 hE1 hE2 : Ω → ℝ) ω) = 0 := by
          simp [finiteConvexX_apply, scaledIndicator_eq_indicator_const, hω0, hω1, hω2]
        have hY0 :
            ((finiteConvexY P M a b E0 E1 E2 hE0 hE1 hE2 : Ω → ℝ) ω) = 0 := by
          simp [finiteConvexY_apply, scaledIndicator_eq_indicator_const, hω0, hω1, hω2]
        have hSup0 :
            ((finiteConvexSup P M b E0 E1 E2 hE0 (hE1.union hE2) : Ω → ℝ) ω) = 0 := by
          simp [finiteConvexSup_apply, scaledIndicator_eq_indicator_const, hω0, hω12]
        change max
            ((finiteConvexX P M a b E0 E1 E2 hE0 hE1 hE2 : Ω → ℝ) ω)
            ((finiteConvexY P M a b E0 E1 E2 hE0 hE1 hE2 : Ω → ℝ) ω) =
          (finiteConvexSup P M b E0 E1 E2 hE0 (hE1.union hE2) : Ω → ℝ) ω
        rw [hX0, hY0, hSup0]
        simp

theorem finiteConvexX_inf_finiteConvexY_eq_finiteConvexInf
    {M a b : ℝ} {E0 E1 E2 : Set Ω}
    (hE0 : MeasurableSet E0) (hE1 : MeasurableSet E1) (hE2 : MeasurableSet E2)
    (h01 : Disjoint E0 E1) (h02 : Disjoint E0 E2) (h12 : Disjoint E1 E2) (hba : b ≤ a) :
    finiteConvexX P M a b E0 E1 E2 hE0 hE1 hE2 ⊓
        finiteConvexY P M a b E0 E1 E2 hE0 hE1 hE2 =
      finiteConvexInf P M a E0 E1 E2 hE0 (hE1.union hE2) := by
  ext ω
  by_cases hω0 : ω ∈ E0
  · have hω1 : ω ∉ E1 := by
      intro hω1
      exact Set.disjoint_left.mp h01 hω0 hω1
    have hω2 : ω ∉ E2 := by
      intro hω2
      exact Set.disjoint_left.mp h02 hω0 hω2
    change min
        ((finiteConvexX P M a b E0 E1 E2 hE0 hE1 hE2 : Ω → ℝ) ω)
        ((finiteConvexY P M a b E0 E1 E2 hE0 hE1 hE2 : Ω → ℝ) ω) =
      (finiteConvexInf P M a E0 E1 E2 hE0 (hE1.union hE2) : Ω → ℝ) ω
    simp [finiteConvexX_apply, finiteConvexY_apply, finiteConvexInf_apply,
      scaledIndicator_eq_indicator_const, hω0, hω1, hω2]
  · by_cases hω1 : ω ∈ E1
    · have hω2 : ω ∉ E2 := by
        intro hω2
        exact Set.disjoint_left.mp h12 hω1 hω2
      change min
          ((finiteConvexX P M a b E0 E1 E2 hE0 hE1 hE2 : Ω → ℝ) ω)
          ((finiteConvexY P M a b E0 E1 E2 hE0 hE1 hE2 : Ω → ℝ) ω) =
        (finiteConvexInf P M a E0 E1 E2 hE0 (hE1.union hE2) : Ω → ℝ) ω
      simp [finiteConvexX_apply, finiteConvexY_apply, finiteConvexInf_apply,
        scaledIndicator_eq_indicator_const, hω0, hω1, hω2]
      exact hba
    · by_cases hω2 : ω ∈ E2
      · have hω12 : ω ∈ E1 ∪ E2 := Or.inr hω2
        change min
            ((finiteConvexX P M a b E0 E1 E2 hE0 hE1 hE2 : Ω → ℝ) ω)
            ((finiteConvexY P M a b E0 E1 E2 hE0 hE1 hE2 : Ω → ℝ) ω) =
          (finiteConvexInf P M a E0 E1 E2 hE0 (hE1.union hE2) : Ω → ℝ) ω
        simp [finiteConvexX_apply, finiteConvexY_apply, finiteConvexInf_apply,
          scaledIndicator_eq_indicator_const, hω0, hω1, hω2, hω12]
        exact hba
      · have hω12 : ω ∉ E1 ∪ E2 := by
          simp [hω1, hω2]
        have hX0 :
            ((finiteConvexX P M a b E0 E1 E2 hE0 hE1 hE2 : Ω → ℝ) ω) = 0 := by
          simp [finiteConvexX_apply, scaledIndicator_eq_indicator_const, hω0, hω1, hω2]
        have hY0 :
            ((finiteConvexY P M a b E0 E1 E2 hE0 hE1 hE2 : Ω → ℝ) ω) = 0 := by
          simp [finiteConvexY_apply, scaledIndicator_eq_indicator_const, hω0, hω1, hω2]
        have hInf0 :
            ((finiteConvexInf P M a E0 E1 E2 hE0 (hE1.union hE2) : Ω → ℝ) ω) = 0 := by
          simp [finiteConvexInf_apply, scaledIndicator_eq_indicator_const, hω0, hω12]
        change min
            ((finiteConvexX P M a b E0 E1 E2 hE0 hE1 hE2 : Ω → ℝ) ω)
            ((finiteConvexY P M a b E0 E1 E2 hE0 hE1 hE2 : Ω → ℝ) ω) =
          (finiteConvexInf P M a E0 E1 E2 hE0 (hE1.union hE2) : Ω → ℝ) ω
        rw [hX0, hY0, hInf0]
        simp

theorem law_sum_threeIndicators_eq_finiteThreeIndicatorLaw
    (x0 x1 x2 : ℝ) {E0 E1 E2 : Set Ω}
    (hE0 : MeasurableSet E0) (hE1 : MeasurableSet E1) (hE2 : MeasurableSet E2)
    (h01 : Disjoint E0 E1) (h02 : Disjoint E0 E2) (h12 : Disjoint E1 E2) :
    law P (scaledIndicatorRV P x0 E0 hE0 + scaledIndicatorRV P x1 E1 hE1 +
      scaledIndicatorRV P x2 E2 hE2) = finiteThreeIndicatorLaw P x0 x1 x2 E0 E1 E2 := by
  classical
  ext s hs
  let A0 : Set Ω := if x0 ∈ s then E0 else ∅
  let A1 : Set Ω := if x1 ∈ s then E1 else ∅
  let A2 : Set Ω := if x2 ∈ s then E2 else ∅
  let A3 : Set Ω := if (0 : ℝ) ∈ s then (E0 ∪ E1 ∪ E2)ᶜ else ∅
  have hpre :
      ((scaledIndicatorRV P x0 E0 hE0 + scaledIndicatorRV P x1 E1 hE1 +
          scaledIndicatorRV P x2 E2 hE2 : RandomVariable P) : Ω → ℝ) ⁻¹' s =
        A0 ∪ A1 ∪ A2 ∪ A3 := by
    ext ω
    by_cases hω0 : ω ∈ E0
    · have hω1 : ω ∉ E1 := by
        intro hω1
        exact Set.disjoint_left.mp h01 hω0 hω1
      have hω2 : ω ∉ E2 := by
        intro hω2
        exact Set.disjoint_left.mp h02 hω0 hω2
      simp [A0, A1, A2, A3, scaledIndicatorRV, scaledIndicator_eq_indicator_const, hω0, hω1,
        hω2]
    · by_cases hω1 : ω ∈ E1
      · have hω2 : ω ∉ E2 := by
          intro hω2
          exact Set.disjoint_left.mp h12 hω1 hω2
        simp [A0, A1, A2, A3, scaledIndicatorRV, scaledIndicator_eq_indicator_const, hω0, hω1,
          hω2]
      · by_cases hω2 : ω ∈ E2
        · simp [A0, A1, A2, A3, scaledIndicatorRV, scaledIndicator_eq_indicator_const, hω0,
            hω1, hω2]
        · simp [A0, A1, A2, A3, scaledIndicatorRV, scaledIndicator_eq_indicator_const, hω0,
            hω1, hω2]
  have hA1 : MeasurableSet A1 := by
    by_cases hx1 : x1 ∈ s <;> simp [A1, hx1, hE1]
  have hA2 : MeasurableSet A2 := by
    by_cases hx2 : x2 ∈ s <;> simp [A2, hx2, hE2]
  have hA3 : MeasurableSet A3 := by
    by_cases h0 : (0 : ℝ) ∈ s <;> simp [A3, h0, hE0, hE1, hE2]
  have hA0A1 : Disjoint A0 A1 := by
    by_cases hx0 : x0 ∈ s <;> by_cases hx1 : x1 ∈ s <;> simp [A0, A1, hx0, hx1, h01]
  have hA0A2 : Disjoint A0 A2 := by
    by_cases hx0 : x0 ∈ s <;> by_cases hx2 : x2 ∈ s <;> simp [A0, A2, hx0, hx2, h02]
  have hA0A3 : Disjoint A0 A3 := by
    by_cases hx0 : x0 ∈ s <;> by_cases h0 : (0 : ℝ) ∈ s
    · refine Set.disjoint_left.2 ?_
      intro ω hω0 hω3
      have hω0' : ω ∈ E0 := by
        simpa [A0, hx0] using hω0
      have hω3' : ω ∈ (E0 ∪ E1 ∪ E2)ᶜ := by
        simpa [A3, h0] using hω3
      exact hω3' (Or.inl (Or.inl hω0'))
    · simp [A0, A3, hx0, h0]
    · simp [A0, A3, hx0, h0]
    · simp [A0, A3, hx0, h0]
  have hA1A2 : Disjoint A1 A2 := by
    by_cases hx1 : x1 ∈ s <;> by_cases hx2 : x2 ∈ s <;> simp [A1, A2, hx1, hx2, h12]
  have hA1A3 : Disjoint A1 A3 := by
    by_cases hx1 : x1 ∈ s <;> by_cases h0 : (0 : ℝ) ∈ s
    · refine Set.disjoint_left.2 ?_
      intro ω hω1 hω3
      have hω1' : ω ∈ E1 := by
        simpa [A1, hx1] using hω1
      have hω3' : ω ∈ (E0 ∪ E1 ∪ E2)ᶜ := by
        simpa [A3, h0] using hω3
      exact hω3' (Or.inl (Or.inr hω1'))
    · simp [A1, A3, hx1, h0]
    · simp [A1, A3, hx1, h0]
    · simp [A1, A3, hx1, h0]
  have hA2A3 : Disjoint A2 A3 := by
    by_cases hx2 : x2 ∈ s <;> by_cases h0 : (0 : ℝ) ∈ s
    · refine Set.disjoint_left.2 ?_
      intro ω hω2 hω3
      have hω2' : ω ∈ E2 := by
        simpa [A2, hx2] using hω2
      have hω3' : ω ∈ (E0 ∪ E1 ∪ E2)ᶜ := by
        simpa [A3, h0] using hω3
      exact hω3' (Or.inr hω2')
    · simp [A2, A3, hx2, h0]
    · simp [A2, A3, hx2, h0]
    · simp [A2, A3, hx2, h0]
  have hPA0 : P A0 = P E0 • s.indicator 1 x0 := by
    by_cases hx0 : x0 ∈ s <;> simp [A0, hx0]
  have hPA1 : P A1 = P E1 • s.indicator 1 x1 := by
    by_cases hx1 : x1 ∈ s <;> simp [A1, hx1]
  have hPA2 : P A2 = P E2 • s.indicator 1 x2 := by
    by_cases hx2 : x2 ∈ s <;> simp [A2, hx2]
  have hPA3 : P A3 = P (E0 ∪ E1 ∪ E2)ᶜ • s.indicator 1 0 := by
    by_cases h0 : (0 : ℝ) ∈ s <;> simp [A3, h0]
  let f : Ω → ℝ :=
    (scaledIndicatorRV P x0 E0 hE0 + scaledIndicatorRV P x1 E1 hE1 +
      scaledIndicatorRV P x2 E2 hE2 : RandomVariable P)
  have hsum_meas : AEMeasurable f P := by
    simpa [f] using
      (scaledIndicatorRV P x0 E0 hE0 + scaledIndicatorRV P x1 E1 hE1 +
        scaledIndicatorRV P x2 E2 hE2).2
  rw [law, Measure.map_apply_of_aemeasurable hsum_meas hs,
    hpre, finiteThreeIndicatorLaw, Measure.add_apply, Measure.add_apply, Measure.add_apply,
    Measure.smul_apply, Measure.smul_apply, Measure.smul_apply, Measure.smul_apply,
    Measure.dirac_apply' _ hs, Measure.dirac_apply' _ hs, Measure.dirac_apply' _ hs,
    Measure.dirac_apply' _ hs]
  rw [← hPA0, ← hPA1, ← hPA2, ← hPA3]
  simpa [add_assoc] using
    measure_union_four_eq_sum (P := P) hA0A1 hA0A2 hA0A3 hA1A2 hA1A3 hA2A3 hA1 hA2 hA3

theorem law_finiteConvexX_eq_finiteThreeIndicatorLaw
    (M a b : ℝ) {E0 E1 E2 : Set Ω}
    (hE0 : MeasurableSet E0) (hE1 : MeasurableSet E1) (hE2 : MeasurableSet E2)
    (h01 : Disjoint E0 E1) (h02 : Disjoint E0 E2) (h12 : Disjoint E1 E2) :
    law P (finiteConvexX P M a b E0 E1 E2 hE0 hE1 hE2) =
      finiteThreeIndicatorLaw P (-M) (-a) (-b) E0 E1 E2 := by
  unfold finiteConvexX
  simpa [add_assoc] using law_sum_threeIndicators_eq_finiteThreeIndicatorLaw
    (P := P) (-M) (-a) (-b) hE0 hE1 hE2 h01 h02 h12

theorem law_finiteConvexY_eq_finiteThreeIndicatorLaw
    (M a b : ℝ) {E0 E1 E2 : Set Ω}
    (hE0 : MeasurableSet E0) (hE1 : MeasurableSet E1) (hE2 : MeasurableSet E2)
    (h01 : Disjoint E0 E1) (h02 : Disjoint E0 E2) (h12 : Disjoint E1 E2) :
    law P (finiteConvexY P M a b E0 E1 E2 hE0 hE1 hE2) =
      finiteThreeIndicatorLaw P (-M) (-b) (-a) E0 E1 E2 := by
  unfold finiteConvexY
  simpa [add_assoc] using law_sum_threeIndicators_eq_finiteThreeIndicatorLaw
    (P := P) (-M) (-b) (-a) hE0 hE1 hE2 h01 h02 h12

theorem law_finiteConvexSup_eq_finiteThreeIndicatorLaw
    (M b : ℝ) {E0 E1 E2 : Set Ω}
    (hE0 : MeasurableSet E0) (hE1 : MeasurableSet E1) (hE2 : MeasurableSet E2)
    (h01 : Disjoint E0 E1) (h02 : Disjoint E0 E2) (h12 : Disjoint E1 E2) :
    law P (finiteConvexSup P M b E0 E1 E2 hE0 (hE1.union hE2)) =
      finiteThreeIndicatorLaw P (-M) (-b) (-b) E0 E1 E2 := by
  unfold finiteConvexSup
  rw [show scaledIndicatorRV P (-M) E0 hE0 + scaledIndicatorRV P (-b) (E1 ∪ E2) (hE1.union hE2) =
      scaledIndicatorRV P (-M) E0 hE0 + scaledIndicatorRV P (-b) E1 hE1 +
        scaledIndicatorRV P (-b) E2 hE2 by
        ext ω
        change scaledIndicator (-M) E0 ω + scaledIndicator (-b) (E1 ∪ E2) ω =
          scaledIndicator (-M) E0 ω + scaledIndicator (-b) E1 ω + scaledIndicator (-b) E2 ω
        rw [scaledIndicator_union_eq_add_of_disjoint (Ω := Ω) (-b) h12]
        ring]
  simpa [add_assoc] using law_sum_threeIndicators_eq_finiteThreeIndicatorLaw
    (P := P) (-M) (-b) (-b) hE0 hE1 hE2 h01 h02 h12

theorem law_finiteConvexInf_eq_finiteThreeIndicatorLaw
    (M a : ℝ) {E0 E1 E2 : Set Ω}
    (hE0 : MeasurableSet E0) (hE1 : MeasurableSet E1) (hE2 : MeasurableSet E2)
    (h01 : Disjoint E0 E1) (h02 : Disjoint E0 E2) (h12 : Disjoint E1 E2) :
    law P (finiteConvexInf P M a E0 E1 E2 hE0 (hE1.union hE2)) =
      finiteThreeIndicatorLaw P (-M) (-a) (-a) E0 E1 E2 := by
  unfold finiteConvexInf
  rw [show scaledIndicatorRV P (-M) E0 hE0 + scaledIndicatorRV P (-a) (E1 ∪ E2) (hE1.union hE2) =
      scaledIndicatorRV P (-M) E0 hE0 + scaledIndicatorRV P (-a) E1 hE1 +
        scaledIndicatorRV P (-a) E2 hE2 by
        ext ω
        change scaledIndicator (-M) E0 ω + scaledIndicator (-a) (E1 ∪ E2) ω =
          scaledIndicator (-M) E0 ω + scaledIndicator (-a) E1 ω + scaledIndicator (-a) E2 ω
        rw [scaledIndicator_union_eq_add_of_disjoint (Ω := Ω) (-a) h12]
        ring]
  simpa [add_assoc] using law_sum_threeIndicators_eq_finiteThreeIndicatorLaw
    (P := P) (-M) (-a) (-a) hE0 hE1 hE2 h01 h02 h12

end Positions

section FiniteThreeIndicatorCDF

variable {Ω : Type*} [MeasurableSpace Ω]
variable (P : Measure Ω) [IsProbabilityMeasure P]

private theorem finiteThreeIndicatorLaw_apply_Iic (x0 x1 x2 x : ℝ) {E0 E1 E2 : Set Ω} :
    finiteThreeIndicatorLaw P x0 x1 x2 E0 E1 E2 (Set.Iic x) =
      P E0 • (Set.Iic x).indicator 1 x0 +
        (P E1 • (Set.Iic x).indicator 1 x1 +
          (P E2 • (Set.Iic x).indicator 1 x2 +
            P (E0 ∪ E1 ∪ E2)ᶜ • (Set.Iic x).indicator 1 0)) := by
  rw [finiteThreeIndicatorLaw, Measure.add_apply, Measure.add_apply, Measure.add_apply,
    Measure.smul_apply, Measure.smul_apply, Measure.smul_apply, Measure.smul_apply,
    Measure.dirac_apply' _ measurableSet_Iic, Measure.dirac_apply' _ measurableSet_Iic,
    Measure.dirac_apply' _ measurableSet_Iic, Measure.dirac_apply' _ measurableSet_Iic]

private theorem finiteThreeIndicatorLaw_isProbabilityMeasure
    (x0 x1 x2 : ℝ) {E0 E1 E2 : Set Ω}
    (hE0 : MeasurableSet E0) (hE1 : MeasurableSet E1) (hE2 : MeasurableSet E2)
    (h01 : Disjoint E0 E1) (h02 : Disjoint E0 E2) (h12 : Disjoint E1 E2) :
    IsProbabilityMeasure (finiteThreeIndicatorLaw P x0 x1 x2 E0 E1 E2) := by
  rw [← law_sum_threeIndicators_eq_finiteThreeIndicatorLaw (P := P) x0 x1 x2
    hE0 hE1 hE2 h01 h02 h12]
  infer_instance

private theorem cdf_finiteThreeIndicatorLaw_of_lt_x0
    {x0 x1 x2 : ℝ} (hx01 : x0 ≤ x1) (hx12 : x1 ≤ x2) (hx20 : x2 ≤ 0)
    {E0 E1 E2 : Set Ω} (hE0 : MeasurableSet E0) (hE1 : MeasurableSet E1) (hE2 : MeasurableSet E2)
    (h01 : Disjoint E0 E1) (h02 : Disjoint E0 E2) (h12 : Disjoint E1 E2) {x : ℝ} (hx : x < x0) :
    ProbabilityTheory.cdf (finiteThreeIndicatorLaw P x0 x1 x2 E0 E1 E2) x = 0 := by
  haveI : IsProbabilityMeasure (finiteThreeIndicatorLaw P x0 x1 x2 E0 E1 E2) :=
    finiteThreeIndicatorLaw_isProbabilityMeasure (P := P) x0 x1 x2 hE0 hE1 hE2 h01 h02 h12
  rw [ProbabilityTheory.cdf_eq_real, measureReal_def,
    finiteThreeIndicatorLaw_apply_Iic (P := P) x0 x1 x2 x]
  have hx0 : ¬ x0 ≤ x := by linarith
  have hx1 : ¬ x1 ≤ x := by linarith
  have hx2 : ¬ x2 ≤ x := by linarith
  have h0 : ¬ (0 : ℝ) ≤ x := by
    have hxlt0 : x < 0 := lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le hx hx01) hx12) hx20
    linarith
  simp [hx0, hx1, hx2, h0]

private theorem cdf_finiteThreeIndicatorLaw_of_x0_le_lt_x1
    {x0 x1 x2 : ℝ} (hx12 : x1 ≤ x2) (hx20 : x2 ≤ 0)
    {E0 E1 E2 : Set Ω} (hE0 : MeasurableSet E0) (hE1 : MeasurableSet E1) (hE2 : MeasurableSet E2)
    (h01 : Disjoint E0 E1) (h02 : Disjoint E0 E2) (h12 : Disjoint E1 E2)
    {x : ℝ} (hx0 : x0 ≤ x) (hx1 : x < x1) :
    ProbabilityTheory.cdf (finiteThreeIndicatorLaw P x0 x1 x2 E0 E1 E2) x = P.real E0 := by
  haveI : IsProbabilityMeasure (finiteThreeIndicatorLaw P x0 x1 x2 E0 E1 E2) :=
    finiteThreeIndicatorLaw_isProbabilityMeasure (P := P) x0 x1 x2 hE0 hE1 hE2 h01 h02 h12
  rw [ProbabilityTheory.cdf_eq_real, measureReal_def,
    finiteThreeIndicatorLaw_apply_Iic (P := P) x0 x1 x2 x]
  have hx1' : ¬ x1 ≤ x := by linarith
  have hx2' : ¬ x2 ≤ x := by linarith
  have h0 : ¬ (0 : ℝ) ≤ x := by
    have hxlt0 : x < 0 := lt_of_lt_of_le (lt_of_lt_of_le hx1 hx12) hx20
    have : ¬ 0 ≤ x := by linarith
    exact this
  simp [hx0, hx1', hx2', h0, Measure.real]

private theorem cdf_finiteThreeIndicatorLaw_of_x1_le_lt_x2
    {x0 x1 x2 : ℝ} (hx01 : x0 ≤ x1) (hx12 : x1 ≤ x2) (hx20 : x2 ≤ 0)
    {E0 E1 E2 : Set Ω} (hE0 : MeasurableSet E0) (hE1 : MeasurableSet E1) (hE2 : MeasurableSet E2)
    (h01 : Disjoint E0 E1) (h02 : Disjoint E0 E2) (h12 : Disjoint E1 E2)
    {x : ℝ} (hx1 : x1 ≤ x) (hx2 : x < x2) :
    ProbabilityTheory.cdf (finiteThreeIndicatorLaw P x0 x1 x2 E0 E1 E2) x =
      P.real E0 + P.real E1 := by
  haveI : IsProbabilityMeasure (finiteThreeIndicatorLaw P x0 x1 x2 E0 E1 E2) :=
    finiteThreeIndicatorLaw_isProbabilityMeasure (P := P) x0 x1 x2 hE0 hE1 hE2 h01 h02 h12
  rw [ProbabilityTheory.cdf_eq_real, measureReal_def,
    finiteThreeIndicatorLaw_apply_Iic (P := P) x0 x1 x2 x]
  have hx0 : x0 ≤ x := le_trans hx01 hx1
  have hx2' : ¬ x2 ≤ x := by linarith
  have h0 : ¬ (0 : ℝ) ≤ x := by
    have hxlt0 : x < 0 := lt_of_lt_of_le hx2 hx20
    linarith
  have hcalc :
      P E0 • (Set.Iic x).indicator 1 x0 +
        (P E1 • (Set.Iic x).indicator 1 x1 +
          (P E2 • (Set.Iic x).indicator 1 x2 + P (E0 ∪ E1 ∪ E2)ᶜ • (Set.Iic x).indicator 1 0)) =
        P E0 + P E1 := by
    simp [hx0, hx1, hx2', h0]
  rw [hcalc, ENNReal.toReal_add (measure_ne_top P E0) (measure_ne_top P E1)]
  simp [Measure.real]

private theorem cdf_finiteThreeIndicatorLaw_of_x2_le_lt_zero
    {x0 x1 x2 : ℝ} (hx01 : x0 ≤ x1) (hx12 : x1 ≤ x2) (hx20 : x2 ≤ 0)
    {E0 E1 E2 : Set Ω} (hE0 : MeasurableSet E0) (hE1 : MeasurableSet E1) (hE2 : MeasurableSet E2)
    (h01 : Disjoint E0 E1) (h02 : Disjoint E0 E2) (h12 : Disjoint E1 E2)
    {x : ℝ} (hx2 : x2 ≤ x) (hx0 : x < 0) :
    ProbabilityTheory.cdf (finiteThreeIndicatorLaw P x0 x1 x2 E0 E1 E2) x =
      P.real E0 + P.real E1 + P.real E2 := by
  haveI : IsProbabilityMeasure (finiteThreeIndicatorLaw P x0 x1 x2 E0 E1 E2) :=
    finiteThreeIndicatorLaw_isProbabilityMeasure (P := P) x0 x1 x2 hE0 hE1 hE2 h01 h02 h12
  rw [ProbabilityTheory.cdf_eq_real, measureReal_def,
    finiteThreeIndicatorLaw_apply_Iic (P := P) x0 x1 x2 x]
  have hx0' : x0 ≤ x := le_trans hx01 (le_trans hx12 hx2)
  have hx1' : x1 ≤ x := le_trans hx12 hx2
  have h0' : ¬ (0 : ℝ) ≤ x := by linarith
  have hcalc :
      P E0 • (Set.Iic x).indicator 1 x0 +
        (P E1 • (Set.Iic x).indicator 1 x1 +
          (P E2 • (Set.Iic x).indicator 1 x2 + P (E0 ∪ E1 ∪ E2)ᶜ • (Set.Iic x).indicator 1 0)) =
        P E0 + (P E1 + P E2) := by
    simp [hx0', hx1', hx2, h0']
  rw [hcalc, ENNReal.toReal_add (measure_ne_top P E0)
    (ENNReal.add_ne_top.2 ⟨measure_ne_top P E1, measure_ne_top P E2⟩)]
  rw [ENNReal.toReal_add (measure_ne_top P E1) (measure_ne_top P E2)]
  simp [Measure.real, add_assoc, add_left_comm]

private theorem cdf_finiteThreeIndicatorLaw_of_nonneg
    {x0 x1 x2 : ℝ} (hx01 : x0 ≤ x1) (hx12 : x1 ≤ x2) (hx20 : x2 ≤ 0)
    {E0 E1 E2 : Set Ω} (hE0 : MeasurableSet E0) (hE1 : MeasurableSet E1)
    (hE2 : MeasurableSet E2) (h01 : Disjoint E0 E1) (h02 : Disjoint E0 E2) (h12 : Disjoint E1 E2)
    {x : ℝ} (hx : 0 ≤ x) :
    ProbabilityTheory.cdf (finiteThreeIndicatorLaw P x0 x1 x2 E0 E1 E2) x = 1 := by
  haveI : IsProbabilityMeasure (finiteThreeIndicatorLaw P x0 x1 x2 E0 E1 E2) :=
    finiteThreeIndicatorLaw_isProbabilityMeasure (P := P) x0 x1 x2 hE0 hE1 hE2 h01 h02 h12
  rw [ProbabilityTheory.cdf_eq_real, measureReal_def,
    finiteThreeIndicatorLaw_apply_Iic (P := P) x0 x1 x2 x]
  have hx0 : x0 ≤ x := le_trans (le_trans hx01 hx12) (le_trans hx20 hx)
  have hx1 : x1 ≤ x := le_trans hx12 (le_trans hx20 hx)
  have hx2 : x2 ≤ x := le_trans hx20 hx
  have hcalc :
      P E0 • (Set.Iic x).indicator 1 x0 +
        (P E1 • (Set.Iic x).indicator 1 x1 +
          (P E2 • (Set.Iic x).indicator 1 x2 + P (E0 ∪ E1 ∪ E2)ᶜ • (Set.Iic x).indicator 1 0)) =
        P E0 + (P E1 + (P E2 + P (E0 ∪ E1 ∪ E2)ᶜ)) := by
    simp [hx0, hx1, hx2, hx]
  have htoReal :
      ((P E0 + (P E1 + (P E2 + P (E0 ∪ E1 ∪ E2)ᶜ))) : ENNReal).toReal = 1 := by
    have hmass : (P E0 + (P E1 + (P E2 + P (E0 ∪ E1 ∪ E2)ᶜ)) : ENNReal) = 1 := by
      simpa [finiteThreeIndicatorLaw] using
        (show (finiteThreeIndicatorLaw P x0 x1 x2 E0 E1 E2) Set.univ = 1 by
          simpa using (measure_univ (μ := finiteThreeIndicatorLaw P x0 x1 x2 E0 E1 E2)))
    rw [hmass]
    simp
  rw [hcalc]
  exact htoReal

end FiniteThreeIndicatorCDF

section FiniteConvexXFormulas

variable {Ω : Type*} [MeasurableSpace Ω]
variable (P : Measure Ω) [IsProbabilityMeasure P]

theorem distLowerQuantile_finiteConvexX_eq_negM
    {h M a b : ℝ} {E0 E1 E2 : Set Ω}
    (hE0 : MeasurableSet E0) (hE1 : MeasurableSet E1) (hE2 : MeasurableSet E2)
    (h01 : Disjoint E0 E1) (h02 : Disjoint E0 E2) (h12 : Disjoint E1 E2)
    (hh : 0 < h) (h3 : 3 * h < 1)
    (hE0mass : P.real E0 = 1 - 3 * h)
    (hba : b < a) (haM : a < M) (hb : 0 < b)
    {q : ℝ} (hq : q ∈ Set.Ioc (0 : ℝ) (1 - 3 * h)) :
    distLowerQuantile (law P (finiteConvexX P M a b E0 E1 E2 hE0 hE1 hE2)) q = -M := by
  have horder01 : -M ≤ -a := by linarith
  have horder12 : -a ≤ -b := by linarith
  have horder20 : -b ≤ (0 : ℝ) := by linarith
  let μ := finiteThreeIndicatorLaw P (-M) (-a) (-b) E0 E1 E2
  have hμ :
      law P (finiteConvexX P M a b E0 E1 E2 hE0 hE1 hE2) = μ := by
    simpa [μ] using
      law_finiteConvexX_eq_finiteThreeIndicatorLaw (P := P) M a b hE0 hE1 hE2 h01 h02 h12
  haveI : IsProbabilityMeasure μ :=
    finiteThreeIndicatorLaw_isProbabilityMeasure (P := P) (-M) (-a) (-b) hE0 hE1 hE2 h01 h02 h12
  suffices hmain : distLowerQuantile μ q = -M by
    simpa [hμ] using hmain
  let S : Set ℝ := {x : ℝ | q ≤ ProbabilityTheory.cdf μ x}
  change sInf S = -M
  apply le_antisymm
  · refine csInf_le (upperLevelSet_bddBelow μ hq.1) ?_
    change q ≤ ProbabilityTheory.cdf μ (-M)
    have hcdf :
        ProbabilityTheory.cdf μ (-M) = P.real E0 := by
      exact cdf_finiteThreeIndicatorLaw_of_x0_le_lt_x1 (P := P) horder12 horder20
        hE0 hE1 hE2 h01 h02 h12 le_rfl (by linarith [haM])
    rw [hcdf, hE0mass]
    linarith [hq.2]
  · refine le_csInf ?_ ?_
    · exact ⟨-M, by
        change q ≤ ProbabilityTheory.cdf μ (-M)
        have hcdf :
            ProbabilityTheory.cdf μ (-M) = P.real E0 := by
          exact cdf_finiteThreeIndicatorLaw_of_x0_le_lt_x1 (P := P) horder12 horder20
            hE0 hE1 hE2 h01 h02 h12 le_rfl (by linarith [haM])
        rw [hcdf, hE0mass]
        linarith [hq.2]⟩
    · intro x hxS
      by_contra hxlt
      have hxlt' : x < -M := by linarith
      have hxq : q ≤ ProbabilityTheory.cdf μ x := by simpa [S] using hxS
      have hcdf0 :
          ProbabilityTheory.cdf μ x = 0 := by
        exact cdf_finiteThreeIndicatorLaw_of_lt_x0 (P := P) horder01 horder12 horder20
          hE0 hE1 hE2 h01 h02 h12 hxlt'
      have : q ≤ 0 := by simpa [hcdf0] using hxq
      exact (not_le_of_gt hq.1) this

theorem distLowerQuantile_finiteConvexX_eq_nega
    {h M a b : ℝ} {E0 E1 E2 : Set Ω}
    (hE0 : MeasurableSet E0) (hE1 : MeasurableSet E1) (hE2 : MeasurableSet E2)
    (h01 : Disjoint E0 E1) (h02 : Disjoint E0 E2) (h12 : Disjoint E1 E2)
    (hh : 0 < h) (h3 : 3 * h < 1)
    (hE0mass : P.real E0 = 1 - 3 * h) (hE1mass : P.real E1 = h)
    (hba : b < a) (haM : a < M) (hb : 0 < b)
    {q : ℝ} (hq : q ∈ Set.Ioc (1 - 3 * h) (1 - 2 * h)) :
    distLowerQuantile (law P (finiteConvexX P M a b E0 E1 E2 hE0 hE1 hE2)) q = -a := by
  have horder01 : -M ≤ -a := by linarith
  have horder12 : -a ≤ -b := by linarith
  have horder20 : -b ≤ (0 : ℝ) := by linarith
  let μ := finiteThreeIndicatorLaw P (-M) (-a) (-b) E0 E1 E2
  have hμ :
      law P (finiteConvexX P M a b E0 E1 E2 hE0 hE1 hE2) = μ := by
    simpa [μ] using
      law_finiteConvexX_eq_finiteThreeIndicatorLaw (P := P) M a b hE0 hE1 hE2 h01 h02 h12
  haveI : IsProbabilityMeasure μ :=
    finiteThreeIndicatorLaw_isProbabilityMeasure (P := P) (-M) (-a) (-b) hE0 hE1 hE2 h01 h02 h12
  suffices hmain : distLowerQuantile μ q = -a by
    simpa [hμ] using hmain
  let S : Set ℝ := {x : ℝ | q ≤ ProbabilityTheory.cdf μ x}
  change sInf S = -a
  apply le_antisymm
  · refine csInf_le (upperLevelSet_bddBelow μ (by linarith [hh, h3, hq.1])) ?_
    change q ≤ ProbabilityTheory.cdf μ (-a)
    have hcdf :
        ProbabilityTheory.cdf μ (-a) =
          P.real E0 + P.real E1 := by
      exact cdf_finiteThreeIndicatorLaw_of_x1_le_lt_x2 (P := P) horder01 horder12 horder20
        hE0 hE1 hE2 h01 h02 h12 le_rfl (by linarith [hba])
    rw [hcdf, hE0mass, hE1mass]
    linarith [hq.2]
  · refine le_csInf ?_ ?_
    · exact ⟨-a, by
        change q ≤ ProbabilityTheory.cdf μ (-a)
        have hcdf :
            ProbabilityTheory.cdf μ (-a) =
              P.real E0 + P.real E1 := by
          exact cdf_finiteThreeIndicatorLaw_of_x1_le_lt_x2 (P := P) horder01 horder12 horder20
            hE0 hE1 hE2 h01 h02 h12 le_rfl (by linarith [hba])
        rw [hcdf, hE0mass, hE1mass]
        linarith [hq.2]⟩
    · intro x hxS
      by_contra hxlt
      have hxlt' : x < -a := by linarith
      have hxq : q ≤ ProbabilityTheory.cdf μ x := by simpa [S] using hxS
      by_cases hxltM : x < -M
      · have hcdf :
            ProbabilityTheory.cdf μ x = 0 := by
          exact cdf_finiteThreeIndicatorLaw_of_lt_x0 (P := P) horder01 horder12 horder20
            hE0 hE1 hE2 h01 h02 h12 hxltM
        have : q ≤ 0 := by simpa [hcdf] using hxq
        linarith [hq.1]
      · have hxgeM : -M ≤ x := le_of_not_gt hxltM
        have hcdf :
            ProbabilityTheory.cdf μ x =
              P.real E0 := by
          exact cdf_finiteThreeIndicatorLaw_of_x0_le_lt_x1 (P := P) horder12 horder20
            hE0 hE1 hE2 h01 h02 h12 hxgeM hxlt'
        have : q ≤ 1 - 3 * h := by simpa [hcdf, hE0mass] using hxq
        linarith [hq.1]

theorem distLowerQuantile_finiteConvexX_eq_negb
    {h M a b : ℝ} {E0 E1 E2 : Set Ω}
    (hE0 : MeasurableSet E0) (hE1 : MeasurableSet E1) (hE2 : MeasurableSet E2)
    (h01 : Disjoint E0 E1) (h02 : Disjoint E0 E2) (h12 : Disjoint E1 E2)
    (hh : 0 < h) (h3 : 3 * h < 1)
    (hE0mass : P.real E0 = 1 - 3 * h) (hE1mass : P.real E1 = h) (hE2mass : P.real E2 = h)
    (hba : b < a) (haM : a < M) (hb : 0 < b)
    {q : ℝ} (hq : q ∈ Set.Ioc (1 - 2 * h) (1 - h)) :
    distLowerQuantile (law P (finiteConvexX P M a b E0 E1 E2 hE0 hE1 hE2)) q = -b := by
  have horder01 : -M ≤ -a := by linarith
  have horder12 : -a ≤ -b := by linarith
  have horder20 : -b ≤ (0 : ℝ) := by linarith
  let μ := finiteThreeIndicatorLaw P (-M) (-a) (-b) E0 E1 E2
  have hμ :
      law P (finiteConvexX P M a b E0 E1 E2 hE0 hE1 hE2) = μ := by
    simpa [μ] using
      law_finiteConvexX_eq_finiteThreeIndicatorLaw (P := P) M a b hE0 hE1 hE2 h01 h02 h12
  haveI : IsProbabilityMeasure μ :=
    finiteThreeIndicatorLaw_isProbabilityMeasure (P := P) (-M) (-a) (-b) hE0 hE1 hE2 h01 h02 h12
  suffices hmain : distLowerQuantile μ q = -b by
    simpa [hμ] using hmain
  let S : Set ℝ := {x : ℝ | q ≤ ProbabilityTheory.cdf μ x}
  change sInf S = -b
  apply le_antisymm
  · refine csInf_le (upperLevelSet_bddBelow μ (by linarith [hh, h3, hq.1])) ?_
    change q ≤ ProbabilityTheory.cdf μ (-b)
    have hcdf :
        ProbabilityTheory.cdf μ (-b) = P.real E0 + P.real E1 + P.real E2 := by
      exact cdf_finiteThreeIndicatorLaw_of_x2_le_lt_zero (P := P) horder01 horder12 horder20
        hE0 hE1 hE2 h01 h02 h12 le_rfl (by linarith [hb])
    rw [hcdf, hE0mass, hE1mass, hE2mass]
    linarith [hq.2]
  · refine le_csInf ?_ ?_
    · exact ⟨-b, by
        change q ≤ ProbabilityTheory.cdf μ (-b)
        have hcdf :
            ProbabilityTheory.cdf μ (-b) = P.real E0 + P.real E1 + P.real E2 := by
          exact cdf_finiteThreeIndicatorLaw_of_x2_le_lt_zero (P := P) horder01 horder12 horder20
            hE0 hE1 hE2 h01 h02 h12 le_rfl (by linarith [hb])
        rw [hcdf, hE0mass, hE1mass, hE2mass]
        linarith [hq.2]⟩
    · intro x hxS
      by_contra hxlt
      have hxlt' : x < -b := by linarith
      have hxq : q ≤ ProbabilityTheory.cdf μ x := by simpa [S] using hxS
      by_cases hxltM : x < -M
      · have hcdf : ProbabilityTheory.cdf μ x = 0 := by
          exact cdf_finiteThreeIndicatorLaw_of_lt_x0 (P := P) horder01 horder12 horder20
            hE0 hE1 hE2 h01 h02 h12 hxltM
        have : q ≤ 0 := by simpa [hcdf] using hxq
        linarith [hq.1]
      · have hxgeM : -M ≤ x := le_of_not_gt hxltM
        by_cases hxlta : x < -a
        · have hcdf : ProbabilityTheory.cdf μ x = P.real E0 := by
            exact cdf_finiteThreeIndicatorLaw_of_x0_le_lt_x1 (P := P) horder12 horder20
              hE0 hE1 hE2 h01 h02 h12 hxgeM hxlta
          have : q ≤ 1 - 3 * h := by simpa [hcdf, hE0mass] using hxq
          linarith [hq.1]
        · have hxgea : -a ≤ x := le_of_not_gt hxlta
          have hcdf : ProbabilityTheory.cdf μ x = P.real E0 + P.real E1 := by
            exact cdf_finiteThreeIndicatorLaw_of_x1_le_lt_x2 (P := P) horder01 horder12 horder20
              hE0 hE1 hE2 h01 h02 h12 hxgea hxlt'
          have htmp : q ≤ (1 - 3 * h) + h := by simpa [hcdf, hE0mass, hE1mass] using hxq
          have : q ≤ 1 - 2 * h := by linarith
          linarith [hq.1]

theorem distLowerQuantile_finiteConvexX_eq_zero
    {h M a b : ℝ} {E0 E1 E2 : Set Ω}
    (hE0 : MeasurableSet E0) (hE1 : MeasurableSet E1) (hE2 : MeasurableSet E2)
    (h01 : Disjoint E0 E1) (h02 : Disjoint E0 E2) (h12 : Disjoint E1 E2)
    (hh : 0 < h) (h3 : 3 * h < 1)
    (hE0mass : P.real E0 = 1 - 3 * h) (hE1mass : P.real E1 = h) (hE2mass : P.real E2 = h)
    (hba : b < a) (haM : a < M) (hb : 0 < b)
    {q : ℝ} (hq : q ∈ Set.Ioc (1 - h) 1) :
    distLowerQuantile (law P (finiteConvexX P M a b E0 E1 E2 hE0 hE1 hE2)) q = 0 := by
  have horder01 : -M ≤ -a := by linarith
  have horder12 : -a ≤ -b := by linarith
  have horder20 : -b ≤ (0 : ℝ) := by linarith
  let μ := finiteThreeIndicatorLaw P (-M) (-a) (-b) E0 E1 E2
  have hμ :
      law P (finiteConvexX P M a b E0 E1 E2 hE0 hE1 hE2) = μ := by
    simpa [μ] using
      law_finiteConvexX_eq_finiteThreeIndicatorLaw (P := P) M a b hE0 hE1 hE2 h01 h02 h12
  haveI : IsProbabilityMeasure μ :=
    finiteThreeIndicatorLaw_isProbabilityMeasure (P := P) (-M) (-a) (-b) hE0 hE1 hE2 h01 h02 h12
  suffices hmain : distLowerQuantile μ q = 0 by
    simpa [hμ] using hmain
  let S : Set ℝ := {x : ℝ | q ≤ ProbabilityTheory.cdf μ x}
  change sInf S = 0
  apply le_antisymm
  · refine csInf_le (upperLevelSet_bddBelow μ (by linarith [hh, h3, hq.1])) ?_
    change q ≤ ProbabilityTheory.cdf μ 0
    have hcdf : ProbabilityTheory.cdf μ 0 = 1 := by
      exact cdf_finiteThreeIndicatorLaw_of_nonneg (P := P) horder01 horder12 horder20
        hE0 hE1 hE2 h01 h02 h12 le_rfl
    rw [hcdf]
    linarith [hq.2]
  · refine le_csInf ?_ ?_
    · exact ⟨0, by
        change q ≤ ProbabilityTheory.cdf μ 0
        have hcdf : ProbabilityTheory.cdf μ 0 = 1 := by
          exact cdf_finiteThreeIndicatorLaw_of_nonneg (P := P) horder01 horder12 horder20
            hE0 hE1 hE2 h01 h02 h12 le_rfl
        rw [hcdf]
        linarith [hq.2]⟩
    · intro x hxS
      by_contra hxlt
      have hxlt0 : x < 0 := by linarith
      have hxq : q ≤ ProbabilityTheory.cdf μ x := by simpa [S] using hxS
      by_cases hxltM : x < -M
      · have hcdf : ProbabilityTheory.cdf μ x = 0 := by
          exact cdf_finiteThreeIndicatorLaw_of_lt_x0 (P := P) horder01 horder12 horder20
            hE0 hE1 hE2 h01 h02 h12 hxltM
        have : q ≤ 0 := by simpa [hcdf] using hxq
        linarith [hq.1]
      · have hxgeM : -M ≤ x := le_of_not_gt hxltM
        by_cases hxlta : x < -a
        · have hcdf : ProbabilityTheory.cdf μ x = P.real E0 := by
            exact cdf_finiteThreeIndicatorLaw_of_x0_le_lt_x1 (P := P) horder12 horder20
              hE0 hE1 hE2 h01 h02 h12 hxgeM hxlta
          have : q ≤ 1 - 3 * h := by simpa [hcdf, hE0mass] using hxq
          linarith [hq.1]
        · have hxgea : -a ≤ x := le_of_not_gt hxlta
          by_cases hxltb : x < -b
          · have hcdf : ProbabilityTheory.cdf μ x = P.real E0 + P.real E1 := by
              exact cdf_finiteThreeIndicatorLaw_of_x1_le_lt_x2 (P := P) horder01 horder12 horder20
                hE0 hE1 hE2 h01 h02 h12 hxgea hxltb
            have htmp : q ≤ (1 - 3 * h) + h := by
              simpa [hcdf, hE0mass, hE1mass] using hxq
            have : q ≤ 1 - 2 * h := by linarith
            linarith [hq.1]
          · have hxgeb : -b ≤ x := le_of_not_gt hxltb
            have hcdf : ProbabilityTheory.cdf μ x = P.real E0 + P.real E1 + P.real E2 := by
              exact cdf_finiteThreeIndicatorLaw_of_x2_le_lt_zero (P := P) horder01 horder12 horder20
                hE0 hE1 hE2 h01 h02 h12 hxgeb hxlt0
            have htmp : q ≤ (1 - 3 * h) + h + h := by
              simpa [hcdf, hE0mass, hE1mass, hE2mass] using hxq
            have : q ≤ 1 - h := by linarith
            linarith [hq.1]

end FiniteConvexXFormulas

section FiniteConvexXES

variable {Ω : Type*} [MeasurableSpace Ω]
variable (P : Measure Ω) [IsProbabilityMeasure P]

private theorem mem_Ioc_of_mem_uIoc {a b q : ℝ} (hab : a ≤ b) (hq : q ∈ Set.uIoc a b) :
    q ∈ Set.Ioc a b := by
  simpa [Set.uIoc, hab] using hq

theorem ES_finiteConvexX_at_p2
    {h M a b : ℝ} {E0 E1 E2 : Set Ω}
    (hE0 : MeasurableSet E0) (hE1 : MeasurableSet E1) (hE2 : MeasurableSet E2)
    (h01 : Disjoint E0 E1) (h02 : Disjoint E0 E2) (h12 : Disjoint E1 E2)
    (hh : 0 < h) (h3 : 3 * h < 1)
    (hE0mass : P.real E0 = 1 - 3 * h) (hE1mass : P.real E1 = h) (hE2mass : P.real E2 = h)
    (hba : b < a) (haM : a < M) (hb : 0 < b) :
    ES P (finiteLevel2 h hh h3) (finiteConvexX P M a b E0 E1 E2 hE0 hE1 hE2) = 0 := by
  let p2 : Level := finiteLevel2 h hh h3
  have hp2_lt : ((p2 : ℝ) < 1) := by
    simp [p2, hh]
  have hdist :
      distES (law P (finiteConvexX P M a b E0 E1 E2 hE0 hE1 hE2)) p2 =
        (1 - (p2 : ℝ))⁻¹ *
          distESIntegral (law P (finiteConvexX P M a b E0 E1 E2 hE0 hE1 hE2))
            p2 := by
    simpa [distES, hp2_lt]
  have hInt :
      distESIntegral (law P (finiteConvexX P M a b E0 E1 E2 hE0 hE1 hE2))
        p2 = 0 := by
    rw [distESIntegral]
    calc
      ∫ q in (p2 : ℝ)..1,
          distLowerQuantile (law P (finiteConvexX P M a b E0 E1 E2 hE0 hE1 hE2)) q =
        ∫ q in (p2 : ℝ)..1, (0 : ℝ) := by
          refine intervalIntegral.integral_congr_ae ?_
          exact Filter.Eventually.of_forall (fun q hq => by
            have hp2_le : (p2 : ℝ) ≤ 1 := p2.2.2
            have hqIoc : q ∈ Set.Ioc (1 - h) 1 := by
              have hq' : q ∈ Set.Ioc (p2 : ℝ) 1 := by
                simpa [Set.uIoc, hp2_le] using hq
              simpa [p2] using hq'
            exact distLowerQuantile_finiteConvexX_eq_zero (P := P)
              hE0 hE1 hE2 h01 h02 h12 hh h3 hE0mass hE1mass hE2mass hba haM hb hqIoc)
      _ = 0 := by simp
  calc
    ES P p2 (finiteConvexX P M a b E0 E1 E2 hE0 hE1 hE2) =
        distES (law P (finiteConvexX P M a b E0 E1 E2 hE0 hE1 hE2)) p2 := rfl
    _ = (1 - (p2 : ℝ))⁻¹ *
          distESIntegral (law P (finiteConvexX P M a b E0 E1 E2 hE0 hE1 hE2))
            p2 := hdist
    _ = 0 := by rw [hInt]; simp

theorem ES_finiteConvexX_at_p1
    {h M a b : ℝ} {E0 E1 E2 : Set Ω}
    (hE0 : MeasurableSet E0) (hE1 : MeasurableSet E1) (hE2 : MeasurableSet E2)
    (h01 : Disjoint E0 E1) (h02 : Disjoint E0 E2) (h12 : Disjoint E1 E2)
    (hh : 0 < h) (h3 : 3 * h < 1)
    (hE0mass : P.real E0 = 1 - 3 * h) (hE1mass : P.real E1 = h) (hE2mass : P.real E2 = h)
    (hba : b < a) (haM : a < M) (hb : 0 < b) :
    ES P (finiteLevel1 h hh h3) (finiteConvexX P M a b E0 E1 E2 hE0 hE1 hE2) = -b / 2 := by
  let p1 : Level := finiteLevel1 h hh h3
  let p2 : Level := finiteLevel2 h hh h3
  let X : RandomVariable P := finiteConvexX P M a b E0 E1 E2 hE0 hE1 hE2
  have hp1_lt : (p1 : ℝ) < 1 := by simp [p1, hh]
  have hdist :
      distES (law P X) p1 = (1 - (p1 : ℝ))⁻¹ * distESIntegral (law P X) p1 := by
    simpa [distES, hp1_lt]
  have hp1_le_p2 : (p1 : ℝ) ≤ (p2 : ℝ) := by
    simp [p1, p2]
    linarith
  have hfi12 : IntervalIntegrable (distLowerQuantile (law P X)) volume (p1 : ℝ) (p2 : ℝ) := by
    refine (intervalIntegrable_const : IntervalIntegrable (fun _ => (-b : ℝ)) volume (p1 : ℝ) (p2 : ℝ)).congr ?_
    intro q hq
    have hqIoc : q ∈ Set.Ioc (1 - 2 * h) (1 - h) := by
      have hq' : q ∈ Set.Ioc (p1 : ℝ) (p2 : ℝ) := by
        simpa [Set.uIoc, hp1_le_p2] using hq
      simpa [p1, p2] using hq'
    symm
    exact distLowerQuantile_finiteConvexX_eq_negb (P := P)
      hE0 hE1 hE2 h01 h02 h12 hh h3 hE0mass hE1mass hE2mass hba haM hb hqIoc
  have hfi23 : IntervalIntegrable (distLowerQuantile (law P X)) volume (p2 : ℝ) 1 := by
    refine (intervalIntegrable_const : IntervalIntegrable (fun _ => (0 : ℝ)) volume (p2 : ℝ) 1).congr ?_
    intro q hq
    have hp2_le : (p2 : ℝ) ≤ 1 := p2.2.2
    have hqIoc : q ∈ Set.Ioc (1 - h) 1 := by
      have hq' : q ∈ Set.Ioc (p2 : ℝ) 1 := by
        simpa [Set.uIoc, hp2_le] using hq
      simpa [p2] using hq'
    symm
    exact distLowerQuantile_finiteConvexX_eq_zero (P := P)
      hE0 hE1 hE2 h01 h02 h12 hh h3 hE0mass hE1mass hE2mass hba haM hb hqIoc
  have hsplitInt :
      ∫ x in (p1 : ℝ)..1, distLowerQuantile (law P X) x =
        (∫ x in (p1 : ℝ)..(p2 : ℝ), distLowerQuantile (law P X) x) +
          ∫ x in (p2 : ℝ)..1, distLowerQuantile (law P X) x := by
    simpa using (intervalIntegral.integral_add_adjacent_intervals hfi12 hfi23).symm
  have h12int :
      ∫ q in (p1 : ℝ)..(p2 : ℝ), distLowerQuantile (law P X) q = -b * h := by
    calc
      ∫ q in (p1 : ℝ)..(p2 : ℝ), distLowerQuantile (law P X) q =
        ∫ q in (p1 : ℝ)..(p2 : ℝ), (-b : ℝ) := by
          refine intervalIntegral.integral_congr_ae ?_
          exact Filter.Eventually.of_forall (fun q hq => by
            have hqIoc : q ∈ Set.Ioc (1 - 2 * h) (1 - h) := by
              have hq' : q ∈ Set.Ioc (p1 : ℝ) (p2 : ℝ) := by
                simpa [Set.uIoc, hp1_le_p2] using hq
              simpa [p1, p2] using hq'
            exact distLowerQuantile_finiteConvexX_eq_negb (P := P)
              hE0 hE1 hE2 h01 h02 h12 hh h3 hE0mass hE1mass hE2mass hba haM hb hqIoc)
      _ = ((p2 : ℝ) - (p1 : ℝ)) * (-b) := by simp [intervalIntegral.integral_const]
      _ = -b * h := by
        simp [p1, p2]
        ring
  have h23int :
      ∫ q in (p2 : ℝ)..1, distLowerQuantile (law P X) q = 0 := by
    calc
      ∫ q in (p2 : ℝ)..1, distLowerQuantile (law P X) q =
        ∫ q in (p2 : ℝ)..1, (0 : ℝ) := by
          refine intervalIntegral.integral_congr_ae ?_
          exact Filter.Eventually.of_forall (fun q hq => by
            have hp2_le : (p2 : ℝ) ≤ 1 := p2.2.2
            have hqIoc : q ∈ Set.Ioc (1 - h) 1 := by
              have hq' : q ∈ Set.Ioc (p2 : ℝ) 1 := by
                simpa [Set.uIoc, hp2_le] using hq
              simpa [p2] using hq'
            exact distLowerQuantile_finiteConvexX_eq_zero (P := P)
              hE0 hE1 hE2 h01 h02 h12 hh h3 hE0mass hE1mass hE2mass hba haM hb hqIoc)
      _ = 0 := by simp
  have hsum :
      (∫ x in (p1 : ℝ)..(p2 : ℝ), distLowerQuantile (law P X) x) +
          ∫ x in (p2 : ℝ)..1, distLowerQuantile (law P X) x =
        -(b * h) := by
    simpa [h12int, h23int]
  calc
    ES P p1 X = distES (law P X) p1 := rfl
    _ = (1 - (p1 : ℝ))⁻¹ * distESIntegral (law P X) p1 := hdist
    _ = (1 - (p1 : ℝ))⁻¹ *
        ((∫ x in (p1 : ℝ)..(p2 : ℝ), distLowerQuantile (law P X) x) +
          ∫ x in (p2 : ℝ)..1, distLowerQuantile (law P X) x) := by
      rw [distESIntegral, hsplitInt]
    _ = (1 - (p1 : ℝ))⁻¹ * (-(b * h)) := by
      exact congrArg (fun z => (1 - (p1 : ℝ))⁻¹ * z) hsum
    _ = -b / 2 := by
      have hp1_eq : (p1 : ℝ) = 1 - 2 * h := by simp [p1]
      rw [hp1_eq]
      field_simp [show h ≠ 0 by linarith]
      ring

theorem ES_finiteConvexX_at_p0
    {h M a b : ℝ} {E0 E1 E2 : Set Ω}
    (hE0 : MeasurableSet E0) (hE1 : MeasurableSet E1) (hE2 : MeasurableSet E2)
    (h01 : Disjoint E0 E1) (h02 : Disjoint E0 E2) (h12 : Disjoint E1 E2)
    (hh : 0 < h) (h3 : 3 * h < 1)
    (hE0mass : P.real E0 = 1 - 3 * h) (hE1mass : P.real E1 = h) (hE2mass : P.real E2 = h)
    (hba : b < a) (haM : a < M) (hb : 0 < b) :
    ES P (finiteLevel0 h hh h3) (finiteConvexX P M a b E0 E1 E2 hE0 hE1 hE2) = -(a + b) / 3 := by
  let p0 : Level := finiteLevel0 h hh h3
  let p1 : Level := finiteLevel1 h hh h3
  let p2 : Level := finiteLevel2 h hh h3
  let X : RandomVariable P := finiteConvexX P M a b E0 E1 E2 hE0 hE1 hE2
  have hp0_lt : (p0 : ℝ) < 1 := by simp [p0, hh]
  have hdist :
      distES (law P X) p0 = (1 - (p0 : ℝ))⁻¹ * distESIntegral (law P X) p0 := by
    simpa [distES, hp0_lt]
  have hp0_le_p1 : (p0 : ℝ) ≤ (p1 : ℝ) := by
    simp [p0, p1]
    linarith
  have hp1_le_p2 : (p1 : ℝ) ≤ (p2 : ℝ) := by
    simp [p1, p2]
    linarith
  have hfi01 : IntervalIntegrable (distLowerQuantile (law P X)) volume (p0 : ℝ) (p1 : ℝ) := by
    refine (intervalIntegrable_const : IntervalIntegrable (fun _ => (-a : ℝ)) volume (p0 : ℝ) (p1 : ℝ)).congr ?_
    intro q hq
    have hqIoc : q ∈ Set.Ioc (1 - 3 * h) (1 - 2 * h) := by
      have hq' : q ∈ Set.Ioc (p0 : ℝ) (p1 : ℝ) := by
        simpa [Set.uIoc, hp0_le_p1] using hq
      simpa [p0, p1] using hq'
    symm
    exact distLowerQuantile_finiteConvexX_eq_nega (P := P)
      hE0 hE1 hE2 h01 h02 h12 hh h3 hE0mass hE1mass hba haM hb hqIoc
  have hfi12 : IntervalIntegrable (distLowerQuantile (law P X)) volume (p1 : ℝ) (p2 : ℝ) := by
    refine (intervalIntegrable_const : IntervalIntegrable (fun _ => (-b : ℝ)) volume (p1 : ℝ) (p2 : ℝ)).congr ?_
    intro q hq
    have hqIoc : q ∈ Set.Ioc (1 - 2 * h) (1 - h) := by
      have hq' : q ∈ Set.Ioc (p1 : ℝ) (p2 : ℝ) := by
        simpa [Set.uIoc, hp1_le_p2] using hq
      simpa [p1, p2] using hq'
    symm
    exact distLowerQuantile_finiteConvexX_eq_negb (P := P)
      hE0 hE1 hE2 h01 h02 h12 hh h3 hE0mass hE1mass hE2mass hba haM hb hqIoc
  have hfi23 : IntervalIntegrable (distLowerQuantile (law P X)) volume (p2 : ℝ) 1 := by
    refine (intervalIntegrable_const : IntervalIntegrable (fun _ => (0 : ℝ)) volume (p2 : ℝ) 1).congr ?_
    intro q hq
    have hp2_le : (p2 : ℝ) ≤ 1 := p2.2.2
    have hqIoc : q ∈ Set.Ioc (1 - h) 1 := by
      have hq' : q ∈ Set.Ioc (p2 : ℝ) 1 := by
        simpa [Set.uIoc, hp2_le] using hq
      simpa [p2] using hq'
    symm
    exact distLowerQuantile_finiteConvexX_eq_zero (P := P)
      hE0 hE1 hE2 h01 h02 h12 hh h3 hE0mass hE1mass hE2mass hba haM hb hqIoc
  have hfi02 : IntervalIntegrable (distLowerQuantile (law P X)) volume (p0 : ℝ) (p2 : ℝ) := by
    exact hfi01.trans hfi12
  have hsplit01 :
      ∫ x in (p0 : ℝ)..(p2 : ℝ), distLowerQuantile (law P X) x =
        (∫ x in (p0 : ℝ)..(p1 : ℝ), distLowerQuantile (law P X) x) +
          ∫ x in (p1 : ℝ)..(p2 : ℝ), distLowerQuantile (law P X) x := by
    simpa using (intervalIntegral.integral_add_adjacent_intervals hfi01 hfi12).symm
  have hsplit :
      ∫ x in (p0 : ℝ)..1, distLowerQuantile (law P X) x =
        (∫ x in (p0 : ℝ)..(p1 : ℝ), distLowerQuantile (law P X) x) +
          ((∫ x in (p1 : ℝ)..(p2 : ℝ), distLowerQuantile (law P X) x) +
            ∫ x in (p2 : ℝ)..1, distLowerQuantile (law P X) x) := by
    calc
      ∫ x in (p0 : ℝ)..1, distLowerQuantile (law P X) x =
          (∫ x in (p0 : ℝ)..(p2 : ℝ), distLowerQuantile (law P X) x) +
            ∫ x in (p2 : ℝ)..1, distLowerQuantile (law P X) x := by
        simpa using (intervalIntegral.integral_add_adjacent_intervals hfi02 hfi23).symm
      _ = (∫ x in (p0 : ℝ)..(p1 : ℝ), distLowerQuantile (law P X) x) +
            ((∫ x in (p1 : ℝ)..(p2 : ℝ), distLowerQuantile (law P X) x) +
              ∫ x in (p2 : ℝ)..1, distLowerQuantile (law P X) x) := by
        rw [hsplit01]
        ring
  have h01int :
      ∫ q in (p0 : ℝ)..(p1 : ℝ), distLowerQuantile (law P X) q = -a * h := by
    calc
      ∫ q in (p0 : ℝ)..(p1 : ℝ), distLowerQuantile (law P X) q =
        ∫ q in (p0 : ℝ)..(p1 : ℝ), (-a : ℝ) := by
          refine intervalIntegral.integral_congr_ae ?_
          exact Filter.Eventually.of_forall (fun q hq => by
            have hqIoc : q ∈ Set.Ioc (1 - 3 * h) (1 - 2 * h) := by
              have hq' : q ∈ Set.Ioc (p0 : ℝ) (p1 : ℝ) := by
                simpa [Set.uIoc, hp0_le_p1] using hq
              simpa [p0, p1] using hq'
            exact distLowerQuantile_finiteConvexX_eq_nega (P := P)
              hE0 hE1 hE2 h01 h02 h12 hh h3 hE0mass hE1mass hba haM hb hqIoc)
      _ = ((p1 : ℝ) - (p0 : ℝ)) * (-a) := by simp [intervalIntegral.integral_const]
      _ = -a * h := by
        simp [p0, p1]
        ring
  have h12int :
      ∫ q in (p1 : ℝ)..(p2 : ℝ), distLowerQuantile (law P X) q = -b * h := by
    calc
      ∫ q in (p1 : ℝ)..(p2 : ℝ), distLowerQuantile (law P X) q =
        ∫ q in (p1 : ℝ)..(p2 : ℝ), (-b : ℝ) := by
          refine intervalIntegral.integral_congr_ae ?_
          exact Filter.Eventually.of_forall (fun q hq => by
            have hqIoc : q ∈ Set.Ioc (1 - 2 * h) (1 - h) := by
              have hq' : q ∈ Set.Ioc (p1 : ℝ) (p2 : ℝ) := by
                simpa [Set.uIoc, hp1_le_p2] using hq
              simpa [p1, p2] using hq'
            exact distLowerQuantile_finiteConvexX_eq_negb (P := P)
              hE0 hE1 hE2 h01 h02 h12 hh h3 hE0mass hE1mass hE2mass hba haM hb hqIoc)
      _ = ((p2 : ℝ) - (p1 : ℝ)) * (-b) := by simp [intervalIntegral.integral_const]
      _ = -b * h := by
        simp [p1, p2]
        ring
  have h23int :
      ∫ q in (p2 : ℝ)..1, distLowerQuantile (law P X) q = 0 := by
    calc
      ∫ q in (p2 : ℝ)..1, distLowerQuantile (law P X) q =
        ∫ q in (p2 : ℝ)..1, (0 : ℝ) := by
          refine intervalIntegral.integral_congr_ae ?_
          exact Filter.Eventually.of_forall (fun q hq => by
            have hp2_le : (p2 : ℝ) ≤ 1 := p2.2.2
            have hqIoc : q ∈ Set.Ioc (1 - h) 1 := by
              have hq' : q ∈ Set.Ioc (p2 : ℝ) 1 := by
                simpa [Set.uIoc, hp2_le] using hq
              simpa [p2] using hq'
            exact distLowerQuantile_finiteConvexX_eq_zero (P := P)
              hE0 hE1 hE2 h01 h02 h12 hh h3 hE0mass hE1mass hE2mass hba haM hb hqIoc)
      _ = 0 := by simp
  have hsum :
      (∫ x in (p0 : ℝ)..(p1 : ℝ), distLowerQuantile (law P X) x) +
          ((∫ x in (p1 : ℝ)..(p2 : ℝ), distLowerQuantile (law P X) x) +
            ∫ x in (p2 : ℝ)..1, distLowerQuantile (law P X) x) =
        -((a + b) * h) := by
    rw [h01int, h12int, h23int]
    ring
  calc
    ES P p0 X = distES (law P X) p0 := rfl
    _ = (1 - (p0 : ℝ))⁻¹ * distESIntegral (law P X) p0 := hdist
    _ = (1 - (p0 : ℝ))⁻¹ *
        ((∫ x in (p0 : ℝ)..(p1 : ℝ), distLowerQuantile (law P X) x) +
          ((∫ x in (p1 : ℝ)..(p2 : ℝ), distLowerQuantile (law P X) x) +
            ∫ x in (p2 : ℝ)..1, distLowerQuantile (law P X) x)) := by
      rw [distESIntegral, hsplit]
    _ = (1 - (p0 : ℝ))⁻¹ * (-((a + b) * h)) := by
      exact congrArg (fun z => (1 - (p0 : ℝ))⁻¹ * z) hsum
    _ = -(a + b) / 3 := by
      have hp0_eq : (p0 : ℝ) = 1 - 3 * h := by simp [p0]
      rw [hp0_eq]
      field_simp [show h ≠ 0 by linarith]
      ring

theorem ES_finiteConvexX_formula_on_Icc_p1_p2
    {h M a b : ℝ} {E0 E1 E2 : Set Ω} {p : Level}
    (hE0 : MeasurableSet E0) (hE1 : MeasurableSet E1) (hE2 : MeasurableSet E2)
    (h01 : Disjoint E0 E1) (h02 : Disjoint E0 E2) (h12 : Disjoint E1 E2)
    (hh : 0 < h) (h3 : 3 * h < 1)
    (hE0mass : P.real E0 = 1 - 3 * h) (hE1mass : P.real E1 = h) (hE2mass : P.real E2 = h)
    (hba : b < a) (haM : a < M) (hb : 0 < b)
    (hp1 : 1 - 2 * h ≤ (p : ℝ)) (hp2 : (p : ℝ) ≤ 1 - h) :
    ES P p (finiteConvexX P M a b E0 E1 E2 hE0 hE1 hE2) =
      -b * ((1 - h) - (p : ℝ)) / (1 - (p : ℝ)) := by
  let p2 : Level := finiteLevel2 h hh h3
  let X : RandomVariable P := finiteConvexX P M a b E0 E1 E2 hE0 hE1 hE2
  have hp_lt : (p : ℝ) < 1 := by linarith [hp2, hh]
  have hdist :
      distES (law P X) p = (1 - (p : ℝ))⁻¹ * distESIntegral (law P X) p := by
    simpa [distES, hp_lt]
  have hp_le_p2 : (p : ℝ) ≤ (p2 : ℝ) := by simpa [p2] using hp2
  have hfi12 : IntervalIntegrable (distLowerQuantile (law P X)) volume (p : ℝ) (p2 : ℝ) := by
    refine (intervalIntegrable_const : IntervalIntegrable (fun _ => (-b : ℝ)) volume (p : ℝ) (p2 : ℝ)).congr ?_
    intro q hq
    have hqIoc : q ∈ Set.Ioc (1 - 2 * h) (1 - h) := by
      have hq' : q ∈ Set.Ioc (p : ℝ) (p2 : ℝ) := by
        simpa [Set.uIoc, hp_le_p2] using hq
      exact ⟨lt_of_le_of_lt hp1 hq'.1, by simpa [p2] using hq'.2⟩
    symm
    exact distLowerQuantile_finiteConvexX_eq_negb (P := P)
      hE0 hE1 hE2 h01 h02 h12 hh h3 hE0mass hE1mass hE2mass hba haM hb hqIoc
  have hfi23 : IntervalIntegrable (distLowerQuantile (law P X)) volume (p2 : ℝ) 1 := by
    refine (intervalIntegrable_const : IntervalIntegrable (fun _ => (0 : ℝ)) volume (p2 : ℝ) 1).congr ?_
    intro q hq
    have hp2_le : (p2 : ℝ) ≤ 1 := p2.2.2
    have hqIoc : q ∈ Set.Ioc (1 - h) 1 := by
      have hq' : q ∈ Set.Ioc (p2 : ℝ) 1 := by
        simpa [Set.uIoc, hp2_le] using hq
      simpa [p2] using hq'
    symm
    exact distLowerQuantile_finiteConvexX_eq_zero (P := P)
      hE0 hE1 hE2 h01 h02 h12 hh h3 hE0mass hE1mass hE2mass hba haM hb hqIoc
  have hsplit :
      ∫ x in (p : ℝ)..1, distLowerQuantile (law P X) x =
        (∫ x in (p : ℝ)..(p2 : ℝ), distLowerQuantile (law P X) x) +
          ∫ x in (p2 : ℝ)..1, distLowerQuantile (law P X) x := by
    simpa using (intervalIntegral.integral_add_adjacent_intervals hfi12 hfi23).symm
  have h12int :
      ∫ q in (p : ℝ)..(p2 : ℝ), distLowerQuantile (law P X) q = ((p2 : ℝ) - (p : ℝ)) * (-b) := by
    calc
      ∫ q in (p : ℝ)..(p2 : ℝ), distLowerQuantile (law P X) q =
        ∫ q in (p : ℝ)..(p2 : ℝ), (-b : ℝ) := by
          refine intervalIntegral.integral_congr_ae ?_
          exact Filter.Eventually.of_forall (fun q hq => by
            have hqIoc : q ∈ Set.Ioc (1 - 2 * h) (1 - h) := by
              have hq' : q ∈ Set.Ioc (p : ℝ) (p2 : ℝ) := by
                simpa [Set.uIoc, hp_le_p2] using hq
              exact ⟨lt_of_le_of_lt hp1 hq'.1, by simpa [p2] using hq'.2⟩
            exact distLowerQuantile_finiteConvexX_eq_negb (P := P)
              hE0 hE1 hE2 h01 h02 h12 hh h3 hE0mass hE1mass hE2mass hba haM hb hqIoc)
      _ = ((p2 : ℝ) - (p : ℝ)) * (-b) := by simp [intervalIntegral.integral_const]
  have h23int :
      ∫ q in (p2 : ℝ)..1, distLowerQuantile (law P X) q = 0 := by
    calc
      ∫ q in (p2 : ℝ)..1, distLowerQuantile (law P X) q =
        ∫ q in (p2 : ℝ)..1, (0 : ℝ) := by
          refine intervalIntegral.integral_congr_ae ?_
          exact Filter.Eventually.of_forall (fun q hq => by
            have hp2_le : (p2 : ℝ) ≤ 1 := p2.2.2
            have hqIoc : q ∈ Set.Ioc (1 - h) 1 := by
              have hq' : q ∈ Set.Ioc (p2 : ℝ) 1 := by
                simpa [Set.uIoc, hp2_le] using hq
              simpa [p2] using hq'
            exact distLowerQuantile_finiteConvexX_eq_zero (P := P)
              hE0 hE1 hE2 h01 h02 h12 hh h3 hE0mass hE1mass hE2mass hba haM hb hqIoc)
      _ = 0 := by simp
  calc
    ES P p X = distES (law P X) p := rfl
    _ = (1 - (p : ℝ))⁻¹ * distESIntegral (law P X) p := hdist
    _ = (1 - (p : ℝ))⁻¹ *
        ((∫ x in (p : ℝ)..(p2 : ℝ), distLowerQuantile (law P X) x) +
          ∫ x in (p2 : ℝ)..1, distLowerQuantile (law P X) x) := by
      rw [distESIntegral, hsplit]
    _ = (1 - (p : ℝ))⁻¹ * (((p2 : ℝ) - (p : ℝ)) * (-b)) := by
      rw [h12int, h23int, add_zero]
    _ = -b * ((1 - h) - (p : ℝ)) / (1 - (p : ℝ)) := by
      have hp_ne : (1 - (p : ℝ)) ≠ 0 := by linarith
      have hp2_eq : (p2 : ℝ) = 1 - h := by simp [p2]
      rw [hp2_eq]
      field_simp [hp_ne]

theorem ES_finiteConvexX_formula_on_Icc_p0_p1
    {h M a b : ℝ} {E0 E1 E2 : Set Ω} {p : Level}
    (hE0 : MeasurableSet E0) (hE1 : MeasurableSet E1) (hE2 : MeasurableSet E2)
    (h01 : Disjoint E0 E1) (h02 : Disjoint E0 E2) (h12 : Disjoint E1 E2)
    (hh : 0 < h) (h3 : 3 * h < 1)
    (hE0mass : P.real E0 = 1 - 3 * h) (hE1mass : P.real E1 = h) (hE2mass : P.real E2 = h)
    (hba : b < a) (haM : a < M) (hb : 0 < b)
    (hp0 : 1 - 3 * h ≤ (p : ℝ)) (hp1 : (p : ℝ) ≤ 1 - 2 * h) :
    ES P p (finiteConvexX P M a b E0 E1 E2 hE0 hE1 hE2) =
      (-a * ((1 - 2 * h) - (p : ℝ)) - b * h) / (1 - (p : ℝ)) := by
  let p1 : Level := finiteLevel1 h hh h3
  let p2 : Level := finiteLevel2 h hh h3
  let X : RandomVariable P := finiteConvexX P M a b E0 E1 E2 hE0 hE1 hE2
  have hp_lt : (p : ℝ) < 1 := by linarith [hp1, hh]
  have hdist :
      distES (law P X) p = (1 - (p : ℝ))⁻¹ * distESIntegral (law P X) p := by
    simpa [distES, hp_lt]
  have hp_le_p1 : (p : ℝ) ≤ (p1 : ℝ) := by simpa [p1] using hp1
  have hp1_le_p2 : (p1 : ℝ) ≤ (p2 : ℝ) := by simp [p1, p2]; linarith
  have hfi01 : IntervalIntegrable (distLowerQuantile (law P X)) volume (p : ℝ) (p1 : ℝ) := by
    refine (intervalIntegrable_const : IntervalIntegrable (fun _ => (-a : ℝ)) volume (p : ℝ) (p1 : ℝ)).congr ?_
    intro q hq
    have hqIoc : q ∈ Set.Ioc (1 - 3 * h) (1 - 2 * h) := by
      have hq' : q ∈ Set.Ioc (p : ℝ) (p1 : ℝ) := by
        simpa [Set.uIoc, hp_le_p1] using hq
      exact ⟨lt_of_le_of_lt hp0 hq'.1, by simpa [p1] using hq'.2⟩
    symm
    exact distLowerQuantile_finiteConvexX_eq_nega (P := P)
      hE0 hE1 hE2 h01 h02 h12 hh h3 hE0mass hE1mass hba haM hb hqIoc
  have hfi12 : IntervalIntegrable (distLowerQuantile (law P X)) volume (p1 : ℝ) (p2 : ℝ) := by
    refine (intervalIntegrable_const : IntervalIntegrable (fun _ => (-b : ℝ)) volume (p1 : ℝ) (p2 : ℝ)).congr ?_
    intro q hq
    have hqIoc : q ∈ Set.Ioc (1 - 2 * h) (1 - h) := by
      have hq' : q ∈ Set.Ioc (p1 : ℝ) (p2 : ℝ) := by
        simpa [Set.uIoc, hp1_le_p2] using hq
      simpa [p1, p2] using hq'
    symm
    exact distLowerQuantile_finiteConvexX_eq_negb (P := P)
      hE0 hE1 hE2 h01 h02 h12 hh h3 hE0mass hE1mass hE2mass hba haM hb hqIoc
  have hfi23 : IntervalIntegrable (distLowerQuantile (law P X)) volume (p2 : ℝ) 1 := by
    refine (intervalIntegrable_const : IntervalIntegrable (fun _ => (0 : ℝ)) volume (p2 : ℝ) 1).congr ?_
    intro q hq
    have hp2_le : (p2 : ℝ) ≤ 1 := p2.2.2
    have hqIoc : q ∈ Set.Ioc (1 - h) 1 := by
      have hq' : q ∈ Set.Ioc (p2 : ℝ) 1 := by
        simpa [Set.uIoc, hp2_le] using hq
      simpa [p2] using hq'
    symm
    exact distLowerQuantile_finiteConvexX_eq_zero (P := P)
      hE0 hE1 hE2 h01 h02 h12 hh h3 hE0mass hE1mass hE2mass hba haM hb hqIoc
  have hfi02 : IntervalIntegrable (distLowerQuantile (law P X)) volume (p : ℝ) (p2 : ℝ) := by
    exact hfi01.trans hfi12
  have hsplit01 :
      ∫ x in (p : ℝ)..(p2 : ℝ), distLowerQuantile (law P X) x =
        (∫ x in (p : ℝ)..(p1 : ℝ), distLowerQuantile (law P X) x) +
          ∫ x in (p1 : ℝ)..(p2 : ℝ), distLowerQuantile (law P X) x := by
    simpa using (intervalIntegral.integral_add_adjacent_intervals hfi01 hfi12).symm
  have hsplit :
      ∫ x in (p : ℝ)..1, distLowerQuantile (law P X) x =
        (∫ x in (p : ℝ)..(p1 : ℝ), distLowerQuantile (law P X) x) +
          ((∫ x in (p1 : ℝ)..(p2 : ℝ), distLowerQuantile (law P X) x) +
            ∫ x in (p2 : ℝ)..1, distLowerQuantile (law P X) x) := by
    calc
      ∫ x in (p : ℝ)..1, distLowerQuantile (law P X) x =
          (∫ x in (p : ℝ)..(p2 : ℝ), distLowerQuantile (law P X) x) +
            ∫ x in (p2 : ℝ)..1, distLowerQuantile (law P X) x := by
        simpa using (intervalIntegral.integral_add_adjacent_intervals hfi02 hfi23).symm
      _ = (∫ x in (p : ℝ)..(p1 : ℝ), distLowerQuantile (law P X) x) +
            ((∫ x in (p1 : ℝ)..(p2 : ℝ), distLowerQuantile (law P X) x) +
              ∫ x in (p2 : ℝ)..1, distLowerQuantile (law P X) x) := by
        rw [hsplit01]
        ring
  have h01int :
      ∫ q in (p : ℝ)..(p1 : ℝ), distLowerQuantile (law P X) q = ((p1 : ℝ) - (p : ℝ)) * (-a) := by
    calc
      ∫ q in (p : ℝ)..(p1 : ℝ), distLowerQuantile (law P X) q =
        ∫ q in (p : ℝ)..(p1 : ℝ), (-a : ℝ) := by
          refine intervalIntegral.integral_congr_ae ?_
          exact Filter.Eventually.of_forall (fun q hq => by
            have hqIoc : q ∈ Set.Ioc (1 - 3 * h) (1 - 2 * h) := by
              have hq' : q ∈ Set.Ioc (p : ℝ) (p1 : ℝ) := by
                simpa [Set.uIoc, hp_le_p1] using hq
              exact ⟨lt_of_le_of_lt hp0 hq'.1, by simpa [p1] using hq'.2⟩
            exact distLowerQuantile_finiteConvexX_eq_nega (P := P)
              hE0 hE1 hE2 h01 h02 h12 hh h3 hE0mass hE1mass hba haM hb hqIoc)
      _ = ((p1 : ℝ) - (p : ℝ)) * (-a) := by simp [intervalIntegral.integral_const]
  have h12int :
      ∫ q in (p1 : ℝ)..(p2 : ℝ), distLowerQuantile (law P X) q = -b * h := by
    calc
      ∫ q in (p1 : ℝ)..(p2 : ℝ), distLowerQuantile (law P X) q =
        ∫ q in (p1 : ℝ)..(p2 : ℝ), (-b : ℝ) := by
          refine intervalIntegral.integral_congr_ae ?_
          exact Filter.Eventually.of_forall (fun q hq => by
            have hqIoc : q ∈ Set.Ioc (1 - 2 * h) (1 - h) := by
              have hq' : q ∈ Set.Ioc (p1 : ℝ) (p2 : ℝ) := by
                simpa [Set.uIoc, hp1_le_p2] using hq
              simpa [p1, p2] using hq'
            exact distLowerQuantile_finiteConvexX_eq_negb (P := P)
              hE0 hE1 hE2 h01 h02 h12 hh h3 hE0mass hE1mass hE2mass hba haM hb hqIoc)
      _ = ((p2 : ℝ) - (p1 : ℝ)) * (-b) := by simp [intervalIntegral.integral_const]
      _ = -b * h := by
        simp [p1, p2]
        ring
  have h23int :
      ∫ q in (p2 : ℝ)..1, distLowerQuantile (law P X) q = 0 := by
    calc
      ∫ q in (p2 : ℝ)..1, distLowerQuantile (law P X) q =
        ∫ q in (p2 : ℝ)..1, (0 : ℝ) := by
          refine intervalIntegral.integral_congr_ae ?_
          exact Filter.Eventually.of_forall (fun q hq => by
            have hp2_le : (p2 : ℝ) ≤ 1 := p2.2.2
            have hqIoc : q ∈ Set.Ioc (1 - h) 1 := by
              have hq' : q ∈ Set.Ioc (p2 : ℝ) 1 := by
                simpa [Set.uIoc, hp2_le] using hq
              simpa [p2] using hq'
            exact distLowerQuantile_finiteConvexX_eq_zero (P := P)
              hE0 hE1 hE2 h01 h02 h12 hh h3 hE0mass hE1mass hE2mass hba haM hb hqIoc)
      _ = 0 := by simp
  calc
    ES P p X = distES (law P X) p := rfl
    _ = (1 - (p : ℝ))⁻¹ * distESIntegral (law P X) p := hdist
    _ = (1 - (p : ℝ))⁻¹ *
        ((∫ x in (p : ℝ)..(p1 : ℝ), distLowerQuantile (law P X) x) +
          ((∫ x in (p1 : ℝ)..(p2 : ℝ), distLowerQuantile (law P X) x) +
            ∫ x in (p2 : ℝ)..1, distLowerQuantile (law P X) x)) := by
      rw [distESIntegral, hsplit]
    _ = (1 - (p : ℝ))⁻¹ * (((p1 : ℝ) - (p : ℝ)) * (-a) + (-b * h)) := by
      rw [h01int, h12int, h23int]
      ring
    _ = (-a * ((1 - 2 * h) - (p : ℝ)) - b * h) / (1 - (p : ℝ)) := by
      have hp_ne : (1 - (p : ℝ)) ≠ 0 := by linarith
      have hp1_eq : (p1 : ℝ) = 1 - 2 * h := by simp [p1]
      rw [hp1_eq]
      field_simp [hp_ne]
      ring

theorem ES_finiteConvexX_formula_on_Icc_zero_p0
    {h M a b : ℝ} {E0 E1 E2 : Set Ω} {p : Level}
    (hE0 : MeasurableSet E0) (hE1 : MeasurableSet E1) (hE2 : MeasurableSet E2)
    (h01 : Disjoint E0 E1) (h02 : Disjoint E0 E2) (h12 : Disjoint E1 E2)
    (hh : 0 < h) (h3 : 3 * h < 1)
    (hE0mass : P.real E0 = 1 - 3 * h) (hE1mass : P.real E1 = h) (hE2mass : P.real E2 = h)
    (hba : b < a) (haM : a < M) (hb : 0 < b)
    (hp0 : (p : ℝ) ≤ 1 - 3 * h) :
    ES P p (finiteConvexX P M a b E0 E1 E2 hE0 hE1 hE2) =
      (-M * ((1 - 3 * h) - (p : ℝ)) - h * (a + b)) / (1 - (p : ℝ)) := by
  let p0 : Level := finiteLevel0 h hh h3
  let p1 : Level := finiteLevel1 h hh h3
  let p2 : Level := finiteLevel2 h hh h3
  let X : RandomVariable P := finiteConvexX P M a b E0 E1 E2 hE0 hE1 hE2
  have hp_lt : (p : ℝ) < 1 := by linarith [hp0, hh, h3]
  have hdist :
      distES (law P X) p = (1 - (p : ℝ))⁻¹ * distESIntegral (law P X) p := by
    simpa [distES, hp_lt]
  have hp_le_p0 : (p : ℝ) ≤ (p0 : ℝ) := by simpa [p0] using hp0
  have hp0_le_p1 : (p0 : ℝ) ≤ (p1 : ℝ) := by simp [p0, p1]; linarith
  have hp1_le_p2 : (p1 : ℝ) ≤ (p2 : ℝ) := by simp [p1, p2]; linarith
  have hfi00 : IntervalIntegrable (distLowerQuantile (law P X)) volume (p : ℝ) (p0 : ℝ) := by
    refine (intervalIntegrable_const : IntervalIntegrable (fun _ => (-M : ℝ)) volume (p : ℝ) (p0 : ℝ)).congr ?_
    intro q hq
    have hqIoc : q ∈ Set.Ioc 0 (1 - 3 * h) := by
      have hq' : q ∈ Set.Ioc (p : ℝ) (p0 : ℝ) := by
        simpa [Set.uIoc, hp_le_p0] using hq
      exact ⟨lt_of_le_of_lt p.2.1 hq'.1, by simpa [p0] using hq'.2⟩
    symm
    exact distLowerQuantile_finiteConvexX_eq_negM (P := P)
      hE0 hE1 hE2 h01 h02 h12 hh h3 hE0mass hba haM hb hqIoc
  have hfi01 : IntervalIntegrable (distLowerQuantile (law P X)) volume (p0 : ℝ) (p1 : ℝ) := by
    refine (intervalIntegrable_const : IntervalIntegrable (fun _ => (-a : ℝ)) volume (p0 : ℝ) (p1 : ℝ)).congr ?_
    intro q hq
    have hqIoc : q ∈ Set.Ioc (1 - 3 * h) (1 - 2 * h) := by
      have hq' : q ∈ Set.Ioc (p0 : ℝ) (p1 : ℝ) := by
        simpa [Set.uIoc, hp0_le_p1] using hq
      simpa [p0, p1] using hq'
    symm
    exact distLowerQuantile_finiteConvexX_eq_nega (P := P)
      hE0 hE1 hE2 h01 h02 h12 hh h3 hE0mass hE1mass hba haM hb hqIoc
  have hfi12 : IntervalIntegrable (distLowerQuantile (law P X)) volume (p1 : ℝ) (p2 : ℝ) := by
    refine (intervalIntegrable_const : IntervalIntegrable (fun _ => (-b : ℝ)) volume (p1 : ℝ) (p2 : ℝ)).congr ?_
    intro q hq
    have hqIoc : q ∈ Set.Ioc (1 - 2 * h) (1 - h) := by
      have hq' : q ∈ Set.Ioc (p1 : ℝ) (p2 : ℝ) := by
        simpa [Set.uIoc, hp1_le_p2] using hq
      simpa [p1, p2] using hq'
    symm
    exact distLowerQuantile_finiteConvexX_eq_negb (P := P)
      hE0 hE1 hE2 h01 h02 h12 hh h3 hE0mass hE1mass hE2mass hba haM hb hqIoc
  have hfi23 : IntervalIntegrable (distLowerQuantile (law P X)) volume (p2 : ℝ) 1 := by
    refine (intervalIntegrable_const : IntervalIntegrable (fun _ => (0 : ℝ)) volume (p2 : ℝ) 1).congr ?_
    intro q hq
    have hp2_le : (p2 : ℝ) ≤ 1 := p2.2.2
    have hqIoc : q ∈ Set.Ioc (1 - h) 1 := by
      have hq' : q ∈ Set.Ioc (p2 : ℝ) 1 := by
        simpa [Set.uIoc, hp2_le] using hq
      simpa [p2] using hq'
    symm
    exact distLowerQuantile_finiteConvexX_eq_zero (P := P)
      hE0 hE1 hE2 h01 h02 h12 hh h3 hE0mass hE1mass hE2mass hba haM hb hqIoc
  have hfi02 : IntervalIntegrable (distLowerQuantile (law P X)) volume (p0 : ℝ) (p2 : ℝ) := by
    exact hfi01.trans hfi12
  have hfi03 : IntervalIntegrable (distLowerQuantile (law P X)) volume (p : ℝ) (p2 : ℝ) := by
    exact hfi00.trans hfi02
  have hsplit01 :
      ∫ x in (p : ℝ)..(p1 : ℝ), distLowerQuantile (law P X) x =
        (∫ x in (p : ℝ)..(p0 : ℝ), distLowerQuantile (law P X) x) +
          ∫ x in (p0 : ℝ)..(p1 : ℝ), distLowerQuantile (law P X) x := by
    simpa using (intervalIntegral.integral_add_adjacent_intervals hfi00 hfi01).symm
  have hsplit02 :
      ∫ x in (p : ℝ)..(p2 : ℝ), distLowerQuantile (law P X) x =
        (∫ x in (p : ℝ)..(p0 : ℝ), distLowerQuantile (law P X) x) +
          ((∫ x in (p0 : ℝ)..(p1 : ℝ), distLowerQuantile (law P X) x) +
            ∫ x in (p1 : ℝ)..(p2 : ℝ), distLowerQuantile (law P X) x) := by
    calc
      ∫ x in (p : ℝ)..(p2 : ℝ), distLowerQuantile (law P X) x =
          (∫ x in (p : ℝ)..(p1 : ℝ), distLowerQuantile (law P X) x) +
            ∫ x in (p1 : ℝ)..(p2 : ℝ), distLowerQuantile (law P X) x := by
        simpa using (intervalIntegral.integral_add_adjacent_intervals (hfi00.trans hfi01) hfi12).symm
      _ = (∫ x in (p : ℝ)..(p0 : ℝ), distLowerQuantile (law P X) x) +
            ((∫ x in (p0 : ℝ)..(p1 : ℝ), distLowerQuantile (law P X) x) +
              ∫ x in (p1 : ℝ)..(p2 : ℝ), distLowerQuantile (law P X) x) := by
        rw [hsplit01]
        ring
  have hsplit :
      ∫ x in (p : ℝ)..1, distLowerQuantile (law P X) x =
        (∫ x in (p : ℝ)..(p0 : ℝ), distLowerQuantile (law P X) x) +
          ((∫ x in (p0 : ℝ)..(p1 : ℝ), distLowerQuantile (law P X) x) +
            ((∫ x in (p1 : ℝ)..(p2 : ℝ), distLowerQuantile (law P X) x) +
              ∫ x in (p2 : ℝ)..1, distLowerQuantile (law P X) x)) := by
    calc
      ∫ x in (p : ℝ)..1, distLowerQuantile (law P X) x =
          (∫ x in (p : ℝ)..(p2 : ℝ), distLowerQuantile (law P X) x) +
            ∫ x in (p2 : ℝ)..1, distLowerQuantile (law P X) x := by
        simpa using (intervalIntegral.integral_add_adjacent_intervals hfi03 hfi23).symm
      _ = (∫ x in (p : ℝ)..(p0 : ℝ), distLowerQuantile (law P X) x) +
            ((∫ x in (p0 : ℝ)..(p1 : ℝ), distLowerQuantile (law P X) x) +
              ((∫ x in (p1 : ℝ)..(p2 : ℝ), distLowerQuantile (law P X) x) +
                ∫ x in (p2 : ℝ)..1, distLowerQuantile (law P X) x)) := by
        rw [hsplit02]
        ring
  have h00int :
      ∫ q in (p : ℝ)..(p0 : ℝ), distLowerQuantile (law P X) q = ((p0 : ℝ) - (p : ℝ)) * (-M) := by
    calc
      ∫ q in (p : ℝ)..(p0 : ℝ), distLowerQuantile (law P X) q =
        ∫ q in (p : ℝ)..(p0 : ℝ), (-M : ℝ) := by
          refine intervalIntegral.integral_congr_ae ?_
          exact Filter.Eventually.of_forall (fun q hq => by
            have hqIoc : q ∈ Set.Ioc 0 (1 - 3 * h) := by
              have hq' : q ∈ Set.Ioc (p : ℝ) (p0 : ℝ) := by
                simpa [Set.uIoc, hp_le_p0] using hq
              exact ⟨lt_of_le_of_lt p.2.1 hq'.1, by simpa [p0] using hq'.2⟩
            exact distLowerQuantile_finiteConvexX_eq_negM (P := P)
              hE0 hE1 hE2 h01 h02 h12 hh h3 hE0mass hba haM hb hqIoc)
      _ = ((p0 : ℝ) - (p : ℝ)) * (-M) := by simp [intervalIntegral.integral_const]
  have h01int :
      ∫ q in (p0 : ℝ)..(p1 : ℝ), distLowerQuantile (law P X) q = -a * h := by
    calc
      ∫ q in (p0 : ℝ)..(p1 : ℝ), distLowerQuantile (law P X) q =
        ∫ q in (p0 : ℝ)..(p1 : ℝ), (-a : ℝ) := by
          refine intervalIntegral.integral_congr_ae ?_
          exact Filter.Eventually.of_forall (fun q hq => by
            have hqIoc : q ∈ Set.Ioc (1 - 3 * h) (1 - 2 * h) := by
              have hq' : q ∈ Set.Ioc (p0 : ℝ) (p1 : ℝ) := by
                simpa [Set.uIoc, hp0_le_p1] using hq
              simpa [p0, p1] using hq'
            exact distLowerQuantile_finiteConvexX_eq_nega (P := P)
              hE0 hE1 hE2 h01 h02 h12 hh h3 hE0mass hE1mass hba haM hb hqIoc)
      _ = ((p1 : ℝ) - (p0 : ℝ)) * (-a) := by simp [intervalIntegral.integral_const]
      _ = -a * h := by
        simp [p0, p1]
        ring
  have h12int :
      ∫ q in (p1 : ℝ)..(p2 : ℝ), distLowerQuantile (law P X) q = -b * h := by
    calc
      ∫ q in (p1 : ℝ)..(p2 : ℝ), distLowerQuantile (law P X) q =
        ∫ q in (p1 : ℝ)..(p2 : ℝ), (-b : ℝ) := by
          refine intervalIntegral.integral_congr_ae ?_
          exact Filter.Eventually.of_forall (fun q hq => by
            have hqIoc : q ∈ Set.Ioc (1 - 2 * h) (1 - h) := by
              have hq' : q ∈ Set.Ioc (p1 : ℝ) (p2 : ℝ) := by
                simpa [Set.uIoc, hp1_le_p2] using hq
              simpa [p1, p2] using hq'
            exact distLowerQuantile_finiteConvexX_eq_negb (P := P)
              hE0 hE1 hE2 h01 h02 h12 hh h3 hE0mass hE1mass hE2mass hba haM hb hqIoc)
      _ = ((p2 : ℝ) - (p1 : ℝ)) * (-b) := by simp [intervalIntegral.integral_const]
      _ = -b * h := by
        simp [p1, p2]
        ring
  have h23int :
      ∫ q in (p2 : ℝ)..1, distLowerQuantile (law P X) q = 0 := by
    calc
      ∫ q in (p2 : ℝ)..1, distLowerQuantile (law P X) q =
        ∫ q in (p2 : ℝ)..1, (0 : ℝ) := by
          refine intervalIntegral.integral_congr_ae ?_
          exact Filter.Eventually.of_forall (fun q hq => by
            have hp2_le : (p2 : ℝ) ≤ 1 := p2.2.2
            have hqIoc : q ∈ Set.Ioc (1 - h) 1 := by
              have hq' : q ∈ Set.Ioc (p2 : ℝ) 1 := by
                simpa [Set.uIoc, hp2_le] using hq
              simpa [p2] using hq'
            exact distLowerQuantile_finiteConvexX_eq_zero (P := P)
              hE0 hE1 hE2 h01 h02 h12 hh h3 hE0mass hE1mass hE2mass hba haM hb hqIoc)
      _ = 0 := by simp
  calc
    ES P p X = distES (law P X) p := rfl
    _ = (1 - (p : ℝ))⁻¹ * distESIntegral (law P X) p := hdist
    _ = (1 - (p : ℝ))⁻¹ *
        ((∫ x in (p : ℝ)..(p0 : ℝ), distLowerQuantile (law P X) x) +
          ((∫ x in (p0 : ℝ)..(p1 : ℝ), distLowerQuantile (law P X) x) +
            ((∫ x in (p1 : ℝ)..(p2 : ℝ), distLowerQuantile (law P X) x) +
              ∫ x in (p2 : ℝ)..1, distLowerQuantile (law P X) x))) := by
      rw [distESIntegral, hsplit]
    _ = (1 - (p : ℝ))⁻¹ * (((p0 : ℝ) - (p : ℝ)) * (-M) + (-a * h + (-b * h))) := by
      rw [h00int, h01int, h12int, h23int]
      ring
    _ = (-M * ((1 - 3 * h) - (p : ℝ)) - h * (a + b)) / (1 - (p : ℝ)) := by
      have hp_ne : (1 - (p : ℝ)) ≠ 0 := by linarith
      have hp0_eq : (p0 : ℝ) = 1 - 3 * h := by simp [p0]
      rw [hp0_eq]
      field_simp [hp_ne]
      ring

end FiniteConvexXES

section FiniteConvexYES

variable {Ω : Type*} [MeasurableSpace Ω]
variable (P : Measure Ω) [IsProbabilityMeasure P]

theorem ES_finiteConvexY_at_p2
    {h M a b : ℝ} {E0 E1 E2 : Set Ω}
    (hE0 : MeasurableSet E0) (hE1 : MeasurableSet E1) (hE2 : MeasurableSet E2)
    (h01 : Disjoint E0 E1) (h02 : Disjoint E0 E2) (h12 : Disjoint E1 E2)
    (hh : 0 < h) (h3 : 3 * h < 1)
    (hE0mass : P.real E0 = 1 - 3 * h) (hE1mass : P.real E1 = h) (hE2mass : P.real E2 = h)
    (hba : b < a) (haM : a < M) (hb : 0 < b) :
    ES P (finiteLevel2 h hh h3) (finiteConvexY P M a b E0 E1 E2 hE0 hE1 hE2) = 0 := by
  simpa [finiteConvexY, finiteConvexX, add_assoc, add_left_comm, add_comm] using
    (ES_finiteConvexX_at_p2 (P := P) (hE0 := hE0) (hE1 := hE2) (hE2 := hE1)
      (h01 := h02) (h02 := h01) (h12 := h12.symm) (hh := hh) (h3 := h3)
      (hE0mass := hE0mass) (hE1mass := hE2mass) (hE2mass := hE1mass)
      (hba := hba) (haM := haM) (hb := hb))

theorem ES_finiteConvexY_at_p1
    {h M a b : ℝ} {E0 E1 E2 : Set Ω}
    (hE0 : MeasurableSet E0) (hE1 : MeasurableSet E1) (hE2 : MeasurableSet E2)
    (h01 : Disjoint E0 E1) (h02 : Disjoint E0 E2) (h12 : Disjoint E1 E2)
    (hh : 0 < h) (h3 : 3 * h < 1)
    (hE0mass : P.real E0 = 1 - 3 * h) (hE1mass : P.real E1 = h) (hE2mass : P.real E2 = h)
    (hba : b < a) (haM : a < M) (hb : 0 < b) :
    ES P (finiteLevel1 h hh h3) (finiteConvexY P M a b E0 E1 E2 hE0 hE1 hE2) = -b / 2 := by
  simpa [finiteConvexY, finiteConvexX, add_assoc, add_left_comm, add_comm] using
    (ES_finiteConvexX_at_p1 (P := P) (hE0 := hE0) (hE1 := hE2) (hE2 := hE1)
      (h01 := h02) (h02 := h01) (h12 := h12.symm) (hh := hh) (h3 := h3)
      (hE0mass := hE0mass) (hE1mass := hE2mass) (hE2mass := hE1mass)
      (hba := hba) (haM := haM) (hb := hb))

theorem ES_finiteConvexY_at_p0
    {h M a b : ℝ} {E0 E1 E2 : Set Ω}
    (hE0 : MeasurableSet E0) (hE1 : MeasurableSet E1) (hE2 : MeasurableSet E2)
    (h01 : Disjoint E0 E1) (h02 : Disjoint E0 E2) (h12 : Disjoint E1 E2)
    (hh : 0 < h) (h3 : 3 * h < 1)
    (hE0mass : P.real E0 = 1 - 3 * h) (hE1mass : P.real E1 = h) (hE2mass : P.real E2 = h)
    (hba : b < a) (haM : a < M) (hb : 0 < b) :
    ES P (finiteLevel0 h hh h3) (finiteConvexY P M a b E0 E1 E2 hE0 hE1 hE2) = -(a + b) / 3 := by
  simpa [finiteConvexY, finiteConvexX, add_assoc, add_left_comm, add_comm] using
    (ES_finiteConvexX_at_p0 (P := P) (hE0 := hE0) (hE1 := hE2) (hE2 := hE1)
      (h01 := h02) (h02 := h01) (h12 := h12.symm) (hh := hh) (h3 := h3)
      (hE0mass := hE0mass) (hE1mass := hE2mass) (hE2mass := hE1mass)
      (hba := hba) (haM := haM) (hb := hb))

end FiniteConvexYES

section FiniteThreeIndicatorNonpos

variable {Ω : Type*} [MeasurableSpace Ω]
variable (P : Measure Ω) [IsProbabilityMeasure P]

private theorem distLowerQuantile_le_zero_of_pos_le_one_of_cdf_zero_eq_one
    (μ : Measure ℝ) [IsProbabilityMeasure μ] {q : ℝ} (hq0 : 0 < q) (hq1 : q ≤ 1)
    (hcdf : ProbabilityTheory.cdf μ 0 = 1) :
    distLowerQuantile μ q ≤ 0 := by
  unfold distLowerQuantile
  refine csInf_le (upperLevelSet_bddBelow μ hq0) ?_
  change q ≤ ProbabilityTheory.cdf μ 0
  rw [hcdf]
  linarith

end FiniteThreeIndicatorNonpos

section FiniteConvexSupInfES

variable {Ω : Type*} [MeasurableSpace Ω]
variable (P : Measure Ω) [IsProbabilityMeasure P]

theorem distLowerQuantile_finiteConvexSup_eq_negb
    {h M b : ℝ} {E0 E1 E2 : Set Ω}
    (hE0 : MeasurableSet E0) (hE1 : MeasurableSet E1) (hE2 : MeasurableSet E2)
    (h01 : Disjoint E0 E1) (h02 : Disjoint E0 E2) (h12 : Disjoint E1 E2)
    (hh : 0 < h) (h3 : 3 * h < 1)
    (hE0mass : P.real E0 = 1 - 3 * h) (hE1mass : P.real E1 = h) (hE2mass : P.real E2 = h)
    (hbM : b < M) (hb : 0 < b)
    {q : ℝ} (hq : q ∈ Set.Ioc (1 - 3 * h) (1 - h)) :
    distLowerQuantile (law P (finiteConvexSup P M b E0 E1 E2 hE0 (hE1.union hE2))) q = -b := by
  let μ := finiteThreeIndicatorLaw P (-M) (-b) (-b) E0 E1 E2
  have hμ :
      law P (finiteConvexSup P M b E0 E1 E2 hE0 (hE1.union hE2)) = μ := by
    simpa [μ] using
      law_finiteConvexSup_eq_finiteThreeIndicatorLaw (P := P) M b hE0 hE1 hE2 h01 h02 h12
  haveI : IsProbabilityMeasure μ :=
    finiteThreeIndicatorLaw_isProbabilityMeasure (P := P) (-M) (-b) (-b) hE0 hE1 hE2 h01 h02 h12
  let S : Set ℝ := {x : ℝ | q ≤ ProbabilityTheory.cdf μ x}
  have horder01 : -M ≤ -b := by linarith
  have horder12 : (-b : ℝ) ≤ -b := le_rfl
  have horder20 : (-b : ℝ) ≤ 0 := by linarith
  have hsum : P.real E0 + P.real E1 + P.real E2 = 1 - h := by
    rw [hE0mass, hE1mass, hE2mass]
    ring
  suffices hmain : distLowerQuantile μ q = -b by
    simpa [hμ] using hmain
  change sInf S = -b
  apply le_antisymm
  · refine csInf_le (upperLevelSet_bddBelow μ (by linarith [hh, h3, hq.1])) ?_
    change q ≤ ProbabilityTheory.cdf μ (-b)
    have hcdf :
        ProbabilityTheory.cdf μ (-b) = P.real E0 + P.real E1 + P.real E2 := by
      exact cdf_finiteThreeIndicatorLaw_of_x2_le_lt_zero (P := P) horder01 horder12 horder20
        hE0 hE1 hE2 h01 h02 h12 le_rfl (by linarith [hb])
    rw [hcdf, hsum]
    linarith [hq.2]
  · refine le_csInf ?_ ?_
    · exact ⟨-b, by
        change q ≤ ProbabilityTheory.cdf μ (-b)
        have hcdf :
            ProbabilityTheory.cdf μ (-b) = P.real E0 + P.real E1 + P.real E2 := by
          exact cdf_finiteThreeIndicatorLaw_of_x2_le_lt_zero (P := P) horder01 horder12 horder20
            hE0 hE1 hE2 h01 h02 h12 le_rfl (by linarith [hb])
        rw [hcdf, hsum]
        linarith [hq.2]⟩
    · intro x hxS
      by_contra hxlt
      have hxlt' : x < -b := by linarith
      have hxq : q ≤ ProbabilityTheory.cdf μ x := by simpa [S] using hxS
      by_cases hxltM : x < -M
      · have hcdf : ProbabilityTheory.cdf μ x = 0 := by
          exact cdf_finiteThreeIndicatorLaw_of_lt_x0 (P := P) horder01 horder12 horder20
            hE0 hE1 hE2 h01 h02 h12 hxltM
        have : q ≤ 0 := by simpa [hcdf] using hxq
        linarith [hq.1]
      · have hxgeM : -M ≤ x := le_of_not_gt hxltM
        have hcdf : ProbabilityTheory.cdf μ x = P.real E0 := by
          exact cdf_finiteThreeIndicatorLaw_of_x0_le_lt_x1 (P := P) horder12 horder20
            hE0 hE1 hE2 h01 h02 h12 hxgeM hxlt'
        have : q ≤ 1 - 3 * h := by simpa [hcdf, hE0mass] using hxq
        linarith [hq.1]

theorem distLowerQuantile_finiteConvexInf_eq_zero
    {h M a : ℝ} {E0 E1 E2 : Set Ω}
    (hE0 : MeasurableSet E0) (hE1 : MeasurableSet E1) (hE2 : MeasurableSet E2)
    (h01 : Disjoint E0 E1) (h02 : Disjoint E0 E2) (h12 : Disjoint E1 E2)
    (hh : 0 < h) (h3 : 3 * h < 1)
    (hE0mass : P.real E0 = 1 - 3 * h) (hE1mass : P.real E1 = h) (hE2mass : P.real E2 = h)
    (haM : a < M) (ha : 0 < a)
    {q : ℝ} (hq : q ∈ Set.Ioc (1 - h) 1) :
    distLowerQuantile (law P (finiteConvexInf P M a E0 E1 E2 hE0 (hE1.union hE2))) q = 0 := by
  let μ := finiteThreeIndicatorLaw P (-M) (-a) (-a) E0 E1 E2
  have hμ :
      law P (finiteConvexInf P M a E0 E1 E2 hE0 (hE1.union hE2)) = μ := by
    simpa [μ] using
      law_finiteConvexInf_eq_finiteThreeIndicatorLaw (P := P) M a hE0 hE1 hE2 h01 h02 h12
  haveI : IsProbabilityMeasure μ :=
    finiteThreeIndicatorLaw_isProbabilityMeasure (P := P) (-M) (-a) (-a) hE0 hE1 hE2 h01 h02 h12
  let S : Set ℝ := {x : ℝ | q ≤ ProbabilityTheory.cdf μ x}
  have horder01 : -M ≤ -a := by linarith
  have horder12 : (-a : ℝ) ≤ -a := le_rfl
  have horder20 : (-a : ℝ) ≤ 0 := by linarith
  suffices hmain : distLowerQuantile μ q = 0 by
    simpa [hμ] using hmain
  change sInf S = 0
  apply le_antisymm
  · refine csInf_le (upperLevelSet_bddBelow μ (by linarith [hh, h3, hq.1])) ?_
    change q ≤ ProbabilityTheory.cdf μ 0
    have hcdf : ProbabilityTheory.cdf μ 0 = 1 := by
      exact cdf_finiteThreeIndicatorLaw_of_nonneg (P := P) horder01 horder12 horder20
        hE0 hE1 hE2 h01 h02 h12 le_rfl
    rw [hcdf]
    linarith [hq.2]
  · refine le_csInf ?_ ?_
    · exact ⟨0, by
        change q ≤ ProbabilityTheory.cdf μ 0
        have hcdf : ProbabilityTheory.cdf μ 0 = 1 := by
          exact cdf_finiteThreeIndicatorLaw_of_nonneg (P := P) horder01 horder12 horder20
            hE0 hE1 hE2 h01 h02 h12 le_rfl
        rw [hcdf]
        linarith [hq.2]⟩
    · intro x hxS
      by_contra hxlt
      have hxlt0 : x < 0 := by linarith
      have hxq : q ≤ ProbabilityTheory.cdf μ x := by simpa [S] using hxS
      by_cases hxltM : x < -M
      · have hcdf : ProbabilityTheory.cdf μ x = 0 := by
          exact cdf_finiteThreeIndicatorLaw_of_lt_x0 (P := P) horder01 horder12 horder20
            hE0 hE1 hE2 h01 h02 h12 hxltM
        have : q ≤ 0 := by simpa [hcdf] using hxq
        linarith [hq.1]
      · have hxgeM : -M ≤ x := le_of_not_gt hxltM
        by_cases hxlta : x < -a
        · have hcdf : ProbabilityTheory.cdf μ x = P.real E0 := by
            exact cdf_finiteThreeIndicatorLaw_of_x0_le_lt_x1 (P := P) horder12 horder20
              hE0 hE1 hE2 h01 h02 h12 hxgeM hxlta
          have : q ≤ 1 - 3 * h := by simpa [hcdf, hE0mass] using hxq
          linarith [hq.1]
        · have hxgea : -a ≤ x := le_of_not_gt hxlta
          have hcdf : ProbabilityTheory.cdf μ x = P.real E0 + P.real E1 + P.real E2 := by
            exact cdf_finiteThreeIndicatorLaw_of_x2_le_lt_zero (P := P) horder01 horder12 horder20
              hE0 hE1 hE2 h01 h02 h12 hxgea hxlt0
          have htmp : q ≤ (1 - 3 * h) + h + h := by
            simpa [hcdf, hE0mass, hE1mass, hE2mass] using hxq
          have : q ≤ 1 - h := by linarith
          linarith [hq.1]

theorem ES_finiteConvexSup_at_p0
    {h M b : ℝ} {E0 E1 E2 : Set Ω}
    (hE0 : MeasurableSet E0) (hE1 : MeasurableSet E1) (hE2 : MeasurableSet E2)
    (h01 : Disjoint E0 E1) (h02 : Disjoint E0 E2) (h12 : Disjoint E1 E2)
    (hh : 0 < h) (h3 : 3 * h < 1)
    (hE0mass : P.real E0 = 1 - 3 * h) (hE1mass : P.real E1 = h) (hE2mass : P.real E2 = h)
    (hbM : b < M) (hb : 0 < b) :
    ES P (finiteLevel0 h hh h3) (finiteConvexSup P M b E0 E1 E2 hE0 (hE1.union hE2)) =
      -(2 * b) / 3 := by
  let p0 : Level := finiteLevel0 h hh h3
  let p2 : Level := finiteLevel2 h hh h3
  let X : RandomVariable P := finiteConvexSup P M b E0 E1 E2 hE0 (hE1.union hE2)
  have hp0_lt : (p0 : ℝ) < 1 := by simp [p0, hh]
  have hdist :
      distES (law P X) p0 = (1 - (p0 : ℝ))⁻¹ * distESIntegral (law P X) p0 := by
    simpa [distES, hp0_lt]
  have hp0_le_p2 : (p0 : ℝ) ≤ (p2 : ℝ) := by
    simp [p0, p2]
    linarith
  have hfi02 : IntervalIntegrable (distLowerQuantile (law P X)) volume (p0 : ℝ) (p2 : ℝ) := by
    refine (intervalIntegrable_const : IntervalIntegrable (fun _ => (-b : ℝ)) volume (p0 : ℝ) (p2 : ℝ)).congr ?_
    intro q hq
    have hqIoc : q ∈ Set.Ioc (1 - 3 * h) (1 - h) := by
      have hq' : q ∈ Set.Ioc (p0 : ℝ) (p2 : ℝ) := by
        simpa [Set.uIoc, hp0_le_p2] using hq
      simpa [p0, p2] using hq'
    symm
    exact distLowerQuantile_finiteConvexSup_eq_negb (P := P)
      hE0 hE1 hE2 h01 h02 h12 hh h3 hE0mass hE1mass hE2mass hbM hb hqIoc
  have hfi23 : IntervalIntegrable (distLowerQuantile (law P X)) volume (p2 : ℝ) 1 := by
    refine (intervalIntegrable_const : IntervalIntegrable (fun _ => (0 : ℝ)) volume (p2 : ℝ) 1).congr ?_
    intro q hq
    have hp2_le : (p2 : ℝ) ≤ 1 := p2.2.2
    have hqIoc : q ∈ Set.Ioc (1 - h) 1 := by
      have hq' : q ∈ Set.Ioc (p2 : ℝ) 1 := by
        simpa [Set.uIoc, hp2_le] using hq
      simpa [p2] using hq'
    have hmain :
        distLowerQuantile (law P X) q = 0 := by
      exact distLowerQuantile_finiteConvexInf_eq_zero
        (P := P) (M := M) (a := b)
        hE0 hE1 hE2 h01 h02 h12 hh h3 hE0mass hE1mass hE2mass hbM hb hqIoc
    simpa using hmain.symm
  have hsplit :
      ∫ x in (p0 : ℝ)..1, distLowerQuantile (law P X) x =
        (∫ x in (p0 : ℝ)..(p2 : ℝ), distLowerQuantile (law P X) x) +
          ∫ x in (p2 : ℝ)..1, distLowerQuantile (law P X) x := by
    simpa using (intervalIntegral.integral_add_adjacent_intervals hfi02 hfi23).symm
  have h02int :
      ∫ q in (p0 : ℝ)..(p2 : ℝ), distLowerQuantile (law P X) q = -b * (2 * h) := by
    calc
      ∫ q in (p0 : ℝ)..(p2 : ℝ), distLowerQuantile (law P X) q =
        ∫ q in (p0 : ℝ)..(p2 : ℝ), (-b : ℝ) := by
          refine intervalIntegral.integral_congr_ae ?_
          exact Filter.Eventually.of_forall (fun q hq => by
            have hqIoc : q ∈ Set.Ioc (1 - 3 * h) (1 - h) := by
              have hq' : q ∈ Set.Ioc (p0 : ℝ) (p2 : ℝ) := by
                simpa [Set.uIoc, hp0_le_p2] using hq
              simpa [p0, p2] using hq'
            exact distLowerQuantile_finiteConvexSup_eq_negb (P := P)
              hE0 hE1 hE2 h01 h02 h12 hh h3 hE0mass hE1mass hE2mass hbM hb hqIoc)
      _ = ((p2 : ℝ) - (p0 : ℝ)) * (-b) := by simp [intervalIntegral.integral_const]
      _ = -b * (2 * h) := by
        simp [p0, p2]
        ring
  have h23int :
      ∫ q in (p2 : ℝ)..1, distLowerQuantile (law P X) q = 0 := by
    calc
      ∫ q in (p2 : ℝ)..1, distLowerQuantile (law P X) q =
        ∫ q in (p2 : ℝ)..1, (0 : ℝ) := by
          refine intervalIntegral.integral_congr_ae ?_
          exact Filter.Eventually.of_forall (fun q hq => by
            have hp2_le : (p2 : ℝ) ≤ 1 := p2.2.2
            have hqIoc : q ∈ Set.Ioc (1 - h) 1 := by
              have hq' : q ∈ Set.Ioc (p2 : ℝ) 1 := by
                simpa [Set.uIoc, hp2_le] using hq
              simpa [p2] using hq'
            simpa using
              (distLowerQuantile_finiteConvexInf_eq_zero (P := P) (M := M) (a := b)
                hE0 hE1 hE2 h01 h02 h12 hh h3 hE0mass hE1mass hE2mass hbM hb hqIoc))
      _ = 0 := by simp
  calc
    ES P p0 X = distES (law P X) p0 := rfl
    _ = (1 - (p0 : ℝ))⁻¹ * distESIntegral (law P X) p0 := hdist
    _ = (1 - (p0 : ℝ))⁻¹ *
        ((∫ x in (p0 : ℝ)..(p2 : ℝ), distLowerQuantile (law P X) x) +
          ∫ x in (p2 : ℝ)..1, distLowerQuantile (law P X) x) := by
      rw [distESIntegral, hsplit]
    _ = (1 - (p0 : ℝ))⁻¹ * (-b * (2 * h)) := by rw [h02int, h23int, add_zero]
    _ = -(2 * b) / 3 := by
      have hp0_eq : (p0 : ℝ) = 1 - 3 * h := by simp [p0]
      rw [hp0_eq]
      field_simp [show h ≠ 0 by linarith]
      ring

theorem ES_finiteConvexInf_at_p2
    {h M a : ℝ} {E0 E1 E2 : Set Ω}
    (hE0 : MeasurableSet E0) (hE1 : MeasurableSet E1) (hE2 : MeasurableSet E2)
    (h01 : Disjoint E0 E1) (h02 : Disjoint E0 E2) (h12 : Disjoint E1 E2)
    (hh : 0 < h) (h3 : 3 * h < 1)
    (hE0mass : P.real E0 = 1 - 3 * h) (hE1mass : P.real E1 = h) (hE2mass : P.real E2 = h)
    (haM : a < M) (ha : 0 < a) :
    ES P (finiteLevel2 h hh h3) (finiteConvexInf P M a E0 E1 E2 hE0 (hE1.union hE2)) = 0 := by
  let p2 : Level := finiteLevel2 h hh h3
  let X : RandomVariable P := finiteConvexInf P M a E0 E1 E2 hE0 (hE1.union hE2)
  have hp2_lt : (p2 : ℝ) < 1 := by simp [p2, hh]
  have hdist :
      distES (law P X) p2 = (1 - (p2 : ℝ))⁻¹ * distESIntegral (law P X) p2 := by
    simpa [distES, hp2_lt]
  have hInt :
      distESIntegral (law P X) p2 = 0 := by
    rw [distESIntegral]
    calc
      ∫ q in (p2 : ℝ)..1, distLowerQuantile (law P X) q =
        ∫ q in (p2 : ℝ)..1, (0 : ℝ) := by
          refine intervalIntegral.integral_congr_ae ?_
          exact Filter.Eventually.of_forall (fun q hq => by
            have hp2_le : (p2 : ℝ) ≤ 1 := p2.2.2
            have hqIoc : q ∈ Set.Ioc (1 - h) 1 := by
              have hq' : q ∈ Set.Ioc (p2 : ℝ) 1 := by
                simpa [Set.uIoc, hp2_le] using hq
              simpa [p2] using hq'
            exact distLowerQuantile_finiteConvexInf_eq_zero (P := P)
              hE0 hE1 hE2 h01 h02 h12 hh h3 hE0mass hE1mass hE2mass haM ha hqIoc)
      _ = 0 := by simp
  calc
    ES P p2 X = distES (law P X) p2 := rfl
    _ = (1 - (p2 : ℝ))⁻¹ * distESIntegral (law P X) p2 := hdist
    _ = 0 := by rw [hInt]; simp

private theorem distES_le_zero_of_lt_one_of_cdf_zero_eq_one
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (hcdf0 : ProbabilityTheory.cdf μ 0 = 1)
    {p : Level} (hp : (p : ℝ) < 1) :
    distES μ p ≤ 0 := by
  unfold distES
  simp [hp]
  have hInt_nonpos : distESIntegral μ p ≤ 0 := by
    unfold distESIntegral
    let f : ℝ → ℝ := fun q => if q = 0 then 0 else distLowerQuantile μ q
    have hcongr :
        ∫ q in (p : ℝ)..1, distLowerQuantile μ q =
          ∫ q in (p : ℝ)..1, f q := by
      refine intervalIntegral.integral_congr_ae ?_
      filter_upwards [] with q
      intro hq
      have hqIoc : q ∈ Set.Ioc (p : ℝ) 1 := by
        simpa [Set.uIoc, le_of_lt hp] using hq
      have hq0 : q ≠ 0 := by linarith [hqIoc.1, p.2.1]
      simp [f, hq0]
    have hnonneg : 0 ≤ ∫ q in (p : ℝ)..1, -(f q) := by
      refine intervalIntegral.integral_nonneg (le_of_lt hp) ?_
      intro q hq
      by_cases hq0 : q = 0
      · simp [f, hq0]
      · have hqge0 : 0 ≤ q := le_trans p.2.1 hq.1
        have hq0' : (0 : ℝ) ≠ q := by exact fun h0q => hq0 h0q.symm
        have hqpos : 0 < q := lt_of_le_of_ne hqge0 hq0'
        have hqle1 : q ≤ 1 := hq.2
        have hqle : distLowerQuantile μ q ≤ 0 :=
          distLowerQuantile_le_zero_of_pos_le_one_of_cdf_zero_eq_one μ hqpos hqle1 hcdf0
        simpa [f, hq0] using neg_nonneg.mpr hqle
    have hneg_eq :
        ∫ q in (p : ℝ)..1, -(f q) = -(∫ q in (p : ℝ)..1, f q) := by
      simp
    have hmainf : ∫ q in (p : ℝ)..1, f q ≤ 0 := by
      linarith [hnonneg, hneg_eq]
    have hmain : ∫ q in (p : ℝ)..1, distLowerQuantile μ q ≤ 0 := by
      rw [hcongr]
      exact hmainf
    simpa using hmain
  have hfac_nonneg : 0 ≤ (1 - (p : ℝ))⁻¹ := by
    refine inv_nonneg.mpr ?_
    linarith
  exact mul_nonpos_of_nonneg_of_nonpos hfac_nonneg hInt_nonpos

private theorem ES_finiteConvexX_le_zero_of_lt_one
    {M a b : ℝ} {E0 E1 E2 : Set Ω}
    (hE0 : MeasurableSet E0) (hE1 : MeasurableSet E1) (hE2 : MeasurableSet E2)
    (h01 : Disjoint E0 E1) (h02 : Disjoint E0 E2) (h12 : Disjoint E1 E2)
    (haM : a < M) (ha : 0 < a) (hb : 0 < b) (hba : b ≤ a) {p : Level} (hp : (p : ℝ) < 1) :
    ES P p (finiteConvexX P M a b E0 E1 E2 hE0 hE1 hE2) ≤ 0 := by
  let μ := finiteThreeIndicatorLaw P (-M) (-a) (-b) E0 E1 E2
  have hμ :
      law P (finiteConvexX P M a b E0 E1 E2 hE0 hE1 hE2) = μ := by
    simpa [μ] using
      law_finiteConvexX_eq_finiteThreeIndicatorLaw (P := P) M a b hE0 hE1 hE2 h01 h02 h12
  haveI : IsProbabilityMeasure μ :=
    finiteThreeIndicatorLaw_isProbabilityMeasure (P := P) (-M) (-a) (-b) hE0 hE1 hE2 h01 h02 h12
  have hcdf0 : ProbabilityTheory.cdf μ 0 = 1 := by
    exact cdf_finiteThreeIndicatorLaw_of_nonneg (P := P)
      (by linarith : (-M : ℝ) ≤ -a) (by linarith : (-a : ℝ) ≤ -b) (by linarith : (-b : ℝ) ≤ 0)
      hE0 hE1 hE2 h01 h02 h12 le_rfl
  have hmain : distES μ p ≤ 0 := distES_le_zero_of_lt_one_of_cdf_zero_eq_one μ hcdf0 hp
  simpa [ES, hμ] using hmain

private theorem ES_finiteConvexY_le_zero_of_lt_one
    {M a b : ℝ} {E0 E1 E2 : Set Ω}
    (hE0 : MeasurableSet E0) (hE1 : MeasurableSet E1) (hE2 : MeasurableSet E2)
    (h01 : Disjoint E0 E1) (h02 : Disjoint E0 E2) (h12 : Disjoint E1 E2)
    (haM : a < M) (ha : 0 < a) (hb : 0 < b) (hba : b ≤ a) {p : Level} (hp : (p : ℝ) < 1) :
    ES P p (finiteConvexY P M a b E0 E1 E2 hE0 hE1 hE2) ≤ 0 := by
  let Y' : RandomVariable P := finiteConvexX P M a b E0 E2 E1 hE0 hE2 hE1
  have hYeq : finiteConvexY P M a b E0 E1 E2 hE0 hE1 hE2 = Y' := by
    ext ω
    simp [Y', finiteConvexX_apply, finiteConvexY_apply, add_assoc, add_left_comm, add_comm]
  let μ := finiteThreeIndicatorLaw P (-M) (-a) (-b) E0 E2 E1
  have hμ : law P Y' = μ := by
    simpa [Y', μ] using
      law_finiteConvexX_eq_finiteThreeIndicatorLaw (P := P) M a b
        (hE0 := hE0) (hE1 := hE2) (hE2 := hE1) h02 h01 h12.symm
  haveI : IsProbabilityMeasure μ :=
    finiteThreeIndicatorLaw_isProbabilityMeasure (P := P) (-M) (-a) (-b) hE0 hE2 hE1 h02 h01
      h12.symm
  have hcdf0 : ProbabilityTheory.cdf μ 0 = 1 := by
    exact cdf_finiteThreeIndicatorLaw_of_nonneg (P := P)
      (by linarith : (-M : ℝ) ≤ -a) (by linarith : (-a : ℝ) ≤ -b) (by linarith : (-b : ℝ) ≤ 0)
      hE0 hE2 hE1 h02 h01 h12.symm le_rfl
  have hmain : distES μ p ≤ 0 := distES_le_zero_of_lt_one_of_cdf_zero_eq_one μ hcdf0 hp
  simpa [hYeq, ES, hμ] using hmain

private theorem ES_finiteConvexSup_le_zero_of_lt_one
    {M b : ℝ} {E0 E1 E2 : Set Ω}
    (hE0 : MeasurableSet E0) (hE1 : MeasurableSet E1) (hE2 : MeasurableSet E2)
    (h01 : Disjoint E0 E1) (h02 : Disjoint E0 E2) (h12 : Disjoint E1 E2)
    (hbM : b < M) (hb : 0 < b) {p : Level} (hp : (p : ℝ) < 1) :
    ES P p (finiteConvexSup P M b E0 E1 E2 hE0 (hE1.union hE2)) ≤ 0 := by
  let μ := finiteThreeIndicatorLaw P (-M) (-b) (-b) E0 E1 E2
  have hμ :
      law P (finiteConvexSup P M b E0 E1 E2 hE0 (hE1.union hE2)) = μ := by
    simpa [μ] using
      law_finiteConvexSup_eq_finiteThreeIndicatorLaw (P := P) M b hE0 hE1 hE2 h01 h02 h12
  haveI : IsProbabilityMeasure μ :=
    finiteThreeIndicatorLaw_isProbabilityMeasure (P := P) (-M) (-b) (-b) hE0 hE1 hE2 h01 h02 h12
  have hcdf0 : ProbabilityTheory.cdf μ 0 = 1 := by
    exact cdf_finiteThreeIndicatorLaw_of_nonneg (P := P)
      (by linarith : (-M : ℝ) ≤ -b) le_rfl (by linarith : (-b : ℝ) ≤ 0)
      hE0 hE1 hE2 h01 h02 h12 le_rfl
  have hInt_nonpos : distESIntegral μ p ≤ 0 := by
    unfold distESIntegral
    let f : ℝ → ℝ := fun q => if q = 0 then 0 else distLowerQuantile μ q
    have hcongr :
        ∫ q in (p : ℝ)..1, distLowerQuantile μ q =
          ∫ q in (p : ℝ)..1, f q := by
      refine intervalIntegral.integral_congr_ae ?_
      filter_upwards [] with q
      intro hq
      have hqIoc : q ∈ Set.Ioc (p : ℝ) 1 := by
        simpa [Set.uIoc, le_of_lt hp] using hq
      have hq0 : q ≠ 0 := by linarith [hqIoc.1, p.2.1]
      simp [f, hq0]
    have hnonneg : 0 ≤ ∫ q in (p : ℝ)..1, -(f q) := by
      refine intervalIntegral.integral_nonneg (le_of_lt hp) ?_
      intro q hq
      by_cases hq0 : q = 0
      · simp [f, hq0]
      · have hqge0 : 0 ≤ q := le_trans p.2.1 hq.1
        have hq0' : (0 : ℝ) ≠ q := by exact fun h0q => hq0 h0q.symm
        have hqpos : 0 < q := lt_of_le_of_ne hqge0 hq0'
        have hqle1 : q ≤ 1 := hq.2
        have hqle : distLowerQuantile μ q ≤ 0 :=
          distLowerQuantile_le_zero_of_pos_le_one_of_cdf_zero_eq_one μ hqpos hqle1 hcdf0
        simpa [f, hq0] using neg_nonneg.mpr hqle
    have hneg_eq :
        ∫ q in (p : ℝ)..1, -(f q) = -(∫ q in (p : ℝ)..1, f q) := by
      simp
    have hmainf : ∫ q in (p : ℝ)..1, f q ≤ 0 := by
      linarith [hnonneg, hneg_eq]
    have hmain : ∫ q in (p : ℝ)..1, distLowerQuantile μ q ≤ 0 := by
      rw [hcongr]
      exact hmainf
    simpa using hmain
  have hmain : distES μ p ≤ 0 := by
    simp [distES, hp]
    have hfac_nonneg : 0 ≤ (1 - (p : ℝ))⁻¹ := by
      refine inv_nonneg.mpr ?_
      linarith
    exact mul_nonpos_of_nonneg_of_nonpos hfac_nonneg hInt_nonpos
  simpa [ES, hμ] using hmain

private theorem ES_finiteConvexInf_le_zero_of_lt_one
    {M a : ℝ} {E0 E1 E2 : Set Ω}
    (hE0 : MeasurableSet E0) (hE1 : MeasurableSet E1) (hE2 : MeasurableSet E2)
    (h01 : Disjoint E0 E1) (h02 : Disjoint E0 E2) (h12 : Disjoint E1 E2)
    (haM : a < M) (ha : 0 < a) {p : Level} (hp : (p : ℝ) < 1) :
    ES P p (finiteConvexInf P M a E0 E1 E2 hE0 (hE1.union hE2)) ≤ 0 := by
  let μ := finiteThreeIndicatorLaw P (-M) (-a) (-a) E0 E1 E2
  have hμ :
      law P (finiteConvexInf P M a E0 E1 E2 hE0 (hE1.union hE2)) = μ := by
    simpa [μ] using
      law_finiteConvexInf_eq_finiteThreeIndicatorLaw (P := P) M a hE0 hE1 hE2 h01 h02 h12
  haveI : IsProbabilityMeasure μ :=
    finiteThreeIndicatorLaw_isProbabilityMeasure (P := P) (-M) (-a) (-a) hE0 hE1 hE2 h01 h02 h12
  have hcdf0 : ProbabilityTheory.cdf μ 0 = 1 := by
    exact cdf_finiteThreeIndicatorLaw_of_nonneg (P := P)
      (by linarith : (-M : ℝ) ≤ -a) le_rfl (by linarith : (-a : ℝ) ≤ 0)
      hE0 hE1 hE2 h01 h02 h12 le_rfl
  have hInt_nonpos : distESIntegral μ p ≤ 0 := by
    unfold distESIntegral
    let f : ℝ → ℝ := fun q => if q = 0 then 0 else distLowerQuantile μ q
    have hcongr :
        ∫ q in (p : ℝ)..1, distLowerQuantile μ q =
          ∫ q in (p : ℝ)..1, f q := by
      refine intervalIntegral.integral_congr_ae ?_
      filter_upwards [] with q
      intro hq
      have hqIoc : q ∈ Set.Ioc (p : ℝ) 1 := by
        simpa [Set.uIoc, le_of_lt hp] using hq
      have hq0 : q ≠ 0 := by linarith [hqIoc.1, p.2.1]
      simp [f, hq0]
    have hnonneg : 0 ≤ ∫ q in (p : ℝ)..1, -(f q) := by
      refine intervalIntegral.integral_nonneg (le_of_lt hp) ?_
      intro q hq
      by_cases hq0 : q = 0
      · simp [f, hq0]
      · have hqge0 : 0 ≤ q := le_trans p.2.1 hq.1
        have hq0' : (0 : ℝ) ≠ q := by exact fun h0q => hq0 h0q.symm
        have hqpos : 0 < q := lt_of_le_of_ne hqge0 hq0'
        have hqle1 : q ≤ 1 := hq.2
        have hqle : distLowerQuantile μ q ≤ 0 :=
          distLowerQuantile_le_zero_of_pos_le_one_of_cdf_zero_eq_one μ hqpos hqle1 hcdf0
        simpa [f, hq0] using neg_nonneg.mpr hqle
    have hneg_eq :
        ∫ q in (p : ℝ)..1, -(f q) = -(∫ q in (p : ℝ)..1, f q) := by
      simp
    have hmainf : ∫ q in (p : ℝ)..1, f q ≤ 0 := by
      linarith [hnonneg, hneg_eq]
    have hmain : ∫ q in (p : ℝ)..1, distLowerQuantile μ q ≤ 0 := by
      rw [hcongr]
      exact hmainf
    simpa using hmain
  have hmain : distES μ p ≤ 0 := by
    simp [distES, hp]
    have hfac_nonneg : 0 ≤ (1 - (p : ℝ))⁻¹ := by
      refine inv_nonneg.mpr ?_
      linarith
    exact mul_nonpos_of_nonneg_of_nonpos hfac_nonneg hInt_nonpos
  simpa [ES, hμ] using hmain

end FiniteConvexSupInfES

section FiniteConvexAESLowerBounds

variable {Ω : Type*} [MeasurableSpace Ω]
variable (P : Measure Ω) [IsProbabilityMeasure P]

/-- A concrete level always provides a lower bound for `AES`, once the penalty is nonnegative and
all strictly subunit levels have nonpositive `ES`. -/
private theorem AES_ge_of_level_witness_of_nonpos_lt_one
    {g : Level → ℝ} (Z : RandomVariable P) (hgnonneg : ∀ p : Level, 0 ≤ g p)
    (hES_nonpos_lt1 : ∀ p : Level, (p : ℝ) < 1 → ES P p Z ≤ 0) (p0 : Level) :
    ES P p0 Z - g p0 ≤ AES P g Z := by
  unfold AES ESg distESg
  refine le_csSup ?_ ?_
  · refine ⟨max 0 (ES P 1 Z), ?_⟩
    intro y hy
    rcases hy with ⟨p, rfl⟩
    by_cases hp : (p : ℝ) < 1
    · have hES : ES P p Z ≤ 0 := hES_nonpos_lt1 p hp
      have hg := hgnonneg p
      have hES' : distES (law P Z) p ≤ 0 := by simpa [ES] using hES
      calc
        distES (law P Z) p - g p ≤ 0 := by linarith
        _ ≤ max 0 (ES P 1 Z) := le_max_left _ _
    · have hp1 : p = 1 := by
        apply Subtype.ext
        have hpge : (1 : ℝ) ≤ p := by linarith
        exact le_antisymm p.2.2 hpge
      subst hp1
      have hg := hgnonneg (1 : Level)
      calc
        distES (law P Z) (1 : Level) - g (1 : Level) ≤ distES (law P Z) (1 : Level) := by
          linarith
        _ = ES P 1 Z := rfl
        _ ≤ max 0 (ES P 1 Z) := le_max_right _ _
  · exact ⟨p0, rfl⟩

/-- The `X ⊔ Y` witness from the finite convex lemma gives the required lower bound at `p₀`. -/
theorem AES_finiteConvexSup_ge_p0
    {g : Level → ℝ} {h u M b : ℝ} {E0 E1 E2 : Set Ω}
    (hE0 : MeasurableSet E0) (hE1 : MeasurableSet E1) (hE2 : MeasurableSet E2)
    (h01 : Disjoint E0 E1) (h02 : Disjoint E0 E2) (h12 : Disjoint E1 E2)
    (hh : 0 < h) (h3 : 3 * h < 1)
    (hE0mass : P.real E0 = 1 - 3 * h) (hE1mass : P.real E1 = h) (hE2mass : P.real E2 = h)
    (hbM : b < M) (hb : 0 < b) (hbu : b = 3 * u / 2)
    (hgnonneg : ∀ p : Level, 0 ≤ g p) :
    -u - g (finiteLevel0 h hh h3) ≤
      AES P g (finiteConvexSup P M b E0 E1 E2 hE0 (hE1.union hE2)) := by
  let Z : RandomVariable P := finiteConvexSup P M b E0 E1 E2 hE0 (hE1.union hE2)
  let p0 : Level := finiteLevel0 h hh h3
  have hAES :
      ES P p0 Z - g p0 ≤ AES P g Z :=
    AES_ge_of_level_witness_of_nonpos_lt_one (P := P) Z hgnonneg
      (fun p hp =>
        ES_finiteConvexSup_le_zero_of_lt_one (P := P) hE0 hE1 hE2 h01 h02 h12 hbM hb hp) p0
  have hES :
      ES P p0 Z = -(2 * b) / 3 := by
    simpa [Z, p0] using
      (ES_finiteConvexSup_at_p0 (P := P) hE0 hE1 hE2 h01 h02 h12 hh h3
        hE0mass hE1mass hE2mass hbM hb)
  calc
    -u - g (finiteLevel0 h hh h3) = ES P p0 Z - g p0 := by
      rw [hES, hbu]
      ring
    _ ≤ AES P g Z := hAES
    _ = AES P g (finiteConvexSup P M b E0 E1 E2 hE0 (hE1.union hE2)) := rfl

/-- The `X ⊓ Y` witness from the finite convex lemma gives the required lower bound at `p₂`. -/
theorem AES_finiteConvexInf_ge_p2
    {g : Level → ℝ} {h M a : ℝ} {E0 E1 E2 : Set Ω}
    (hE0 : MeasurableSet E0) (hE1 : MeasurableSet E1) (hE2 : MeasurableSet E2)
    (h01 : Disjoint E0 E1) (h02 : Disjoint E0 E2) (h12 : Disjoint E1 E2)
    (hh : 0 < h) (h3 : 3 * h < 1)
    (hE0mass : P.real E0 = 1 - 3 * h) (hE1mass : P.real E1 = h) (hE2mass : P.real E2 = h)
    (haM : a < M) (ha : 0 < a) (hgnonneg : ∀ p : Level, 0 ≤ g p) :
    -g (finiteLevel2 h hh h3) ≤
      AES P g (finiteConvexInf P M a E0 E1 E2 hE0 (hE1.union hE2)) := by
  let Z : RandomVariable P := finiteConvexInf P M a E0 E1 E2 hE0 (hE1.union hE2)
  let p2 : Level := finiteLevel2 h hh h3
  have hAES :
      ES P p2 Z - g p2 ≤ AES P g Z :=
    AES_ge_of_level_witness_of_nonpos_lt_one (P := P) Z hgnonneg
      (fun p hp =>
        ES_finiteConvexInf_le_zero_of_lt_one (P := P) hE0 hE1 hE2 h01 h02 h12 haM ha hp) p2
  have hES : ES P p2 Z = 0 := by
    simpa [Z, p2] using
      (ES_finiteConvexInf_at_p2 (P := P) hE0 hE1 hE2 h01 h02 h12 hh h3
        hE0mass hE1mass hE2mass haM ha)
  calc
    -g (finiteLevel2 h hh h3) = ES P p2 Z - g p2 := by
      change -g p2 = ES P p2 Z - g p2
      rw [hES]
      ring
    _ ≤ AES P g Z := hAES
    _ = AES P g (finiteConvexInf P M a E0 E1 E2 hE0 (hE1.union hE2)) := rfl

end FiniteConvexAESLowerBounds


section RhoLine

variable {Ω : Type*} [MeasurableSpace Ω]
variable (P : Measure Ω) [IsProbabilityMeasure P]

/-- The affine-line envelope `ρ_ℓ` from the finite convex manuscript proof. -/
def finiteRhoLine (g : Level → ℝ) (h r : ℝ) (hh : 0 < h) (h3 : 3 * h < 1)
    (Z : RandomVariable P) : ℝ :=
  sSup (Set.range fun p : Level => ES P p Z - finiteSupportLine g h r hh h3 p)

end RhoLine

section FiniteConvexRhoLineUpperBounds

variable {Ω : Type*} [MeasurableSpace Ω]
variable (P : Measure Ω) [IsProbabilityMeasure P]

/-- The affine support line is monotone when its slope is nonnegative. -/
private theorem finiteSupportLine_mono
    {g : Level → ℝ} {h r : ℝ} (hh : 0 < h) (h3 : 3 * h < 1) (hr : 0 ≤ r)
    {p q : Level} (hpq : (p : ℝ) ≤ q) :
    finiteSupportLine g h r hh h3 p ≤ finiteSupportLine g h r hh h3 q := by
  have hdiff :
      finiteSupportLine g h r hh h3 q - finiteSupportLine g h r hh h3 p =
        r * ((q : ℝ) - (p : ℝ)) := by
    simp [finiteSupportLine]
    ring_nf
  nlinarith

/-- The affine support line is increasing on `[0,1]` when its slope is nonnegative. -/
private theorem finiteSupportLine_zero_le
    {g : Level → ℝ} {h r : ℝ} (hh : 0 < h) (h3 : 3 * h < 1) (hr : 0 ≤ r) (p : Level) :
    finiteSupportLine g h r hh h3 0 ≤ finiteSupportLine g h r hh h3 p := by
  exact finiteSupportLine_mono hh h3 hr p.2.1

/-- Secant bound for `x ↦ 1 / x` on a positive interval. -/
private theorem inv_le_secant
    {A B x : ℝ} (hA : 0 < A) (hAB : A < B) (hxA : A ≤ x) (hxB : x ≤ B) :
    1 / x ≤ ((B - x) / (B - A)) * (1 / A) + ((x - A) / (B - A)) * (1 / B) := by
  have hB : 0 < B := lt_trans hA hAB
  have hx : 0 < x := lt_of_lt_of_le hA hxA
  have hBA : 0 < B - A := sub_pos.mpr hAB
  field_simp [hA.ne', hB.ne', hx.ne', hBA.ne']
  have hprod : 0 ≤ (x - A) * (B - x) := by
    nlinarith
  nlinarith

/-- A function of the form `c/x + s*x + t` is bounded above on a positive interval by the maximum
of its endpoint values. This is the endpoint-max step used in the finite convex proof. -/
private theorem invAffine_le_max_endpoints
    {A B x c s t : ℝ} (hA : 0 < A) (hAB : A < B) (hxA : A ≤ x) (hxB : x ≤ B) (hc : 0 ≤ c) :
    c / x + s * x + t ≤ max (c / A + s * A + t) (c / B + s * B + t) := by
  let α : ℝ := (B - x) / (B - A)
  let β : ℝ := (x - A) / (B - A)
  have hBA : 0 < B - A := sub_pos.mpr hAB
  have hα : 0 ≤ α := by
    dsimp [α]
    refine div_nonneg ?_ hBA.le
    linarith
  have hβ : 0 ≤ β := by
    dsimp [β]
    refine div_nonneg ?_ hBA.le
    linarith
  have hαβ : α + β = 1 := by
    dsimp [α, β]
    field_simp [hBA.ne']
    ring
  have hinv :
      c / x ≤ α * (c / A) + β * (c / B) := by
    have hbase := inv_le_secant hA hAB hxA hxB
    have hscaled := mul_le_mul_of_nonneg_left hbase hc
    simpa [α, β, mul_add, add_mul, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
      hscaled
  have hlin : α * (s * A + t) + β * (s * B + t) = s * x + t := by
    dsimp [α, β]
    field_simp [hBA.ne']
    ring
  have hcomb :
      c / x + (s * x + t) ≤
        α * (c / A + s * A + t) + β * (c / B + s * B + t) := by
    calc
      c / x + (s * x + t) ≤ (α * (c / A) + β * (c / B)) + (s * x + t) := by
        nlinarith [hinv]
      _ = α * (c / A + s * A + t) + β * (c / B + s * B + t) := by
        rw [← hlin]
        ring
  have hmax :
      α * (c / A + s * A + t) + β * (c / B + s * B + t) ≤
        max (c / A + s * A + t) (c / B + s * B + t) := by
    let m : ℝ := max (c / A + s * A + t) (c / B + s * B + t)
    have hAmax : c / A + s * A + t ≤ m := le_max_left _ _
    have hBmax : c / B + s * B + t ≤ m := le_max_right _ _
    calc
      α * (c / A + s * A + t) + β * (c / B + s * B + t) ≤ α * m + β * m := by
        gcongr
      _ = m := by
        calc
          α * m + β * m = (α + β) * m := by ring
          _ = m := by rw [hαβ]; ring
  simpa [add_comm, add_left_comm, add_assoc] using le_trans hcomb hmax

private theorem scaledIndicator_nonpos_of_nonpos (c : ℝ) (hc : c ≤ 0) (A : Set Ω) (ω : Ω) :
    scaledIndicator c A ω ≤ 0 := by
  by_cases hω : ω ∈ A
  · simp [scaledIndicator_eq_indicator_const, hω, hc]
  · simp [scaledIndicator_eq_indicator_const, hω]

private theorem finiteConvexX_pointwise_nonpos
    {M a b : ℝ} {E0 E1 E2 : Set Ω}
    (hE0 : MeasurableSet E0) (hE1 : MeasurableSet E1) (hE2 : MeasurableSet E2)
    (haM : a < M) (ha : 0 < a) (hb : 0 < b) (ω : Ω) :
    (finiteConvexX P M a b E0 E1 E2 hE0 hE1 hE2 : Ω → ℝ) ω ≤ 0 := by
  have h0 : scaledIndicator (-M) E0 ω ≤ 0 := by
    apply scaledIndicator_nonpos_of_nonpos
    linarith
  have h1 : scaledIndicator (-a) E1 ω ≤ 0 := by
    apply scaledIndicator_nonpos_of_nonpos
    linarith
  have h2 : scaledIndicator (-b) E2 ω ≤ 0 := by
    apply scaledIndicator_nonpos_of_nonpos
    linarith
  have hsum :
      scaledIndicator (-M) E0 ω + scaledIndicator (-a) E1 ω + scaledIndicator (-b) E2 ω ≤ 0 := by
    nlinarith
  simpa [finiteConvexX_apply] using hsum

private theorem finiteConvexY_pointwise_nonpos
    {M a b : ℝ} {E0 E1 E2 : Set Ω}
    (hE0 : MeasurableSet E0) (hE1 : MeasurableSet E1) (hE2 : MeasurableSet E2)
    (haM : a < M) (ha : 0 < a) (hb : 0 < b) (ω : Ω) :
    (finiteConvexY P M a b E0 E1 E2 hE0 hE1 hE2 : Ω → ℝ) ω ≤ 0 := by
  have h0 : scaledIndicator (-M) E0 ω ≤ 0 := by
    apply scaledIndicator_nonpos_of_nonpos
    linarith
  have h1 : scaledIndicator (-b) E1 ω ≤ 0 := by
    apply scaledIndicator_nonpos_of_nonpos
    linarith
  have h2 : scaledIndicator (-a) E2 ω ≤ 0 := by
    apply scaledIndicator_nonpos_of_nonpos
    linarith
  have hsum :
      scaledIndicator (-M) E0 ω + scaledIndicator (-b) E1 ω + scaledIndicator (-a) E2 ω ≤ 0 := by
    nlinarith
  simpa [finiteConvexY_apply] using hsum

private theorem distUpperQuantile_le_zero_of_ae_le_zero
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : ∀ᵐ x ∂μ, x ≤ 0) :
    distUpperQuantile μ ≤ 0 := by
  unfold distUpperQuantile
  rw [essSup_eq_sInf]
  let S : Set ℝ := {a : ℝ | μ {x : ℝ | a < x} = 0}
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
  · change μ (Set.Ioi 0) = 0
    simpa [ae_iff, not_le] using hμ

private theorem ES_finiteConvexX_at_one_le_zero
    {M a b : ℝ} {E0 E1 E2 : Set Ω}
    (hE0 : MeasurableSet E0) (hE1 : MeasurableSet E1) (hE2 : MeasurableSet E2)
    (haM : a < M) (ha : 0 < a) (hb : 0 < b) :
    ES P 1 (finiteConvexX P M a b E0 E1 E2 hE0 hE1 hE2) ≤ 0 := by
  let X : RandomVariable P := finiteConvexX P M a b E0 E1 E2 hE0 hE1 hE2
  change distES (law P X) (1 : Level) ≤ 0
  simp [distES]
  refine distUpperQuantile_le_zero_of_ae_le_zero (μ := law P X) ?_
  rw [law]
  exact (ae_map_iff X.2 (measurableSet_le measurable_id measurable_const)).2 <|
    Filter.Eventually.of_forall
      (finiteConvexX_pointwise_nonpos (P := P) hE0 hE1 hE2 haM ha hb)

private theorem ES_finiteConvexY_at_one_le_zero
    {M a b : ℝ} {E0 E1 E2 : Set Ω}
    (hE0 : MeasurableSet E0) (hE1 : MeasurableSet E1) (hE2 : MeasurableSet E2)
    (haM : a < M) (ha : 0 < a) (hb : 0 < b) :
    ES P 1 (finiteConvexY P M a b E0 E1 E2 hE0 hE1 hE2) ≤ 0 := by
  let Y : RandomVariable P := finiteConvexY P M a b E0 E1 E2 hE0 hE1 hE2
  change distES (law P Y) (1 : Level) ≤ 0
  simp [distES]
  refine distUpperQuantile_le_zero_of_ae_le_zero (μ := law P Y) ?_
  rw [law]
  exact (ae_map_iff Y.2 (measurableSet_le measurable_id measurable_const)).2 <|
    Filter.Eventually.of_forall
      (finiteConvexY_pointwise_nonpos (P := P) hE0 hE1 hE2 haM ha hb)

/-- If all ES levels are nonpositive and the affine support line lies below `g`, then the AES
envelope is bounded above by the affine-line envelope `ρ_ℓ`. -/
private theorem AES_le_finiteRhoLine_of_ES_nonpos_lt1
    {g : Level → ℝ} {h r : ℝ} (hh : 0 < h) (h3 : 3 * h < 1) (hr : 0 ≤ r)
    (Z : RandomVariable P)
    (hline : ∀ p : Level, finiteSupportLine g h r hh h3 p ≤ g p)
    (hES_nonpos_lt1 : ∀ p : Level, (p : ℝ) < 1 → ES P p Z ≤ 0) :
    AES P g Z ≤ finiteRhoLine P g h r hh h3 Z := by
  let B : Set ℝ := Set.range fun p : Level => ES P p Z - finiteSupportLine g h r hh h3 p
  let C : ℝ := max 0 (ES P 1 Z) - finiteSupportLine g h r hh h3 0
  have hBdd : BddAbove B := by
    refine ⟨C, ?_⟩
    intro y hy
    rcases hy with ⟨p, rfl⟩
    have hmono : finiteSupportLine g h r hh h3 0 ≤ finiteSupportLine g h r hh h3 p :=
      finiteSupportLine_zero_le hh h3 hr p
    by_cases hp : (p : ℝ) < 1
    · have hES : ES P p Z ≤ 0 := hES_nonpos_lt1 p hp
      have h1 :
          ES P p Z - finiteSupportLine g h r hh h3 p ≤ 0 - finiteSupportLine g h r hh h3 p := by
        linarith
      have h2 :
          0 - finiteSupportLine g h r hh h3 p ≤ 0 - finiteSupportLine g h r hh h3 0 := by
        linarith
      have h3' : 0 - finiteSupportLine g h r hh h3 0 ≤ C := by
        unfold C
        exact sub_le_sub_right (le_max_left 0 (ES P 1 Z)) _
      exact le_trans h1 (le_trans h2 h3')
    · have hp1 : p = 1 := by
        apply Subtype.ext
        have hpge : (1 : ℝ) ≤ p := by linarith
        exact le_antisymm p.2.2 hpge
      subst hp1
      have h1 :
          ES P (1 : Level) Z - finiteSupportLine g h r hh h3 1 ≤
            max 0 (ES P 1 Z) - finiteSupportLine g h r hh h3 1 := by
        exact sub_le_sub_right (le_max_right 0 (ES P 1 Z)) _
      have h2 :
          max 0 (ES P 1 Z) - finiteSupportLine g h r hh h3 1 ≤ C := by
        unfold C
        linarith
      exact le_trans h1 h2
  unfold AES ESg distESg finiteRhoLine
  refine csSup_le ?_ ?_
  · exact Set.range_nonempty _
  · intro y hy
    rcases hy with ⟨p, rfl⟩
    have hlinep : finiteSupportLine g h r hh h3 p ≤ g p := hline p
    have hterm :
        ES P p Z - g p ≤ ES P p Z - finiteSupportLine g h r hh h3 p := by
      linarith
    have hsSup :
        ES P p Z - finiteSupportLine g h r hh h3 p ≤
          sSup (Set.range fun q : Level => ES P q Z - finiteSupportLine g h r hh h3 q) :=
      le_csSup hBdd ⟨p, rfl⟩
    exact le_trans hterm hsSup

theorem AES_finiteConvexX_le_finiteRhoLine
    {g : Level → ℝ} {h r M a b : ℝ} {E0 E1 E2 : Set Ω}
    (hE0 : MeasurableSet E0) (hE1 : MeasurableSet E1) (hE2 : MeasurableSet E2)
    (h01 : Disjoint E0 E1) (h02 : Disjoint E0 E2) (h12 : Disjoint E1 E2)
    (hh : 0 < h) (h3 : 3 * h < 1) (hr : 0 ≤ r)
    (haM : a < M) (ha : 0 < a) (hb : 0 < b) (hba : b ≤ a)
    (hline : ∀ p : Level, finiteSupportLine g h r hh h3 p ≤ g p) :
    AES P g (finiteConvexX P M a b E0 E1 E2 hE0 hE1 hE2) ≤
      finiteRhoLine P g h r hh h3 (finiteConvexX P M a b E0 E1 E2 hE0 hE1 hE2) := by
  refine
    AES_le_finiteRhoLine_of_ES_nonpos_lt1 (P := P) hh h3 hr
      (finiteConvexX P M a b E0 E1 E2 hE0 hE1 hE2) hline ?_
  intro p hp
  exact ES_finiteConvexX_le_zero_of_lt_one (P := P) hE0 hE1 hE2 h01 h02 h12 haM ha hb hba hp

theorem AES_finiteConvexY_le_finiteRhoLine
    {g : Level → ℝ} {h r M a b : ℝ} {E0 E1 E2 : Set Ω}
    (hE0 : MeasurableSet E0) (hE1 : MeasurableSet E1) (hE2 : MeasurableSet E2)
    (h01 : Disjoint E0 E1) (h02 : Disjoint E0 E2) (h12 : Disjoint E1 E2)
    (hh : 0 < h) (h3 : 3 * h < 1) (hr : 0 ≤ r)
    (haM : a < M) (ha : 0 < a) (hb : 0 < b) (hba : b ≤ a)
    (hline : ∀ p : Level, finiteSupportLine g h r hh h3 p ≤ g p) :
    AES P g (finiteConvexY P M a b E0 E1 E2 hE0 hE1 hE2) ≤
      finiteRhoLine P g h r hh h3 (finiteConvexY P M a b E0 E1 E2 hE0 hE1 hE2) := by
  refine
    AES_le_finiteRhoLine_of_ES_nonpos_lt1 (P := P) hh h3 hr
      (finiteConvexY P M a b E0 E1 E2 hE0 hE1 hE2) hline ?_
  intro p hp
  exact ES_finiteConvexY_le_zero_of_lt_one (P := P) hE0 hE1 hE2 h01 h02 h12 haM ha hb hba hp

end FiniteConvexRhoLineUpperBounds

section FiniteConvexLineValues

variable {Ω : Type*} [MeasurableSpace Ω]
variable (P : Measure Ω) [IsProbabilityMeasure P]

theorem finiteConvexX_minus_line_at_p0
    {g : Level → ℝ} {h r u M a b : ℝ} {E0 E1 E2 : Set Ω}
    (hE0 : MeasurableSet E0) (hE1 : MeasurableSet E1) (hE2 : MeasurableSet E2)
    (h01 : Disjoint E0 E1) (h02 : Disjoint E0 E2) (h12 : Disjoint E1 E2)
    (hh : 0 < h) (h3 : 3 * h < 1) (hu : u = r * h)
    (hE0mass : P.real E0 = 1 - 3 * h) (hE1mass : P.real E1 = h) (hE2mass : P.real E2 = h)
    (hba : b < a) (haM : a < M) (hb : 0 < b) (habu : a + b = 15 * u / 2) :
    ES P (finiteLevel0 h hh h3) (finiteConvexX P M a b E0 E1 E2 hE0 hE1 hE2) -
        finiteSupportLine g h r hh h3 (finiteLevel0 h hh h3) =
      -(3 * u / 2) - g (finiteLevel1 h hh h3) := by
  have hES := ES_finiteConvexX_at_p0 (P := P) hE0 hE1 hE2 h01 h02 h12 hh h3
    hE0mass hE1mass hE2mass hba haM hb
  rw [hES, finiteSupportLine_apply_p0, hu]
  linarith

theorem finiteConvexX_minus_line_at_p1
    {g : Level → ℝ} {h r u M a b : ℝ} {E0 E1 E2 : Set Ω}
    (hE0 : MeasurableSet E0) (hE1 : MeasurableSet E1) (hE2 : MeasurableSet E2)
    (h01 : Disjoint E0 E1) (h02 : Disjoint E0 E2) (h12 : Disjoint E1 E2)
    (hh : 0 < h) (h3 : 3 * h < 1) (hu : u = r * h)
    (hE0mass : P.real E0 = 1 - 3 * h) (hE1mass : P.real E1 = h) (hE2mass : P.real E2 = h)
    (hba : b < a) (haM : a < M) (hb : 0 < b) (hbu : b = 3 * u / 2) :
    ES P (finiteLevel1 h hh h3) (finiteConvexX P M a b E0 E1 E2 hE0 hE1 hE2) -
        finiteSupportLine g h r hh h3 (finiteLevel1 h hh h3) =
      -(3 * u / 4) - g (finiteLevel1 h hh h3) := by
  have hES := ES_finiteConvexX_at_p1 (P := P) hE0 hE1 hE2 h01 h02 h12 hh h3
    hE0mass hE1mass hE2mass hba haM hb
  rw [hES, finiteSupportLine_apply_p1, hbu]
  ring

theorem finiteConvexX_minus_line_at_p2
    {g : Level → ℝ} {h r u M a b : ℝ} {E0 E1 E2 : Set Ω}
    (hE0 : MeasurableSet E0) (hE1 : MeasurableSet E1) (hE2 : MeasurableSet E2)
    (h01 : Disjoint E0 E1) (h02 : Disjoint E0 E2) (h12 : Disjoint E1 E2)
    (hh : 0 < h) (h3 : 3 * h < 1) (hu : u = r * h)
    (hE0mass : P.real E0 = 1 - 3 * h) (hE1mass : P.real E1 = h) (hE2mass : P.real E2 = h)
    (hba : b < a) (haM : a < M) (hb : 0 < b) :
    ES P (finiteLevel2 h hh h3) (finiteConvexX P M a b E0 E1 E2 hE0 hE1 hE2) -
        finiteSupportLine g h r hh h3 (finiteLevel2 h hh h3) =
      -u - g (finiteLevel1 h hh h3) := by
  have hES := ES_finiteConvexX_at_p2 (P := P) hE0 hE1 hE2 h01 h02 h12 hh h3
    hE0mass hE1mass hE2mass hba haM hb
  rw [hES, finiteSupportLine_apply_p2, hu]
  ring

theorem finiteConvexY_minus_line_at_p1
    {g : Level → ℝ} {h r u M a b : ℝ} {E0 E1 E2 : Set Ω}
    (hE0 : MeasurableSet E0) (hE1 : MeasurableSet E1) (hE2 : MeasurableSet E2)
    (h01 : Disjoint E0 E1) (h02 : Disjoint E0 E2) (h12 : Disjoint E1 E2)
    (hh : 0 < h) (h3 : 3 * h < 1) (hu : u = r * h)
    (hE0mass : P.real E0 = 1 - 3 * h) (hE1mass : P.real E1 = h) (hE2mass : P.real E2 = h)
    (hba : b < a) (haM : a < M) (hb : 0 < b) (hbu : b = 3 * u / 2) :
    ES P (finiteLevel1 h hh h3) (finiteConvexY P M a b E0 E1 E2 hE0 hE1 hE2) -
        finiteSupportLine g h r hh h3 (finiteLevel1 h hh h3) =
      -(3 * u / 4) - g (finiteLevel1 h hh h3) := by
  have hES := ES_finiteConvexY_at_p1 (P := P) hE0 hE1 hE2 h01 h02 h12 hh h3
    hE0mass hE1mass hE2mass hba haM hb
  rw [hES, finiteSupportLine_apply_p1, hbu]
  ring

theorem ES_finiteConvexX_at_zero
    {h M a b : ℝ} {E0 E1 E2 : Set Ω}
    (hE0 : MeasurableSet E0) (hE1 : MeasurableSet E1) (hE2 : MeasurableSet E2)
    (h01 : Disjoint E0 E1) (h02 : Disjoint E0 E2) (h12 : Disjoint E1 E2)
    (hh : 0 < h) (h3 : 3 * h < 1)
    (hE0mass : P.real E0 = 1 - 3 * h) (hE1mass : P.real E1 = h) (hE2mass : P.real E2 = h)
    (hba : b < a) (haM : a < M) (hb : 0 < b) :
    ES P 0 (finiteConvexX P M a b E0 E1 E2 hE0 hE1 hE2) =
      -(1 - 3 * h) * M - h * (a + b) := by
  have hES :=
    ES_finiteConvexX_formula_on_Icc_zero_p0 (P := P)
      hE0 hE1 hE2 h01 h02 h12 hh h3 hE0mass hE1mass hE2mass hba haM hb
      (p := (0 : Level)) (by
        change (0 : ℝ) ≤ 1 - 3 * h
        linarith [h3])
  calc
    ES P 0 (finiteConvexX P M a b E0 E1 E2 hE0 hE1 hE2) =
        (-M * ((1 - 3 * h) - (0 : ℝ)) - h * (a + b)) / (1 - (0 : ℝ)) := hES
    _ = -(1 - 3 * h) * M - h * (a + b) := by ring

theorem finiteConvexX_minus_line_at_zero
    {g : Level → ℝ} {h r M a b : ℝ} {E0 E1 E2 : Set Ω}
    (hE0 : MeasurableSet E0) (hE1 : MeasurableSet E1) (hE2 : MeasurableSet E2)
    (h01 : Disjoint E0 E1) (h02 : Disjoint E0 E2) (h12 : Disjoint E1 E2)
    (hh : 0 < h) (h3 : 3 * h < 1)
    (hE0mass : P.real E0 = 1 - 3 * h) (hE1mass : P.real E1 = h) (hE2mass : P.real E2 = h)
    (hba : b < a) (haM : a < M) (hb : 0 < b) :
    ES P 0 (finiteConvexX P M a b E0 E1 E2 hE0 hE1 hE2) -
        finiteSupportLine g h r hh h3 0 =
      (-(1 - 3 * h) * M - h * (a + b)) - finiteSupportLine g h r hh h3 0 := by
  rw [ES_finiteConvexX_at_zero (P := P) hE0 hE1 hE2 h01 h02 h12 hh h3
    hE0mass hE1mass hE2mass hba haM hb]

end FiniteConvexLineValues

section FiniteConvexRhoLineMaximizers

variable {Ω : Type*} [MeasurableSpace Ω]
variable (P : Measure Ω) [IsProbabilityMeasure P]

theorem finiteConvexY_eq_finiteConvexX_swap
    {M a b : ℝ} {E0 E1 E2 : Set Ω}
    (hE0 : MeasurableSet E0) (hE1 : MeasurableSet E1) (hE2 : MeasurableSet E2) :
    finiteConvexY P M a b E0 E1 E2 hE0 hE1 hE2 =
      finiteConvexX P M a b E0 E2 E1 hE0 hE2 hE1 := by
  ext ω
  simp [finiteConvexX_apply, finiteConvexY_apply, add_assoc, add_left_comm, add_comm]

private theorem finiteConvexX_minus_line_le_at_p1_on_Icc_zero_p0
    {g : Level → ℝ} {h r u M a b : ℝ} {E0 E1 E2 : Set Ω} {p : Level}
    (hE0 : MeasurableSet E0) (hE1 : MeasurableSet E1) (hE2 : MeasurableSet E2)
    (h01 : Disjoint E0 E1) (h02 : Disjoint E0 E2) (h12 : Disjoint E1 E2)
    (hh : 0 < h) (h3 : 3 * h < 1) (hr : 0 ≤ r) (hu : u = r * h)
    (hE0mass : P.real E0 = 1 - 3 * h) (hE1mass : P.real E1 = h) (hE2mass : P.real E2 = h)
    (hba : b < a) (haM : a < M) (hb : 0 < b) (habu : a + b = 15 * u / 2)
    (hMlarge :
      (-(1 - 3 * h) * M - h * (a + b)) - finiteSupportLine g h r hh h3 0 <
        -(3 * u / 4) - g (finiteLevel1 h hh h3))
    (hp0 : (p : ℝ) ≤ 1 - 3 * h) :
    ES P p (finiteConvexX P M a b E0 E1 E2 hE0 hE1 hE2) -
        finiteSupportLine g h r hh h3 p ≤
      -(3 * u / 4) - g (finiteLevel1 h hh h3) := by
  let p1 : Level := finiteLevel1 h hh h3
  let x : ℝ := 1 - (p : ℝ)
  have hA : 0 < 3 * h := by nlinarith
  have hAB : 3 * h < 1 := by linarith [h3]
  have hxA : 3 * h ≤ x := by
    dsimp [x]
    linarith
  have hxB : x ≤ 1 := by
    dsimp [x]
    linarith [p.2.1]
  have hc : 0 ≤ h * (3 * M - (a + b)) := by
    nlinarith
  have hformula :=
    ES_finiteConvexX_formula_on_Icc_zero_p0 (P := P)
      hE0 hE1 hE2 h01 h02 h12 hh h3 hE0mass hE1mass hE2mass hba haM hb hp0
  have hterm :
      ES P p (finiteConvexX P M a b E0 E1 E2 hE0 hE1 hE2) -
          finiteSupportLine g h r hh h3 p =
        (h * (3 * M - (a + b))) / x + r * x + (-M - g p1 - 2 * u) := by
    rw [hformula]
    dsimp [x, p1, finiteSupportLine]
    field_simp [show 1 - (p : ℝ) ≠ 0 by linarith]
    ring_nf
    rw [hu]
    ring
  have hbound :
      (h * (3 * M - (a + b))) / x + r * x + (-M - g p1 - 2 * u) ≤
        max
          ((h * (3 * M - (a + b))) / (3 * h) + r * (3 * h) + (-M - g p1 - 2 * u))
          ((h * (3 * M - (a + b))) / 1 + r * 1 + (-M - g p1 - 2 * u)) := by
    exact invAffine_le_max_endpoints hA hAB hxA hxB hc
  have hAeq :
      (h * (3 * M - (a + b))) / (3 * h) + r * (3 * h) + (-M - g p1 - 2 * u) =
        -(3 * u / 2) - g p1 := by
    have hh0 : h ≠ 0 := by linarith
    dsimp [p1]
    rw [hu, habu]
    field_simp [hh0]
    nlinarith
  have hBeq :
      (h * (3 * M - (a + b))) / 1 + r * 1 + (-M - g p1 - 2 * u) =
        (-(1 - 3 * h) * M - h * (a + b)) - finiteSupportLine g h r hh h3 0 := by
    dsimp [p1, finiteSupportLine]
    rw [hu]
    ring
  have hp0lt :
      -(3 * u / 2) - g p1 < -(3 * u / 4) - g p1 := by
    nlinarith [hb, hu]
  calc
    ES P p (finiteConvexX P M a b E0 E1 E2 hE0 hE1 hE2) -
        finiteSupportLine g h r hh h3 p =
        (h * (3 * M - (a + b))) / x + r * x + (-M - g p1 - 2 * u) := hterm
    _ ≤ max
          ((h * (3 * M - (a + b))) / (3 * h) + r * (3 * h) + (-M - g p1 - 2 * u))
          ((h * (3 * M - (a + b))) / 1 + r * 1 + (-M - g p1 - 2 * u)) := hbound
    _ ≤ -(3 * u / 4) - g p1 := by
      rw [hAeq, hBeq]
      exact max_le hp0lt.le hMlarge.le

private theorem finiteConvexX_minus_line_le_at_p1_on_Icc_p0_p1
    {g : Level → ℝ} {h r u M a b : ℝ} {E0 E1 E2 : Set Ω} {p : Level}
    (hE0 : MeasurableSet E0) (hE1 : MeasurableSet E1) (hE2 : MeasurableSet E2)
    (h01 : Disjoint E0 E1) (h02 : Disjoint E0 E2) (h12 : Disjoint E1 E2)
    (hh : 0 < h) (h3 : 3 * h < 1) (hr : 0 ≤ r) (hu : u = r * h)
    (hE0mass : P.real E0 = 1 - 3 * h) (hE1mass : P.real E1 = h) (hE2mass : P.real E2 = h)
    (hba : b < a) (haM : a < M) (hb : 0 < b) (habu : a + b = 15 * u / 2)
    (hbu : b = 3 * u / 2) (hp0 : 1 - 3 * h ≤ (p : ℝ)) (hp1 : (p : ℝ) ≤ 1 - 2 * h) :
    ES P p (finiteConvexX P M a b E0 E1 E2 hE0 hE1 hE2) -
        finiteSupportLine g h r hh h3 p ≤
      -(3 * u / 4) - g (finiteLevel1 h hh h3) := by
  let p1L : Level := finiteLevel1 h hh h3
  let x : ℝ := 1 - (p : ℝ)
  have hA : 0 < 2 * h := by nlinarith
  have hAB : 2 * h < 3 * h := by nlinarith
  have hxA : 2 * h ≤ x := by
    dsimp [x]
    linarith
  have hxB : x ≤ 3 * h := by
    dsimp [x]
    linarith
  have hc : 0 ≤ h * (2 * a - b) := by
    nlinarith
  have hformula :=
    ES_finiteConvexX_formula_on_Icc_p0_p1 (P := P)
      hE0 hE1 hE2 h01 h02 h12 hh h3 hE0mass hE1mass hE2mass hba haM hb hp0 hp1
  have hterm :
      ES P p (finiteConvexX P M a b E0 E1 E2 hE0 hE1 hE2) -
          finiteSupportLine g h r hh h3 p =
        (h * (2 * a - b)) / x + r * x + (-a - g p1L - 2 * u) := by
    rw [hformula]
    dsimp [x, p1L, finiteSupportLine]
    field_simp [show 1 - (p : ℝ) ≠ 0 by linarith]
    rw [hu]
    ring
  have hbound :
      (h * (2 * a - b)) / x + r * x + (-a - g p1L - 2 * u) ≤
        max
          ((h * (2 * a - b)) / (2 * h) + r * (2 * h) + (-a - g p1L - 2 * u))
          ((h * (2 * a - b)) / (3 * h) + r * (3 * h) + (-a - g p1L - 2 * u)) := by
    exact invAffine_le_max_endpoints hA hAB hxA hxB hc
  have hAeq :
      (h * (2 * a - b)) / (2 * h) + r * (2 * h) + (-a - g p1L - 2 * u) =
        -(3 * u / 4) - g p1L := by
    have hh0 : h ≠ 0 := by linarith
    rw [hu, hbu]
    field_simp [hh0]
    nlinarith
  have hBeq :
      (h * (2 * a - b)) / (3 * h) + r * (3 * h) + (-a - g p1L - 2 * u) =
        -(3 * u / 2) - g p1L := by
    have hh0 : h ≠ 0 := by linarith
    have hau : a = 6 * u := by
      linarith [habu, hbu]
    rw [hu, hbu, hau]
    field_simp [hh0]
    nlinarith
  have hp0lt :
      -(3 * u / 2) - g p1L < -(3 * u / 4) - g p1L := by
    nlinarith [hb, hbu]
  calc
    ES P p (finiteConvexX P M a b E0 E1 E2 hE0 hE1 hE2) -
        finiteSupportLine g h r hh h3 p =
        (h * (2 * a - b)) / x + r * x + (-a - g p1L - 2 * u) := hterm
    _ ≤ max
          ((h * (2 * a - b)) / (2 * h) + r * (2 * h) + (-a - g p1L - 2 * u))
          ((h * (2 * a - b)) / (3 * h) + r * (3 * h) + (-a - g p1L - 2 * u)) := hbound
    _ ≤ -(3 * u / 4) - g p1L := by
      rw [hAeq, hBeq]
      exact max_le le_rfl hp0lt.le

private theorem finiteConvexX_minus_line_le_at_p1_on_Icc_p1_p2
    {g : Level → ℝ} {h r u M a b : ℝ} {E0 E1 E2 : Set Ω} {p : Level}
    (hE0 : MeasurableSet E0) (hE1 : MeasurableSet E1) (hE2 : MeasurableSet E2)
    (h01 : Disjoint E0 E1) (h02 : Disjoint E0 E2) (h12 : Disjoint E1 E2)
    (hh : 0 < h) (h3 : 3 * h < 1) (hr : 0 ≤ r) (hu : u = r * h)
    (hE0mass : P.real E0 = 1 - 3 * h) (hE1mass : P.real E1 = h) (hE2mass : P.real E2 = h)
    (hba : b < a) (haM : a < M) (hb : 0 < b) (hbu : b = 3 * u / 2)
    (hp1 : 1 - 2 * h ≤ (p : ℝ)) (hp2 : (p : ℝ) ≤ 1 - h) :
    ES P p (finiteConvexX P M a b E0 E1 E2 hE0 hE1 hE2) -
        finiteSupportLine g h r hh h3 p ≤
      -(3 * u / 4) - g (finiteLevel1 h hh h3) := by
  let p1L : Level := finiteLevel1 h hh h3
  let p2L : Level := finiteLevel2 h hh h3
  let x : ℝ := 1 - (p : ℝ)
  have hA : 0 < h := hh
  have hAB : h < 2 * h := by nlinarith
  have hxA : h ≤ x := by
    dsimp [x]
    linarith
  have hxB : x ≤ 2 * h := by
    dsimp [x]
    linarith
  have hc : 0 ≤ b * h := by nlinarith
  have hformula :=
    ES_finiteConvexX_formula_on_Icc_p1_p2 (P := P)
      hE0 hE1 hE2 h01 h02 h12 hh h3 hE0mass hE1mass hE2mass hba haM hb hp1 hp2
  have hterm :
      ES P p (finiteConvexX P M a b E0 E1 E2 hE0 hE1 hE2) -
          finiteSupportLine g h r hh h3 p =
        (b * h) / x + r * x + (-b - g p1L - 2 * u) := by
    rw [hformula]
    dsimp [x, p1L, finiteSupportLine]
    field_simp [show 1 - (p : ℝ) ≠ 0 by linarith]
    rw [hu]
    ring
  have hbound :
      (b * h) / x + r * x + (-b - g p1L - 2 * u) ≤
        max
          ((b * h) / h + r * h + (-b - g p1L - 2 * u))
          ((b * h) / (2 * h) + r * (2 * h) + (-b - g p1L - 2 * u)) := by
    exact invAffine_le_max_endpoints hA hAB hxA hxB hc
  have hAeq :
      (b * h) / h + r * h + (-b - g p1L - 2 * u) = -u - g p1L := by
    have hh0 : h ≠ 0 := by linarith
    rw [hu]
    field_simp [hh0]
    nlinarith
  have hBeq :
      (b * h) / (2 * h) + r * (2 * h) + (-b - g p1L - 2 * u) =
        -(3 * u / 4) - g p1L := by
    have hh0 : h ≠ 0 := by linarith
    rw [hu, hbu]
    field_simp [hh0]
    nlinarith
  have hp2lt :
      -u - g p1L < -(3 * u / 4) - g p1L := by
    nlinarith [hb, hbu]
  calc
    ES P p (finiteConvexX P M a b E0 E1 E2 hE0 hE1 hE2) -
        finiteSupportLine g h r hh h3 p =
        (b * h) / x + r * x + (-b - g p1L - 2 * u) := hterm
    _ ≤ max
          ((b * h) / h + r * h + (-b - g p1L - 2 * u))
          ((b * h) / (2 * h) + r * (2 * h) + (-b - g p1L - 2 * u)) := hbound
    _ ≤ -(3 * u / 4) - g p1L := by
      rw [hAeq, hBeq]
      exact max_le hp2lt.le le_rfl

private theorem finiteConvexX_minus_line_le_at_p1_on_Icc_p2_one
    {g : Level → ℝ} {h r u M a b : ℝ} {E0 E1 E2 : Set Ω} {p : Level}
    (hE0 : MeasurableSet E0) (hE1 : MeasurableSet E1) (hE2 : MeasurableSet E2)
    (h01 : Disjoint E0 E1) (h02 : Disjoint E0 E2) (h12 : Disjoint E1 E2)
    (hh : 0 < h) (h3 : 3 * h < 1) (hr : 0 ≤ r) (hu : u = r * h)
    (hE0mass : P.real E0 = 1 - 3 * h) (hE1mass : P.real E1 = h) (hE2mass : P.real E2 = h)
    (hba : b < a) (haM : a < M) (hb : 0 < b) (hbu : b = 3 * u / 2)
    (hp2 : 1 - h ≤ (p : ℝ)) :
    ES P p (finiteConvexX P M a b E0 E1 E2 hE0 hE1 hE2) -
        finiteSupportLine g h r hh h3 p ≤
      -(3 * u / 4) - g (finiteLevel1 h hh h3) := by
  let p1L : Level := finiteLevel1 h hh h3
  let p2L : Level := finiteLevel2 h hh h3
  have hp2mono : (p2L : ℝ) ≤ p := by simpa [p2L] using hp2
  have hline_mono : finiteSupportLine g h r hh h3 p2L ≤ finiteSupportLine g h r hh h3 p :=
    finiteSupportLine_mono (hh := hh) (h3 := h3) (hr := hr) hp2mono
  have hupper_p2 : 0 - finiteSupportLine g h r hh h3 p2L ≤ -(3 * u / 4) - g p1L := by
    rw [finiteSupportLine_apply_p2, hu]
    nlinarith [hb, hbu]
  by_cases hp1 : (p : ℝ) < 1
  · have hES : ES P p (finiteConvexX P M a b E0 E1 E2 hE0 hE1 hE2) ≤ 0 :=
        ES_finiteConvexX_le_zero_of_lt_one (P := P) hE0 hE1 hE2 h01 h02 h12 haM (by linarith)
          hb (by linarith) hp1
    have hterm : ES P p (finiteConvexX P M a b E0 E1 E2 hE0 hE1 hE2) -
        finiteSupportLine g h r hh h3 p ≤
      0 - finiteSupportLine g h r hh h3 p2L := by
      linarith
    exact le_trans hterm hupper_p2
  · have hp_eq : p = 1 := by
      apply Subtype.ext
      have hpge : (1 : ℝ) ≤ p := by linarith
      exact le_antisymm p.2.2 hpge
    subst hp_eq
    have hES : ES P 1 (finiteConvexX P M a b E0 E1 E2 hE0 hE1 hE2) ≤ 0 :=
      ES_finiteConvexX_at_one_le_zero (P := P) hE0 hE1 hE2 haM (by linarith) hb
    have hterm : ES P 1 (finiteConvexX P M a b E0 E1 E2 hE0 hE1 hE2) -
        finiteSupportLine g h r hh h3 1 ≤
      0 - finiteSupportLine g h r hh h3 p2L := by
      linarith
    exact le_trans hterm hupper_p2

private theorem finiteConvexX_minus_line_le_at_p1
    {g : Level → ℝ} {h r u M a b : ℝ} {E0 E1 E2 : Set Ω} (p : Level)
    (hE0 : MeasurableSet E0) (hE1 : MeasurableSet E1) (hE2 : MeasurableSet E2)
    (h01 : Disjoint E0 E1) (h02 : Disjoint E0 E2) (h12 : Disjoint E1 E2)
    (hh : 0 < h) (h3 : 3 * h < 1) (hr : 0 ≤ r) (hu : u = r * h)
    (hE0mass : P.real E0 = 1 - 3 * h) (hE1mass : P.real E1 = h) (hE2mass : P.real E2 = h)
    (hba : b < a) (haM : a < M) (hb : 0 < b) (habu : a + b = 15 * u / 2)
    (hbu : b = 3 * u / 2)
    (hMlarge :
      (-(1 - 3 * h) * M - h * (a + b)) - finiteSupportLine g h r hh h3 0 <
        -(3 * u / 4) - g (finiteLevel1 h hh h3)) :
    ES P p (finiteConvexX P M a b E0 E1 E2 hE0 hE1 hE2) -
        finiteSupportLine g h r hh h3 p ≤
      -(3 * u / 4) - g (finiteLevel1 h hh h3) := by
  by_cases hp0 : (p : ℝ) ≤ 1 - 3 * h
  · exact finiteConvexX_minus_line_le_at_p1_on_Icc_zero_p0
      (P := P) hE0 hE1 hE2 h01 h02 h12 hh h3 hr hu
      hE0mass hE1mass hE2mass hba haM hb habu hMlarge hp0
  · by_cases hp1 : (p : ℝ) ≤ 1 - 2 * h
    · have hp0' : 1 - 3 * h ≤ (p : ℝ) := by linarith
      exact finiteConvexX_minus_line_le_at_p1_on_Icc_p0_p1
        (P := P) hE0 hE1 hE2 h01 h02 h12 hh h3 hr hu hE0mass hE1mass hE2mass
        hba haM hb habu hbu hp0' hp1
    · by_cases hp2 : (p : ℝ) ≤ 1 - h
      · have hp1' : 1 - 2 * h ≤ (p : ℝ) := by linarith
        exact finiteConvexX_minus_line_le_at_p1_on_Icc_p1_p2
          (P := P) hE0 hE1 hE2 h01 h02 h12 hh h3 hr hu hE0mass hE1mass hE2mass
          hba haM hb hbu hp1' hp2
      · have hp2' : 1 - h ≤ (p : ℝ) := by linarith
        exact finiteConvexX_minus_line_le_at_p1_on_Icc_p2_one
          (P := P) hE0 hE1 hE2 h01 h02 h12 hh h3 hr hu hE0mass hE1mass hE2mass
          hba haM hb hbu hp2'

theorem finiteRhoLine_finiteConvexX_eq_at_p1
    {g : Level → ℝ} {h r u M a b : ℝ} {E0 E1 E2 : Set Ω}
    (hE0 : MeasurableSet E0) (hE1 : MeasurableSet E1) (hE2 : MeasurableSet E2)
    (h01 : Disjoint E0 E1) (h02 : Disjoint E0 E2) (h12 : Disjoint E1 E2)
    (hh : 0 < h) (h3 : 3 * h < 1) (hr : 0 ≤ r) (hu : u = r * h)
    (hE0mass : P.real E0 = 1 - 3 * h) (hE1mass : P.real E1 = h) (hE2mass : P.real E2 = h)
    (hba : b < a) (haM : a < M) (hb : 0 < b) (habu : a + b = 15 * u / 2)
    (hbu : b = 3 * u / 2)
    (hMlarge :
      (-(1 - 3 * h) * M - h * (a + b)) - finiteSupportLine g h r hh h3 0 <
        -(3 * u / 4) - g (finiteLevel1 h hh h3)) :
    finiteRhoLine P g h r hh h3 (finiteConvexX P M a b E0 E1 E2 hE0 hE1 hE2) =
      -(3 * u / 4) - g (finiteLevel1 h hh h3) := by
  let p1 : Level := finiteLevel1 h hh h3
  let X : RandomVariable P := finiteConvexX P M a b E0 E1 E2 hE0 hE1 hE2
  have hub :
      finiteRhoLine P g h r hh h3 X ≤ -(3 * u / 4) - g p1 := by
    unfold finiteRhoLine
    refine csSup_le ?_ ?_
    · exact Set.range_nonempty _
    · intro y hy
      rcases hy with ⟨p, rfl⟩
      exact finiteConvexX_minus_line_le_at_p1 (P := P) p
        hE0 hE1 hE2 h01 h02 h12 hh h3 hr hu hE0mass hE1mass hE2mass hba haM hb habu hbu
        hMlarge
  have hBdd : BddAbove (Set.range fun p : Level => ES P p X - finiteSupportLine g h r hh h3 p) :=
    ⟨-(3 * u / 4) - g p1, by
      intro y hy
      rcases hy with ⟨p, rfl⟩
      exact finiteConvexX_minus_line_le_at_p1 (P := P) p
        hE0 hE1 hE2 h01 h02 h12 hh h3 hr hu hE0mass hE1mass hE2mass hba haM hb habu hbu
        hMlarge⟩
  have hlb :
      -(3 * u / 4) - g p1 ≤ finiteRhoLine P g h r hh h3 X := by
    unfold finiteRhoLine
    refine le_csSup hBdd ?_
    refine ⟨p1, ?_⟩
    simpa [X, p1] using
      (finiteConvexX_minus_line_at_p1 (P := P) (g := g)
        hE0 hE1 hE2 h01 h02 h12 hh h3 hu
        hE0mass hE1mass hE2mass hba haM hb hbu)
  exact le_antisymm hub hlb

theorem finiteRhoLine_finiteConvexY_eq_at_p1
    {g : Level → ℝ} {h r u M a b : ℝ} {E0 E1 E2 : Set Ω}
    (hE0 : MeasurableSet E0) (hE1 : MeasurableSet E1) (hE2 : MeasurableSet E2)
    (h01 : Disjoint E0 E1) (h02 : Disjoint E0 E2) (h12 : Disjoint E1 E2)
    (hh : 0 < h) (h3 : 3 * h < 1) (hr : 0 ≤ r) (hu : u = r * h)
    (hE0mass : P.real E0 = 1 - 3 * h) (hE1mass : P.real E1 = h) (hE2mass : P.real E2 = h)
    (hba : b < a) (haM : a < M) (hb : 0 < b) (habu : a + b = 15 * u / 2)
    (hbu : b = 3 * u / 2)
    (hMlarge :
      (-(1 - 3 * h) * M - h * (a + b)) - finiteSupportLine g h r hh h3 0 <
        -(3 * u / 4) - g (finiteLevel1 h hh h3)) :
    finiteRhoLine P g h r hh h3 (finiteConvexY P M a b E0 E1 E2 hE0 hE1 hE2) =
      -(3 * u / 4) - g (finiteLevel1 h hh h3) := by
  have hYeq := finiteConvexY_eq_finiteConvexX_swap
    (P := P) (M := M) (a := a) (b := b) hE0 hE1 hE2
  rw [hYeq]
  simpa using
    (finiteRhoLine_finiteConvexX_eq_at_p1 (P := P)
      (g := g) (h := h) (r := r) (u := u) (M := M) (a := a) (b := b)
      (E0 := E0) (E1 := E2) (E2 := E1)
      hE0 hE2 hE1 h02 h01 h12.symm hh h3 hr hu hE0mass hE2mass hE1mass
      hba haM hb habu hbu hMlarge)

end FiniteConvexRhoLineMaximizers

section Contradiction

variable {Ω : Type*} [MeasurableSpace Ω]
variable (P : Measure Ω)

/-- A strict lower/upper bound mismatch on a concrete pair witnesses failure of submodularity. -/
theorem not_submodular_of_bounds {ρ : RandomVariable P → ℝ} {X Y : RandomVariable P}
    {xUpper yUpper infLower supLower : ℝ}
    (hX : ρ X ≤ xUpper) (hY : ρ Y ≤ yUpper)
    (hInf : infLower ≤ ρ (X ⊓ Y)) (hSup : supLower ≤ ρ (X ⊔ Y))
    (hgap : xUpper + yUpper < infLower + supLower) :
    ¬ Submodular ρ := by
  intro hsub
  have hsubXY := hsub X Y
  linarith

variable [IsProbabilityMeasure P]

/-- Constructive finite convex witness theorem for `AES`.

This theorem is the first Lean-friendly milestone for the finite convex argument: once explicit
upper bounds for `X,Y` and lower bounds for `X ⊓ Y, X ⊔ Y` are established, submodularity fails.
The numerical comparison is written in the same `h,r,u` variables used in the manuscript. -/
theorem not_submodular_AES_of_finiteConvex_bounds
    {g : Level → ℝ} {h r u a b M : ℝ} {E0 E1 E2 : Set Ω}
    (hE0 : MeasurableSet E0) (hE1 : MeasurableSet E1) (hE2 : MeasurableSet E2)
    (hh : 0 < h) (h3 : 3 * h < 1) (hu : u = r * h)
    (hX :
      AES P g (finiteConvexX P M a b E0 E1 E2 hE0 hE1 hE2) ≤
        -(3 * u / 4) - g (finiteLevel1 h hh h3))
    (hY :
      AES P g (finiteConvexY P M a b E0 E1 E2 hE0 hE1 hE2) ≤
        -(3 * u / 4) - g (finiteLevel1 h hh h3))
    (hSup :
      -u - g (finiteLevel0 h hh h3) ≤
        AES P g
          (finiteConvexX P M a b E0 E1 E2 hE0 hE1 hE2 ⊔
            finiteConvexY P M a b E0 E1 E2 hE0 hE1 hE2))
    (hInf :
      -g (finiteLevel2 h hh h3) ≤
        AES P g
          (finiteConvexX P M a b E0 E1 E2 hE0 hE1 hE2 ⊓
            finiteConvexY P M a b E0 E1 E2 hE0 hE1 hE2))
    (hsmall :
      g (finiteLevel0 h hh h3) + g (finiteLevel2 h hh h3) -
        2 * g (finiteLevel1 h hh h3) < r * h / 2) :
    ¬ Submodular (AES P g) := by
  let p0 : Level := finiteLevel0 h hh h3
  let p1 : Level := finiteLevel1 h hh h3
  let p2 : Level := finiteLevel2 h hh h3
  let X : RandomVariable P := finiteConvexX P M a b E0 E1 E2 hE0 hE1 hE2
  let Y : RandomVariable P := finiteConvexY P M a b E0 E1 E2 hE0 hE1 hE2
  have hX' : AES P g X ≤ -(3 * u / 4) - g p1 := by
    simpa only [X, p1] using hX
  have hY' : AES P g Y ≤ -(3 * u / 4) - g p1 := by
    simpa only [Y, p1] using hY
  have hSup' : -u - g p0 ≤ AES P g (X ⊔ Y) := by
    simpa only [X, Y, p0] using hSup
  have hInf' : -g p2 ≤ AES P g (X ⊓ Y) := by
    simpa only [X, Y, p2] using hInf
  have hsmall' : g p0 + g p2 - 2 * g p1 < r * h / 2 := by
    simpa only [p0, p1, p2] using hsmall
  have hgap : (-(3 * u / 4) - g p1) + (-(3 * u / 4) - g p1) < (-g p2) + (-u - g p0) := by
    have hu' : u = r * h := hu
    linarith [hsmall']
  exact not_submodular_of_bounds (P := P)
    (ρ := AES P g)
    (X := X) (Y := Y) hX' hY' hInf' hSup' hgap

/-- A stronger finite-convex contradiction theorem: the lower bounds for `X ⊔ Y` and `X ⊓ Y`
are proved internally from the explicit `ES` formulas, so only the `X,Y` upper bounds remain as
external inputs. -/
theorem not_submodular_AES_of_finiteConvex_XYbounds
    {g : Level → ℝ} {h r u a b M : ℝ} {E0 E1 E2 : Set Ω}
    (hE0 : MeasurableSet E0) (hE1 : MeasurableSet E1) (hE2 : MeasurableSet E2)
    (h01 : Disjoint E0 E1) (h02 : Disjoint E0 E2) (h12 : Disjoint E1 E2)
    (hh : 0 < h) (h3 : 3 * h < 1) (hu : u = r * h) (hbu : b = 3 * u / 2)
    (hE0mass : P.real E0 = 1 - 3 * h) (hE1mass : P.real E1 = h) (hE2mass : P.real E2 = h)
    (haM : a < M) (hbM : b < M) (ha : 0 < a) (hb : 0 < b) (hba : b ≤ a)
    (hgnonneg : ∀ p : Level, 0 ≤ g p)
    (hX :
      AES P g (finiteConvexX P M a b E0 E1 E2 hE0 hE1 hE2) ≤
        -(3 * u / 4) - g (finiteLevel1 h hh h3))
    (hY :
      AES P g (finiteConvexY P M a b E0 E1 E2 hE0 hE1 hE2) ≤
        -(3 * u / 4) - g (finiteLevel1 h hh h3))
    (hsmall :
      g (finiteLevel0 h hh h3) + g (finiteLevel2 h hh h3) -
        2 * g (finiteLevel1 h hh h3) < r * h / 2) :
    ¬ Submodular (AES P g) := by
  have hSup :
      -u - g (finiteLevel0 h hh h3) ≤
        AES P g
          (finiteConvexX P M a b E0 E1 E2 hE0 hE1 hE2 ⊔
            finiteConvexY P M a b E0 E1 E2 hE0 hE1 hE2) := by
    rw [finiteConvexX_sup_finiteConvexY_eq_finiteConvexSup (P := P) hE0 hE1 hE2 h01 h02 h12 hba]
    exact AES_finiteConvexSup_ge_p0 (P := P) (g := g) hE0 hE1 hE2 h01 h02 h12 hh h3
      hE0mass hE1mass hE2mass hbM hb hbu hgnonneg
  have hInf :
      -g (finiteLevel2 h hh h3) ≤
        AES P g
          (finiteConvexX P M a b E0 E1 E2 hE0 hE1 hE2 ⊓
            finiteConvexY P M a b E0 E1 E2 hE0 hE1 hE2) := by
    rw [finiteConvexX_inf_finiteConvexY_eq_finiteConvexInf (P := P) hE0 hE1 hE2 h01 h02 h12 hba]
    exact AES_finiteConvexInf_ge_p2 (P := P) (g := g) hE0 hE1 hE2 h01 h02 h12 hh h3
      hE0mass hE1mass hE2mass haM ha hgnonneg
  exact not_submodular_AES_of_finiteConvex_bounds (P := P) hE0 hE1 hE2 hh h3 hu hX hY hSup hInf
    hsmall

/-- The finite-convex witness theorem matching the manuscript's back half:
from the explicit witness data `h,r,u,a,b,M,E0,E1,E2`, together with the support-line bound and
the smallness condition, one gets a direct contradiction to submodularity of `AES P g`. -/
theorem not_submodular_AES_of_finiteConvex_witness
    {g : Level → ℝ} {h r u a b M : ℝ} {E0 E1 E2 : Set Ω}
    (hE0 : MeasurableSet E0) (hE1 : MeasurableSet E1) (hE2 : MeasurableSet E2)
    (h01 : Disjoint E0 E1) (h02 : Disjoint E0 E2) (h12 : Disjoint E1 E2)
    (hh : 0 < h) (h3 : 3 * h < 1) (hr : 0 ≤ r) (hu : u = r * h)
    (hE0mass : P.real E0 = 1 - 3 * h) (hE1mass : P.real E1 = h) (hE2mass : P.real E2 = h)
    (hba : b < a) (haM : a < M) (ha : 0 < a) (hb : 0 < b)
    (habu : a + b = 15 * u / 2) (hbu : b = 3 * u / 2)
    (hline : ∀ p : Level, finiteSupportLine g h r hh h3 p ≤ g p)
    (hgnonneg : ∀ p : Level, 0 ≤ g p)
    (hMlarge :
      (-(1 - 3 * h) * M - h * (a + b)) - finiteSupportLine g h r hh h3 0 <
        -(3 * u / 4) - g (finiteLevel1 h hh h3))
    (hsmall :
      g (finiteLevel0 h hh h3) + g (finiteLevel2 h hh h3) -
        2 * g (finiteLevel1 h hh h3) < r * h / 2) :
    ¬ Submodular (AES P g) := by
  have hbM : b < M := by
    linarith
  have hXline :
      AES P g (finiteConvexX P M a b E0 E1 E2 hE0 hE1 hE2) ≤
        finiteRhoLine P g h r hh h3 (finiteConvexX P M a b E0 E1 E2 hE0 hE1 hE2) :=
    AES_finiteConvexX_le_finiteRhoLine (P := P) hE0 hE1 hE2 h01 h02 h12 hh h3 hr
      haM ha hb hba.le hline
  have hXrho :
      finiteRhoLine P g h r hh h3 (finiteConvexX P M a b E0 E1 E2 hE0 hE1 hE2) =
        -(3 * u / 4) - g (finiteLevel1 h hh h3) :=
    finiteRhoLine_finiteConvexX_eq_at_p1 (P := P) (g := g)
      hE0 hE1 hE2 h01 h02 h12 hh h3 hr hu
      hE0mass hE1mass hE2mass hba haM hb habu hbu hMlarge
  have hX :
      AES P g (finiteConvexX P M a b E0 E1 E2 hE0 hE1 hE2) ≤
        -(3 * u / 4) - g (finiteLevel1 h hh h3) := by
    calc
      AES P g (finiteConvexX P M a b E0 E1 E2 hE0 hE1 hE2) ≤
          finiteRhoLine P g h r hh h3 (finiteConvexX P M a b E0 E1 E2 hE0 hE1 hE2) := hXline
      _ = -(3 * u / 4) - g (finiteLevel1 h hh h3) := hXrho
  have hYline :
      AES P g (finiteConvexY P M a b E0 E1 E2 hE0 hE1 hE2) ≤
        finiteRhoLine P g h r hh h3 (finiteConvexY P M a b E0 E1 E2 hE0 hE1 hE2) :=
    AES_finiteConvexY_le_finiteRhoLine (P := P) hE0 hE1 hE2 h01 h02 h12 hh h3 hr
      haM ha hb hba.le hline
  have hYrho :
      finiteRhoLine P g h r hh h3 (finiteConvexY P M a b E0 E1 E2 hE0 hE1 hE2) =
        -(3 * u / 4) - g (finiteLevel1 h hh h3) :=
    finiteRhoLine_finiteConvexY_eq_at_p1 (P := P) (g := g)
      hE0 hE1 hE2 h01 h02 h12 hh h3 hr hu
      hE0mass hE1mass hE2mass hba haM hb habu hbu hMlarge
  have hY :
      AES P g (finiteConvexY P M a b E0 E1 E2 hE0 hE1 hE2) ≤
        -(3 * u / 4) - g (finiteLevel1 h hh h3) := by
    calc
      AES P g (finiteConvexY P M a b E0 E1 E2 hE0 hE1 hE2) ≤
          finiteRhoLine P g h r hh h3 (finiteConvexY P M a b E0 E1 E2 hE0 hE1 hE2) := hYline
      _ = -(3 * u / 4) - g (finiteLevel1 h hh h3) := hYrho
  exact not_submodular_AES_of_finiteConvex_XYbounds (P := P)
    hE0 hE1 hE2 h01 h02 h12 hh h3 hu hbu
    hE0mass hE1mass hE2mass haM hbM ha hb hba.le hgnonneg hX hY hsmall

/-- A witness theorem with the affine support line and the large-`M` choice produced internally
from a convex real-valued penalty function. This isolates two Lean-friendly parts of the front
half of the manuscript proof: tangent-line support and the archimedean choice of `M`. -/
theorem not_submodular_AES_of_finiteConvex_real_witness
    {f : ℝ → ℝ} {h r u a b : ℝ} {E0 E1 E2 : Set Ω}
    (hE0 : MeasurableSet E0) (hE1 : MeasurableSet E1) (hE2 : MeasurableSet E2)
    (h01 : Disjoint E0 E1) (h02 : Disjoint E0 E2) (h12 : Disjoint E1 E2)
    (hh : 0 < h) (h3 : 3 * h < 1) (hr : 0 ≤ r) (hu : u = r * h)
    (hE0mass : P.real E0 = 1 - 3 * h) (hE1mass : P.real E1 = h) (hE2mass : P.real E2 = h)
    (hba : b < a) (ha : 0 < a) (hb : 0 < b)
    (habu : a + b = 15 * u / 2) (hbu : b = 3 * u / 2)
    (hconv : ConvexOn ℝ (Set.Icc (0 : ℝ) 1) f)
    (hderiv : HasDerivAt f r (1 - 2 * h))
    (hnonneg : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 ≤ f x)
    (hsmall :
      f (finiteLevel0 h hh h3) + f (finiteLevel2 h hh h3) -
        2 * f (finiteLevel1 h hh h3) < r * h / 2) :
    ¬ Submodular (AES P (fun p : Level => f p)) := by
  obtain ⟨M, haM, hMlarge⟩ := exists_M_for_finiteConvex
    (g := fun p : Level => f p) (h := h) (r := r) (u := u) (a := a) (b := b) hh h3
  have hline : ∀ p : Level, finiteSupportLine (fun q : Level => f q) h r hh h3 p ≤ f p :=
    finiteSupportLine_le_of_convexOn_hasDerivAt (hh := hh) (h3 := h3) hconv hderiv
  have hgnonneg : ∀ p : Level, 0 ≤ f p := by
    intro p
    exact hnonneg p p.2
  exact not_submodular_AES_of_finiteConvex_witness (P := P)
    (g := fun p : Level => f p)
    hE0 hE1 hE2 h01 h02 h12 hh h3 hr hu
    hE0mass hE1mass hE2mass hba haM ha hb habu hbu hline hgnonneg hMlarge hsmall

end Contradiction

end AesSubmodularity
