import Formalization.AesSubmodularity.Bridge

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

@[simp] theorem finiteSupportLine_apply_one (g : Level → ℝ) (h r : ℝ) (hh : 0 < h)
    (h3 : 3 * h < 1) :
    finiteSupportLine g h r hh h3 1 =
      g (finiteLevel1 h hh h3) + 2 * r * h := by
  simp [finiteSupportLine]
  ring_nf

end SupportLine

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

section RhoLine

variable {Ω : Type*} [MeasurableSpace Ω]
variable (P : Measure Ω) [IsProbabilityMeasure P]

/-- The affine-line envelope `ρ_ℓ` from the finite convex manuscript proof. -/
def finiteRhoLine (g : Level → ℝ) (h r : ℝ) (hh : 0 < h) (h3 : 3 * h < 1)
    (Z : RandomVariable P) : ℝ :=
  sSup (Set.range fun p : Level => ES P p Z - finiteSupportLine g h r hh h3 p)

end RhoLine

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

end Contradiction

end AesSubmodularity
