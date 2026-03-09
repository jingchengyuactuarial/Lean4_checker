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

end FiniteConvexXES


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
