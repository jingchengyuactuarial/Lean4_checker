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

end Positions

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
  have hgap :
      (-(3 * u / 4) - g p1) + (-(3 * u / 4) - g p1) <
        (-g p2) + (-u - g p0) := by
    have hu' : u = r * h := hu
    linarith [hsmall']
  exact not_submodular_of_bounds (P := P)
    (ρ := AES P g)
    (X := X) (Y := Y) hX' hY' hInf' hSup' hgap

end Contradiction

end AesSubmodularity
