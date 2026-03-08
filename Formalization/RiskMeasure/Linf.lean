import Formalization.RiskMeasure.Atomless
import Formalization.RiskMeasure.RandomVariable
import Mathlib.MeasureTheory.Function.LpSpace.Indicator

/-!
# `L∞` Bridge Layer

This file provides a thin project-level bridge to `mathlib`'s `MeasureTheory.Lp ℝ ∞ μ`.
It is intentionally lightweight:

- `Linf μ` is just an abbreviation for `Lp ℝ ∞ μ`;
- `NoAtomsProbabilitySpace μ` packages the reusable assumptions
  `[IsProbabilityMeasure μ] [NoAtoms μ]`;
- constant positions, indicator positions, and bounded random variables can be moved into `L∞`.

The stronger event-splitting hypothesis needed by the AES proof still lives in
`RiskMeasure.Atomless`.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace RiskMeasure

section

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Project-level alias for the ambient `L^\infty` space under `μ`. -/
abbrev Linf (μ : Measure Ω) := MeasureTheory.Lp ℝ ∞ μ

/-- A probability space with `mathlib`'s reusable `NoAtoms` assumption. This is weaker than the
project-level `StronglyAtomless`, which additionally demands exact event splitting. -/
class NoAtomsProbabilitySpace (μ : Measure Ω) : Prop where
  isProbabilityMeasure : IsProbabilityMeasure μ
  noAtoms : MeasureTheory.NoAtoms μ

attribute [instance] NoAtomsProbabilitySpace.isProbabilityMeasure
attribute [instance] NoAtomsProbabilitySpace.noAtoms

/-- An `L^\infty` space on a no-atom probability space. -/
abbrev AtomlessLinf (μ : Measure Ω) [NoAtomsProbabilitySpace μ] := Linf μ

variable (μ : Measure Ω)

/-- Deterministic cash as an element of `L^\infty`. -/
def linfConst [IsFiniteMeasure μ] (c : ℝ) : Linf μ :=
  MeasureTheory.Lp.const ∞ μ c

@[simp] theorem coeFn_linfConst [IsFiniteMeasure μ] (c : ℝ) :
    linfConst μ c =ᵐ[μ] fun _ : Ω => c := by
  simpa [linfConst] using (MeasureTheory.Lp.coeFn_const (p := ∞) (μ := μ) c)

/-- Event indicator positions `c 1_A` as elements of `L^\infty`. -/
def linfIndicator [IsFiniteMeasure μ] (A : Set Ω) (hA : MeasurableSet A) (c : ℝ) : Linf μ :=
  MeasureTheory.indicatorConstLp ∞ hA (measure_ne_top μ A) c

theorem coeFn_linfIndicator [IsFiniteMeasure μ] (A : Set Ω) (hA : MeasurableSet A) (c : ℝ) :
    linfIndicator μ A hA c =ᵐ[μ] A.indicator (fun _ => c) := by
  simpa [linfIndicator] using
    (MeasureTheory.indicatorConstLp_coeFn (p := ∞) (s := A) (hs := hA)
      (hμs := measure_ne_top μ A) (c := c))

theorem norm_linfIndicator_eq [IsFiniteMeasure μ] (A : Set Ω) (hA : MeasurableSet A)
    (hA_pos : μ A ≠ 0) (c : ℝ) :
    ‖linfIndicator μ A hA c‖ = ‖c‖ := by
  simpa [linfIndicator] using
    (MeasureTheory.norm_indicatorConstLp_top (s := A) (hs := hA)
      (hμs := measure_ne_top μ A) (c := c) hA_pos)

namespace RandomVariable

/-- An `L^\infty` position can always be viewed as an almost-everywhere measurable random
variable. -/
def ofLinf (X : Linf μ) : RandomVariable μ :=
  ⟨X, (MeasureTheory.Lp.aestronglyMeasurable X).aemeasurable⟩

@[simp] theorem coeFn_ofLinf (X : Linf μ) : ((ofLinf (μ := μ) X : RandomVariable μ) : Ω → ℝ) = X :=
  rfl

/-- An essentially bounded random variable gives an `L^\infty` element. -/
def toLinf [IsFiniteMeasure μ] (X : RandomVariable μ) (hX : EssentiallyBounded μ X) : Linf μ := by
  let a := essLowerBound μ X
  let b := essUpperBound μ X
  have h_mem : ∀ᵐ ω ∂μ, (X : Ω → ℝ) ω ∈ Set.Icc a b := by
    filter_upwards [ae_essLowerBound_le (P := μ) X hX, ae_le_essUpperBound (P := μ) X hX]
      with ω h_lower h_upper
    exact ⟨h_lower, h_upper⟩
  exact (MeasureTheory.memLp_of_bounded h_mem X.2.aestronglyMeasurable ∞).toLp X

theorem coeFn_toLinf [IsFiniteMeasure μ] (X : RandomVariable μ) (hX : EssentiallyBounded μ X) :
    RandomVariable.toLinf (μ := μ) X hX =ᵐ[μ] X := by
  dsimp [RandomVariable.toLinf]
  exact MeasureTheory.MemLp.coeFn_toLp _

end RandomVariable

end

end RiskMeasure
