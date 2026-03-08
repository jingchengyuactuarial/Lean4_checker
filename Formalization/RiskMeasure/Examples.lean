import Formalization.RiskMeasure.Basic

/-!
# Small Working Examples

These examples are intentionally simple. Their job is to keep the initial standalone
repository executable while we grow a richer API for `VaR`, `ES`, and law invariance.
-/

namespace RiskMeasure

section RealExamples

/-- The identity map on `ℝ`, viewed as a toy risk measure in the loss convention. -/
def idReal : ℝ → ℝ := fun x => x

example : Monotone idReal := by
  intro x y h
  exact h

example : Normalized idReal := rfl

example : CashAdditive (selfCash ℝ) idReal := by
  intro x m
  simp [idReal, selfCash]

example : Subadditive idReal := by
  intro x y
  exact le_rfl

example : PosHomogeneous idReal := by
  intro a x
  change ((a : ℝ) * x) = (a : ℝ) * x
  rfl

example : Coherent (selfCash ℝ) idReal := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x y h
    exact h
  · intro x m
    simp [idReal, selfCash]
  · intro x y
    exact le_rfl
  · intro a x
    change ((a : ℝ) * x) = (a : ℝ) * x
    rfl

end RealExamples

section FunctionExamples

variable (Ω : Type*)

/-- Deterministic cash as a constant real-valued position. -/
def cashFunction : ℝ →+ Ω → ℝ where
  toFun m := fun _ => m
  map_zero' := by
    funext ω
    rfl
  map_add' m n := by
    funext ω
    rfl

example (m : ℝ) : cashFunction Ω m = Function.const Ω m := rfl

end FunctionExamples

end RiskMeasure
