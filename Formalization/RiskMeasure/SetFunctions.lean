import Formalization.RiskMeasure.Axioms

/-!
# Set Functions and Probability Profiles

The AES proof passes from submodular risk measures on random variables to
submodular set functions on events, and then to one-dimensional profiles.
-/

open MeasureTheory

namespace RiskMeasure

section

variable {Ω C : Type*} [MeasurableSpace Ω]

/-- A set functional depends only on event probability. -/
def DependsOnlyOnProbability (P : Measure Ω) (μ : Set Ω → C) : Prop :=
  ∀ ⦃A B : Set Ω⦄, MeasurableSet A → MeasurableSet B → P A = P B → μ A = μ B

/-- A one-dimensional profile representing a set functional through event probabilities. -/
def EventProfile (P : Measure Ω) (μ : Set Ω → C) (φ : ℝ → C) : Prop :=
  ∀ ⦃A : Set Ω⦄, MeasurableSet A → μ A = φ (P A).toReal

/-- Set-function submodularity, exposed under a dedicated name for event-based arguments. -/
abbrev SetSubmodular [Preorder C] [Add C] (μ : Set Ω → C) : Prop :=
  Submodular μ

/-- Decreasing increments on `[0,1]`, the profile property used in the AES proof. -/
def DecreasingIncrements (φ : ℝ → ℝ) : Prop :=
  ∀ ⦃s t h : ℝ⦄, 0 ≤ s → s ≤ t → 0 ≤ h → t + h ≤ 1 →
    φ (s + h) + φ t ≥ φ s + φ (t + h)

end

end RiskMeasure
