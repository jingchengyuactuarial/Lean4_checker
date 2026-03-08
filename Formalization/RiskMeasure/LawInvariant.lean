import Mathlib.Probability.IdentDistrib
import Formalization.RiskMeasure.RandomVariable

/-!
# Law Invariance

Law invariance is a central hypothesis in the AES proof: it is what turns
event-based constructions into one-dimensional profiles indexed by probability.
-/

noncomputable section

open MeasureTheory
open ProbabilityTheory

namespace RiskMeasure

section

variable {Ω : Type*} [MeasurableSpace Ω]
variable (P : Measure Ω) [IsProbabilityMeasure P]
variable {C : Type*}

/-- Real probability laws as a subtype of real measures. -/
abbrev ProbabilityLaw := {μ : Measure ℝ // IsProbabilityMeasure μ}

/-- A risk functional is law-invariant if equal laws imply equal evaluations. -/
def LawInvariant (ρ : RandomVariable P → C) : Prop :=
  ∀ ⦃X Y : RandomVariable P⦄, law P X = law P Y → ρ X = ρ Y

/-- A risk functional factors through law if it is induced by a map on real probability laws. -/
def FactorsThroughLaw (ρ : RandomVariable P → C) : Prop :=
  ∃ f : ProbabilityLaw → C, ∀ X : RandomVariable P, ρ X = f ⟨law P X, inferInstance⟩

/-- A law-induced functional is automatically law-invariant. -/
theorem FactorsThroughLaw.lawInvariant {ρ : RandomVariable P → C}
    (hρ : FactorsThroughLaw P ρ) : LawInvariant P ρ := by
  rcases hρ with ⟨f, hf⟩
  intro X Y hXY
  rw [hf X, hf Y]
  apply congrArg f
  apply Subtype.ext
  exact hXY

/-- The canonical way to build a law-invariant functional from a map on laws. -/
def ofLaw (f : ProbabilityLaw → C) : RandomVariable P → C :=
  fun X => f ⟨law P X, inferInstance⟩

/-- Any functional defined by evaluating a map on the law factors through law by construction. -/
theorem ofLaw_factorsThroughLaw (f : ProbabilityLaw → C) :
    FactorsThroughLaw P (ofLaw P f) := by
  refine ⟨f, ?_⟩
  intro X
  rfl

/-- Any functional defined directly from the law is law-invariant. -/
theorem ofLaw_lawInvariant (f : ProbabilityLaw → C) :
    LawInvariant P (ofLaw P f) :=
  (ofLaw_factorsThroughLaw (P := P) f).lawInvariant (P := P)

/-- A law-invariant functional takes the same value on identically distributed random variables. -/
theorem LawInvariant.of_identDistrib {ρ : RandomVariable P → C} (hρ : LawInvariant P ρ)
    {X Y : RandomVariable P} (hXY : IdentDistrib (X : Ω → ℝ) (Y : Ω → ℝ) P P) : ρ X = ρ Y :=
  hρ hXY.map_eq

/-- Any law-induced functional takes the same value on identically distributed random variables. -/
theorem FactorsThroughLaw.of_identDistrib {ρ : RandomVariable P → C}
    (hρ : FactorsThroughLaw P ρ) {X Y : RandomVariable P}
    (hXY : IdentDistrib (X : Ω → ℝ) (Y : Ω → ℝ) P P) : ρ X = ρ Y :=
  hρ.lawInvariant (P := P) |>.of_identDistrib (P := P) hXY

end

end RiskMeasure
