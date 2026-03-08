import Mathlib.MeasureTheory.Function.EssSup
import Mathlib.Probability.HasLaw
import Mathlib.Topology.UnitInterval

/-!
# Random Variables and Laws

This file isolates the basic objects used by the AES proof:

- confidence levels in `[0,1]`;
- almost-everywhere measurable real-valued random variables under a fixed measure;
- pushforward laws of such random variables.
-/

noncomputable section

open MeasureTheory
open Filter

namespace RiskMeasure

/-- Confidence levels live in the unit interval `[0,1]`. -/
abbrev Level := unitInterval

section

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Real-valued random variables represented by almost-everywhere measurable functions. -/
abbrev RandomVariable (P : Measure Ω) := {X : Ω → ℝ // AEMeasurable X P}

variable (P : Measure Ω)

/-- The law of an almost-everywhere measurable real-valued random variable. -/
def law (X : RandomVariable P) : Measure ℝ :=
  P.map X

section

variable [IsProbabilityMeasure P]

instance instIsProbabilityMeasureLaw (X : RandomVariable P) :
    IsProbabilityMeasure (law P X) :=
  Measure.isProbabilityMeasure_map X.2

end

/-- Constant random variable under the reference measure `P`. -/
def const (c : ℝ) : RandomVariable P :=
  ⟨fun _ => c, by fun_prop⟩

instance : Zero (RandomVariable P) := ⟨const P 0⟩

instance : Add (RandomVariable P) where
  add X Y := ⟨X.1 + Y.1, X.2.add Y.2⟩

instance : SMul ℕ (RandomVariable P) where
  smul n X := ⟨n • X.1, by
    simpa [nsmul_eq_mul, smul_eq_mul] using X.2.const_mul (n : ℝ)⟩

@[simp] theorem coe_zero : ((0 : RandomVariable P) : Ω → ℝ) = 0 := by
  funext ω
  change (const P 0 : Ω → ℝ) ω = 0
  rfl

@[simp] theorem coe_add (X Y : RandomVariable P) : ((X + Y : RandomVariable P) : Ω → ℝ) = X + Y :=
  rfl

@[simp] theorem coe_nsmul (n : ℕ) (X : RandomVariable P) :
    ((n • X : RandomVariable P) : Ω → ℝ) = n • (X : Ω → ℝ) :=
  rfl

instance : AddCommMonoid (RandomVariable P) :=
  Function.Injective.addCommMonoid (fun X : RandomVariable P => (X : Ω → ℝ))
    Subtype.coe_injective (coe_zero (P := P)) (coe_add (P := P))
      (fun X n => coe_nsmul (P := P) n X)

instance : SMul NNReal (RandomVariable P) where
  smul a X := ⟨a • X.1, by
    simpa [smul_eq_mul] using X.2.const_mul (a : ℝ)⟩

instance : SMul ℝ (RandomVariable P) where
  smul a X := ⟨a • X.1, by
    simpa [smul_eq_mul] using X.2.const_mul a⟩

/-- Deterministic cash embedded as constant random variables. -/
def cashEmbedding : ℝ →+ RandomVariable P where
  toFun := const P
  map_zero' := by
    ext ω
    simp [const]
  map_add' x y := by
    ext ω
    simp [const]

/-- Two positions are comonotone if they never move in opposite directions across states. -/
def ComonotoneFun {Ω' : Type*} (X Y : Ω' → ℝ) : Prop :=
  ∀ ω₁ ω₂, 0 ≤ (X ω₁ - X ω₂) * (Y ω₁ - Y ω₂)

/-- Comonotonicity for packaged random variables. -/
def Comonotone (X Y : RandomVariable P) : Prop :=
  ComonotoneFun X.1 Y.1

/-- Essential upper bound of a random variable. -/
def essUpperBound (X : RandomVariable P) : ℝ :=
  essSup X P

/-- Essential lower bound of a random variable. -/
def essLowerBound (X : RandomVariable P) : ℝ :=
  essInf X P

/-- A random variable is essentially bounded if it is almost surely bounded above and below. -/
def EssentiallyBounded (X : RandomVariable P) : Prop :=
  Filter.IsBoundedUnder (· ≤ ·) (ae P) X.1 ∧ Filter.IsBoundedUnder (· ≥ ·) (ae P) X.1

/-- An essentially bounded random variable is almost surely bounded above by its essential upper
bound. -/
theorem ae_le_essUpperBound (X : RandomVariable P) (hX : EssentiallyBounded P X) :
    ∀ᵐ ω ∂P, X.1 ω ≤ essUpperBound P X := by
  simpa [essUpperBound] using (ae_le_essSup (μ := P) (f := X.1) (hf := hX.1))

/-- An essentially bounded random variable is almost surely bounded below by its essential lower
bound. -/
theorem ae_essLowerBound_le (X : RandomVariable P) (hX : EssentiallyBounded P X) :
    ∀ᵐ ω ∂P, essLowerBound P X ≤ X.1 ω := by
  simpa [essLowerBound] using (ae_essInf_le (μ := P) (f := X.1) (hf := hX.2))

end

end RiskMeasure
