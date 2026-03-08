import Mathlib

/-!
# Basic Axioms for Risk Measures

This file introduces a small, reusable API for abstract risk measures.

The conventions here are deliberately lightweight:
- positions live in a type `X`;
- capital requirements live in a type `C`;
- deterministic cash is injected into positions by an additive map `cash : C →+ X`.

The monotonicity convention is the "loss convention":
if `x ≤ y`, then `ρ x ≤ ρ y`.
-/

namespace RiskMeasure

section OrderAxioms

variable {X C : Type*}

/-- Monotonicity in the loss convention. -/
def Monotone [Preorder X] [Preorder C] (ρ : X → C) : Prop :=
  ∀ ⦃x y : X⦄, x ≤ y → ρ x ≤ ρ y

/-- Antitonicity, useful for payoff-convention formulations. -/
def Antitone [Preorder X] [Preorder C] (ρ : X → C) : Prop :=
  ∀ ⦃x y : X⦄, x ≤ y → ρ y ≤ ρ x

end OrderAxioms

section AlgebraicAxioms

variable {X C : Type*}

/-- A normalized risk measure vanishes at zero. -/
def Normalized [Zero X] [Zero C] (ρ : X → C) : Prop :=
  ρ 0 = 0

/-- Cash additivity with respect to a chosen cash embedding `cash : C →+ X`. -/
def CashAdditive [AddMonoid X] [AddMonoid C] (cash : C →+ X) (ρ : X → C) : Prop :=
  ∀ x m, ρ (x + cash m) = ρ x + m

/-- Subadditivity. -/
def Subadditive [Add X] [Preorder C] [Add C] (ρ : X → C) : Prop :=
  ∀ (x y : X), ρ (x + y) ≤ ρ x + ρ y

/-- Positive homogeneity for nonnegative scalars. -/
def PosHomogeneous [SMul NNReal X] [SMul NNReal C] (ρ : X → C) : Prop :=
  ∀ (a : NNReal) (x : X), ρ (a • x) = a • ρ x

/-- Convexity in the usual two-point form. -/
def Convex [Add X] [SMul ℝ X] [Preorder C] [Add C] [SMul ℝ C] (ρ : X → C) : Prop :=
  ∀ (x y : X) (a b : ℝ), 0 ≤ a → 0 ≤ b → a + b = 1 →
    ρ (a • x + b • y) ≤ a • ρ x + b • ρ y

/-- A coherent risk measure in the loss convention. -/
def Coherent [Preorder X] [Preorder C] [AddMonoid X] [AddMonoid C]
    [SMul NNReal X] [SMul NNReal C] (cash : C →+ X) (ρ : X → C) : Prop :=
  Monotone ρ ∧ CashAdditive cash ρ ∧ Subadditive ρ ∧ PosHomogeneous ρ

end AlgebraicAxioms

section CashEmbeddings

variable (C : Type*) [AddMonoid C]

/-- The default cash embedding when positions and capital requirements live in the same type. -/
def selfCash : C →+ C := AddMonoidHom.id C

end CashEmbeddings

end RiskMeasure
