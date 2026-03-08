import Mathlib.Analysis.Convex.Integral
import Mathlib.Order.Hom.Set
import Formalization.RiskMeasure.RandomVariable
import Formalization.RiskMeasure.LawInvariant

/-!
# Certainty Equivalents

This file isolates generalized inverses and certainty equivalents of the form
`ℓ⁻¹ (E[ℓ(X)])`. This is a natural next target after the AES infrastructure,
since it uses law invariance and bounded random variables but avoids the
quantile/shortfall profile layer.
-/

noncomputable section

open MeasureTheory

namespace RiskMeasure

/-- Generalized inverse of a real function, in the lower-inverse convention. -/
def generalizedInverse (ℓ : ℝ → ℝ) (y : ℝ) : ℝ :=
  sInf {x : ℝ | y ≤ ℓ x}

section GeneralizedInverse

variable {ℓ : ℝ → ℝ}

/-- A lower generalized inverse recovers the original point on the image of a strictly increasing
function. -/
@[simp] theorem generalizedInverse_apply (hmono : StrictMono ℓ) (x : ℝ) :
    generalizedInverse ℓ (ℓ x) = x := by
  have hset : {z : ℝ | ℓ x ≤ ℓ z} = Set.Ici x := by
    ext z
    simp [hmono.le_iff_le]
  simp [generalizedInverse, hset]

/-- For a strictly increasing bijection, the lower generalized inverse agrees with the order
isomorphism inverse from `mathlib`. -/
theorem generalizedInverse_eq_orderIso_symm (hmono : StrictMono ℓ)
    (hsurj : Function.Surjective ℓ) :
    generalizedInverse ℓ = (hmono.orderIsoOfSurjective ℓ hsurj).symm := by
  funext y
  let e : ℝ ≃o ℝ := hmono.orderIsoOfSurjective ℓ hsurj
  have hset : {x : ℝ | y ≤ ℓ x} = Set.Ici (e.symm y) := by
    ext x
    constructor
    · intro hx
      have hxy : e (e.symm y) ≤ e x := by
        simpa [e] using hx
      exact (e.le_iff_le.mp hxy)
    · intro hx
      have hxy : e (e.symm y) ≤ e x := e.le_iff_le.mpr hx
      simpa [e] using hxy
  rw [generalizedInverse, hset, csInf_Ici]

/-- The lower generalized inverse of a strictly increasing bijection is monotone. -/
theorem monotone_generalizedInverse (hmono : StrictMono ℓ) (hsurj : Function.Surjective ℓ) :
    Monotone (generalizedInverse ℓ) := by
  simpa [generalizedInverse_eq_orderIso_symm (ℓ := ℓ) hmono hsurj] using
    (hmono.orderIsoOfSurjective ℓ hsurj).symm.monotone

/-- Convexity transfers to concavity of the generalized inverse once the underlying loss function is
packaged as an order isomorphism. -/
theorem concaveOn_generalizedInverse_univ_of_convexOn (hconv : ConvexOn ℝ Set.univ ℓ)
    (hmono : StrictMono ℓ) (hsurj : Function.Surjective ℓ) :
    ConcaveOn ℝ Set.univ (generalizedInverse ℓ) := by
  let e : ℝ ≃o ℝ := hmono.orderIsoOfSurjective ℓ hsurj
  have heconv : ConvexOn ℝ Set.univ e := by
    simpa [e] using hconv
  simpa [generalizedInverse_eq_orderIso_symm (ℓ := ℓ) hmono hsurj, e] using
    (OrderIso.concaveOn_symm e heconv)

end GeneralizedInverse

/-- Distribution-level certainty equivalent induced by a loss function `ℓ`. -/
def distCE (μ : Measure ℝ) [IsProbabilityMeasure μ] (ℓ : ℝ → ℝ) : ℝ :=
  generalizedInverse ℓ (∫ x, ℓ x ∂μ)

section GeneralizedInverse

variable {ℓ : ℝ → ℝ}

/-- Distribution-level certainty equivalents can be rewritten using the `mathlib` order isomorphism
inverse once the loss function is strictly increasing and surjective. -/
theorem distCE_eq_orderIso_symm (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hmono : StrictMono ℓ) (hsurj : Function.Surjective ℓ) :
    distCE μ ℓ = (hmono.orderIsoOfSurjective ℓ hsurj).symm (∫ x, ℓ x ∂μ) := by
  rw [distCE, generalizedInverse_eq_orderIso_symm (ℓ := ℓ) hmono hsurj]

end GeneralizedInverse

section

variable {Ω : Type*} [MeasurableSpace Ω]
variable (P : Measure Ω) [IsProbabilityMeasure P]

/-- Certainty equivalent for random variables under the reference probability measure `P`. -/
def CE (ℓ : ℝ → ℝ) (X : RandomVariable P) : ℝ :=
  distCE (law P X) ℓ

/-- Long-form alias for `CE`. -/
abbrev CertaintyEquivalent := CE P

/-- `CE` factors through the law of the underlying random variable. -/
theorem CE_factorsThroughLaw (ℓ : ℝ → ℝ) : FactorsThroughLaw P (CE P ℓ) := by
  refine ⟨fun μ => by
    let _ : IsProbabilityMeasure μ.1 := μ.2
    exact distCE μ.1 ℓ, ?_⟩
  intro X
  rfl

/-- `CE` is law-invariant. -/
theorem CE_lawInvariant (ℓ : ℝ → ℝ) : LawInvariant P (CE P ℓ) :=
  (CE_factorsThroughLaw (P := P) ℓ).lawInvariant (P := P)

end

end RiskMeasure
