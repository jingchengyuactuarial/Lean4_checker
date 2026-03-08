import Formalization.RiskMeasure.Axioms
import Formalization.RiskMeasure.Quantile
import Formalization.RiskMeasure.LawInvariant

/-!
# Distortion and Spectral Risk Measures

This file organizes the distortion/Choquet layer around two complementary
representations:

- the primitive spectral form `∫ VaR_p dν`, which is easiest to use in Lean;
- a bundled `DistortionFunction`, carrying both a normalized monotone map on
  levels and the level-measure used by its spectral representation.
-/

noncomputable section

open MeasureTheory

namespace RiskMeasure

/-- A distortion function is monotone and normalized at the endpoints of `[0,1]`. -/
def IsDistortionFunction (g : Level → Level) : Prop :=
  Monotone g ∧ g 0 = 0 ∧ g 1 = 1

/-- Bundled distortion functions together with the spectral measure used for
their quantile representation. -/
structure DistortionFunction where
  toFun : Level → Level
  monotone' : Monotone toFun
  map_zero' : toFun 0 = 0
  map_one' : toFun 1 = 1
  spectralMeasure : Measure Level
  isProbability_spectralMeasure : IsProbabilityMeasure spectralMeasure

instance : CoeFun DistortionFunction (fun _ => Level → Level) := ⟨DistortionFunction.toFun⟩

attribute [instance] DistortionFunction.isProbability_spectralMeasure

/-- The unbundled axioms associated with a bundled distortion function. -/
theorem DistortionFunction.isDistortionFunction (g : DistortionFunction) :
    IsDistortionFunction g := by
  exact ⟨g.monotone', g.map_zero', g.map_one'⟩

/-- Distribution-level spectral risk given by a probability measure on confidence levels. -/
def distSpectralRisk (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (ν : Measure Level) [IsProbabilityMeasure ν] : ℝ :=
  ∫ p, distVaR μ p ∂ν

/-- Distribution-level Choquet risk associated with a bundled distortion function. -/
def distChoquetRisk (μ : Measure ℝ) [IsProbabilityMeasure μ] (g : DistortionFunction) : ℝ :=
  distSpectralRisk μ g.spectralMeasure

/-- Distribution-level distortion risk. -/
abbrev distDistortionRisk (μ : Measure ℝ) [IsProbabilityMeasure μ] (g : DistortionFunction) : ℝ :=
  distChoquetRisk μ g

/-- Choquet and distortion risk are the same functional in the current API. -/
theorem distChoquetRisk_eq_distDistortionRisk (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (g : DistortionFunction) :
    distChoquetRisk μ g = distDistortionRisk μ g := rfl

section

variable {Ω : Type*} [MeasurableSpace Ω]
variable (P : Measure Ω) [IsProbabilityMeasure P]

/-- Spectral risk for random variables under the reference probability measure `P`. -/
def SpectralRisk (ν : Measure Level) [IsProbabilityMeasure ν] (X : RandomVariable P) : ℝ :=
  distSpectralRisk (law P X) ν

/-- Choquet risk for random variables under the reference probability measure `P`. -/
def ChoquetRisk (g : DistortionFunction) (X : RandomVariable P) : ℝ :=
  distChoquetRisk (law P X) g

/-- Distortion risk for random variables under the reference probability measure `P`. -/
abbrev DistortionRisk (g : DistortionFunction) (X : RandomVariable P) : ℝ :=
  ChoquetRisk P g X

/-- `SpectralRisk` factors through the law of the underlying random variable. -/
theorem SpectralRisk_factorsThroughLaw (ν : Measure Level) [IsProbabilityMeasure ν] :
    FactorsThroughLaw P (SpectralRisk P ν) := by
  refine ⟨fun μ => by
    let _ : IsProbabilityMeasure μ.1 := μ.2
    exact distSpectralRisk μ.1 ν, ?_⟩
  intro X
  rfl

/-- `SpectralRisk` is law-invariant. -/
theorem SpectralRisk_lawInvariant (ν : Measure Level) [IsProbabilityMeasure ν] :
    LawInvariant P (SpectralRisk P ν) :=
  (SpectralRisk_factorsThroughLaw (P := P) ν).lawInvariant (P := P)

/-- Choquet risk is exactly spectral risk evaluated at the bundled kernel. -/
theorem ChoquetRisk_eq_SpectralRisk (g : DistortionFunction) :
    ChoquetRisk P g = SpectralRisk P g.spectralMeasure := rfl

/-- `ChoquetRisk` factors through law. -/
theorem ChoquetRisk_factorsThroughLaw (g : DistortionFunction) :
    FactorsThroughLaw P (ChoquetRisk P g) :=
  SpectralRisk_factorsThroughLaw (P := P) g.spectralMeasure

/-- `ChoquetRisk` is law-invariant. -/
theorem ChoquetRisk_lawInvariant (g : DistortionFunction) :
    LawInvariant P (ChoquetRisk P g) :=
  (ChoquetRisk_factorsThroughLaw (P := P) g).lawInvariant (P := P)

/-- `DistortionRisk` factors through law. -/
theorem DistortionRisk_factorsThroughLaw (g : DistortionFunction) :
    FactorsThroughLaw P (DistortionRisk P g) :=
  ChoquetRisk_factorsThroughLaw (P := P) g

/-- `DistortionRisk` is law-invariant. -/
theorem DistortionRisk_lawInvariant (g : DistortionFunction) :
    LawInvariant P (DistortionRisk P g) :=
  ChoquetRisk_lawInvariant (P := P) g

/-- The monetary property of Choquet risk under the current random-variable API. -/
def ChoquetMonetary (g : DistortionFunction) : Prop :=
  Monetary (cashEmbedding P) (ChoquetRisk P g)

/-- The comonotone-additive property of Choquet risk. -/
def ChoquetComonotoneAdditive (g : DistortionFunction) : Prop :=
  ComonotoneAdditive (Comonotone (P := P)) (ChoquetRisk P g)

/-- The coherent property of Choquet risk. -/
def ChoquetCoherent (g : DistortionFunction) : Prop :=
  Coherent (cashEmbedding P) (ChoquetRisk P g)

/-- Distortion and Choquet monetary properties are the same statement. -/
theorem distortionRisk_monetary_iff_choquet (g : DistortionFunction) :
    Monetary (cashEmbedding P) (DistortionRisk P g) ↔ ChoquetMonetary (P := P) g :=
  Iff.rfl

/-- Distortion and Choquet comonotone additivity are the same statement. -/
theorem distortionRisk_comonotoneAdditive_iff_choquet (g : DistortionFunction) :
    ComonotoneAdditive (Comonotone (P := P)) (DistortionRisk P g) ↔
      ChoquetComonotoneAdditive (P := P) g :=
  Iff.rfl

/-- Distortion and Choquet coherence are the same statement. -/
theorem distortionRisk_coherent_iff_choquet (g : DistortionFunction) :
    Coherent (cashEmbedding P) (DistortionRisk P g) ↔ ChoquetCoherent (P := P) g :=
  Iff.rfl

end

end RiskMeasure
