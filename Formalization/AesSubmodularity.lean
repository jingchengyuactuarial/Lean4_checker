import Formalization.RiskMeasure

namespace AesSubmodularity

/-!
This file is the entry point for the Lean formalization of the AES submodularity
result from `../aes_submodularity_proof.tex`.

Planned layers:
1. Reuse the abstract axioms from `Formalization.RiskMeasure.Axioms`.
2. Use the random-variable, law-invariance, and indicator modules to encode
   the event-based reductions appearing in the paper proof.
3. Isolate the bridge from event submodularity to one-dimensional concavity on
   `[0,1]`, together with the stronger atomless splitting property the proof
   actually uses.
4. Formalize the AES theorem on top of the quantile/ES/AES interface.
-/

open MeasureTheory
open RiskMeasure

section LawReduction

variable {Ω C : Type*} [MeasurableSpace Ω]
variable (P : Measure Ω) [IsProbabilityMeasure P]

/-- First AES reduction step: by law invariance, a risk functional evaluated on `c 1_A` depends
only on the probability of `A`. -/
theorem lawInvariant_scaledIndicator_eq_of_measure_eq
    {ρ : RandomVariable P → C} (hρ : LawInvariant P ρ) (c : ℝ)
    {A B : Set Ω} (hA : MeasurableSet A) (hB : MeasurableSet B) (hAB : P A = P B) :
    ρ (scaledIndicatorRV P c A hA) = ρ (scaledIndicatorRV P c B hB) := by
  exact hρ.of_identDistrib (P := P)
    (identDistrib_scaledIndicator_of_measure_eq (P := P) c hA hB hAB)

end LawReduction

end AesSubmodularity
