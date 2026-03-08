import Formalization.AesSubmodularity.Bridge

namespace AesSubmodularity

/-!
This file is the entry point for the Lean formalization of the AES submodularity
result from `../aes_submodularity_proof.tex`.

Planned layers:
1. Reuse the abstract axioms from `Formalization.RiskMeasure.Axioms`.
2. Use the random-variable, law-invariance, and indicator modules to encode
   the event-based reductions appearing in the paper proof.
3. Isolate the bridge from event submodularity to one-dimensional midpoint
   concavity / local boundedness on `(0,1]`, together with the stronger
   atomless splitting property the proof actually uses.
4. Replace the draft's incorrect endpoint-continuity step with a Lean-valid
   real-analysis bridge (e.g. Bernstein-Doetsch / slope-at-origin).
5. Formalize the final AES characterization on top of the quantile/ES/AES
   interface.
-/

end AesSubmodularity
