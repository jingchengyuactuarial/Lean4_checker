import Formalization.RiskMeasure.Basic

namespace AesSubmodularity

/-!
This file is the entry point for the Lean formalization of the AES submodularity
result from `../aes_submodularity_proof.tex`.

Planned layers:
1. Reuse the generic risk-measure API from `Formalization.RiskMeasure.Basic`.
2. Isolate generic lemmas about submodularity, concavity, and atomless spaces.
3. Formalize the theorem after choosing a Lean-friendly ES/AES interface.
-/

example : True := trivial

end AesSubmodularity
