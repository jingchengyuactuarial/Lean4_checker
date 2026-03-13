# Lean4_checker

Lean 4 project for the AES submodularity formalization, with the current public
snapshot focused on the two AES lemmas that have already been checked and are
ready to share.

## Current verified AES results

- Finite-tail convex lemma:
  the folded-witness formalization is centered in
  `Formalization/AesSubmodularity/FiniteConvexFolded.lean`, with the current
  end-to-end theorem
  `AesSubmodularity.not_submodular_AES_of_convexOn_of_stronglyAtomless`.
- Infinite-tail collapse lemma:
  the bridge and collapse formalization is centered in
  `Formalization/AesSubmodularity/Bridge.lean` and
  `Formalization/RiskMeasure/Shortfall.lean`, with the current theorem
  `AesSubmodularity.AESExt_eq_ES_of_submodular_of_forall_eventuallyLarge_of_isLUB`.

## Scope of this snapshot

This repository snapshot intentionally exposes only the Lean development needed
for those two verified lemma lines and their supporting risk-measure
infrastructure. Older draft routes and unverified extensions are not part of
the current public story.

## Main modules

- `Formalization/RiskMeasure/RandomVariable.lean`
- `Formalization/RiskMeasure/Quantile.lean`
- `Formalization/RiskMeasure/Shortfall.lean`
- `Formalization/RiskMeasure/LawInvariant.lean`
- `Formalization/RiskMeasure/Indicators.lean`
- `Formalization/RiskMeasure/SetFunctions.lean`
- `Formalization/RiskMeasure/Atomless.lean`
- `Formalization/RiskMeasure/AtomlessUniform.lean`
- `Formalization/AesSubmodularity/Bridge.lean`
- `Formalization/AesSubmodularity/FiniteConvexFolded.lean`
- `Formalization/AesSubmodularity.lean`

## Build

```bash
source $HOME/.elan/env
lake build Formalization
```

## Notes

- The finite-tail result currently uses the theorem statement above as the
  checked Lean endpoint for Lemma 1.
- The infinite-tail result currently uses the theorem statement above as the
  checked Lean endpoint for Lemma 2.
- If the paper statement is later tightened or repackaged, the comparison
  should be made against these compiled theorems rather than against informal
  progress notes.
