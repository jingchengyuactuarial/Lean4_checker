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

## Reusable infrastructure already in the repository

The verified AES lemmas sit on top of a reusable risk-measure layer that
already contains:

- confidence levels in `[0,1]`, random variables, laws, quantiles, `VaR`, and
  `ES`;
- shortfall-type envelopes such as `ESg`, `AES`, `OCE`, and `ShortfallRisk`;
- law invariance, event indicators `c 1_A`, and probability-profile reductions
  for set functions;
- stronger atomless splitting tools used to transport folded witnesses from the
  unit interval to general probability spaces.

## Library-first notes

The formalization strategy is still to reuse `mathlib` whenever the right
abstraction already exists, instead of rebuilding parallel APIs inside this
repository. In the current AES development, the most useful pieces have been:

- `IdentDistrib` / law-level arguments for law invariance;
- `ProbabilityTheory.cdf` and related measure-equality lemmas for
  distribution-level calculations;
- `ConvexOn`, one-sided derivatives, and interval-integral tools for the
  convex-analysis steps;
- indicator-function measurability and integral lemmas for event-based witness
  reductions.

The main gap not covered directly by `mathlib` is the stronger splitting form
of atomlessness used in the paper proof, which is why the project contains the
dedicated atomless transport layer.

## Proof-facing bridge pattern

The repository separates reusable risk-measure theory from proof-facing bridge
lemmas:

- `Formalization/RiskMeasure/...` stores definitions and reusable pointwise
  lemmas;
- `Formalization/<ProofName>/Bridge.lean` stores narrow wrappers, profile
  identities, and reduction lemmas that are mostly useful inside one proof.

This keeps the core API from turning into a collection of one-off theorem
wrappers while still making the main proof route readable.

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

## References

- Artzner, Delbaen, Eber, Heath, "Coherent Measures of Risk", *Mathematical
  Finance*, 1999.
- Acerbi, Tasche, "On the Coherence of Expected Shortfall", *Journal of Banking
  & Finance*, 2002.
- Föllmer, Schied, *Stochastic Finance*, de Gruyter, 4th edition, 2016.
