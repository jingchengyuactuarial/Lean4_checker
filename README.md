# formalization

Standalone Lean 4 project for reusable risk-measure foundations, built on top of `mathlib`.

## Current scope

- abstract axioms for monotone, cash-additive, subadditive, submodular, supermodular,
  convex, and coherent risk measures;
- concrete distribution-level and random-variable-level definitions for common risk measures;
- AES-proof support modules for law invariance, indicator positions, set-function profiles,
  and stronger atomless splitting hypotheses;
- a placeholder entry point for the AES submodularity project.

## Implemented risk measures

The current risk-measure layer defines:

- `CE` as the generalized-inverse certainty equivalent `ℓ⁻¹(E[ℓ(X)])`;
- `VaR` from the lower quantile induced by `ProbabilityTheory.cdf`;
- `ES` as the normalized integral of `VaR` over the tail;
- `ESg` and `AES` as supremum envelopes of penalized expected shortfall;
- `OCE` as the infimum envelope `inf_m (m + E[ℓ(X - m)])`;
- `ShortfallRisk` as the acceptance-threshold version `inf {m | E[ℓ(X-m)] ≤ r}`;
- distortion / spectral / Choquet risk measures through bundled distortion functions and
  probability measures on confidence levels;
- `MAD` as mean absolute deviation around the mean;
- `median` as the lower median, i.e. the `1/2` quantile;
- `MMD` as mean median deviation around that median;
- `Gini` as the Gini mean difference `E |X - X'|`;
- `variance` by directly reusing `mathlib`'s `Var[X; P]`.

The current random-variable API works on the subtype of almost-everywhere measurable real-valued
functions under a fixed probability measure `P`.

For the AES proof specifically, the repository now also isolates:

- law invariance as a standalone property;
- event indicators and scaled indicators `c 1_A`;
- probability-profile and decreasing-increments abstractions for set functions;
- a project-level strong atomless splitting property, since `mathlib`'s `NoAtoms` is weaker than
  the exact splitting used in the paper proof.

## Library-first notes

The current formalization strategy is to reuse `mathlib` aggressively whenever the abstraction
already exists, instead of rebuilding parallel APIs inside this repository. In practice this has
been especially helpful in four places:

- `ProbabilityTheory.IdentDistrib` / `HasLaw` for law-invariance arguments;
- `ProbabilityTheory.cdf` and related measure-equality lemmas for distribution-level work;
- `ConvexOn` / `ConcaveOn` / Jensen / `OrderIso` for inverse-function and profile arguments;
- indicator-function measurability and integral lemmas for positions of the form `c 1_A`.

The main place where `mathlib` currently does not reach the exact AES proof is atomlessness:
`MeasureTheory.NoAtoms` is available, but it only gives singleton-nullness, not the stronger event
splitting property `∀ t ≤ P(A), ∃ B ⊆ A, P(B) = t` used in the paper proof.

## Quick start

```bash
source $HOME/.elan/env
lake build
```

## Current module layout

- `Formalization/RiskMeasure/Axioms.lean`
- `Formalization/RiskMeasure/RandomVariable.lean`
- `Formalization/RiskMeasure/CertaintyEquivalent.lean`
- `Formalization/RiskMeasure/Quantile.lean`
- `Formalization/RiskMeasure/Shortfall.lean`
- `Formalization/RiskMeasure/Distortion.lean`
- `Formalization/RiskMeasure/Deviation.lean`
- `Formalization/RiskMeasure/LawInvariant.lean`
- `Formalization/RiskMeasure/Indicators.lean`
- `Formalization/RiskMeasure/SetFunctions.lean`
- `Formalization/RiskMeasure/Atomless.lean`
- `Formalization/RiskMeasure/Common.lean` as a convenience re-export
- `Formalization/AesSubmodularity.lean`

## References

This library is being organized around standard definitions from the risk-measure literature.
The main starting references are:

- Artzner, Delbaen, Eber, Heath, "Coherent Measures of Risk", *Mathematical Finance*, 1999.
- Acerbi, Tasche, "On the Coherence of Expected Shortfall", *Journal of Banking & Finance*, 2002.
- Föllmer, Schied, *Stochastic Finance*, de Gruyter, 4th edition, 2016.

## Significant Contributions

- Jingcheng Yu: project direction, mathematical specification, and target formalization goals.
- GPT-5.4: standalone Lean package scaffolding, initial risk-measure API design, concrete
  measure-theoretic implementations for `VaR`, `ES`, `AES`, `ESg`, `MAD`, `median`, `MMD`,
  integration of `mathlib` variance, README/documentation drafting, and build validation.
