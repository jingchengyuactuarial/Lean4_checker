# formalization

Standalone Lean 4 project for reusable risk-measure foundations, built on top of `mathlib`.

## Current scope

- abstract axioms for monotone, cash-additive, subadditive, submodular, supermodular,
  convex, and coherent risk measures;
- concrete distribution-level and random-variable-level definitions for common risk measures;
- a placeholder entry point for the AES submodularity project.

## Implemented risk measures

The current `Formalization/RiskMeasure/Common.lean` module defines:

- `VaR` from the lower quantile induced by `ProbabilityTheory.cdf`;
- `ES` as the normalized integral of `VaR` over the tail;
- `ESg` and `AES` as supremum envelopes of penalized expected shortfall;
- `MAD` as mean absolute deviation around the mean;
- `median` as the lower median, i.e. the `1/2` quantile;
- `MMD` as mean median deviation around that median;
- `variance` by directly reusing `mathlib`'s `Var[X; P]`.

The current random-variable API works on the subtype of almost-everywhere measurable real-valued
functions under a fixed probability measure `P`.

## Quick start

```bash
source $HOME/.elan/env
lake build
```

## Current module layout

- `Formalization/RiskMeasure/Basic.lean`
- `Formalization/RiskMeasure/Common.lean`
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
