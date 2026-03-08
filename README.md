# formalization

Standalone Lean 4 project for reusable risk-measure foundations.

Current scope:

- abstract axioms for monotone, cash-additive, subadditive, convex, and coherent risk measures;
- a small working example on `ℝ`;
- a placeholder entry point for the AES submodularity project.

Planned scope:

- `VaR` and quantile-style definitions;
- `ES` / `CVaR`;
- law invariance and atomless-space lemmas;
- the AES submodularity theorem from the LaTeX manuscript.

## Quick start

```bash
source $HOME/.elan/env
lake build
```

## Current module layout

- `Formalization/RiskMeasure/Basic.lean`
- `Formalization/RiskMeasure/Examples.lean`
- `Formalization/AesSubmodularity.lean`

## GitHub notes

When you create the empty GitHub repository, this project can be pushed directly as a standalone
Lean package. The generated GitHub Actions workflows are already present in `.github/workflows/`.
