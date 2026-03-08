import Formalization.RiskMeasure.Quantile
import Formalization.RiskMeasure.Shortfall
import Formalization.RiskMeasure.Deviation

/-!
# Common Risk Measures

This file is the convenience entry point for the common named risk measures.
The underlying implementation is now split by category:

- quantiles and `VaR`;
- shortfall-type functionals such as `ES`, `ESg`, and `AES`;
- deviation-type functionals such as `MAD`, `median`, `MMD`, and `variance`.

AES-proof-specific support layers such as law invariance, event indicators,
set-function profiles, and atomless splitting live in separate modules.
-/
