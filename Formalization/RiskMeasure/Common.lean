import Formalization.RiskMeasure.Basic

/-!
# Common Risk-Measure Interfaces

This file introduces names for standard families of risk measures that appear
throughout the actuarial and mathematical-finance literature.

At this stage the emphasis is on reusable interfaces rather than on committing
to one fully formalized probabilistic implementation for every example.
-/

namespace RiskMeasure

section Families

variable (I X C : Type*)

/-- Value-at-Risk as an indexed family of risk measures. -/
abbrev ValueAtRisk := I → X → C

/-- Short alias for Value-at-Risk. -/
abbrev VaR := ValueAtRisk I X C

/-- Expected shortfall / CVaR as an indexed family of risk measures. -/
abbrev ExpectedShortfall := I → X → C

/-- Short alias for expected shortfall. -/
abbrev ES := ExpectedShortfall I X C

/-- Mean absolute deviation. -/
abbrev MeanAbsoluteDeviation := X → C

/-- Mean-median deviation. -/
abbrev MeanMedianDeviation := X → C

/-- Variance viewed as a risk functional. -/
abbrev Variance := X → C

end Families

section PenalizedShortfall

variable {I X C : Type*}

/-- Penalized expected shortfall built from an ES family and a penalty profile. -/
def ExpectedShortfallWithPenalty [SupSet C] [Sub C]
    (es : I → X → C) (g : I → C) : X → C :=
  fun x => sSup (Set.range fun i => es i x - g i)

/-- Short alias used in parts of the literature for penalized expected shortfall. -/
abbrev ESg [SupSet C] [Sub C] (es : I → X → C) (g : I → C) : X → C :=
  ExpectedShortfallWithPenalty es g

/-- Adjusted expected shortfall. -/
abbrev AdjustedExpectedShortfall [SupSet C] [Sub C]
    (es : I → X → C) (g : I → C) : X → C :=
  ExpectedShortfallWithPenalty es g

/-- Short alias for adjusted expected shortfall. -/
abbrev AES [SupSet C] [Sub C] (es : I → X → C) (g : I → C) : X → C :=
  AdjustedExpectedShortfall es g

example [SupSet C] [Sub C] (es : I → X → C) (g : I → C) :
    AES es g = ESg es g := rfl

end PenalizedShortfall

end RiskMeasure
