import Formalization.RiskMeasure.Atomless
import Formalization.RiskMeasure.Axioms

/-!
# Set Functions and Probability Profiles

The AES proof passes from submodular risk measures on random variables to
submodular set functions on events, and then to one-dimensional profiles.
-/

open MeasureTheory

namespace RiskMeasure

section

variable {Ω C : Type*} [MeasurableSpace Ω]

/-- A set functional depends only on event probability. -/
def DependsOnlyOnProbability (P : Measure Ω) (μ : Set Ω → C) : Prop :=
  ∀ ⦃A B : Set Ω⦄, MeasurableSet A → MeasurableSet B → P A = P B → μ A = μ B

/-- A one-dimensional profile representing a set functional through event probabilities. -/
def EventProfile (P : Measure Ω) (μ : Set Ω → C) (φ : ℝ → C) : Prop :=
  ∀ ⦃A : Set Ω⦄, MeasurableSet A → μ A = φ (P A).toReal

/-- Set-function submodularity, exposed under a dedicated name for event-based arguments. -/
abbrev SetSubmodular [Preorder C] [Add C] (μ : Set Ω → C) : Prop :=
  Submodular μ

/-- Event submodularity restricted to measurable sets. This is the exact form typically used in
probability-space arguments, including the AES reduction. -/
def MeasurableSetSubmodular (μ : Set Ω → ℝ) : Prop :=
  ∀ ⦃A B : Set Ω⦄, MeasurableSet A → MeasurableSet B →
    μ (A ∩ B) + μ (A ∪ B) ≤ μ A + μ B

/-- Decreasing increments on `[0,1]`, the profile property used in the AES proof. -/
def DecreasingIncrements (φ : ℝ → ℝ) : Prop :=
  ∀ ⦃s t h : ℝ⦄, 0 ≤ s → s ≤ t → 0 ≤ h → t + h ≤ 1 →
    φ (s + h) + φ t ≥ φ s + φ (t + h)

end

section ProbabilityProfiles

open MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω]
variable (P : Measure Ω)

/-- Full set-function submodularity implies measurable-event submodularity. -/
theorem MeasurableSetSubmodular.of_setSubmodular {μ : Set Ω → ℝ}
    (hμ : SetSubmodular μ) : MeasurableSetSubmodular μ := by
  intro A B hA hB
  exact hμ A B

/-- Any explicit event profile automatically depends only on event probability. -/
theorem DependsOnlyOnProbability.of_eventProfile {μ : Set Ω → ℝ} {φ : ℝ → ℝ}
    (hφ : EventProfile P μ φ) : DependsOnlyOnProbability P μ := by
  intro A B hA hB hAB
  rw [hφ hA, hφ hB, hAB]

variable [IsProbabilityMeasure P]

/-- Noncomputably choose a one-dimensional profile from a set functional that depends only on event
probability. -/
noncomputable def profileFromProbability (hsplit : HasFullEventSplitting P) (μ : Set Ω → C) :
    ℝ → C :=
  fun t =>
    if ht : 0 ≤ t ∧ t ≤ 1 then
      let A :=
        Classical.choose (exists_measurableSet_measureReal_eq (P := P) hsplit ht.1 ht.2)
      μ A
    else
      μ ∅

/-- On the unit interval, the chosen profile agrees with the chosen witness event. -/
theorem profileFromProbability_eq (hsplit : HasFullEventSplitting P) (μ : Set Ω → C)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    profileFromProbability P hsplit μ t =
      μ (Classical.choose (exists_measurableSet_measureReal_eq (P := P) hsplit ht0 ht1)) := by
  simp [profileFromProbability, ht0, ht1]

/-- Exact splitting upgrades "depends only on probability" to an explicit one-dimensional event
profile. -/
theorem EventProfile.of_dependsOnlyOnProbability {μ : Set Ω → C}
    (hsplit : HasFullEventSplitting P) (hμ : DependsOnlyOnProbability P μ) :
    EventProfile P μ (profileFromProbability P hsplit μ) := by
  intro A hA
  have ht0 : 0 ≤ P.real A := by positivity
  have ht1 : P.real A ≤ 1 := measureReal_le_one (μ := P)
  let B : Set Ω := Classical.choose (exists_measurableSet_measureReal_eq (P := P) hsplit ht0 ht1)
  have hB : MeasurableSet B :=
    (Classical.choose_spec (exists_measurableSet_measureReal_eq (P := P) hsplit ht0 ht1)).1
  have hBreal : P.real B = P.real A :=
    (Classical.choose_spec (exists_measurableSet_measureReal_eq (P := P) hsplit ht0 ht1)).2
  have hBA : P B = P A :=
    (measureReal_eq_measureReal_iff (μ := P) (ν := P) (s := B) (t := A)).mp hBreal
  change μ A = profileFromProbability P hsplit μ (P.real A)
  rw [profileFromProbability_eq (P := P) hsplit μ ht0 ht1]
  exact hμ hA hB hBA.symm

/-- An event profile over a submodular set function has decreasing increments whenever the
underlying probability space admits exact event splitting. -/
theorem decreasingIncrements_of_measurableSetSubmodular_of_eventProfile
    {μ : Set Ω → ℝ} {φ : ℝ → ℝ} (hsplit : HasFullEventSplitting P)
    (hμ : MeasurableSetSubmodular μ) (hφ : EventProfile P μ φ) :
    DecreasingIncrements φ := by
  intro s t h hs0 hst hh0 hth1
  have ht0 : 0 ≤ t := le_trans hs0 hst
  have ht1 : t ≤ 1 := by linarith
  rcases exists_measurableSet_measureReal_eq (P := P) hsplit ht0 ht1 with ⟨T, hT, hTreal⟩
  rcases exists_subset_measurableSet_measureReal_eq (P := P) hsplit hT hs0
      (by simpa [hTreal] using hst) with
    ⟨S, hST, hS, hSreal⟩
  have hhTcompl : h ≤ P.real Tᶜ := by
    rw [probReal_compl_eq_one_sub (μ := P) hT, hTreal]
    linarith
  rcases exists_subset_measurableSet_measureReal_eq (P := P) hsplit hT.compl hh0 hhTcompl with
    ⟨H, hHT, hH, hHreal⟩
  have hSH : Disjoint S H := by
    refine Set.disjoint_left.2 ?_
    intro ω hωS hωH
    exact hHT hωH (hST hωS)
  have hTH : Disjoint T H := by
    refine Set.disjoint_left.2 ?_
    intro ω hωT hωH
    exact hHT hωH hωT
  have h_inter : (S ∪ H) ∩ T = S := by
    ext ω
    constructor
    · intro hω
      rcases hω with ⟨hω, hωT⟩
      rcases hω with hωS | hωH
      · exact hωS
      · exact False.elim (hHT hωH hωT)
    · intro hωS
      exact ⟨Or.inl hωS, hST hωS⟩
  have h_union : (S ∪ H) ∪ T = T ∪ H := by
    ext ω
    constructor
    · intro hω
      rcases hω with hω | hωT
      · rcases hω with hωS | hωH
        · exact Or.inl (hST hωS)
        · exact Or.inr hωH
      · exact Or.inl hωT
    · intro hω
      rcases hω with hωT | hωH
      · exact Or.inr hωT
      · exact Or.inl (Or.inr hωH)
  have hSUH_real : P.real (S ∪ H) = s + h := by
    rw [measureReal_union hSH hH, hSreal, hHreal]
  have hTUH_real : P.real (T ∪ H) = t + h := by
    rw [measureReal_union hTH hH, hTreal, hHreal]
  have hS_eval : μ S = φ s := by
    rw [hφ hS]
    simpa [Measure.real] using congrArg φ hSreal
  have hT_eval : μ T = φ t := by
    rw [hφ hT]
    simpa [Measure.real] using congrArg φ hTreal
  have hSUH_eval : μ (S ∪ H) = φ (s + h) := by
    rw [hφ (hS.union hH)]
    simpa [Measure.real] using congrArg φ hSUH_real
  have hTUH_eval : μ (T ∪ H) = φ (t + h) := by
    rw [hφ (hT.union hH)]
    simpa [Measure.real] using congrArg φ hTUH_real
  have hsub : μ ((S ∪ H) ∩ T) + μ ((S ∪ H) ∪ T) ≤ μ (S ∪ H) + μ T := hμ (hS.union hH) hT
  rw [h_inter, h_union, hS_eval, hTUH_eval, hSUH_eval, hT_eval] at hsub
  exact hsub

/-- An event profile over a submodular set function has decreasing increments whenever the
underlying probability space admits exact event splitting. -/
theorem decreasingIncrements_of_setSubmodular_of_eventProfile
    {μ : Set Ω → ℝ} {φ : ℝ → ℝ} (hsplit : HasFullEventSplitting P)
    (hμ : SetSubmodular μ) (hφ : EventProfile P μ φ) :
    DecreasingIncrements φ := by
  exact decreasingIncrements_of_measurableSetSubmodular_of_eventProfile (P := P) hsplit
    (MeasurableSetSubmodular.of_setSubmodular hμ) hφ

/-- Combined bridge used in the AES proof: a submodular set function that depends only on event
probability induces a one-dimensional profile with decreasing increments. -/
theorem decreasingIncrements_of_measurableSetSubmodular_of_dependsOnlyOnProbability
    {μ : Set Ω → ℝ} (hsplit : HasFullEventSplitting P) (hμ : MeasurableSetSubmodular μ)
    (hdep : DependsOnlyOnProbability P μ) :
    DecreasingIncrements (profileFromProbability P hsplit μ) := by
  exact decreasingIncrements_of_measurableSetSubmodular_of_eventProfile (P := P) hsplit hμ
    (EventProfile.of_dependsOnlyOnProbability (P := P) hsplit hdep)

/-- Combined bridge used in the AES proof: a submodular set function that depends only on event
probability induces a one-dimensional profile with decreasing increments. -/
theorem decreasingIncrements_of_setSubmodular_of_dependsOnlyOnProbability
    {μ : Set Ω → ℝ} (hsplit : HasFullEventSplitting P) (hμ : SetSubmodular μ)
    (hdep : DependsOnlyOnProbability P μ) :
    DecreasingIncrements (profileFromProbability P hsplit μ) := by
  exact decreasingIncrements_of_measurableSetSubmodular_of_dependsOnlyOnProbability
    (P := P) hsplit (MeasurableSetSubmodular.of_setSubmodular hμ) hdep

end ProbabilityProfiles

end RiskMeasure
