import Formalization.RiskMeasure.Atomless
import Mathlib.Data.Real.Archimedean
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Constructions.UnitInterval
import Mathlib.MeasureTheory.Measure.Real

/-!
# Atomless Transport Helpers

This file collects small exact-splitting lemmas that are convenient when building
transport constructions on strongly atomless probability spaces.

The long-term target is a reusable uniform-realization layer. For now we record
the finite partition facts that the later folded witness construction will need.
-/

open MeasureTheory
open scoped unitInterval

namespace RiskMeasure

open unitInterval

/-- The standard uniform probability measure on `[0,1]`, viewed as a measure on `ℝ`. -/
noncomputable def uniformMeasure : Measure ℝ :=
  volume.restrict (Set.Icc (0 : ℝ) 1)

@[simp] theorem map_subtype_val_unitInterval_volume :
    Measure.map ((↑) : I → ℝ) (volume : Measure I) = uniformMeasure := by
  simpa [uniformMeasure] using unitInterval.measurePreserving_coe.map_eq

instance : IsProbabilityMeasure uniformMeasure where
  measure_univ := by
    rw [uniformMeasure, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, Real.volume_Icc,
      sub_zero, ENNReal.ofReal_one]

@[simp] theorem map_projIcc_uniformMeasure :
    Measure.map (Set.projIcc (0 : ℝ) 1 zero_le_one) uniformMeasure = (volume : Measure I) := by
  rw [← map_subtype_val_unitInterval_volume]
  rw [Measure.map_map (μ := (volume : Measure I)) (f := ((↑) : I → ℝ))
    (g := Set.projIcc (0 : ℝ) 1 zero_le_one) (continuous_projIcc.measurable)
    measurable_subtype_coe]
  have hfun :
      Set.projIcc (0 : ℝ) 1 zero_le_one ∘ ((↑) : I → ℝ) = fun x : I => x := by
    funext x
    exact Set.projIcc_val zero_le_one x
  rw [hfun]
  ext s hs
  simp

section CutFamily

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Recover a real-valued coordinate from an increasing family of measurable cuts. -/
noncomputable def cutValue (F : ℝ → Set Ω) (ω : Ω) : ℝ :=
  sInf {x : ℝ | ω ∈ F x}

theorem cutValue_mem_Iic_iff
    {F : ℝ → Set Ω} (hmono : Monotone F)
    (hright : ∀ x : ℝ, F x = ⋂ n : ℕ, F (x + 1 / (n + 1 : ℝ)))
    (hnonempty : ∀ ω : Ω, ({x : ℝ | ω ∈ F x} : Set ℝ).Nonempty)
    (hbbd : ∀ ω : Ω, BddBelow ({x : ℝ | ω ∈ F x} : Set ℝ))
    {ω : Ω} {x : ℝ} :
    cutValue F ω ≤ x ↔ ω ∈ F x := by
  let S : Set ℝ := {y : ℝ | ω ∈ F y}
  constructor
  · intro hx
    rw [hright x]
    simp only [Set.mem_iInter]
    intro n
    have hε : 0 < 1 / (n + 1 : ℝ) := by positivity
    obtain ⟨a, haS, ha_lt⟩ := Real.lt_sInf_add_pos (hnonempty ω) hε
    have ha_le : a ≤ x + 1 / (n + 1 : ℝ) := by
      have hsInf_le : sInf S ≤ x := hx
      linarith
    exact hmono ha_le haS
  · intro hx
    exact csInf_le (hbbd ω) hx

theorem preimage_cutValue_Iic
    {F : ℝ → Set Ω} (hmono : Monotone F)
    (hright : ∀ x : ℝ, F x = ⋂ n : ℕ, F (x + 1 / (n + 1 : ℝ)))
    (hnonempty : ∀ ω : Ω, ({x : ℝ | ω ∈ F x} : Set ℝ).Nonempty)
    (hbbd : ∀ ω : Ω, BddBelow ({x : ℝ | ω ∈ F x} : Set ℝ))
    (x : ℝ) :
    cutValue F ⁻¹' Set.Iic x = F x := by
  ext ω
  exact cutValue_mem_Iic_iff hmono hright hnonempty hbbd

theorem measurable_cutValue
    {F : ℝ → Set Ω} (hmeas : ∀ x : ℝ, MeasurableSet (F x)) (hmono : Monotone F)
    (hright : ∀ x : ℝ, F x = ⋂ n : ℕ, F (x + 1 / (n + 1 : ℝ)))
    (hnonempty : ∀ ω : Ω, ({x : ℝ | ω ∈ F x} : Set ℝ).Nonempty)
    (hbbd : ∀ ω : Ω, BddBelow ({x : ℝ | ω ∈ F x} : Set ℝ)) :
    Measurable (cutValue F) := by
  refine measurable_of_Iic fun x => ?_
  simpa [preimage_cutValue_Iic hmono hright hnonempty hbbd x] using hmeas x

section Probability

variable (P : Measure Ω) [IsProbabilityMeasure P]

theorem map_cutValue_eq_uniformMeasure
    {F : ℝ → Set Ω} (hmeas : ∀ x : ℝ, MeasurableSet (F x)) (hmono : Monotone F)
    (hright : ∀ x : ℝ, F x = ⋂ n : ℕ, F (x + 1 / (n + 1 : ℝ)))
    (hnonempty : ∀ ω : Ω, ({x : ℝ | ω ∈ F x} : Set ℝ).Nonempty)
    (hbbd : ∀ ω : Ω, BddBelow ({x : ℝ | ω ∈ F x} : Set ℝ))
    (hmeasure : ∀ x : ℝ, P (F x) = uniformMeasure (Set.Iic x)) :
    Measure.map (cutValue F) P = uniformMeasure := by
  have hcutMeas : Measurable (cutValue F) :=
    measurable_cutValue hmeas hmono hright hnonempty hbbd
  refine Measure.ext_of_Iic _ _ fun x => ?_
  rw [Measure.map_apply hcutMeas measurableSet_Iic,
    preimage_cutValue_Iic hmono hright hnonempty hbbd x, hmeasure x]

end Probability

end CutFamily

section Probability

variable {Ω : Type*} [MeasurableSpace Ω]
variable (P : Measure Ω) [IsProbabilityMeasure P]

/-- Under exact event splitting, any target mass between `A` and `B` can be realized by a
measurable intermediate set `C` with `A ⊆ C ⊆ B`. -/
theorem exists_intermediate_measurableSet_measureReal_eq_of_subset
    (hsplit : HasFullEventSplitting P)
    {A B : Set Ω} (hA : MeasurableSet A) (hB : MeasurableSet B) (hAB : A ⊆ B)
    {t : ℝ} (htA : P.real A ≤ t) (htB : t ≤ P.real B) :
    ∃ C, A ⊆ C ∧ C ⊆ B ∧ MeasurableSet C ∧ P.real C = t := by
  have hdelta0 : 0 ≤ t - P.real A := sub_nonneg.mpr htA
  have hdelta_le : t - P.real A ≤ P.real (B \ A) := by
    rw [measureReal_diff hAB hA]
    linarith
  obtain ⟨D, hDsub, hD, hDreal⟩ :=
    exists_subset_measurableSet_measureReal_eq (P := P) hsplit (hB.diff hA) hdelta0 hdelta_le
  let C : Set Ω := A ∪ D
  have hAD : Disjoint A D := by
    refine Set.disjoint_left.2 ?_
    intro ω hωA hωD
    exact (hDsub hωD).2 hωA
  have hCsub : C ⊆ B := by
    intro ω hωC
    rcases hωC with hωA | hωD
    · exact hAB hωA
    · exact (hDsub hωD).1
  have hCreal : P.real C = t := by
    rw [show C = A ∪ D by rfl, measureReal_union hAD hD, hDreal]
    linarith
  exact ⟨C, Set.subset_union_left, hCsub, hA.union hD, hCreal⟩

/-- Under exact event splitting, two prescribed masses summing to at most `1`
can be realized by disjoint measurable events. -/
theorem exists_disjoint_measurableSet_measureReal_eq_pair
    (hsplit : HasFullEventSplitting P) {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b ≤ 1) :
    ∃ A B : Set Ω,
      MeasurableSet A ∧
      MeasurableSet B ∧
      Disjoint A B ∧
      P.real A = a ∧
      P.real B = b := by
  obtain ⟨A, hA, hAreal⟩ :=
    exists_measurableSet_measureReal_eq (P := P) hsplit ha (by linarith)
  have hbAcompl : b ≤ P.real (Aᶜ : Set Ω) := by
    rw [probReal_compl_eq_one_sub (μ := P) hA, hAreal]
    linarith
  obtain ⟨B, hBA, hB, hBreal⟩ :=
    exists_subset_measurableSet_measureReal_eq (P := P) hsplit hA.compl hb hbAcompl
  refine ⟨A, B, hA, hB, ?_, hAreal, hBreal⟩
  refine Set.disjoint_left.2 ?_
  intro ω hωA hωB
  exact hBA hωB hωA

/-- Under exact event splitting, three prescribed masses summing to `1` can be
realized by a measurable partition of the whole space. -/
theorem exists_three_disjoint_measurableSet_measureReal_eq
    (hsplit : HasFullEventSplitting P) {a b c : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hsum : a + b + c = 1) :
    ∃ A B C : Set Ω,
      MeasurableSet A ∧
      MeasurableSet B ∧
      MeasurableSet C ∧
      Disjoint A B ∧
      Disjoint A C ∧
      Disjoint B C ∧
      P.real A = a ∧
      P.real B = b ∧
      P.real C = c := by
  obtain ⟨A, B, hA, hB, hAB, hAreal, hBreal⟩ :=
    exists_disjoint_measurableSet_measureReal_eq_pair (P := P) hsplit ha hb (by linarith [hc, hsum])
  let C : Set Ω := (A ∪ B)ᶜ
  have hC : MeasurableSet C := (hA.union hB).compl
  have hAC : Disjoint A C := by
    refine Set.disjoint_left.2 ?_
    intro ω hωA hωC
    exact hωC (Or.inl hωA)
  have hBC : Disjoint B C := by
    refine Set.disjoint_left.2 ?_
    intro ω hωB hωC
    exact hωC (Or.inr hωB)
  have hABreal :
      P.real (A ∪ B : Set Ω) = a + b := by
    rw [Measure.real, measure_union hAB hB, ENNReal.toReal_add (measure_ne_top P A)
      (measure_ne_top P B)]
    have hAreal' : (P A).toReal = a := by
      simpa [Measure.real] using hAreal
    have hBreal' : (P B).toReal = b := by
      simpa [Measure.real] using hBreal
    rw [hAreal', hBreal']
  have hCreal : P.real C = c := by
    rw [show C = (A ∪ B : Set Ω)ᶜ by rfl, probReal_compl_eq_one_sub (μ := P) (hA.union hB),
      hABreal]
    linarith
  exact ⟨A, B, C, hA, hB, hC, hAB, hAC, hBC, hAreal, hBreal, hCreal⟩

section Dyadic

/-- A finite dyadic chain of measurable cuts with the prescribed masses `k / 2^n`. -/
structure DyadicLevel (n : ℕ) where
  cut : ℕ → Set Ω
  measurable_cut : ∀ k : ℕ, MeasurableSet (cut k)
  monotone_cut : Monotone cut
  cut_zero : cut 0 = ∅
  cut_top : cut (2 ^ n) = Set.univ
  measure_cut : ∀ {k : ℕ}, k ≤ 2 ^ n → P.real (cut k) = k / (2 ^ n : ℝ)

noncomputable def dyadicLevelZero : DyadicLevel (P := P) 0 where
  cut k := if k = 0 then ∅ else Set.univ
  measurable_cut k := by
    by_cases hk : k = 0
    · simp [hk]
    · simp [hk]
  monotone_cut := by
    intro i j hij
    by_cases hi : i = 0
    · simp [hi]
    · have hj : j ≠ 0 := by
        intro hj
        omega
      simp [hi, hj]
  cut_zero := by simp
  cut_top := by simp
  measure_cut := by
    intro k hk
    have hk' : k = 0 ∨ k = 1 := by omega
    rcases hk' with rfl | rfl
    · simp
    · simp

theorem exists_dyadicLevel_succ (hsplit : HasFullEventSplitting P) {n : ℕ}
    (prev : DyadicLevel (P := P) n) :
    ∃ next : DyadicLevel (P := P) (n + 1), ∀ {k : ℕ}, k ≤ 2 ^ n → next.cut (2 * k) = prev.cut k := by
  have hOddWitness :
      ∀ {k : ℕ}, k ≤ 2 ^ (n + 1) → ¬ Even k →
        ∃ C, prev.cut (k / 2) ⊆ C ∧ C ⊆ prev.cut ((k + 1) / 2) ∧
          MeasurableSet C ∧ P.real C = (k : ℝ) / (2 ^ (n + 1) : ℝ) := by
    intro k hk hodd
    have hkdiv : k / 2 ≤ 2 ^ n := by omega
    have hkdiv_succ : (k + 1) / 2 ≤ 2 ^ n := by
      have hkmod : k % 2 = 1 := Nat.odd_iff.mp (Nat.not_even_iff_odd.mp hodd)
      have hdecomp : 2 * (k / 2) = k - 1 := Nat.two_mul_odd_div_two hkmod
      omega
    have hleft :
        P.real (prev.cut (k / 2)) ≤ (k : ℝ) / (2 ^ (n + 1) : ℝ) := by
      rw [prev.measure_cut hkdiv]
      have hk' : k = 2 * (k / 2) + 1 := by
        have hkmod : k % 2 = 1 := Nat.odd_iff.mp (Nat.not_even_iff_odd.mp hodd)
        have hdecomp : 2 * (k / 2) = k - 1 := Nat.two_mul_odd_div_two hkmod
        omega
      have hk'' : (k : ℝ) = 2 * ((k / 2 : ℕ) : ℝ) + 1 := by
        exact_mod_cast hk'
      have hpow : (0 : ℝ) < (2 ^ n : ℝ) := by positivity
      rw [pow_succ]
      field_simp [hpow.ne']
      nlinarith
    have hright :
        (k : ℝ) / (2 ^ (n + 1) : ℝ) ≤ P.real (prev.cut ((k + 1) / 2)) := by
      rw [prev.measure_cut hkdiv_succ]
      have hnat : k + 1 = 2 * ((k + 1) / 2) := by
        have hkmod : k % 2 = 1 := Nat.odd_iff.mp (Nat.not_even_iff_odd.mp hodd)
        have hdecomp : 2 * (k / 2) = k - 1 := Nat.two_mul_odd_div_two hkmod
        omega
      have hnat' : ((k + 1 : ℕ) : ℝ) = 2 * ((((k + 1) / 2 : ℕ) : ℝ)) := by
        exact_mod_cast hnat
      have hk1 : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by norm_num
      have hbound : (k : ℝ) ≤ 2 * ((((k + 1) / 2 : ℕ) : ℝ)) := by
        linarith
      have hpow : (0 : ℝ) < (2 ^ n : ℝ) := by positivity
      rw [pow_succ]
      field_simp [hpow.ne']
      simpa [mul_comm] using hbound
    exact exists_intermediate_measurableSet_measureReal_eq_of_subset
      (P := P) hsplit (prev.measurable_cut (k / 2)) (prev.measurable_cut ((k + 1) / 2))
      (prev.monotone_cut (by omega)) hleft hright
  let nextCut : ℕ → Set Ω := fun k =>
    if hk : k ≤ 2 ^ (n + 1) then
      if he : Even k then
        prev.cut (k / 2)
      else
        Classical.choose (hOddWitness hk he)
    else
      Set.univ
  have hNextMeas : ∀ k : ℕ, MeasurableSet (nextCut k) := by
    intro k
    by_cases hk : k ≤ 2 ^ (n + 1)
    · by_cases he : Even k
      · simp [nextCut, hk, he, prev.measurable_cut]
      · simp [nextCut, hk, he]
        exact (Classical.choose_spec (hOddWitness hk he)).2.2.1
    · simp [nextCut, hk]
  have hLower : ∀ {k : ℕ}, k ≤ 2 ^ (n + 1) → prev.cut (k / 2) ⊆ nextCut k := by
    intro k hk
    by_cases he : Even k
    · simp [nextCut, hk, he]
    · simp [nextCut, hk, he]
      exact (Classical.choose_spec (hOddWitness hk he)).1
  have hUpper : ∀ {k : ℕ}, k ≤ 2 ^ (n + 1) → nextCut k ⊆ prev.cut ((k + 1) / 2) := by
    intro k hk
    by_cases he : Even k
    · have hsucc : (k + 1) / 2 = k / 2 := by
        have hmul : k / 2 * 2 = k := Nat.div_two_mul_two_of_even he
        omega
      simp [nextCut, hk, he, hsucc]
    · simp [nextCut, hk, he]
      exact (Classical.choose_spec (hOddWitness hk he)).2.1
  have hNextMono : Monotone nextCut := by
    intro i j hij
    by_cases hj : j ≤ 2 ^ (n + 1)
    · have hi : i ≤ 2 ^ (n + 1) := le_trans hij hj
      by_cases hEq : i = j
      · simpa [hEq]
      · have hlt : i < j := lt_of_le_of_ne hij hEq
        exact Set.Subset.trans (hUpper hi)
          (Set.Subset.trans
            (prev.monotone_cut (by omega))
            (hLower hj))
    · simpa [nextCut, hj] using (Set.subset_univ (nextCut i))
  have hNextZero : nextCut 0 = ∅ := by
    have hk : 0 ≤ 2 ^ (n + 1) := by positivity
    have he : Even 0 := by exact ⟨0, by simp⟩
    simp [nextCut, hk, he, prev.cut_zero]
  have hNextTop : nextCut (2 ^ (n + 1)) = Set.univ := by
    have hk : 2 ^ (n + 1) ≤ 2 ^ (n + 1) := le_rfl
    have he : Even (2 ^ (n + 1)) := by
      refine ⟨2 ^ n, ?_⟩
      rw [pow_succ]
      ring
    have hdiv : (2 ^ (n + 1)) / 2 = 2 ^ n := by
      have hmul : (2 ^ (n + 1)) / 2 * 2 = 2 ^ (n + 1) := Nat.div_two_mul_two_of_even he
      rw [pow_succ] at hmul
      omega
    simp [nextCut, hk, he, hdiv, prev.cut_top]
  have hNextMeasure : ∀ {k : ℕ}, k ≤ 2 ^ (n + 1) →
      P.real (nextCut k) = k / (2 ^ (n + 1) : ℝ) := by
    intro k hk
    by_cases he : Even k
    · have hkdiv : k / 2 ≤ 2 ^ n := by omega
      simp [nextCut, hk, he, prev.measure_cut hkdiv]
      have hpow : (0 : ℝ) < (2 ^ n : ℝ) := by positivity
      rw [pow_succ]
      field_simp [hpow.ne']
      exact_mod_cast Nat.div_two_mul_two_of_even he
    · simp [nextCut, hk, he]
      exact (Classical.choose_spec (hOddWitness hk he)).2.2.2
  refine ⟨
    { cut := nextCut
      measurable_cut := hNextMeas
      monotone_cut := hNextMono
      cut_zero := hNextZero
      cut_top := hNextTop
      measure_cut := hNextMeasure },
    ?_⟩
  intro k hk
  have hk' : 2 * k ≤ 2 ^ (n + 1) := by
    rw [pow_succ]
    omega
  have he : Even (2 * k) := by
    refine ⟨k, by omega⟩
  have hdiv : (2 * k) / 2 = k := by omega
  simp [nextCut, hk', he, hdiv]

noncomputable def dyadicLevel (hsplit : HasFullEventSplitting P) :
    (n : ℕ) → DyadicLevel (P := P) n
  | 0 => dyadicLevelZero (P := P)
  | n + 1 => Classical.choose (exists_dyadicLevel_succ (P := P) hsplit (dyadicLevel hsplit n))

theorem dyadicLevel_succ_even (hsplit : HasFullEventSplitting P) {n k : ℕ} (hk : k ≤ 2 ^ n) :
    (dyadicLevel (P := P) hsplit (n + 1)).cut (2 * k) = (dyadicLevel (P := P) hsplit n).cut k :=
  Classical.choose_spec
    (exists_dyadicLevel_succ (P := P) hsplit (dyadicLevel (P := P) hsplit n)) hk

noncomputable def dyadicCutFamily (hsplit : HasFullEventSplitting P) (x : ℝ) : Set Ω :=
  ⋂ n : ℕ, ⋂ k : ℕ,
    if hk : k ≤ 2 ^ n then
      if x < (k : ℝ) / (2 ^ n : ℝ) then (dyadicLevel (P := P) hsplit n).cut k else Set.univ
    else
      Set.univ

theorem mem_dyadicCutFamily_iff (hsplit : HasFullEventSplitting P) {x : ℝ} {ω : Ω} :
    ω ∈ dyadicCutFamily (P := P) hsplit x ↔
      ∀ n (k : ℕ), k ≤ 2 ^ n → x < (k : ℝ) / (2 ^ n : ℝ) →
        ω ∈ (dyadicLevel (P := P) hsplit n).cut k := by
  constructor
  · intro h n k hk hxk
    have hn : ω ∈ ⋂ k : ℕ,
        if hk : k ≤ 2 ^ n then
          if x < (k : ℝ) / (2 ^ n : ℝ) then (dyadicLevel (P := P) hsplit n).cut k else Set.univ
        else Set.univ := Set.mem_iInter.1 h n
    have hk' : ω ∈ if hk : k ≤ 2 ^ n then
          if x < (k : ℝ) / (2 ^ n : ℝ) then (dyadicLevel (P := P) hsplit n).cut k else Set.univ
        else Set.univ := Set.mem_iInter.1 hn k
    simpa [hk, hxk] using hk'
  · intro h
    refine Set.mem_iInter.2 ?_
    intro n
    refine Set.mem_iInter.2 ?_
    intro k
    by_cases hk : k ≤ 2 ^ n
    · by_cases hxk : x < (k : ℝ) / (2 ^ n : ℝ)
      · simpa [hk, hxk] using h n k hk hxk
      · simp [hk, hxk]
    · simp [hk]

theorem monotone_dyadicCutFamily (hsplit : HasFullEventSplitting P) :
    Monotone (dyadicCutFamily (P := P) hsplit) := by
  intro x y hxy ω hω
  rw [mem_dyadicCutFamily_iff (P := P) hsplit] at hω ⊢
  intro n k hk hyk
  exact hω n k hk (lt_of_le_of_lt hxy hyk)

theorem dyadicCutFamily_rightContinuous (hsplit : HasFullEventSplitting P) (x : ℝ) :
    dyadicCutFamily (P := P) hsplit x =
      ⋂ m : ℕ, dyadicCutFamily (P := P) hsplit (x + 1 / (m + 1 : ℝ)) := by
  ext ω
  constructor
  · intro h
    refine Set.mem_iInter.2 ?_
    intro m
    have hxle : x ≤ x + 1 / (m + 1 : ℝ) := by
      have hnonneg : 0 ≤ 1 / (m + 1 : ℝ) := by positivity
      linarith
    exact (monotone_dyadicCutFamily (P := P) hsplit hxle) h
  · intro h
    rw [mem_dyadicCutFamily_iff (P := P) hsplit]
    intro n k hk hxk
    obtain ⟨m, hm⟩ := exists_nat_one_div_lt (sub_pos.mpr hxk)
    have hmemb : ω ∈ dyadicCutFamily (P := P) hsplit (x + 1 / (m + 1 : ℝ)) := Set.mem_iInter.1 h m
    have hxk' : x + 1 / (m + 1 : ℝ) < (k : ℝ) / (2 ^ n : ℝ) := by
      linarith
    exact (mem_dyadicCutFamily_iff (P := P) hsplit).1 hmemb n k hk hxk'

noncomputable def dyadicUpperIndex (x : ℝ) (n : ℕ) : ℕ :=
  Nat.floor (x * 2 ^ n) + 1

noncomputable def dyadicUpperApprox (x : ℝ) (n : ℕ) : ℝ :=
  (dyadicUpperIndex x n : ℝ) / (2 ^ n : ℝ)

noncomputable def dyadicUpperCut (hsplit : HasFullEventSplitting P) (x : ℝ) (n : ℕ) : Set Ω :=
  (dyadicLevel (P := P) hsplit n).cut (dyadicUpperIndex x n)

theorem dyadicUpperIndex_le_pow {x : ℝ} {n : ℕ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    dyadicUpperIndex x n ≤ 2 ^ n := by
  have hpow : (0 : ℝ) < 2 ^ n := by positivity
  have hlt' : x * 2 ^ n < (2 ^ n : ℕ) := by
    simpa using (mul_lt_mul_of_pos_right hx1 hpow)
  dsimp [dyadicUpperIndex]
  exact Nat.succ_le_of_lt ((Nat.floor_lt (by positivity)).2 hlt')

theorem dyadicUpperIndex_succ_le {x : ℝ} {n : ℕ} (hx0 : 0 ≤ x) :
    dyadicUpperIndex x (n + 1) ≤ 2 * dyadicUpperIndex x n := by
  dsimp [dyadicUpperIndex]
  have hlt1 : x * 2 ^ n < (Nat.floor (x * 2 ^ n) : ℝ) + 1 := Nat.lt_floor_add_one _
  have hlt2 : x * 2 ^ (n + 1) < (2 * (Nat.floor (x * 2 ^ n) + 1) : ℕ) := by
    rw [pow_succ]
    norm_num
    nlinarith
  exact Nat.succ_le_of_lt ((Nat.floor_lt (by positivity)).2 hlt2)

theorem dyadicCutFamily_eq_iInter_upper (hsplit : HasFullEventSplitting P) {x : ℝ}
    (hx0 : 0 ≤ x) (hx1 : x < 1) :
    dyadicCutFamily (P := P) hsplit x = ⋂ n : ℕ, dyadicUpperCut (P := P) hsplit x n := by
  ext ω
  constructor
  · intro h
    refine Set.mem_iInter.2 ?_
    intro n
    rw [mem_dyadicCutFamily_iff (P := P) hsplit] at h
    exact h n (dyadicUpperIndex x n)
      (dyadicUpperIndex_le_pow (x := x) hx0 hx1)
      (by
        have hpow : (0 : ℝ) < 2 ^ n := by positivity
        have hk1 :
            ((Nat.floor (x * 2 ^ n) + 1 : ℕ) : ℝ) = (Nat.floor (x * 2 ^ n) : ℝ) + 1 := by
          norm_num
        dsimp [dyadicUpperCut, dyadicUpperApprox, dyadicUpperIndex]
        field_simp [hpow.ne']
        have hlt : x * 2 ^ n < (Nat.floor (x * 2 ^ n) : ℝ) + 1 := Nat.lt_floor_add_one _
        nlinarith)
  · intro h
    rw [mem_dyadicCutFamily_iff (P := P) hsplit]
    intro n k hk hxk
    have hmin : dyadicUpperIndex x n ≤ k := by
      have hpow : (0 : ℝ) < 2 ^ n := by positivity
      dsimp [dyadicUpperIndex]
      have hlt' := mul_lt_mul_of_pos_right hxk hpow
      have hlt : x * 2 ^ n < (k : ℕ) := by
        simpa [div_eq_mul_inv, hpow.ne'] using hlt'
      exact Nat.succ_le_of_lt ((Nat.floor_lt (by positivity)).2 hlt)
    have hω : ω ∈ dyadicUpperCut (P := P) hsplit x n := Set.mem_iInter.1 h n
    exact (dyadicLevel (P := P) hsplit n).monotone_cut hmin hω

theorem dyadicUpperCut_succ_subset (hsplit : HasFullEventSplitting P) {x : ℝ} {n : ℕ}
    (hx0 : 0 ≤ x) (hx1 : x < 1) :
    dyadicUpperCut (P := P) hsplit x (n + 1) ⊆ dyadicUpperCut (P := P) hsplit x n := by
  have hstep : dyadicUpperIndex x (n + 1) ≤ 2 * dyadicUpperIndex x n :=
    dyadicUpperIndex_succ_le (x := x) hx0
  have hpow : dyadicUpperIndex x n ≤ 2 ^ n := dyadicUpperIndex_le_pow (x := x) hx0 hx1
  refine Set.Subset.trans ((dyadicLevel (P := P) hsplit (n + 1)).monotone_cut hstep) ?_
  simpa [dyadicUpperCut, dyadicLevel_succ_even (P := P) hsplit hpow]

theorem dyadicUpperCut_antitone (hsplit : HasFullEventSplitting P) {x : ℝ}
    (hx0 : 0 ≤ x) (hx1 : x < 1) : Antitone (dyadicUpperCut (P := P) hsplit x) := by
  exact antitone_nat_of_succ_le (fun n => dyadicUpperCut_succ_subset (P := P) hsplit hx0 hx1)

theorem measure_dyadicUpperCut {x : ℝ} {n : ℕ} (hsplit : HasFullEventSplitting P)
    (hx0 : 0 ≤ x) (hx1 : x < 1) :
    P (dyadicUpperCut (P := P) hsplit x n) = ENNReal.ofReal (dyadicUpperApprox x n) := by
  have hreal : P.real (dyadicUpperCut (P := P) hsplit x n) = dyadicUpperApprox x n := by
    dsimp [dyadicUpperCut, dyadicUpperApprox, dyadicUpperIndex]
    exact (dyadicLevel (P := P) hsplit n).measure_cut (dyadicUpperIndex_le_pow (x := x) hx0 hx1)
  have hfin : P (dyadicUpperCut (P := P) hsplit x n) ≠ ⊤ := measure_ne_top P _
  rw [Measure.real] at hreal
  have h := congrArg ENNReal.ofReal hreal
  simpa [hfin] using h

theorem dyadicUpperApprox_gt_self {x : ℝ} {n : ℕ} : x < dyadicUpperApprox x n := by
  have hpow : (0 : ℝ) < 2 ^ n := by positivity
  have hk1 : ((Nat.floor (x * 2 ^ n) + 1 : ℕ) : ℝ) = (Nat.floor (x * 2 ^ n) : ℝ) + 1 := by
    norm_num
  dsimp [dyadicUpperApprox, dyadicUpperIndex]
  field_simp [hpow.ne']
  have hlt : x * 2 ^ n < (Nat.floor (x * 2 ^ n) : ℝ) + 1 := Nat.lt_floor_add_one _
  nlinarith

theorem dyadicUpperApprox_le_self_add_inv {x : ℝ} {n : ℕ} (hx0 : 0 ≤ x) :
    dyadicUpperApprox x n ≤ x + 1 / (2 ^ n : ℝ) := by
  have hpow : (0 : ℝ) < 2 ^ n := by positivity
  have hfloor : (Nat.floor (x * 2 ^ n) : ℝ) ≤ x * 2 ^ n := Nat.floor_le (by positivity)
  have hk1 : ((Nat.floor (x * 2 ^ n) + 1 : ℕ) : ℝ) = (Nat.floor (x * 2 ^ n) : ℝ) + 1 := by
    norm_num
  dsimp [dyadicUpperApprox, dyadicUpperIndex]
  field_simp [hpow.ne']
  nlinarith

theorem tendsto_inv_pow_two : Filter.Tendsto (fun n : ℕ => (1 : ℝ) / (2 ^ n : ℝ))
    Filter.atTop (nhds 0) := by
  simpa [one_div] using
    (tendsto_inv_atTop_zero.comp (tendsto_pow_atTop_atTop_of_one_lt (show (1 : ℝ) < 2 by norm_num)))

theorem tendsto_dyadicUpperApprox {x : ℝ} (hx0 : 0 ≤ x) :
    Filter.Tendsto (dyadicUpperApprox x) Filter.atTop (nhds x) := by
  have hupper : Filter.Tendsto (fun n : ℕ => x + 1 / (2 ^ n : ℝ)) Filter.atTop (nhds x) := by
    simpa using (tendsto_inv_pow_two.const_add x)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupper ?_ ?_
  · intro n
    exact le_of_lt (dyadicUpperApprox_gt_self (x := x) (n := n))
  · intro n
    exact dyadicUpperApprox_le_self_add_inv (x := x) hx0

theorem dyadicCutFamily_of_lt_zero (hsplit : HasFullEventSplitting P) {x : ℝ} (hx : x < 0) :
    dyadicCutFamily (P := P) hsplit x = ∅ := by
  ext ω
  constructor
  · intro h
    have hω := (mem_dyadicCutFamily_iff (P := P) hsplit).1 h 0 0 (by norm_num) (by simpa using hx)
    simpa [dyadicLevel, dyadicLevelZero]
      using hω
  · intro h
    cases h

theorem dyadicCutFamily_of_one_le (hsplit : HasFullEventSplitting P) {x : ℝ} (hx : 1 ≤ x) :
    dyadicCutFamily (P := P) hsplit x = Set.univ := by
  ext ω
  constructor
  · intro _h
    simp
  · intro _hω
    rw [mem_dyadicCutFamily_iff (P := P) hsplit]
    intro n k hk hxk
    have hqle : (k : ℝ) / (2 ^ n : ℝ) ≤ 1 := by
      have hpow : (0 : ℝ) < 2 ^ n := by positivity
      have hk' : (k : ℝ) ≤ 2 ^ n := by exact_mod_cast hk
      exact (div_le_iff₀ hpow).2 (by simpa using hk')
    exfalso
    nlinarith

theorem measurableSet_dyadicCutFamily (hsplit : HasFullEventSplitting P) (x : ℝ) :
    MeasurableSet (dyadicCutFamily (P := P) hsplit x) := by
  refine MeasurableSet.iInter ?_
  intro n
  refine MeasurableSet.iInter ?_
  intro k
  by_cases hk : k ≤ 2 ^ n
  · by_cases hxk : x < (k : ℝ) / (2 ^ n : ℝ)
    · simp [dyadicCutFamily, hk, hxk, (dyadicLevel (P := P) hsplit n).measurable_cut]
    · simp [dyadicCutFamily, hk, hxk]
  · simp [dyadicCutFamily, hk]

theorem measure_dyadicCutFamily_of_mem_Ico (hsplit : HasFullEventSplitting P) {x : ℝ}
    (hx0 : 0 ≤ x) (hx1 : x < 1) :
    P (dyadicCutFamily (P := P) hsplit x) = ENNReal.ofReal x := by
  have hEqSet : dyadicCutFamily (P := P) hsplit x = ⋂ n : ℕ, dyadicUpperCut (P := P) hsplit x n :=
    dyadicCutFamily_eq_iInter_upper (P := P) hsplit hx0 hx1
  rw [hEqSet]
  have hmeas : ∀ n : ℕ, NullMeasurableSet (dyadicUpperCut (P := P) hsplit x n) P := by
    intro n
    exact ((dyadicLevel (P := P) hsplit n).measurable_cut _).nullMeasurableSet
  have hmeasT :
      Filter.Tendsto (fun n : ℕ => P (dyadicUpperCut (P := P) hsplit x n)) Filter.atTop
        (nhds (P (⋂ n : ℕ, dyadicUpperCut (P := P) hsplit x n))) :=
    tendsto_measure_iInter_atTop hmeas (dyadicUpperCut_antitone (P := P) hsplit hx0 hx1)
      ⟨0, measure_ne_top P _⟩
  have hμeq : ∀ n : ℕ, P (dyadicUpperCut (P := P) hsplit x n) = ENNReal.ofReal (dyadicUpperApprox x n) := by
    intro n
    exact measure_dyadicUpperCut (P := P) hsplit hx0 hx1
  have hμof : Filter.Tendsto (fun n : ℕ => ENNReal.ofReal (dyadicUpperApprox x n)) Filter.atTop
      (nhds (ENNReal.ofReal x)) := by
    exact ENNReal.continuous_ofReal.continuousAt.tendsto.comp (tendsto_dyadicUpperApprox (x := x) hx0)
  have hμt :
      Filter.Tendsto (fun n : ℕ => P (dyadicUpperCut (P := P) hsplit x n)) Filter.atTop
        (nhds (ENNReal.ofReal x)) := by
    simpa [hμeq] using hμof
  exact tendsto_nhds_unique hmeasT hμt

theorem uniformMeasure_Iic_of_lt_zero {x : ℝ} (hx : x < 0) :
    uniformMeasure (Set.Iic x) = 0 := by
  rw [uniformMeasure, Measure.restrict_apply measurableSet_Iic]
  have hset : Set.Iic x ∩ Set.Icc 0 1 = (∅ : Set ℝ) := by
    ext y
    constructor
    · intro hy
      rcases hy with ⟨hyx, hy0, _hy1⟩
      have hyx' : y ≤ x := by simpa using hyx
      linarith
    · intro hy
      cases hy
  simp [hset]

theorem uniformMeasure_Iic_of_mem_Ico {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    uniformMeasure (Set.Iic x) = ENNReal.ofReal x := by
  rw [uniformMeasure, Measure.restrict_apply measurableSet_Iic]
  have hset : Set.Iic x ∩ Set.Icc 0 1 = Set.Icc 0 x := by
    ext y
    constructor
    · intro hy
      rcases hy with ⟨hyx, hy0, _hy1⟩
      have hyx' : y ≤ x := by simpa using hyx
      exact ⟨hy0, hyx'⟩
    · intro hy
      rcases hy with ⟨hy0, hyx⟩
      exact ⟨by simpa using hyx, hy0, le_trans hyx (le_of_lt hx1)⟩
  simp [hset, Real.volume_Icc]

theorem uniformMeasure_Iic_of_one_le {x : ℝ} (hx : 1 ≤ x) :
    uniformMeasure (Set.Iic x) = 1 := by
  rw [uniformMeasure, Measure.restrict_apply measurableSet_Iic]
  have hset : Set.Iic x ∩ Set.Icc 0 1 = Set.Icc 0 1 := by
    ext y
    constructor
    · intro hy
      rcases hy with ⟨_hyx, hy0, hy1⟩
      exact ⟨hy0, hy1⟩
    · intro hy
      rcases hy with ⟨hy0, hy1⟩
      exact ⟨by simpa using le_trans hy1 hx, hy0, hy1⟩
  simp [hset, Real.volume_Icc]

theorem measure_dyadicCutFamily_eq_uniform_Iic (hsplit : HasFullEventSplitting P) (x : ℝ) :
    P (dyadicCutFamily (P := P) hsplit x) = uniformMeasure (Set.Iic x) := by
  by_cases hx0 : x < 0
  · rw [dyadicCutFamily_of_lt_zero (P := P) hsplit hx0, uniformMeasure_Iic_of_lt_zero hx0]
    simp
  · have hx0' : 0 ≤ x := le_of_not_gt hx0
    by_cases hx1 : x < 1
    · rw [measure_dyadicCutFamily_of_mem_Ico (P := P) hsplit hx0' hx1,
        uniformMeasure_Iic_of_mem_Ico hx0' hx1]
    · have hx1' : 1 ≤ x := le_of_not_gt hx1
      rw [dyadicCutFamily_of_one_le (P := P) hsplit hx1', uniformMeasure_Iic_of_one_le hx1']
      simp

theorem exists_realUniformCoord_of_fullEventSplitting (hsplit : HasFullEventSplitting P) :
    ∃ U : Ω → ℝ, Measurable U ∧ Measure.map U P = uniformMeasure := by
  let F : ℝ → Set Ω := dyadicCutFamily (P := P) hsplit
  have hmeas : ∀ x : ℝ, MeasurableSet (F x) := measurableSet_dyadicCutFamily (P := P) hsplit
  have hmono : Monotone F := monotone_dyadicCutFamily (P := P) hsplit
  have hright : ∀ x : ℝ, F x = ⋂ n : ℕ, F (x + 1 / (n + 1 : ℝ)) :=
    dyadicCutFamily_rightContinuous (P := P) hsplit
  have hnonempty : ∀ ω : Ω, ({x : ℝ | ω ∈ F x} : Set ℝ).Nonempty := by
    intro ω
    refine ⟨1, ?_⟩
    simpa [F, dyadicCutFamily_of_one_le (P := P) hsplit (show (1 : ℝ) ≤ 1 by norm_num)] using
      (show ω ∈ (Set.univ : Set Ω) by simp)
  have hbbd : ∀ ω : Ω, BddBelow ({x : ℝ | ω ∈ F x} : Set ℝ) := by
    intro ω
    refine ⟨0, ?_⟩
    intro x hx
    by_contra hxneg
    have hxlt : x < 0 := lt_of_not_ge hxneg
    have hempty : F x = ∅ := dyadicCutFamily_of_lt_zero (P := P) hsplit hxlt
    simpa [F, hempty] using hx
  refine ⟨cutValue F, ?_, ?_⟩
  · exact measurable_cutValue hmeas hmono hright hnonempty hbbd
  · exact map_cutValue_eq_uniformMeasure (P := P) hmeas hmono hright hnonempty hbbd
      (measure_dyadicCutFamily_eq_uniform_Iic (P := P) hsplit)

end Dyadic

end Probability

end RiskMeasure
