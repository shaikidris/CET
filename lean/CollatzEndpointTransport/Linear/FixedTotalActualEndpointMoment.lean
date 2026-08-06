/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik
-/
import CollatzEndpointTransport.Linear.FixedTotalOddCountMGF

/-!
# Fixed Total Actual Endpoint Moment

The critical endpoint-information theorem in actual shell coordinates.

`FixedTotalGlobalEndpointMoment` proves the estimate after decomposing a
non-all-even source by its first odd position.  This file identifies that
finite mixture with the literal fibers of `sourceEndpoint` on
`SourceCode M`, including the all-even level.
-/

namespace CollatzEndpointTransport

namespace FixedTotal

open Nat Finset

noncomputable section

/-- Actual endpoint values at odd-count level `s`. -/
def actualLevelEndpointSet (M s : ℕ) : Finset ℕ :=
  (sourceOddLevel M s).image sourceEndpoint

/-- Actual endpoint-fiber cardinality at odd-count level `s`. -/
def actualLevelFiberCard (M s y : ℕ) : ℕ :=
  (mapFiber (sourceOddLevel M s) sourceEndpoint y).card

/-- Critical actual-shell contribution at one odd-count level. -/
def actualLevelCriticalContribution (M s : ℕ) : ℝ :=
  Real.sqrt (3 ^ s) *
      (∑ y ∈ actualLevelEndpointSet M s,
        (actualLevelFiberCard M s y : ℝ) *
          Real.sqrt (actualLevelFiberCard M s y)) /
    Real.sqrt (sourceOddLevel M s).card

/-- Literal critical endpoint information of the dyadic shell. -/
def actualCriticalEndpointInformation (M : ℕ) : ℝ :=
  Real.sqrt 3 / (2 ^ M : ℝ) *
    ∑ s ∈ Finset.range (M + 1),
      actualLevelCriticalContribution M s

theorem actualLevelFiberCard_eq_levelEndpointFiberCard
    {M s y : ℕ} (hs : 0 < s) :
    actualLevelFiberCard M s y =
      levelEndpointFiberCard M s y := by
  classical
  simp only [actualLevelFiberCard, mapFiber, sourceOddLevel,
    levelEndpointFiberCard, mixedFiberCard, levelCohortSet,
    cohortEndpoint, SourceCode, sourceCodeOddCount]
  rw [Finset.card_filter]
  simp only [Finset.sum_filter]
  rw [Fintype.sum_sum_type]
  simp only [hs.ne'.symm, ↓reduceIte, Finset.sum_const_zero, zero_add]
  rw [← Finset.univ_sigma_univ, Finset.sum_sigma]
  apply Finset.sum_congr rfl
  intro u hu
  rw [Finset.card_filter]
  simp only [fixedSet, Finset.sum_filter]

theorem levelSourceCard_eq_card_sourceOddLevel
    {M s : ℕ} (hs : 0 < s) :
    levelSourceCard M s = (sourceOddLevel M s).card := by
  classical
  simp only [levelSourceCard, levelCohortSet, sourceOddLevel,
    SourceCode, sourceCodeOddCount]
  rw [Finset.card_filter]
  rw [Fintype.sum_sum_type]
  simp only [hs.ne'.symm, ↓reduceIte, Finset.sum_const_zero, zero_add]
  rw [← Finset.univ_sigma_univ, Finset.sum_sigma]
  apply Finset.sum_congr rfl
  intro u hu
  change
    ((Finset.univ : Finset (Composition (M - (u : ℕ)))).filter
      (fun c => c.length = s)).card =
        ∑ c : Composition (M - (u : ℕ)),
          if c.length = s then 1 else 0
  rw [Finset.card_filter]

theorem actualLevelEndpointSet_eq_levelEndpointSet
    {M s : ℕ} (hs : 0 < s) :
    actualLevelEndpointSet M s = levelEndpointSet M s := by
  classical
  ext y
  constructor
  · intro hy
    rw [actualLevelEndpointSet, Finset.mem_image] at hy
    rcases hy with ⟨x, hx, rfl⟩
    have hsx : sourceCodeOddCount x = s :=
      (Finset.mem_filter.mp hx).2
    cases x with
    | inl e =>
        simp [sourceCodeOddCount] at hsx
        omega
    | inr p =>
        rcases p with ⟨u, c⟩
        rw [levelEndpointSet, mixedTargetSet, Finset.mem_biUnion]
        refine ⟨u, Finset.mem_univ _, ?_⟩
        rw [Finset.mem_image]
        refine ⟨c, ?_, rfl⟩
        rw [levelCohortSet, fixedSet, Finset.mem_filter]
        exact ⟨Finset.mem_univ _, by
          simpa [sourceCodeOddCount] using hsx⟩
  · intro hy
    rw [levelEndpointSet, mixedTargetSet, Finset.mem_biUnion] at hy
    rcases hy with ⟨u, hu, hyu⟩
    rw [Finset.mem_image] at hyu
    rcases hyu with ⟨c, hc, rfl⟩
    rw [actualLevelEndpointSet, Finset.mem_image]
    refine
      ⟨(Sum.inr ⟨u, c⟩ : SourceCode M), ?_, rfl⟩
    rw [sourceOddLevel, Finset.mem_filter]
    have hlen :
        c.length = s :=
      (Finset.mem_filter.mp hc).2
    exact ⟨Finset.mem_univ _, by
      simpa [sourceCodeOddCount] using hlen⟩

theorem actualLevelCriticalContribution_eq_level
    {M s : ℕ} (hs : 0 < s) :
    actualLevelCriticalContribution M s =
      levelCriticalContribution M s := by
  rw [actualLevelCriticalContribution, levelCriticalContribution,
    levelCriticalNumerator]
  rw [actualLevelEndpointSet_eq_levelEndpointSet hs]
  simp_rw [actualLevelFiberCard_eq_levelEndpointFiberCard hs]
  rw [← levelSourceCard_eq_card_sourceOddLevel hs]

theorem actualLevelCriticalContribution_zero
    (M : ℕ) :
    actualLevelCriticalContribution M 0 = 1 := by
  classical
  have hcard : (sourceOddLevel M 0).card = 1 := by
    rw [card_sourceOddLevel]
    simp
  obtain ⟨x, hset⟩ := Finset.card_eq_one.mp hcard
  have hendpoint :
      actualLevelEndpointSet M 0 = {sourceEndpoint x} := by
    simp [actualLevelEndpointSet, hset]
  have hfiber :
      actualLevelFiberCard M 0 (sourceEndpoint x) = 1 := by
    rw [actualLevelFiberCard, mapFiber, hset]
    have hfilter :
        ({x} : Finset (SourceCode M)).filter
            (fun z => sourceEndpoint z = sourceEndpoint x) =
          {x} := by
      ext z
      simp only [Finset.mem_filter, Finset.mem_singleton]
      constructor
      · exact fun hz => hz.1
      · intro hz
        subst z
        exact ⟨rfl, rfl⟩
    rw [hfilter]
    simp
  simp [actualLevelCriticalContribution, hendpoint, hfiber, hcard]

/-- The literal shell endpoint information is exactly the decomposed finite
quantity bounded in `FixedTotalGlobalEndpointMoment`. -/
theorem actualCriticalEndpointInformation_eq
    (M : ℕ) :
    actualCriticalEndpointInformation M =
      criticalEndpointInformation M := by
  unfold actualCriticalEndpointInformation criticalEndpointInformation
  congr 1
  rw [Finset.sum_range_succ']
  rw [actualLevelCriticalContribution_zero]
  have hsum :
      (∑ s ∈ Finset.range M,
          actualLevelCriticalContribution M (s + 1)) =
        ∑ s ∈ Finset.Icc 1 M,
          actualLevelCriticalContribution M s := by
    apply Finset.sum_bij
        (fun s hs => s + 1)
    · intro s hs
      rw [Finset.mem_Icc]
      exact ⟨by omega, by
        have := Finset.mem_range.mp hs
        omega⟩
    · intro a₁ ha₁ a₂ ha₂ heq
      omega
    · intro s hs
      have hs' := Finset.mem_Icc.mp hs
      refine ⟨s - 1, Finset.mem_range.mpr (by omega), by omega⟩
    · intro s hs
      rfl
  rw [hsum]
  have hlevels :
      (∑ s ∈ Finset.Icc 1 M,
          actualLevelCriticalContribution M s) =
        ∑ s ∈ Finset.Icc 1 M,
          levelCriticalContribution M s := by
    apply Finset.sum_congr rfl
    intro s hs
    exact actualLevelCriticalContribution_eq_level
      (Finset.mem_Icc.mp hs).1
  rw [hlevels]
  ring

theorem actualCriticalEndpointInformation_le
    (M : ℕ) (hM : 1 ≤ M) :
    actualCriticalEndpointInformation M ≤
      9 * Real.sqrt 3 * (M : ℝ) * Real.sqrt M := by
  rw [actualCriticalEndpointInformation_eq]
  exact criticalEndpointInformation_le M hM

end

end FixedTotal

end CollatzEndpointTransport
