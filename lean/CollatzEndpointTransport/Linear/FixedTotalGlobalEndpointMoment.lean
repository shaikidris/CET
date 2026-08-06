/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik
-/
import CollatzEndpointTransport.Linear.FiniteFiberMixture

/-!
# Fixed Total Global Endpoint Moment

Global critical endpoint-information bound.

The fixed-total cohorts are mixed over the first odd position.  We use the
finite `3/2` mixture inequality from `FiniteFiberMixture`, incurring a
conservative factor `sqrt M`.  This changes only a polynomial prefactor;
the later nonlinear pullback still has a density exponent linear in `D`.
-/

set_option maxHeartbeats 2000000

namespace CollatzEndpointTransport

namespace FixedTotal

open Nat Finset

noncomputable section

local instance globalCompositionDecidableEq (N : ℕ) :
    DecidableEq (Composition N) :=
  Classical.decEq _

/-- Fixed-length cohort at first-odd position `u`. -/
def levelCohortSet (M s : ℕ) (u : Fin M) :
    Finset (Composition (M - (u : ℕ))) :=
  fixedSet (M - (u : ℕ)) s

/-- Total number of non-all-even sources at odd-count level `s`. -/
def levelSourceCard (M s : ℕ) : ℕ :=
  ∑ u : Fin M, (levelCohortSet M s u).card

/-- Endpoint values reached by odd-count level `s`. -/
def levelEndpointSet (M s : ℕ) : Finset ℕ :=
  mixedTargetSet (Finset.univ : Finset (Fin M))
    (levelCohortSet M s) (fun u => cohortEndpoint u)

/-- Endpoint fiber cardinality after mixing first-odd positions. -/
def levelEndpointFiberCard (M s : ℕ) (y : ℕ) : ℕ :=
  mixedFiberCard (Finset.univ : Finset (Fin M))
    (levelCohortSet M s) (fun u => cohortEndpoint u) y

/-- Unnormalised critical endpoint moment at odd-count level `s`. -/
def levelCriticalNumerator (M s : ℕ) : ℝ :=
  Real.sqrt (3 ^ s) *
    ∑ y ∈ levelEndpointSet M s,
      (levelEndpointFiberCard M s y : ℝ) *
        Real.sqrt (levelEndpointFiberCard M s y)

/-- Critical level moment divided by the square root of its source count. -/
def levelCriticalContribution (M s : ℕ) : ℝ :=
  levelCriticalNumerator M s / Real.sqrt (levelSourceCard M s)

theorem levelCriticalNumerator_le
    (M s : ℕ) :
    levelCriticalNumerator M s ≤
      Real.sqrt M *
        ∑ u : Fin M, cohortCriticalNumerator M u s := by
  have hmix :=
    mixedFiberCritical_le
      (U := (Finset.univ : Finset (Fin M)))
      (W := levelCohortSet M s)
      (f := fun u => cohortEndpoint u)
  have hsqrt : 0 ≤ Real.sqrt (3 ^ s) := Real.sqrt_nonneg _
  have hscaled := mul_le_mul_of_nonneg_left hmix hsqrt
  simpa [levelCriticalNumerator, levelEndpointSet,
    levelEndpointFiberCard, levelCohortSet, cohortCriticalNumerator,
    Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm] using hscaled

theorem fixedCriticalNumerator_eq_zero_of_card_eq_zero
    {N s : ℕ} (hzero : (fixedSet N s).card = 0) :
    fixedCriticalNumerator N s = 0 := by
  have hset : fixedSet N s = ∅ := Finset.card_eq_zero.mp hzero
  simp [fixedCriticalNumerator, fixedFiberCard, residueFiber, hset]

theorem fixedCriticalNumerator_nonneg
    (N s : ℕ) :
    0 ≤ fixedCriticalNumerator N s := by
  apply mul_nonneg (Real.sqrt_nonneg _)
  exact Finset.sum_nonneg fun a ha =>
    mul_nonneg (by positivity) (Real.sqrt_nonneg _)

theorem fixedCriticalNumerator_div_level_le
    (M s : ℕ) (u : Fin M)
    (hlevel : 0 < levelSourceCard M s) :
    fixedCriticalNumerator (M - (u : ℕ)) s /
        Real.sqrt (levelSourceCard M s) ≤
      fixedCriticalContribution (M - (u : ℕ)) s := by
  let W := fixedSet (M - (u : ℕ)) s
  have hWle : W.card ≤ levelSourceCard M s := by
    exact Finset.single_le_sum
      (fun i _ => Nat.zero_le (levelCohortSet M s i).card)
      (Finset.mem_univ u)
  by_cases hWzero : W.card = 0
  · have hnum :
        fixedCriticalNumerator (M - (u : ℕ)) s = 0 :=
      fixedCriticalNumerator_eq_zero_of_card_eq_zero hWzero
    simp [hnum, fixedCriticalContribution]
  · have hsqrtW : 0 < Real.sqrt W.card := by
      apply Real.sqrt_pos.mpr
      exact_mod_cast Nat.pos_of_ne_zero hWzero
    have hsqrtLevel : 0 < Real.sqrt (levelSourceCard M s) := by
      exact Real.sqrt_pos.mpr (by exact_mod_cast hlevel)
    have hsqrtLe :
        Real.sqrt W.card ≤ Real.sqrt (levelSourceCard M s) := by
      exact Real.sqrt_le_sqrt (by exact_mod_cast hWle)
    unfold fixedCriticalContribution
    exact div_le_div_of_nonneg_left
      (fixedCriticalNumerator_nonneg _ _)
      hsqrtW hsqrtLe

theorem levelCriticalContribution_le
    (M s : ℕ) :
    levelCriticalContribution M s ≤
      Real.sqrt M *
        ∑ u : Fin M,
          fixedCriticalContribution (M - (u : ℕ)) s := by
  by_cases hlevel : levelSourceCard M s = 0
  · have hall :
        ∀ u : Fin M, (levelCohortSet M s u).card = 0 := by
      intro u
      have hle :
          (levelCohortSet M s u).card ≤ levelSourceCard M s :=
        Finset.single_le_sum
          (fun i _ => Nat.zero_le (levelCohortSet M s i).card)
          (Finset.mem_univ u)
      omega
    have htarget : levelEndpointSet M s = ∅ := by
      apply Finset.eq_empty_iff_forall_not_mem.mpr
      intro y hy
      rcases Finset.mem_biUnion.mp hy with ⟨u, hu, hyu⟩
      have hset :
          levelCohortSet M s u = ∅ :=
        Finset.card_eq_zero.mp (hall u)
      simp [hset] at hyu
    simp [levelCriticalContribution, levelCriticalNumerator,
      levelEndpointSet, htarget, hlevel]
    unfold fixedCriticalContribution fixedCriticalNumerator
    positivity
  · have hlevelPos : 0 < levelSourceCard M s :=
      Nat.pos_of_ne_zero hlevel
    have hsqrtLevel :
        0 < Real.sqrt (levelSourceCard M s) := by
      exact Real.sqrt_pos.mpr (by exact_mod_cast hlevelPos)
    calc
      levelCriticalContribution M s =
          levelCriticalNumerator M s /
            Real.sqrt (levelSourceCard M s) := rfl
      _ ≤ (Real.sqrt M *
            ∑ u : Fin M, cohortCriticalNumerator M u s) /
            Real.sqrt (levelSourceCard M s) := by
        exact div_le_div_of_nonneg_right
          (levelCriticalNumerator_le M s)
          (Real.sqrt_nonneg _)
      _ ≤ (Real.sqrt M *
            ∑ u : Fin M,
              fixedCriticalNumerator (M - (u : ℕ)) s) /
            Real.sqrt (levelSourceCard M s) := by
        gcongr
        exact cohortCriticalNumerator_le M _ s
      _ = Real.sqrt M *
            ∑ u : Fin M,
              (fixedCriticalNumerator (M - (u : ℕ)) s /
                Real.sqrt (levelSourceCard M s)) := by
        simp only [div_eq_mul_inv]
        calc
          Real.sqrt M *
                (∑ u : Fin M,
                  fixedCriticalNumerator (M - (u : ℕ)) s) *
                (Real.sqrt (levelSourceCard M s))⁻¹ =
              (∑ u : Fin M,
                  Real.sqrt M *
                    fixedCriticalNumerator (M - (u : ℕ)) s) *
                (Real.sqrt (levelSourceCard M s))⁻¹ := by
            rw [Finset.mul_sum]
          _ = ∑ u : Fin M,
                (Real.sqrt M *
                  fixedCriticalNumerator (M - (u : ℕ)) s) *
                    (Real.sqrt (levelSourceCard M s))⁻¹ := by
            rw [Finset.sum_mul]
          _ = Real.sqrt M *
                ∑ u : Fin M,
                  fixedCriticalNumerator (M - (u : ℕ)) s *
                    (Real.sqrt (levelSourceCard M s))⁻¹ := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro u hu
            ring
      _ ≤ Real.sqrt M *
            ∑ u : Fin M,
              fixedCriticalContribution (M - (u : ℕ)) s := by
        gcongr
        exact fixedCriticalNumerator_div_level_le M s _ hlevelPos

theorem fixedCriticalContribution_eq_zero_of_lt_length
    {N s : ℕ} (h : N < s) :
    fixedCriticalContribution N s = 0 := by
  have hset : fixedSet N s = ∅ := by
    apply Finset.eq_empty_iff_forall_not_mem.mpr
    intro c hc
    have hlen : c.length = s := (Finset.mem_filter.mp hc).2
    have hle := c.length_le
    omega
  simp [fixedCriticalContribution, fixedCriticalNumerator,
    fixedFiberCard, residueFiber, hset]

theorem sum_fixedCriticalContribution_le
    (M : ℕ) (u : Fin M) :
    (∑ s ∈ Finset.Icc 1 M,
        fixedCriticalContribution (M - (u : ℕ)) s) ≤
      8 * (M - (u : ℕ)) * (2 ^ (M - (u : ℕ) - 1) : ℝ) := by
  let N := M - (u : ℕ)
  have hN : 0 < N := by dsimp [N]; omega
  have hNM : N ≤ M := by dsimp [N]; omega
  have hsubset : Finset.Icc 1 N ⊆ Finset.Icc 1 M := by
    intro s hs
    exact Finset.mem_Icc.mpr
      ⟨(Finset.mem_Icc.mp hs).1,
        (Finset.mem_Icc.mp hs).2.trans hNM⟩
  have hsumEq :
      (∑ s ∈ Finset.Icc 1 M,
          fixedCriticalContribution N s) =
        ∑ s ∈ Finset.Icc 1 N,
          fixedCriticalContribution N s := by
    symm
    apply Finset.sum_subset hsubset
    intro s hsM hsNot
    have hsN : N < s := by
      have hsOne : 1 ≤ s := (Finset.mem_Icc.mp hsM).1
      by_contra hnot
      have hsLe : s ≤ N := Nat.le_of_not_gt hnot
      exact hsNot (Finset.mem_Icc.mpr ⟨hsOne, hsLe⟩)
    exact fixedCriticalContribution_eq_zero_of_lt_length hsN
  have hden : (0 : ℝ) < 2 ^ (N - 1) := by positivity
  have havg := fixedCriticalAverage_le N hN
  have hsumBound :
      (∑ s ∈ Finset.Icc 1 N,
          fixedCriticalContribution N s) ≤
        8 * N * (2 ^ (N - 1) : ℝ) := by
    apply (div_le_iff₀ hden).mp
    simpa [fixedCriticalAverage, mul_assoc] using havg
  simpa [N, hsumEq] using hsumBound

/-- Critical endpoint information, expressed exactly through the finite
source coding.  The leading `1` is the all-even word. -/
def criticalEndpointInformation (M : ℕ) : ℝ :=
  Real.sqrt 3 / (2 ^ M : ℝ) *
    (1 + ∑ s ∈ Finset.Icc 1 M, levelCriticalContribution M s)

theorem sum_levelCriticalContribution_le
    (M : ℕ) :
    (∑ s ∈ Finset.Icc 1 M, levelCriticalContribution M s) ≤
      Real.sqrt M * (8 * M * (2 ^ M : ℝ)) := by
  calc
    (∑ s ∈ Finset.Icc 1 M, levelCriticalContribution M s) ≤
        ∑ s ∈ Finset.Icc 1 M,
          Real.sqrt M *
            ∑ u : Fin M,
              fixedCriticalContribution (M - (u : ℕ)) s := by
      exact Finset.sum_le_sum fun s hs =>
        levelCriticalContribution_le M s
    _ = Real.sqrt M *
        ∑ u : Fin M, ∑ s ∈ Finset.Icc 1 M,
          fixedCriticalContribution (M - (u : ℕ)) s := by
      rw [← Finset.mul_sum, Finset.sum_comm]
    _ ≤ Real.sqrt M *
        ∑ u : Fin M,
          (8 * (M - (u : ℕ)) *
            (2 ^ (M - (u : ℕ) - 1) : ℝ)) := by
      gcongr
      exact sum_fixedCriticalContribution_le M _
    _ ≤ Real.sqrt M * (8 * M * (2 ^ M : ℝ)) := by
      gcongr
      calc
        (∑ u : Fin M,
            ((8 : ℝ) * (M - (u : ℕ)) *
              (2 ^ (M - (u : ℕ) - 1) : ℝ))) ≤
            ∑ u : Fin M,
              ((8 : ℝ) * M *
                (2 ^ (M - (u : ℕ) - 1) : ℝ)) := by
          apply Finset.sum_le_sum
          intro u hu
          have huNonneg : (0 : ℝ) ≤ (u : ℕ) := by positivity
          have hfactor :
              (0 : ℝ) ≤ 2 ^ (M - (u : ℕ) - 1) := by positivity
          nlinarith
        _ = (8 : ℝ) * M *
            (∑ u : Fin M,
              (2 ^ (M - (u : ℕ) - 1) : ℝ)) := by
          rw [Finset.mul_sum]
        _ ≤ (8 : ℝ) * M * (2 ^ M : ℝ) := by
          gcongr
          have hgeom := one_add_reverse_pow_sum M
          exact_mod_cast (by omega :
            (∑ u : Fin M, 2 ^ (M - (u : ℕ) - 1)) ≤ 2 ^ M)

/-- **Global critical endpoint-information theorem.**

The `M^(3/2)` polynomial is a conservative formal mixture loss.  It is
sufficient for the optimized nonlinear pullback because the exponential
rate remains unchanged. -/
theorem criticalEndpointInformation_le
    (M : ℕ) (hM : 1 ≤ M) :
    criticalEndpointInformation M ≤
      9 * Real.sqrt 3 * (M : ℝ) * Real.sqrt M := by
  have hpow : (0 : ℝ) < 2 ^ M := by positivity
  have hsum := sum_levelCriticalContribution_le M
  have hMreal : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hsqrtM : 1 ≤ Real.sqrt M := by
    simpa using Real.sqrt_le_sqrt hMreal
  have hpowOne : (1 : ℝ) ≤ 2 ^ M := by
    exact one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
  have hdivOne : (1 : ℝ) / 2 ^ M ≤ 1 :=
    (div_le_one hpow).2 hpowOne
  have honeLe : (1 : ℝ) / 2 ^ M ≤ (M : ℝ) * Real.sqrt M := by
    exact hdivOne.trans <|
      one_le_mul_of_one_le_of_one_le hMreal hsqrtM
  unfold criticalEndpointInformation
  calc
    Real.sqrt 3 / (2 ^ M : ℝ) *
        (1 + ∑ s ∈ Finset.Icc 1 M,
          levelCriticalContribution M s) ≤
      Real.sqrt 3 / (2 ^ M : ℝ) *
        (1 + Real.sqrt M * (8 * M * (2 ^ M : ℝ))) := by
      gcongr
    _ ≤ 9 * Real.sqrt 3 * (M : ℝ) * Real.sqrt M := by
      have hsqrt3 : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg _
      calc
        Real.sqrt 3 / (2 ^ M : ℝ) *
            (1 + Real.sqrt M * (8 * M * (2 ^ M : ℝ))) =
          Real.sqrt 3 * ((1 : ℝ) / 2 ^ M) +
            8 * Real.sqrt 3 * M * Real.sqrt M := by
          field_simp
          ring
        _ ≤ Real.sqrt 3 * (M * Real.sqrt M) +
            8 * Real.sqrt 3 * M * Real.sqrt M := by
          gcongr
        _ = 9 * Real.sqrt 3 * M * Real.sqrt M := by ring

end

end FixedTotal

end CollatzEndpointTransport
