/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik
-/
import CollatzEndpointTransport.Linear.FixedTotalFiberSplit

/-!
# Fixed Total Level Bad Mass

One-level endpoint estimate for the fixed-total linear pullback.

The source mass missing a target is bounded by an ordinary-fiber term plus
the literal critical endpoint-information contribution.  This is still a
finite theorem: no asymptotics, probability spaces, or limiting arguments
occur here.
-/

namespace CollatzEndpointTransport

namespace FixedTotal

open Nat Finset

noncomputable section

theorem actualLevelBadMass_eq_sum_bad
    (S : Set ℕ) (M s : ℕ) :
    actualLevelBadMass S M s =
      ∑ y ∈ actualLevelBadEndpointSet S M s,
        actualLevelFiberCard M s y := by
  classical
  simp [actualLevelBadMass, actualLevelBadEndpointSet,
    Finset.sum_filter]

/-- The raw one-level heavy/ordinary decomposition. -/
theorem actualLevelBadMass_cast_le_raw
    (S : Set ℕ) (M s : ℕ) (E : ℝ)
    (hE : 0 < E) (hs : s ≤ M) :
    (actualLevelBadMass S M s : ℝ) ≤
      E ^ 2 *
          ((sourceOddLevel M s).card : ℝ) /
          (3 : ℝ) ^ (s + 1) *
          (actualLevelBadEndpointSet S M s).card +
        E⁻¹ * Real.sqrt
            ((3 : ℝ) ^ (s + 1) /
              (sourceOddLevel M s).card) *
          (∑ y ∈ actualLevelEndpointSet M s,
            (actualLevelFiberCard M s y : ℝ) *
              Real.sqrt (actualLevelFiberCard M s y)) := by
  classical
  have hNnat : 0 < (sourceOddLevel M s).card := by
    rw [card_sourceOddLevel]
    exact Nat.choose_pos hs
  have hN :
      0 < ((sourceOddLevel M s).card : ℝ) := by
    exact_mod_cast hNnat
  have hR : 0 < (3 : ℝ) ^ (s + 1) := by positivity
  rw [actualLevelBadMass_eq_sum_bad]
  push_cast
  calc
    (∑ y ∈ actualLevelBadEndpointSet S M s,
        (actualLevelFiberCard M s y : ℝ)) ≤
      ∑ y ∈ actualLevelBadEndpointSet S M s,
        (E ^ 2 *
            ((sourceOddLevel M s).card : ℝ) /
            (3 : ℝ) ^ (s + 1) +
          E⁻¹ * Real.sqrt
              ((3 : ℝ) ^ (s + 1) /
                (sourceOddLevel M s).card) *
            (actualLevelFiberCard M s y : ℝ) *
              Real.sqrt (actualLevelFiberCard M s y)) := by
        apply Finset.sum_le_sum
        intro y hy
        exact fiber_le_ordinary_add_critical hE hN hR (by positivity)
    _ =
      E ^ 2 *
          ((sourceOddLevel M s).card : ℝ) /
          (3 : ℝ) ^ (s + 1) *
          (actualLevelBadEndpointSet S M s).card +
        E⁻¹ * Real.sqrt
            ((3 : ℝ) ^ (s + 1) /
              (sourceOddLevel M s).card) *
          (∑ y ∈ actualLevelBadEndpointSet S M s,
            (actualLevelFiberCard M s y : ℝ) *
              Real.sqrt (actualLevelFiberCard M s y)) := by
        rw [Finset.sum_add_distrib]
        congr 1
        · simp only [Finset.sum_const, nsmul_eq_mul]
          ring
        · rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro y hy
          ring
    _ ≤
      E ^ 2 *
          ((sourceOddLevel M s).card : ℝ) /
          (3 : ℝ) ^ (s + 1) *
          (actualLevelBadEndpointSet S M s).card +
        E⁻¹ * Real.sqrt
            ((3 : ℝ) ^ (s + 1) /
              (sourceOddLevel M s).card) *
          (∑ y ∈ actualLevelEndpointSet M s,
            (actualLevelFiberCard M s y : ℝ) *
              Real.sqrt (actualLevelFiberCard M s y)) := by
        gcongr
        intro y hy
        rw [actualLevelBadEndpointSet, Finset.mem_filter] at hy
        exact hy.1

end

end FixedTotal

end CollatzEndpointTransport
