/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik
-/
import CollatzEndpointTransport.Linear.FixedTotalLevelBadMass
import CollatzEndpointTransport.Linear.OptimizedLinearPullbackConstants

/-!
# Fixed Total Nonlinear Shell

The exact nonlinear shell pullback produced by the fixed-total endpoint
moment.

For a `(C,D)`-dense target, the ordinary fibers contribute the exact
binomial factor `((1 + exp (-D log 3))/2)^M`.  The heavy fibers contribute
the literal critical endpoint information.  No asymptotic absorption is
performed in this file.
-/

namespace CollatzEndpointTransport

namespace FixedTotal

open Nat Finset

noncomputable section

theorem three_pow_rpow_one_sub_div
    (D : ℝ) (n : ℕ) :
    ((3 : ℝ) ^ n) ^ (1 - D) / (3 : ℝ) ^ n =
      (Real.exp (-D * Real.log 3)) ^ n := by
  have h3 : (0 : ℝ) < 3 := by norm_num
  have hpow : 0 < (3 : ℝ) ^ n := pow_pos h3 _
  have hpowexp :
      (3 : ℝ) ^ n =
        Real.exp ((n : ℝ) * Real.log 3) := by
    calc
      (3 : ℝ) ^ n =
          (Real.exp (Real.log 3)) ^ n := by
            rw [Real.exp_log h3]
      _ = Real.exp ((n : ℝ) * Real.log 3) := by
            rw [← Real.exp_nat_mul]
  rw [hpowexp]
  rw [Real.rpow_def_of_pos (Real.exp_pos _)]
  rw [Real.log_exp]
  rw [← Real.exp_sub]
  rw [← Real.exp_nat_mul]
  congr 1
  push_cast
  ring

theorem levelCriticalFactor_eq
    (M s : ℕ) (hs : s ≤ M) :
    Real.sqrt
          ((3 : ℝ) ^ (s + 1) /
            (sourceOddLevel M s).card) *
        (∑ y ∈ actualLevelEndpointSet M s,
          (actualLevelFiberCard M s y : ℝ) *
            Real.sqrt (actualLevelFiberCard M s y)) =
      Real.sqrt 3 * actualLevelCriticalContribution M s := by
  have hNnat : 0 < (sourceOddLevel M s).card := by
    rw [card_sourceOddLevel]
    exact Nat.choose_pos hs
  have hN :
      0 < ((sourceOddLevel M s).card : ℝ) := by
    exact_mod_cast hNnat
  have h3s : 0 ≤ (3 : ℝ) ^ s := by positivity
  unfold actualLevelCriticalContribution
  rw [Real.sqrt_div (by positivity)]
  rw [pow_succ]
  rw [Real.sqrt_mul h3s]
  field_simp [ne_of_gt (Real.sqrt_pos.2 hN)]
  ring

/-- One odd-count level after inserting the `(C,D)` target bound. -/
theorem actualLevelBadMass_cast_le
    {S : Set ℕ} {C D : ℝ}
    (hS : QuantitativeDensity.IsCDDense S C D)
    (M s : ℕ) (E : ℝ)
    (hE : 0 < E) (hs : s ≤ M) :
    (actualLevelBadMass S M s : ℝ) ≤
      C * E ^ 2 * (sourceOddLevel M s).card *
          (Real.exp (-D * Real.log 3)) ^ (s + 1) +
        E⁻¹ * Real.sqrt 3 *
          actualLevelCriticalContribution M s := by
  have hraw :=
    actualLevelBadMass_cast_le_raw S M s E hE hs
  have hcard :=
    card_actualLevelBadEndpointSet_le hS M s
  calc
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
              Real.sqrt (actualLevelFiberCard M s y)) := hraw
    _ ≤
      E ^ 2 *
          ((sourceOddLevel M s).card : ℝ) /
          (3 : ℝ) ^ (s + 1) *
          (C * ((3 : ℝ) ^ (s + 1)) ^ (1 - D)) +
        E⁻¹ * Real.sqrt
            ((3 : ℝ) ^ (s + 1) /
              (sourceOddLevel M s).card) *
          (∑ y ∈ actualLevelEndpointSet M s,
            (actualLevelFiberCard M s y : ℝ) *
              Real.sqrt (actualLevelFiberCard M s y)) := by
        gcongr
    _ =
      C * E ^ 2 * (sourceOddLevel M s).card *
          (Real.exp (-D * Real.log 3)) ^ (s + 1) +
        E⁻¹ * Real.sqrt 3 *
          actualLevelCriticalContribution M s := by
        rw [show
          E⁻¹ * Real.sqrt
                ((3 : ℝ) ^ (s + 1) /
                  (sourceOddLevel M s).card) *
              (∑ y ∈ actualLevelEndpointSet M s,
                (actualLevelFiberCard M s y : ℝ) *
                  Real.sqrt (actualLevelFiberCard M s y)) =
            E⁻¹ *
              (Real.sqrt
                  ((3 : ℝ) ^ (s + 1) /
                    (sourceOddLevel M s).card) *
                (∑ y ∈ actualLevelEndpointSet M s,
                  (actualLevelFiberCard M s y : ℝ) *
                    Real.sqrt (actualLevelFiberCard M s y))) by ring]
        rw [levelCriticalFactor_eq M s hs]
        rw [show
          E ^ 2 * ((sourceOddLevel M s).card : ℝ) /
                (3 : ℝ) ^ (s + 1) *
                (C * ((3 : ℝ) ^ (s + 1)) ^ (1 - D)) =
            C * E ^ 2 * (sourceOddLevel M s).card *
              (((3 : ℝ) ^ (s + 1)) ^ (1 - D) /
                (3 : ℝ) ^ (s + 1)) by ring]
        rw [three_pow_rpow_one_sub_div]
        ring

/-- Exact finite-shell nonlinear pullback before estimating the critical
information term. -/
theorem sourceEndpointBad_div_pow_le
    {S : Set ℕ} {C D : ℝ}
    (hS : QuantitativeDensity.IsCDDense S C D)
    (M : ℕ) (hM : 1 ≤ M) (E : ℝ) (hE : 0 < E) :
    ((sourceEndpointBad S M).card : ℝ) / (2 ^ M : ℝ) ≤
      C * E ^ 2 * Real.exp (-D * Real.log 3) *
          ((1 + Real.exp (-D * Real.log 3)) / 2) ^ M +
        E⁻¹ * actualCriticalEndpointInformation M := by
  classical
  rw [card_sourceEndpointBad_eq_sum_levelBadMass]
  push_cast
  have hlevels :
      (∑ s ∈ Finset.range (M + 1),
          (actualLevelBadMass S M s : ℝ)) ≤
        ∑ s ∈ Finset.range (M + 1),
          (C * E ^ 2 * (sourceOddLevel M s).card *
              (Real.exp (-D * Real.log 3)) ^ (s + 1) +
            E⁻¹ * Real.sqrt 3 *
              actualLevelCriticalContribution M s) := by
    apply Finset.sum_le_sum
    intro s hs
    exact actualLevelBadMass_cast_le hS M s E hE
      (Nat.le_of_lt_succ (Finset.mem_range.mp hs))
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 ^ M)).2
  calc
    (∑ s ∈ Finset.range (M + 1),
        (actualLevelBadMass S M s : ℝ)) ≤
      ∑ s ∈ Finset.range (M + 1),
        (C * E ^ 2 * (sourceOddLevel M s).card *
            (Real.exp (-D * Real.log 3)) ^ (s + 1) +
          E⁻¹ * Real.sqrt 3 *
            actualLevelCriticalContribution M s) := hlevels
    _ =
      C * E ^ 2 * Real.exp (-D * Real.log 3) *
          (1 + Real.exp (-D * Real.log 3)) ^ M +
        E⁻¹ * Real.sqrt 3 *
          (∑ s ∈ Finset.range (M + 1),
            actualLevelCriticalContribution M s) := by
        rw [Finset.sum_add_distrib]
        congr 1
        · have hchoose :
              (∑ s ∈ Finset.range (M + 1),
                (M.choose s : ℝ) *
                  (Real.exp (-D * Real.log 3)) ^ s) =
                (1 + Real.exp (-D * Real.log 3)) ^ M := by
            calc
              (∑ s ∈ Finset.range (M + 1),
                (M.choose s : ℝ) *
                  (Real.exp (-D * Real.log 3)) ^ s) =
                  (Real.exp (-D * Real.log 3) + 1) ^ M := by
                    rw [add_pow]
                    apply Finset.sum_congr rfl
                    intro s hs
                    simp [mul_assoc, mul_left_comm, mul_comm]
              _ = (1 + Real.exp (-D * Real.log 3)) ^ M := by ring
          simp_rw [card_sourceOddLevel]
          rw [show
            (∑ s ∈ Finset.range (M + 1),
              C * E ^ 2 * (M.choose s : ℝ) *
                (Real.exp (-D * Real.log 3)) ^ (s + 1)) =
              C * E ^ 2 * Real.exp (-D * Real.log 3) *
                (∑ s ∈ Finset.range (M + 1),
                  (M.choose s : ℝ) *
                    (Real.exp (-D * Real.log 3)) ^ s) by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro s hs
              ring]
          rw [hchoose]
        · rw [Finset.mul_sum]
    _ =
      (C * E ^ 2 * Real.exp (-D * Real.log 3) *
          ((1 + Real.exp (-D * Real.log 3)) / 2) ^ M +
        E⁻¹ * actualCriticalEndpointInformation M) *
          (2 ^ M : ℝ) := by
        unfold actualCriticalEndpointInformation
        rw [div_pow]
        field_simp
        ring

theorem oddCountRate_pow_eq_exp
    (D : ℝ) (M : ℕ) :
    ((1 + Real.exp (-D * Real.log 3)) / 2) ^ M =
      Real.exp (-OptimizedLinearPullback.psi D * M) := by
  have hinner :=
    OptimizedLinearPullback.psi_inner_pos D
  calc
    ((1 + Real.exp (-D * Real.log 3)) / 2) ^ M =
        (Real.exp
          (Real.log ((1 + Real.exp (-D * Real.log 3)) / 2))) ^ M := by
      rw [Real.exp_log hinner]
    _ = Real.exp
        ((M : ℝ) *
          Real.log ((1 + Real.exp (-D * Real.log 3)) / 2)) := by
      rw [← Real.exp_nat_mul]
    _ = Real.exp (-OptimizedLinearPullback.psi D * M) := by
      congr 1
      unfold OptimizedLinearPullback.psi
      push_cast
      ring

/-- The exact nonlinear shell estimate after the optimal balanced
heavy-fiber threshold `E = exp (psi(D) M / 3)`. -/
theorem sourceEndpointBad_div_pow_le_nonlinear
    {S : Set ℕ} {C D : ℝ}
    (hS : QuantitativeDensity.IsCDDense S C D)
    (M : ℕ) (hM : 1 ≤ M) :
    ((sourceEndpointBad S M).card : ℝ) / (2 ^ M : ℝ) ≤
      (C * Real.exp (-D * Real.log 3) +
          9 * Real.sqrt 3 * (M : ℝ) * Real.sqrt M) *
        Real.exp
          (-(OptimizedLinearPullback.psi D / 3) * M) := by
  let w := OptimizedLinearPullback.psi D / 3
  let E := Real.exp (w * M)
  have hE : 0 < E := Real.exp_pos _
  have hbase :=
    sourceEndpointBad_div_pow_le hS M hM E hE
  have hinfo :=
    actualCriticalEndpointInformation_le M hM
  calc
    ((sourceEndpointBad S M).card : ℝ) / (2 ^ M : ℝ) ≤
      C * E ^ 2 * Real.exp (-D * Real.log 3) *
          ((1 + Real.exp (-D * Real.log 3)) / 2) ^ M +
        E⁻¹ * actualCriticalEndpointInformation M := hbase
    _ ≤
      C * E ^ 2 * Real.exp (-D * Real.log 3) *
          ((1 + Real.exp (-D * Real.log 3)) / 2) ^ M +
        E⁻¹ *
          (9 * Real.sqrt 3 * (M : ℝ) * Real.sqrt M) := by
      gcongr
    _ =
      (C * Real.exp (-D * Real.log 3) +
          9 * Real.sqrt 3 * (M : ℝ) * Real.sqrt M) *
        Real.exp (-w * M) := by
      rw [oddCountRate_pow_eq_exp]
      unfold E w
      have hcombine :
          Real.exp
                (OptimizedLinearPullback.psi D / 3 * (M : ℝ)) ^ 2 *
              Real.exp
                (-OptimizedLinearPullback.psi D * (M : ℝ)) =
            Real.exp
              (-(OptimizedLinearPullback.psi D / 3 * (M : ℝ))) := by
        rw [pow_two, ← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
      rw [show
        C * Real.exp
              (OptimizedLinearPullback.psi D / 3 * (M : ℝ)) ^ 2 *
            Real.exp (-D * Real.log 3) *
            Real.exp (-OptimizedLinearPullback.psi D * (M : ℝ)) =
          C * Real.exp (-D * Real.log 3) *
            (Real.exp
                (OptimizedLinearPullback.psi D / 3 * (M : ℝ)) ^ 2 *
              Real.exp
                (-OptimizedLinearPullback.psi D * (M : ℝ))) by ring]
      rw [hcombine]
      rw [← Real.exp_neg]
      ring
    _ =
      (C * Real.exp (-D * Real.log 3) +
          9 * Real.sqrt 3 * (M : ℝ) * Real.sqrt M) *
        Real.exp
          (-(OptimizedLinearPullback.psi D / 3) * M) := rfl

end

end FixedTotal

end CollatzEndpointTransport
