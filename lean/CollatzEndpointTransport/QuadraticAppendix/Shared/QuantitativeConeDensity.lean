/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik
-/
import CollatzEndpointTransport.QuadraticAppendix.Shared.QuantitativeConeRobustness

/-!
# Quantitative Cone Density

Concrete analytic completion of the cone-core estimate used by the
quadratic pullback.

The paper retains the slightly sharper exponent

  D * (1 + eta) - 2 * eta.

For the live choice `eta = D / 4`, it is enough (and formally simpler) to
retain `D - 2 * eta = D / 2`.  The proof below keeps the `N^(1-D)` factor
from density and bounds only the scale contribution by `N^(2*eta)`.
-/

namespace CollatzEndpointTransport

namespace QuantitativeDensity

open scoped Real

noncomputable section

/-- A geometric sum with ratio nine is controlled by its last term. -/
theorem sum_nine_pow_le_three_halves (J : ℕ) :
    (∑ k ∈ Finset.range (J + 1), (9 : ℝ) ^ k) ≤
      (3 / 2 : ℝ) * 9 ^ J := by
  induction J with
  | zero => norm_num
  | succ J ih =>
      rw [Finset.sum_range_succ, pow_succ]
      calc
        (∑ k ∈ Finset.range (J + 1), (9 : ℝ) ^ k) + 9 ^ (J + 1)
            ≤ (3 / 2 : ℝ) * 9 ^ J + 9 ^ (J + 1) :=
          add_le_add_right ih _
        _ ≤ (3 / 2 : ℝ) * 9 ^ (J + 1) := by
          have hp : 0 ≤ (9 : ℝ) ^ J := by positivity
          rw [pow_succ]
          nlinarith

/-- The logarithmic cutoff contributes at most `N^(2*eta)`. -/
theorem nine_pow_floor_eta_natLog_le_rpow
    {eta : ℝ} {N : ℕ} (heta : 0 ≤ eta) (hN : 0 < N) :
    ((9 ^ ⌊eta * Nat.log 3 N⌋₊ : ℕ) : ℝ) ≤
      (N : ℝ) ^ (2 * eta) := by
  let L := Nat.log 3 N
  let J := ⌊eta * L⌋₊
  have hN0 : N ≠ 0 := Nat.ne_of_gt hN
  have hpowNat : 3 ^ L ≤ N := by
    simpa [L] using Nat.pow_log_le_self 3 hN0
  have hpowReal : ((3 : ℝ) ^ L) ≤ (N : ℝ) := by
    exact_mod_cast hpowNat
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hlog :
      (L : ℝ) * Real.log 3 ≤ Real.log N := by
    have := Real.log_le_log (by positivity : (0 : ℝ) < (3 : ℝ) ^ L) hpowReal
    simpa [Real.log_pow] using this
  have hJ :
      (J : ℝ) ≤ eta * L := by
    dsimp [J]
    exact Nat.floor_le (mul_nonneg heta (Nat.cast_nonneg L))
  have hlog9 : Real.log 9 = 2 * Real.log 3 := by
    calc
      Real.log 9 = Real.log ((3 : ℝ) ^ (2 : ℕ)) := by norm_num
      _ = 2 * Real.log 3 := by rw [Real.log_pow]; norm_num
  change ((9 ^ J : ℕ) : ℝ) ≤ (N : ℝ) ^ (2 * eta)
  rw [Nat.cast_pow]
  change (9 : ℝ) ^ J ≤ (N : ℝ) ^ (2 * eta)
  rw [← Real.rpow_natCast]
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 9),
    Real.rpow_def_of_pos (by exact_mod_cast hN)]
  rw [Real.exp_le_exp, hlog9]
  nlinarith

/-- One affine cone fiber is bounded by a scale factor that preserves the
`N^(1-D)` density gain. -/
theorem cone_badPrefix_term_le
    {S : Set ℕ} {C D : ℝ}
    (hS : IsCDDense S C D)
    {N k i : ℕ} (hN : 0 < N) (hi : i < 2 * 3 ^ k) :
    ((badPrefix S (3 ^ k * N + i)).card : ℝ) ≤
      C * (3 : ℝ) ^ (k + 1) * (N : ℝ) ^ (1 - D) := by
  have hyPos : 0 < 3 ^ k * N + i :=
    Nat.add_pos_left (Nat.mul_pos (by positivity) hN) i
  have hraw := hS.bad_bound (3 ^ k * N + i) hyPos
  have hN12 : N + 2 ≤ 3 * N := by omega
  have hyBound : 3 ^ k * N + i ≤ 3 ^ (k + 1) * N := by
    have hyBoundLt : 3 ^ k * N + i < 3 ^ (k + 1) * N := by
      calc
        3 ^ k * N + i < 3 ^ k * N + 2 * 3 ^ k :=
          Nat.add_lt_add_left hi _
        _ = 3 ^ k * (N + 2) := by ring
        _ ≤ 3 ^ k * (3 * N) := Nat.mul_le_mul_left _ hN12
        _ = 3 ^ (k + 1) * N := by rw [pow_succ]; ring
    exact hyBoundLt.le
  have hyBoundReal :
      ((3 ^ k * N + i : ℕ) : ℝ) ≤
        (3 : ℝ) ^ (k + 1) * N := by
    exact_mod_cast hyBound
  have hExp0 : 0 ≤ 1 - D := by linarith [hS.D_le_one]
  have hExp1 : 1 - D ≤ 1 := by linarith [hS.D_pos]
  have hpowMono :
      ((3 ^ k * N + i : ℕ) : ℝ) ^ (1 - D) ≤
        ((3 : ℝ) ^ (k + 1) * N) ^ (1 - D) :=
    Real.rpow_le_rpow (by positivity) hyBoundReal hExp0
  have hbasePow :
      ((3 : ℝ) ^ (k + 1)) ^ (1 - D) ≤
        (3 : ℝ) ^ (k + 1) := by
    calc
      ((3 : ℝ) ^ (k + 1)) ^ (1 - D)
          ≤ ((3 : ℝ) ^ (k + 1)) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by
          exact one_le_pow₀ (by norm_num)) hExp1
      _ = (3 : ℝ) ^ (k + 1) := by simp
  have hfactor :
      ((3 : ℝ) ^ (k + 1) * N) ^ (1 - D) ≤
        (3 : ℝ) ^ (k + 1) * (N : ℝ) ^ (1 - D) := by
    rw [Real.mul_rpow (by positivity) (by positivity)]
    exact mul_le_mul_of_nonneg_right hbasePow (Real.rpow_nonneg (by positivity) _)
  exact hraw.trans (by
    simpa [mul_assoc] using
      (mul_le_mul_of_nonneg_left (hpowMono.trans hfactor) hS.C_pos.le))

/-- Quantitative cone density with the deliberately weakened retained
exponent `D - 2*eta`.  At `eta=D/4` this is exactly `D/2`. -/
theorem coneCore_dense_weakened
    {S : Set ℕ} {C D eta : ℝ}
    (hS : IsCDDense S C D)
    (heta0 : 0 < eta) (hetaD : 2 * eta < D) :
    IsCDDense (coneCore 2 eta S) (12 * C) (D - 2 * eta) := by
  have hC : 0 < 12 * C := mul_pos (by norm_num) hS.C_pos
  have hRet0 : 0 < D - 2 * eta := by linarith
  have hRet1 : D - 2 * eta ≤ 1 := by
    linarith [hS.D_le_one]
  refine ⟨hC, hRet0, hRet1, ?_⟩
  intro N hN
  let J := ⌊eta * Nat.log 3 N⌋₊
  have hfinite :=
    card_badPrefix_coneCore_le_badPrefix_sum
      (S := S) (K := 2) (N := N) (eta := eta) heta0.le
  have hfiniteReal :
      ((badPrefix (coneCore 2 eta S) N).card : ℝ) ≤
        ∑ k ∈ Finset.range (J + 1),
          ∑ i ∈ Finset.range (2 * 3 ^ k),
            ((badPrefix S (3 ^ k * N + i)).card : ℝ) := by
    dsimp [J]
    exact_mod_cast hfinite
  have hterms :
      (∑ k ∈ Finset.range (J + 1),
          ∑ i ∈ Finset.range (2 * 3 ^ k),
            ((badPrefix S (3 ^ k * N + i)).card : ℝ)) ≤
        6 * C * (N : ℝ) ^ (1 - D) *
          ∑ k ∈ Finset.range (J + 1), (9 : ℝ) ^ k := by
    calc
      _ ≤ ∑ k ∈ Finset.range (J + 1),
          ∑ _i ∈ Finset.range (2 * 3 ^ k),
            C * (3 : ℝ) ^ (k + 1) * (N : ℝ) ^ (1 - D) := by
        apply Finset.sum_le_sum
        intro k hk
        apply Finset.sum_le_sum
        intro i hi
        exact cone_badPrefix_term_le hS hN (Finset.mem_range.mp hi)
      _ = 6 * C * (N : ℝ) ^ (1 - D) *
          ∑ k ∈ Finset.range (J + 1), (9 : ℝ) ^ k := by
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        push_cast
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k _
        rw [pow_succ]
        rw [show (9 : ℝ) ^ k = (3 : ℝ) ^ k * 3 ^ k by
          rw [show (9 : ℝ) = 3 * 3 by norm_num, mul_pow]]
        ring
  have hgeom :
      (∑ k ∈ Finset.range (J + 1), (9 : ℝ) ^ k) ≤
        (3 / 2 : ℝ) * (N : ℝ) ^ (2 * eta) := by
    calc
      _ ≤ (3 / 2 : ℝ) * 9 ^ J := sum_nine_pow_le_three_halves J
      _ ≤ (3 / 2 : ℝ) * (N : ℝ) ^ (2 * eta) :=
        mul_le_mul_of_nonneg_left
          (by simpa [J] using
            nine_pow_floor_eta_natLog_le_rpow heta0.le hN)
          (by norm_num)
  have hNpow0 : 0 ≤ (N : ℝ) ^ (1 - D) :=
    Real.rpow_nonneg (by positivity) _
  have hcombine :
      (N : ℝ) ^ (1 - D) * (N : ℝ) ^ (2 * eta) =
        (N : ℝ) ^ (1 - (D - 2 * eta)) := by
    rw [← Real.rpow_add (by exact_mod_cast hN)]
    congr 1
    ring
  calc
    ((badPrefix (coneCore 2 eta S) N).card : ℝ)
        ≤ ∑ k ∈ Finset.range (J + 1),
          ∑ i ∈ Finset.range (2 * 3 ^ k),
            ((badPrefix S (3 ^ k * N + i)).card : ℝ) := hfiniteReal
    _ ≤ 6 * C * (N : ℝ) ^ (1 - D) *
          ∑ k ∈ Finset.range (J + 1), (9 : ℝ) ^ k := hterms
    _ ≤ 6 * C * (N : ℝ) ^ (1 - D) *
          ((3 / 2 : ℝ) * (N : ℝ) ^ (2 * eta)) := by
      exact mul_le_mul_of_nonneg_left hgeom
        (mul_nonneg (mul_nonneg (by norm_num) hS.C_pos.le) hNpow0)
    _ ≤ 12 * C * (N : ℝ) ^ (1 - (D - 2 * eta)) := by
      rw [← hcombine]
      have hp : 0 ≤ (N : ℝ) ^ (2 * eta) :=
        Real.rpow_nonneg (by positivity) _
      have hprod :
          0 ≤ C * (N : ℝ) ^ (1 - D) * (N : ℝ) ^ (2 * eta) :=
        mul_nonneg (mul_nonneg hS.C_pos.le hNpow0) hp
      have hprod' :
          0 ≤ C * (N : ℝ) ^ (1 - D) * (N : ℝ) ^ (eta * 2) := by
        simpa [mul_comm] using hprod
      ring_nf
      nlinarith [hprod']

end

end QuantitativeDensity

end CollatzEndpointTransport
