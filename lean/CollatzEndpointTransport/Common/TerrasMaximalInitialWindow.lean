/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik
-/
import CollatzEndpointTransport.Common.TerrasMaximalBarrierDensity
import CollatzEndpointTransport.Common.TerrasInitialWindow

/-!
# Terras Maximal Initial Window

The shared maximal-barrier initial logarithmic window.

A single two-sided maximal parity barrier controls both the multiplicative
phase and the complete affine correction. Consequently the exceptional shell
rate is quadratic in the tolerance, with no prefix-union or correction-tail
loss.
-/

namespace CollatzEndpointTransport

namespace Terras

open Nat Finset
open scoped Real

noncomputable section

theorem three_rpow_maximalBarrierHeight
    (t : ℝ) (M : ℕ) :
    (3 : ℝ) ^ (maximalBarrierHeight t M) =
      (2 : ℝ) ^ (t * (M : ℝ) / 2) := by
  rw [three_rpow_eq_two_rpow_lg3]
  congr 1
  unfold maximalBarrierHeight
  have hlg3 : QuantitativeDensity.lg3 ≠ 0 :=
    ne_of_gt QuantitativeDensity.lg3_pos
  field_simp [hlg3]
  ring

theorem maximalBarrier_phase_half
    {n M : ℕ} {t : ℝ}
    (ht : 0 ≤ t)
    (hnShell : n ∈ Finset.Ico (2 ^ M) (2 ^ (M + 1))) :
    (3 : ℝ) ^ (maximalBarrierHeight t M) ≤
      (n : ℝ) ^ (t / 2) := by
  have hnLowerNat : 2 ^ M ≤ n := (Finset.mem_Ico.mp hnShell).1
  have hnLower : (2 : ℝ) ^ M ≤ n := by exact_mod_cast hnLowerNat
  rw [three_rpow_maximalBarrierHeight]
  calc
    (2 : ℝ) ^ (t * (M : ℝ) / 2) =
        ((2 : ℝ) ^ M) ^ (t / 2) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
      congr 1
      ring
    _ ≤ (n : ℝ) ^ (t / 2) :=
      Real.rpow_le_rpow (by positivity) hnLower (by positivity)

theorem maximalBarrier_phase_two
    {n M : ℕ} {t : ℝ}
    (ht : 0 < t)
    (hstart : 2 ≤ t * M)
    (hnShell : n ∈ Finset.Ico (2 ^ M) (2 ^ (M + 1))) :
    2 * (3 : ℝ) ^ (maximalBarrierHeight t M) ≤
      (n : ℝ) ^ t := by
  have hhalf := maximalBarrier_phase_half ht.le hnShell
  have htwoExp :
      (1 : ℝ) ≤ t * (M : ℝ) / 2 := by
    norm_num at hstart ⊢
    linarith
  have htwo :
      (2 : ℝ) ≤ (n : ℝ) ^ (t / 2) := by
    have h2pow :
        (2 : ℝ) ≤ (2 : ℝ) ^ (t * (M : ℝ) / 2) := by
      simpa using
        (Real.rpow_le_rpow_of_exponent_le
          (show (1 : ℝ) ≤ 2 by norm_num) htwoExp)
    exact h2pow.trans
      (by
        rw [← three_rpow_maximalBarrierHeight]
        exact hhalf)
  have hnPosNat : 0 < n := by
    have hpow : 0 < 2 ^ M := by positivity
    exact lt_of_lt_of_le hpow (Finset.mem_Ico.mp hnShell).1
  have hnR : (0 : ℝ) < n := by exact_mod_cast hnPosNat
  calc
    2 * (3 : ℝ) ^ (maximalBarrierHeight t M)
        ≤ (n : ℝ) ^ (t / 2) * (n : ℝ) ^ (t / 2) :=
      mul_le_mul htwo hhalf (by positivity) (by positivity)
    _ = (n : ℝ) ^ t := by
      rw [← Real.rpow_add hnR]
      congr 1
      ring

theorem two_affineConstant_le_n_mul_central
    {n k M : ℕ}
    (hM : 4 ≤ M) (hkM : k ≤ M)
    (hnShell : n ∈ Finset.Ico (2 ^ M) (2 ^ (M + 1))) :
    2 * (2 + Real.sqrt 3) ≤
      (n : ℝ) * centralOrbitScale k := by
  have hs0 : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg 3
  have hs2 : (Real.sqrt 3) ^ 2 = (3 : ℝ) := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  have hconst : 2 * (2 + Real.sqrt 3) ≤ (9 : ℝ) := by
    nlinarith
  have hnLowerNat : 2 ^ M ≤ n := (Finset.mem_Ico.mp hnShell).1
  have hnLower : (2 : ℝ) ^ M ≤ n := by exact_mod_cast hnLowerNat
  have hnPosNat : 0 < n := by
    have hpow : 0 < 2 ^ M := by positivity
    omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hnPosNat
  have hscale :=
    centralOrbitScale_ge_n_rpow_neg_b hkM hnShell
  have ha0 : 0 < QuantitativeDensity.a0 :=
    QuantitativeDensity.a0_pos
  have h16 : (16 : ℝ) ≤ n := by
    calc
      (16 : ℝ) = (2 : ℝ) ^ (4 : ℕ) := by norm_num
      _ ≤ (2 : ℝ) ^ M :=
        pow_le_pow_right₀ (by norm_num) hM
      _ ≤ n := hnLower
  have hnA0 :
      (16 : ℝ) ^ QuantitativeDensity.a0 ≤
        (n : ℝ) ^ QuantitativeDensity.a0 :=
    Real.rpow_le_rpow (by norm_num) h16 ha0.le
  have h16a0 :
      (16 : ℝ) ^ QuantitativeDensity.a0 = 9 := by
    calc
      (16 : ℝ) ^ QuantitativeDensity.a0 =
          (2 : ℝ) ^ (4 * QuantitativeDensity.a0) := by
        rw [show (16 : ℝ) = (2 : ℝ) ^ (4 : ℕ) by norm_num,
          ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
        norm_num
      _ = (3 : ℝ) ^ (2 : ℝ) := by
        rw [three_rpow_eq_two_rpow_lg3]
        congr 1
        unfold QuantitativeDensity.a0
        ring
      _ = 9 := by norm_num
  have hA0Scale :
      (n : ℝ) ^ QuantitativeDensity.a0 ≤
        (n : ℝ) * centralOrbitScale k := by
    have hExp :
        QuantitativeDensity.a0 =
          1 + (-QuantitativeDensity.bConst) := by
      unfold QuantitativeDensity.bConst
      ring
    rw [hExp, Real.rpow_add hnR, Real.rpow_one]
    exact mul_le_mul_of_nonneg_left hscale hnR.le
  calc
    2 * (2 + Real.sqrt 3) ≤ 9 := hconst
    _ = (16 : ℝ) ^ QuantitativeDensity.a0 := h16a0.symm
    _ ≤ (n : ℝ) ^ QuantitativeDensity.a0 := hnA0
    _ ≤ (n : ℝ) * centralOrbitScale k := hA0Scale

theorem orbit_lower_of_fixed_barrier
    {n k : ℕ} {h t : ℝ}
    (hn : 0 < n)
    (hS : (k : ℝ) / 2 - h ≤ (oddCount k n : ℝ))
    (hphase : (3 : ℝ) ^ h ≤ (n : ℝ) ^ t) :
    centralOrbitScale k * (n : ℝ) ^ (1 - t) ≤
      ((T^[k]) n : ℝ) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hInv :
      (n : ℝ) / (n : ℝ) ^ t ≤ (n : ℝ) / (3 : ℝ) ^ h :=
    div_le_div_of_nonneg_left hnR.le (by positivity) hphase
  have hThree :
      (3 : ℝ) ^ ((k : ℝ) / 2 - h) ≤
        (3 : ℝ) ^ oddCount k n := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hS
  rw [iterate_eq_affineCorrection]
  calc
    centralOrbitScale k * (n : ℝ) ^ (1 - t)
        = centralOrbitScale k * ((n : ℝ) / (n : ℝ) ^ t) := by
          rw [Real.rpow_sub hnR, Real.rpow_one]
    _ ≤ centralOrbitScale k * ((n : ℝ) / (3 : ℝ) ^ h) :=
      mul_le_mul_of_nonneg_left hInv (centralOrbitScale_pos k).le
    _ = (n : ℝ) / (2 : ℝ) ^ k *
        (3 : ℝ) ^ ((k : ℝ) / 2 - h) := by
      unfold centralOrbitScale
      rw [Real.rpow_sub (by norm_num : (0 : ℝ) < 3)]
      ring
    _ ≤ (n : ℝ) / (2 : ℝ) ^ k *
        (3 : ℝ) ^ oddCount k n :=
      mul_le_mul_of_nonneg_left hThree (by positivity)
    _ ≤ ((n : ℝ) / (2 : ℝ) ^ k + affineCorrection k n) *
        (3 : ℝ) ^ oddCount k n :=
      mul_le_mul_of_nonneg_right
        (le_add_of_nonneg_right (affineCorrection_nonneg k n))
        (by positivity)

theorem orbit_upper_of_fixed_barrier
    {n k : ℕ} {h t C : ℝ}
    (hn : 0 < n)
    (hS : (oddCount k n : ℝ) ≤ (k : ℝ) / 2 + h)
    (hphase : 2 * (3 : ℝ) ^ h ≤ (n : ℝ) ^ t)
    (hcorr :
      affineCorrection k n * (3 : ℝ) ^ ((k : ℝ) / 2) ≤
        C * (3 : ℝ) ^ h)
    (hcorrAbsorb :
      2 * (C * (3 : ℝ) ^ h * (3 : ℝ) ^ h) ≤
        centralOrbitScale k * (n : ℝ) ^ (1 + t)) :
    ((T^[k]) n : ℝ) ≤
      centralOrbitScale k * (n : ℝ) ^ (1 + t) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hThree :
      (3 : ℝ) ^ oddCount k n ≤
        (3 : ℝ) ^ ((k : ℝ) / 2 + h) := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hS
  have hMain :
      (n : ℝ) / (2 : ℝ) ^ k * (3 : ℝ) ^ oddCount k n ≤
        (centralOrbitScale k * (n : ℝ) ^ (1 + t)) / 2 := by
    calc
      _ ≤ (n : ℝ) / (2 : ℝ) ^ k *
          (3 : ℝ) ^ ((k : ℝ) / 2 + h) :=
        mul_le_mul_of_nonneg_left hThree (by positivity)
      _ = centralOrbitScale k * ((n : ℝ) * (3 : ℝ) ^ h) := by
        unfold centralOrbitScale
        rw [Real.rpow_add (by norm_num)]
        ring
      _ ≤ centralOrbitScale k * ((n : ℝ) * ((n : ℝ) ^ t / 2)) := by
        apply mul_le_mul_of_nonneg_left _ (centralOrbitScale_pos k).le
        apply mul_le_mul_of_nonneg_left _ hnR.le
        linarith
      _ = (centralOrbitScale k * (n : ℝ) ^ (1 + t)) / 2 := by
        rw [Real.rpow_add hnR, Real.rpow_one]
        ring
  have hCorr :
      affineCorrection k n * (3 : ℝ) ^ oddCount k n ≤
        (centralOrbitScale k * (n : ℝ) ^ (1 + t)) / 2 := by
    calc
      _ ≤ affineCorrection k n *
          (3 : ℝ) ^ ((k : ℝ) / 2 + h) :=
        mul_le_mul_of_nonneg_left hThree
          (affineCorrection_nonneg k n)
      _ = (affineCorrection k n * (3 : ℝ) ^ ((k : ℝ) / 2)) *
          (3 : ℝ) ^ h := by
        rw [Real.rpow_add (by norm_num)]
        ring
      _ ≤ (C * (3 : ℝ) ^ h) * (3 : ℝ) ^ h :=
        mul_le_mul_of_nonneg_right hcorr (by positivity)
      _ ≤ (centralOrbitScale k * (n : ℝ) ^ (1 + t)) / 2 := by
        linarith
  rw [iterate_eq_affineCorrection]
  calc
    _ = (n : ℝ) / (2 : ℝ) ^ k * (3 : ℝ) ^ oddCount k n +
        affineCorrection k n * (3 : ℝ) ^ oddCount k n := by ring
    _ ≤ (centralOrbitScale k * (n : ℝ) ^ (1 + t)) / 2 +
        (centralOrbitScale k * (n : ℝ) ^ (1 + t)) / 2 :=
      add_le_add hMain hCorr
    _ = _ := by ring

/-- The maximal parity barrier supplies the complete two-sided initial-window
orbit envelope. -/
theorem orbit_envelope_of_maximalBarrier
    {n k M : ℕ} {t : ℝ}
    (ht : 0 < t) (hM : 4 ≤ M) (hstart : 2 ≤ t * M)
    (hkM : k ≤ M)
    (hnShell : n ∈ Finset.Ico (2 ^ M) (2 ^ (M + 1)))
    (hreg : MaximalParityRegular n M (maximalBarrierHeight t M)) :
    centralOrbitScale k * (n : ℝ) ^ (1 - t) ≤ ((T^[k]) n : ℝ) ∧
      ((T^[k]) n : ℝ) ≤
        centralOrbitScale k * (n : ℝ) ^ (1 + t) := by
  have hnPos : 0 < n := by
    have hpow : 0 < 2 ^ M := by positivity
    exact lt_of_lt_of_le hpow (Finset.mem_Ico.mp hnShell).1
  have hbounds := hreg k hkM
  have hSlo :
      (k : ℝ) / 2 - maximalBarrierHeight t M ≤ oddCount k n := by
    exact sub_le_iff_le_add.mpr ((abs_le.mp hbounds).1 |> fun h => by linarith)
  have hShi :
      (oddCount k n : ℝ) ≤
        (k : ℝ) / 2 + maximalBarrierHeight t M := by
    exact (abs_le.mp hbounds).2 |> fun h => by linarith
  have hphaseHalf := maximalBarrier_phase_half ht.le hnShell
  have hphase :
      (3 : ℝ) ^ (maximalBarrierHeight t M) ≤ (n : ℝ) ^ t := by
    have hnOne : (1 : ℝ) ≤ n := by exact_mod_cast hnPos
    exact hphaseHalf.trans
      (Real.rpow_le_rpow_of_exponent_le hnOne (by linarith))
  have hphaseTwo := maximalBarrier_phase_two ht hstart hnShell
  have hcorr := affineCorrection_scaled_le_maximal
    (n := n) (M := M) (k := k) (h := maximalBarrierHeight t M)
    (maximalBarrierHeight_nonneg ht.le) hkM hreg
  have hscale := two_affineConstant_le_n_mul_central hM hkM hnShell
  have hcorrAbsorb :
      2 * ((2 + Real.sqrt 3) *
          (3 : ℝ) ^ (maximalBarrierHeight t M) *
          (3 : ℝ) ^ (maximalBarrierHeight t M)) ≤
        centralOrbitScale k * (n : ℝ) ^ (1 + t) := by
    have hphaseSq :
        (3 : ℝ) ^ (maximalBarrierHeight t M) *
            (3 : ℝ) ^ (maximalBarrierHeight t M) ≤
          (n : ℝ) ^ t := by
      calc
        _ = (3 : ℝ) ^ (2 * maximalBarrierHeight t M) := by
          rw [← Real.rpow_add (by norm_num)]
          congr 1
          ring
        _ = (2 : ℝ) ^ (t * M) := by
          rw [three_rpow_eq_two_rpow_lg3]
          congr 1
          unfold maximalBarrierHeight
          have hlg3 : QuantitativeDensity.lg3 ≠ 0 :=
            ne_of_gt QuantitativeDensity.lg3_pos
          field_simp [hlg3]
          ring
        _ = ((2 : ℝ) ^ M) ^ t := by
          rw [mul_comm, Real.rpow_mul (by norm_num), Real.rpow_natCast]
        _ ≤ (n : ℝ) ^ t := by
          have hnLowerNat : 2 ^ M ≤ n := (Finset.mem_Ico.mp hnShell).1
          have hnLower : (2 : ℝ) ^ M ≤ n := by exact_mod_cast hnLowerNat
          exact Real.rpow_le_rpow (by positivity) hnLower ht.le
    have hmul :
        2 * (2 + Real.sqrt 3) *
            ((3 : ℝ) ^ (maximalBarrierHeight t M) *
              (3 : ℝ) ^ (maximalBarrierHeight t M)) ≤
          ((n : ℝ) * centralOrbitScale k) * (n : ℝ) ^ t :=
      mul_le_mul hscale hphaseSq (by positivity)
        (mul_nonneg (Nat.cast_nonneg n) (centralOrbitScale_pos k).le)
    rw [Real.rpow_add (by exact_mod_cast hnPos : (0 : ℝ) < n),
      Real.rpow_one]
    nlinarith
  exact
    ⟨orbit_lower_of_fixed_barrier hnPos hSlo hphase,
      orbit_upper_of_fixed_barrier hnPos hShi hphaseTwo hcorr hcorrAbsorb⟩

end

end Terras

end CollatzEndpointTransport
