/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik
-/
import CollatzEndpointTransport.Common.QuantitativeDensityConstants
import CollatzEndpointTransport.Common.TerrasAffineIterate

/-!
# Terras Orbit Envelope

Deterministic two-sided orbit envelope from parity and affine correction.

This file is the algebraic core of the quantitative initial-window lemma.
It separates the exact Collatz identity from the scalar shell estimates:

* a lower/upper bound on the odd count controls the multiplicative term;
* the affine-correction estimate controls the additive term;
* two explicit scalar inequalities pay for the requested orbit tolerance.
-/

namespace CollatzEndpointTransport

namespace Terras

open Nat Finset
open scoped Real

/-- The deterministic central scale `(sqrt 3 / 2)^k`. -/
noncomputable def centralOrbitScale (k : ℕ) : ℝ :=
  (3 : ℝ) ^ ((k : ℝ) / 2) / (2 : ℝ) ^ k

theorem centralOrbitScale_pos (k : ℕ) :
    0 < centralOrbitScale k := by
  unfold centralOrbitScale
  positivity

theorem centralOrbitScale_eq (k : ℕ) :
    centralOrbitScale k = (Real.sqrt 3 / 2) ^ k := by
  unfold centralOrbitScale
  rw [Real.rpow_div_two_eq_sqrt (k : ℝ) (by norm_num),
    Real.rpow_natCast, div_pow]

/-- Change of base for real powers, specialized to `log_2 3`. -/
theorem three_rpow_eq_two_rpow_lg3 (x : ℝ) :
    (3 : ℝ) ^ x =
      (2 : ℝ) ^ (QuantitativeDensity.lg3 * x) := by
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3),
    Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
  congr 1
  have hlog2 : Real.log 2 ≠ 0 :=
    ne_of_gt (Real.log_pos (by norm_num))
  unfold QuantitativeDensity.lg3 Real.logb
  field_simp

theorem centralOrbitScale_eq_two_rpow_neg_b (k : ℕ) :
    centralOrbitScale k =
      (2 : ℝ) ^ (-QuantitativeDensity.bConst * k) := by
  unfold centralOrbitScale
  rw [three_rpow_eq_two_rpow_lg3, ← Real.rpow_natCast,
    ← Real.rpow_sub (by norm_num : (0 : ℝ) < 2)]
  congr 1
  unfold QuantitativeDensity.bConst QuantitativeDensity.a0
  ring

theorem centralOrbitScale_ge_n_rpow_neg_b
    {n k M : ℕ}
    (hkM : k ≤ M)
    (hnShell : n ∈ Finset.Ico (2 ^ M) (2 ^ (M + 1))) :
    (n : ℝ) ^ (-QuantitativeDensity.bConst) ≤
      centralOrbitScale k := by
  have hb : 0 < QuantitativeDensity.bConst :=
    QuantitativeDensity.bConst_pos
  have hkMR : (k : ℝ) ≤ M := by exact_mod_cast hkM
  have hExp :
      -QuantitativeDensity.bConst * M ≤
        -QuantitativeDensity.bConst * k := by
    nlinarith
  have hScaleM :
      (2 : ℝ) ^ (-QuantitativeDensity.bConst * M) ≤
        centralOrbitScale k := by
    rw [centralOrbitScale_eq_two_rpow_neg_b]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hExp
  have hnLowerNat : 2 ^ M ≤ n := (Finset.mem_Ico.mp hnShell).1
  have hnLower : (2 : ℝ) ^ M ≤ n := by exact_mod_cast hnLowerNat
  have hBase :
      (n : ℝ) ^ (-QuantitativeDensity.bConst) ≤
        ((2 : ℝ) ^ M) ^ (-QuantitativeDensity.bConst) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) hnLower (by linarith)
  have hEq :
      ((2 : ℝ) ^ M) ^ (-QuantitativeDensity.bConst) =
        (2 : ℝ) ^ (-QuantitativeDensity.bConst * M) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    congr 1
    ring
  rw [hEq] at hBase
  exact hBase.trans hScaleM

/-- The lower orbit envelope follows from a lower parity bound and the phase
budget `3^(eta*k) ≤ n^t`.  The correction is nonnegative and therefore helps
the lower bound. -/
theorem orbit_lower_of_parityCorrection
    {n k : ℕ} {eta t : ℝ}
    (hn : 0 < n)
    (hS :
      (k : ℝ) / 2 - eta * k ≤ (oddCount k n : ℝ))
    (hphase :
      (3 : ℝ) ^ (eta * k) ≤ (n : ℝ) ^ t) :
    centralOrbitScale k * (n : ℝ) ^ (1 - t) ≤
      ((T^[k]) n : ℝ) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have h3eta : 0 < (3 : ℝ) ^ (eta * k) := by positivity
  have hInv :
      (n : ℝ) / (n : ℝ) ^ t ≤
        (n : ℝ) / (3 : ℝ) ^ (eta * k) :=
    div_le_div_of_nonneg_left hnR.le h3eta hphase
  have hScale : 0 ≤ centralOrbitScale k :=
    (centralOrbitScale_pos k).le
  have hTarget :
      centralOrbitScale k * (n : ℝ) ^ (1 - t) ≤
        (n : ℝ) / (2 : ℝ) ^ k *
          (3 : ℝ) ^ ((k : ℝ) / 2 - eta * k) := by
    rw [Real.rpow_sub hnR, Real.rpow_one]
    calc
      centralOrbitScale k * ((n : ℝ) / (n : ℝ) ^ t)
          ≤ centralOrbitScale k *
              ((n : ℝ) / (3 : ℝ) ^ (eta * k)) :=
        mul_le_mul_of_nonneg_left hInv hScale
      _ = (n : ℝ) / (2 : ℝ) ^ k *
          (3 : ℝ) ^ ((k : ℝ) / 2 - eta * k) := by
        unfold centralOrbitScale
        rw [Real.rpow_sub (by norm_num : (0 : ℝ) < 3)]
        ring
  have hThree :
      (3 : ℝ) ^ ((k : ℝ) / 2 - eta * k) ≤
        (3 : ℝ) ^ oddCount k n := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hS
  rw [iterate_eq_affineCorrection]
  calc
    centralOrbitScale k * (n : ℝ) ^ (1 - t)
        ≤ (n : ℝ) / (2 : ℝ) ^ k *
            (3 : ℝ) ^ ((k : ℝ) / 2 - eta * k) := hTarget
    _ ≤ (n : ℝ) / (2 : ℝ) ^ k *
          (3 : ℝ) ^ oddCount k n :=
      mul_le_mul_of_nonneg_left hThree (by positivity)
    _ ≤ ((n : ℝ) / (2 : ℝ) ^ k + affineCorrection k n) *
          (3 : ℝ) ^ oddCount k n := by
      exact mul_le_mul_of_nonneg_right
        (le_add_of_nonneg_right (affineCorrection_nonneg k n))
        (by positivity)

/-- The upper orbit envelope.  The target is split equally between the
multiplicative main term and the affine correction. -/
theorem orbit_upper_of_parityCorrection
    {n k : ℕ} {eta t : ℝ}
    (hn : 0 < n)
    (hS :
      (oddCount k n : ℝ) ≤ (k : ℝ) / 2 + eta * k)
    (hphase :
      2 * (3 : ℝ) ^ (eta * k) ≤ (n : ℝ) ^ t)
    (hcorr :
      affineCorrection k n * (3 : ℝ) ^ ((k : ℝ) / 2) ≤
        (n : ℝ) ^ eta)
    (hcorrAbsorb :
      2 * ((n : ℝ) ^ eta * (3 : ℝ) ^ (eta * k)) ≤
        centralOrbitScale k * (n : ℝ) ^ (1 + t)) :
    ((T^[k]) n : ℝ) ≤
      centralOrbitScale k * (n : ℝ) ^ (1 + t) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hThree :
      (3 : ℝ) ^ oddCount k n ≤
        (3 : ℝ) ^ ((k : ℝ) / 2 + eta * k) := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hS
  have hMain :
      (n : ℝ) / (2 : ℝ) ^ k * (3 : ℝ) ^ oddCount k n ≤
        (centralOrbitScale k * (n : ℝ) ^ (1 + t)) / 2 := by
    calc
      (n : ℝ) / (2 : ℝ) ^ k * (3 : ℝ) ^ oddCount k n
          ≤ (n : ℝ) / (2 : ℝ) ^ k *
              (3 : ℝ) ^ ((k : ℝ) / 2 + eta * k) :=
        mul_le_mul_of_nonneg_left hThree (by positivity)
      _ = centralOrbitScale k *
          ((n : ℝ) * (3 : ℝ) ^ (eta * k)) := by
        unfold centralOrbitScale
        rw [Real.rpow_add (by norm_num)]
        ring
      _ ≤ centralOrbitScale k *
          ((n : ℝ) * ((n : ℝ) ^ t / 2)) := by
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
      affineCorrection k n * (3 : ℝ) ^ oddCount k n
          ≤ affineCorrection k n *
              (3 : ℝ) ^ ((k : ℝ) / 2 + eta * k) :=
        mul_le_mul_of_nonneg_left hThree
          (affineCorrection_nonneg k n)
      _ = (affineCorrection k n * (3 : ℝ) ^ ((k : ℝ) / 2)) *
          (3 : ℝ) ^ (eta * k) := by
        rw [Real.rpow_add (by norm_num)]
        ring
      _ ≤ (n : ℝ) ^ eta * (3 : ℝ) ^ (eta * k) :=
        mul_le_mul_of_nonneg_right hcorr (by positivity)
      _ ≤ (centralOrbitScale k * (n : ℝ) ^ (1 + t)) / 2 := by
        linarith
  rw [iterate_eq_affineCorrection]
  calc
    ((n : ℝ) / (2 : ℝ) ^ k + affineCorrection k n) *
          (3 : ℝ) ^ oddCount k n =
        (n : ℝ) / (2 : ℝ) ^ k * (3 : ℝ) ^ oddCount k n +
          affineCorrection k n * (3 : ℝ) ^ oddCount k n := by ring
    _ ≤ (centralOrbitScale k * (n : ℝ) ^ (1 + t)) / 2 +
          (centralOrbitScale k * (n : ℝ) ^ (1 + t)) / 2 :=
      add_le_add hMain hCorr
    _ = centralOrbitScale k * (n : ℝ) ^ (1 + t) := by ring

end Terras

end CollatzEndpointTransport
