/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik
-/
import CollatzEndpointTransport.QuadraticAppendix.Shared.QuantitativeBasePullback
import CollatzEndpointTransport.QuadraticAppendix.Shared.QuantitativeConeDensity

/-!
# Quantitative Base Pullback Density

Real-power completion of the deterministic base-map fiber estimate.

This is the analytic base-pullback density estimate. It
turns the exact finite-fiber count into the shell estimate

  bad <= 12 C 2^M 3^(-D*alpha*M).
-/

namespace CollatzEndpointTransport

namespace QuantitativeDensity

open scoped Real

noncomputable section

theorem baseNumeratorScale_le_two_pow
    {alpha : ℝ} {M : ℕ}
    (ha0 : 0 ≤ alpha) (ha1 : alpha ≤ 1 / 2) :
    baseNumeratorScale alpha M ≤ 2 ^ M := by
  let J := ⌊alpha * M⌋₊
  have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  have hJfloor : (J : ℝ) ≤ alpha * M := by
    dsimp [J]
    exact Nat.floor_le (mul_nonneg ha0 hM0)
  have hJhalf : (J : ℝ) ≤ (M : ℝ) / 2 := by
    nlinarith
  have h2J : 2 * J ≤ M := by
    exact_mod_cast (show (2 : ℝ) * J ≤ M by nlinarith)
  change 3 ^ J ≤ 2 ^ M
  calc
    3 ^ J ≤ 4 ^ J := Nat.pow_le_pow_left (by omega) J
    _ = 2 ^ (2 * J) := by
      rw [show 4 = 2 ^ 2 by norm_num, ← pow_mul]
    _ ≤ 2 ^ M := Nat.pow_le_pow_right (by omega) h2J

/-- A ceiling-division fiber costs at most twice the corresponding real
ratio when the numerator dominates the denominator scale. -/
theorem cast_ceilDiv_le_two_mul_div
    {A B : ℕ} (hA : 0 < A) (hAB : A ≤ B) :
    ((B ⌈/⌉ A : ℕ) : ℝ) ≤ 2 * (B : ℝ) / A := by
  rw [Nat.ceilDiv_eq_add_pred_div]
  have hcast :
      ((((B + A - 1) / A : ℕ) : ℝ)) ≤
        ((B + A - 1 : ℕ) : ℝ) / A :=
    Nat.cast_div_le
  have hsub : B + A - 1 ≤ B + A := Nat.sub_le _ _
  have hsum :
      (((B + A - 1 : ℕ) : ℝ) / A) ≤
        ((B : ℝ) + A) / A := by
    apply div_le_div_of_nonneg_right
    · exact_mod_cast hsub
    · positivity
  have hratio : (A : ℝ) ≤ B := by exact_mod_cast hAB
  have hAreal : (0 : ℝ) < A := by exact_mod_cast hA
  calc
    ((((B + A - 1) / A : ℕ) : ℝ))
        ≤ ((B + A - 1 : ℕ) : ℝ) / A := hcast
    _ ≤ ((B : ℝ) + A) / A := hsum
    _ = (B : ℝ) / A + 1 := by field_simp
    _ ≤ (B : ℝ) / A + (B : ℝ) / A := by
      gcongr
      exact (one_le_div hAreal).2 hratio
    _ = 2 * (B : ℝ) / A := by ring

/-- The floor in `A=3^floor(alpha*M)` costs at most one factor of three. -/
theorem baseNumeratorScale_neg_rpow_le
    {alpha D : ℝ} {M : ℕ}
    (ha0 : 0 ≤ alpha) (hD0 : 0 ≤ D) (hD1 : D ≤ 1) :
    (baseNumeratorScale alpha M : ℝ) ^ (-D) ≤
      3 * (3 : ℝ) ^ (-D * alpha * M) := by
  let J := ⌊alpha * M⌋₊
  have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  have hfloor :
      alpha * M < (J : ℝ) + 1 := by
    dsimp [J]
    exact Nat.lt_floor_add_one _
  have hExp : -D * J ≤ D - D * alpha * M := by
    nlinarith
  have hpow :
      (3 : ℝ) ^ (-D * J) ≤
        (3 : ℝ) ^ (D - D * alpha * M) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) hExp
  have hthreeD : (3 : ℝ) ^ D ≤ 3 := by
    simpa using
      (Real.rpow_le_rpow_of_exponent_le (x := (3 : ℝ)) (by norm_num) hD1)
  change (((3 ^ J : ℕ) : ℝ)) ^ (-D) ≤
    3 * (3 : ℝ) ^ (-D * alpha * M)
  rw [Nat.cast_pow]
  norm_num only [Nat.cast_ofNat]
  have hleft :
      ((3 : ℝ) ^ J) ^ (-D) = (3 : ℝ) ^ (-D * J) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    ring_nf
  rw [hleft]
  calc
    (3 : ℝ) ^ (-D * J)
        ≤ (3 : ℝ) ^ (D - D * alpha * M) := hpow
    _ = (3 : ℝ) ^ D * (3 : ℝ) ^ (-D * alpha * M) := by
      rw [show D - D * alpha * M = D + (-D * alpha * M) by ring,
        Real.rpow_add (by norm_num)]
    _ ≤ 3 * (3 : ℝ) ^ (-D * alpha * M) :=
      mul_le_mul_of_nonneg_right hthreeD (Real.rpow_nonneg (by norm_num) _)

/-- Concrete shell estimate for the deterministic base pullback. -/
theorem card_shellBad_basePullback_le_rpow
    {S : Set ℕ} {C D alpha : ℝ} {M : ℕ}
    (hS : IsCDDense S C D)
    (ha0 : 0 ≤ alpha) (ha1 : alpha ≤ 1 / 2) :
    ((shellBad (basePullback alpha S) M).card : ℝ) ≤
      12 * C * (2 ^ M : ℕ) *
        (3 : ℝ) ^ (-D * alpha * M) := by
  let A := baseNumeratorScale alpha M
  let B := 2 ^ M
  have hA : 0 < A := baseNumeratorScale_pos alpha M
  have hAB : A ≤ B := by
    simpa [A, B] using baseNumeratorScale_le_two_pow ha0 ha1
  have hcount := card_shellBad_basePullback_le S alpha M
  have hcountReal :
      ((shellBad (basePullback alpha S) M).card : ℝ) ≤
        ((badPrefix S (2 * A)).card : ℝ) * ((B ⌈/⌉ A : ℕ) : ℝ) := by
    dsimp [A, B]
    exact_mod_cast hcount
  have hbad := hS.bad_bound (2 * A) (by positivity)
  have hfiber := cast_ceilDiv_le_two_mul_div hA hAB
  have hAreal : (0 : ℝ) < A := by exact_mod_cast hA
  have hExp0 : 0 ≤ 1 - D := by linarith [hS.D_le_one]
  have htwoPow :
      (2 : ℝ) ^ (1 - D) ≤ 2 := by
    simpa using
      (Real.rpow_le_rpow_of_exponent_le (x := (2 : ℝ)) (by norm_num)
        (by linarith [hS.D_pos] : 1 - D ≤ 1))
  have hAneg :=
    baseNumeratorScale_neg_rpow_le
      (M := M) ha0 hS.D_pos.le hS.D_le_one
  have hAneg' :
      (A : ℝ) ^ (-D) ≤ 3 * (3 : ℝ) ^ (-D * alpha * M) := by
    simpa [A] using hAneg
  have hAshift :
      (A : ℝ) ^ (1 - D) = (A : ℝ) * (A : ℝ) ^ (-D) := by
    rw [show 1 - D = 1 + (-D) by ring, Real.rpow_add hAreal,
      Real.rpow_one]
  calc
    ((shellBad (basePullback alpha S) M).card : ℝ)
        ≤ ((badPrefix S (2 * A)).card : ℝ) *
            ((B ⌈/⌉ A : ℕ) : ℝ) := hcountReal
    _ ≤ (C * ((2 * A : ℕ) : ℝ) ^ (1 - D)) *
          (2 * (B : ℝ) / A) :=
      mul_le_mul hbad hfiber (Nat.cast_nonneg _)
        (mul_nonneg hS.C_pos.le (Real.rpow_nonneg (by positivity) _))
    _ = 2 * C * (B : ℝ) * (2 : ℝ) ^ (1 - D) *
          (A : ℝ) ^ (-D) := by
      rw [show (((2 * A : ℕ) : ℝ)) = (2 : ℝ) * A by norm_num]
      rw [Real.mul_rpow (by norm_num) hAreal.le]
      rw [hAshift]
      field_simp
      ring
    _ ≤ 4 * C * (B : ℝ) * (A : ℝ) ^ (-D) := by
      have hnonneg : 0 ≤ 2 * C * (B : ℝ) * (A : ℝ) ^ (-D) := by
        exact mul_nonneg
          (mul_nonneg (mul_nonneg (by norm_num) hS.C_pos.le) (by positivity))
          (Real.rpow_nonneg hAreal.le _)
      nlinarith
    _ ≤ 12 * C * (B : ℝ) *
          (3 : ℝ) ^ (-D * alpha * M) := by
      have hcoef : 0 ≤ 4 * C * (B : ℝ) :=
        mul_nonneg (mul_nonneg (by norm_num) hS.C_pos.le) (by positivity)
      exact (mul_le_mul_of_nonneg_left hAneg' hcoef).trans_eq (by ring)
    _ = 12 * C * (2 ^ M : ℕ) *
          (3 : ℝ) ^ (-D * alpha * M) := by simp [B]

end

end QuantitativeDensity

end CollatzEndpointTransport
