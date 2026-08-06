/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik
-/
import Mathlib.Algebra.GeomSum
import CollatzEndpointTransport.Common.AffineCorrection
import CollatzEndpointTransport.Common.TerrasMaximalBarrier

/-!
# Terras Affine Maximal Barrier

Affine-correction control under a two-sided maximal parity barrier.

Unlike the earlier prefix-union estimate, the maximal event has no union
over prefix lengths. Its deterministic payoff is also uniform in the
horizon: the correction is bounded by a finite geometric series.
-/

namespace CollatzEndpointTransport

namespace Terras

open Nat Finset

noncomputable section

/-- Every parity prefix through `M` stays within distance `h` of half its
length. -/
def MaximalParityRegular (n M : ℕ) (h : ℝ) : Prop :=
  ∀ H : ℕ, H ≤ M →
    |(oddCount H n : ℝ) - (H : ℝ) / 2| ≤ h

/-- The geometric ratio in the affine-correction estimate. -/
def affineGeomRatio : ℝ := Real.sqrt 3 / 2

theorem affineGeomRatio_pos : 0 < affineGeomRatio := by
  unfold affineGeomRatio
  positivity

theorem affineGeomRatio_lt_one : affineGeomRatio < 1 := by
  unfold affineGeomRatio
  have hs0 : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg 3
  have hs2 : (Real.sqrt 3) ^ 2 = (3 : ℝ) := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  nlinarith

theorem oddCount_lower_of_maximalRegular
    {n M H : ℕ} {h : ℝ}
    (hreg : MaximalParityRegular n M h) (hHM : H ≤ M) :
    (H : ℝ) / 2 - h ≤ oddCount H n := by
  have habs := hreg H hHM
  have hlower := (abs_le.mp habs).1
  push_cast
  linarith

/-- A single affine summand is paid for by one term of a fixed geometric
series. -/
theorem affineCorrectionTerm_scaled_le_maximal
    {n M k i : ℕ} {h : ℝ}
    (hh : 0 ≤ h) (hik : i < k) (hkM : k ≤ M)
    (hreg : MaximalParityRegular n M h) :
    affineCorrectionTerm k n i * (3 : ℝ) ^ ((k : ℝ) / 2) ≤
      (3 : ℝ) ^ h / 2 * affineGeomRatio ^ (k - 1 - i) := by
  have hiM : i + 1 ≤ M := by omega
  have hS := oddCount_lower_of_maximalRegular hreg hiM
  have hki : k = (i + 1) + (k - 1 - i) := by omega
  have hExp :
      (k : ℝ) / 2 ≤
        oddCount (i + 1) n + h + ((k - 1 - i : ℕ) : ℝ) / 2 := by
    have hkiR :
        (k : ℝ) = (i + 1 : ℕ) + (k - 1 - i : ℕ) := by
      exact_mod_cast hki
    push_cast at hS hkiR
    nlinarith
  have hbase :
      (3 : ℝ) ^ ((k : ℝ) / 2) ≤
        (3 : ℝ) ^ oddCount (i + 1) n *
          (3 : ℝ) ^ h *
          (3 : ℝ) ^ (((k - 1 - i : ℕ) : ℝ) / 2) := by
    calc
      (3 : ℝ) ^ ((k : ℝ) / 2) ≤
          (3 : ℝ) ^
            ((oddCount (i + 1) n : ℝ) + h +
              ((k - 1 - i : ℕ) : ℝ) / 2) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) hExp
      _ = (3 : ℝ) ^ oddCount (i + 1) n *
          (3 : ℝ) ^ h *
          (3 : ℝ) ^ (((k - 1 - i : ℕ) : ℝ) / 2) := by
        rw [Real.rpow_add (by norm_num), Real.rpow_add (by norm_num),
          Real.rpow_natCast]
  have hden :
      0 < (3 : ℝ) ^ oddCount (i + 1) n * (2 : ℝ) ^ (k - i) := by
    positivity
  have hraw :
      affineCorrectionTerm k n i * (3 : ℝ) ^ ((k : ℝ) / 2) ≤
        (3 : ℝ) ^ h *
          (3 : ℝ) ^ (((k - 1 - i : ℕ) : ℝ) / 2) /
            (2 : ℝ) ^ (k - i) := by
    unfold affineCorrectionTerm
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hden).2
    calc
      parityDigitR n i * (3 : ℝ) ^ ((k : ℝ) / 2) ≤
          (3 : ℝ) ^ ((k : ℝ) / 2) := by
        simpa only [one_mul] using
          mul_le_mul_of_nonneg_right (parityDigitR_le_one n i)
            (Real.rpow_nonneg (by norm_num) _)
      _ ≤ (3 : ℝ) ^ oddCount (i + 1) n *
          (3 : ℝ) ^ h *
          (3 : ℝ) ^ (((k - 1 - i : ℕ) : ℝ) / 2) := hbase
      _ = ((3 : ℝ) ^ h *
          (3 : ℝ) ^ (((k - 1 - i : ℕ) : ℝ) / 2) /
            (2 : ℝ) ^ (k - i)) *
          ((3 : ℝ) ^ oddCount (i + 1) n *
            (2 : ℝ) ^ (k - i)) := by
        field_simp
        ring
  calc
    _ ≤ (3 : ℝ) ^ h *
          (3 : ℝ) ^ (((k - 1 - i : ℕ) : ℝ) / 2) /
            (2 : ℝ) ^ (k - i) := hraw
    _ = (3 : ℝ) ^ h / 2 *
          affineGeomRatio ^ (k - 1 - i) := by
      have hd : k - i = (k - 1 - i) + 1 := by omega
      rw [hd, pow_succ, Real.rpow_div_two_eq_sqrt _ (by norm_num),
        Real.rpow_natCast]
      unfold affineGeomRatio
      rw [div_pow]
      field_simp
      ring

/-- **Finite affine-correction bound under the maximal barrier.**

The constant is independent of `M` and `k`; it is the sum of the geometric
series with ratio `sqrt(3)/2`. -/
theorem affineCorrection_scaled_le_maximal
    {n M k : ℕ} {h : ℝ}
    (hh : 0 ≤ h) (hkM : k ≤ M)
    (hreg : MaximalParityRegular n M h) :
    affineCorrection k n * (3 : ℝ) ^ ((k : ℝ) / 2) ≤
      (2 + Real.sqrt 3) * (3 : ℝ) ^ h := by
  have hterm :
      ∀ i ∈ Finset.range k,
        affineCorrectionTerm k n i * (3 : ℝ) ^ ((k : ℝ) / 2) ≤
          (3 : ℝ) ^ h / 2 * affineGeomRatio ^ (k - 1 - i) := by
    intro i hi
    exact affineCorrectionTerm_scaled_le_maximal hh
      (Finset.mem_range.mp hi) hkM hreg
  have hsum :
      affineCorrection k n * (3 : ℝ) ^ ((k : ℝ) / 2) ≤
        (3 : ℝ) ^ h / 2 *
          ∑ j ∈ Finset.range k, affineGeomRatio ^ j := by
    calc
      affineCorrection k n * (3 : ℝ) ^ ((k : ℝ) / 2) =
          ∑ i ∈ Finset.range k,
            affineCorrectionTerm k n i *
              (3 : ℝ) ^ ((k : ℝ) / 2) := by
        simp only [affineCorrection, Finset.sum_mul]
      _ ≤ ∑ i ∈ Finset.range k,
          ((3 : ℝ) ^ h / 2 *
            affineGeomRatio ^ (k - 1 - i)) :=
        Finset.sum_le_sum hterm
      _ = (3 : ℝ) ^ h / 2 *
          ∑ j ∈ Finset.range k,
            affineGeomRatio ^ (k - 1 - j) := by
        rw [Finset.mul_sum]
      _ = (3 : ℝ) ^ h / 2 *
          ∑ j ∈ Finset.range k, affineGeomRatio ^ j := by
        rw [Finset.sum_range_reflect]
  have hgeom :
      ∑ j ∈ Finset.range k, affineGeomRatio ^ j <
        (1 - affineGeomRatio)⁻¹ := by
    rw [inv_eq_one_div, lt_div_iff₀ (sub_pos.mpr affineGeomRatio_lt_one)]
    rw [geom_sum_mul_neg]
    have hpow : 0 < affineGeomRatio ^ k :=
      pow_pos affineGeomRatio_pos k
    linarith
  have hconstant :
      ((1 - affineGeomRatio)⁻¹ : ℝ) = 2 * (2 + Real.sqrt 3) := by
    unfold affineGeomRatio
    have hs2 : (Real.sqrt 3) ^ 2 = (3 : ℝ) := by
      nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
    have hden : 2 - Real.sqrt 3 ≠ 0 := by
      nlinarith [affineGeomRatio_lt_one]
    field_simp
    nlinarith
  calc
    _ ≤ (3 : ℝ) ^ h / 2 *
        ∑ j ∈ Finset.range k, affineGeomRatio ^ j := hsum
    _ ≤ (3 : ℝ) ^ h / 2 * (1 - affineGeomRatio)⁻¹ := by
      exact mul_le_mul_of_nonneg_left hgeom.le (by positivity)
    _ = (2 + Real.sqrt 3) * (3 : ℝ) ^ h := by
      rw [hconstant]
      ring

end

end Terras

end CollatzEndpointTransport
