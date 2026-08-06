/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik
-/
import CollatzEndpointTransport.Common.AffineCorrection

/-!
# Terras Affine Iterate

Exact affine iterate identity for the half-Collatz map.

For

  T n = n / 2          when n is even,
  T n = (3n + 1) / 2   when n is odd,

and the correction `affineCorrection k n` defined in
`AffineCorrection.lean`, this file proves

  T^[k](n)
    = (n / 2^k + affineCorrection k n) * 3^(oddCount k n).

The proof is an exact induction.  The two load-bearing recurrences are:

* the odd count adds the current parity digit;
* the next correction is half the old correction plus the new odd-step
  contribution.
-/

namespace CollatzEndpointTransport

namespace Terras

open Nat Finset

/-- `oddCount` is the sum of the parity digits over the corresponding
natural-number range. -/
theorem oddCount_eq_sum_range (H n : ℕ) :
    oddCount H n =
      ∑ i ∈ Finset.range H,
        if parityBit ((T^[i]) n) then 1 else 0 := by
  classical
  unfold oddCount
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  change (∑ i : Fin H,
      if parityBit ((T^[(i : ℕ)]) n) = true then 1 else 0) =
    ∑ i ∈ Finset.range H,
      if parityBit ((T^[i]) n) then 1 else 0
  simpa using
    (Fin.sum_univ_eq_sum_range
      (fun i => if parityBit ((T^[i]) n) = true then (1 : ℕ) else 0) H)

/-- One more iterate adds exactly the current parity digit to the odd count. -/
theorem oddCount_succ (k n : ℕ) :
    oddCount (k + 1) n =
      oddCount k n +
        if parityBit ((T^[k]) n) then 1 else 0 := by
  rw [oddCount_eq_sum_range, oddCount_eq_sum_range,
    Finset.sum_range_succ]

/-- Every old correction summand gains exactly one additional factor of two
in its denominator when the horizon is increased. -/
theorem affineCorrectionTerm_succ_old
    {k n i : ℕ} (hi : i < k) :
    affineCorrectionTerm (k + 1) n i =
      affineCorrectionTerm k n i / 2 := by
  have hsub : k + 1 - i = (k - i) + 1 := by omega
  unfold affineCorrectionTerm
  rw [hsub, pow_succ]
  ring

/-- The final correction summand at horizon `k+1`. -/
theorem affineCorrectionTerm_succ_last (k n : ℕ) :
    affineCorrectionTerm (k + 1) n k =
      parityDigitR n k /
        ((3 : ℝ) ^ oddCount (k + 1) n * 2) := by
  simp [affineCorrectionTerm]

/-- Autonomous one-step recurrence for the affine correction. -/
theorem affineCorrection_succ (k n : ℕ) :
    affineCorrection (k + 1) n =
      affineCorrection k n / 2 +
        parityDigitR n k /
          ((3 : ℝ) ^ oddCount (k + 1) n * 2) := by
  rw [affineCorrection, affineCorrection, Finset.sum_range_succ]
  calc
    (∑ x ∈ Finset.range k, affineCorrectionTerm (k + 1) n x) +
          affineCorrectionTerm (k + 1) n k =
        (∑ x ∈ Finset.range k, affineCorrectionTerm k n x / 2) +
          affineCorrectionTerm (k + 1) n k := by
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      exact affineCorrectionTerm_succ_old (Finset.mem_range.mp hi)
    _ = (∑ x ∈ Finset.range k, affineCorrectionTerm k n x) / 2 +
          parityDigitR n k /
            ((3 : ℝ) ^ oddCount (k + 1) n * 2) := by
      rw [Finset.sum_div, affineCorrectionTerm_succ_last]

/-- Real form of one half-Collatz step, with the parity digit explicit. -/
theorem T_cast_step (x : ℕ) :
    (T x : ℝ) =
      ((3 : ℝ) ^ (if parityBit x then 1 else 0) * x +
        (if parityBit x then 1 else 0)) / 2 := by
  rcases Nat.even_or_odd x with he | ho
  · have hx : x % 2 = 0 := Nat.even_iff.mp he
    have hp : parityBit x = false := by
      simp [parityBit, hx]
    rw [hp]
    norm_num
    have hT := two_mul_T_of_even hx
    have hTR : (2 : ℝ) * T x = x := by exact_mod_cast hT
    linarith
  · have hx : x % 2 = 1 := Nat.odd_iff.mp ho
    have hp : parityBit x = true := by
      simp [parityBit, hx]
    rw [hp]
    norm_num
    have hT := two_mul_T_of_odd hx
    have hTR : (2 : ℝ) * T x = 3 * x + 1 := by exact_mod_cast hT
    linarith

/-- Real one-step recurrence at time `k`. -/
theorem iterate_succ_cast (k n : ℕ) :
    ((T^[k + 1]) n : ℝ) =
      ((3 : ℝ) ^ (if parityBit ((T^[k]) n) then 1 else 0) *
          ((T^[k]) n : ℝ) +
        parityDigitR n k) / 2 := by
  rw [Function.iterate_succ_apply']
  rw [T_cast_step]
  rfl

/-- **Exact affine iterate identity.**

This is the precise Lean form of

`T^k(m) = (m/2^k + r_k(m)) 3^(sum_{i<k} p_i(m))`.
-/
theorem iterate_eq_affineCorrection (k n : ℕ) :
    ((T^[k]) n : ℝ) =
      ((n : ℝ) / (2 : ℝ) ^ k + affineCorrection k n) *
        (3 : ℝ) ^ oddCount k n := by
  induction k with
  | zero =>
      simp [affineCorrection, oddCount]
  | succ k ih =>
      rw [iterate_succ_cast, affineCorrection_succ, oddCount_succ, ih]
      by_cases hp : parityBit ((T^[k]) n) = true
      · simp [hp, parityDigitR, pow_succ]
        field_simp
        ring
      · have hpFalse : parityBit ((T^[k]) n) = false := by
          cases h : parityBit ((T^[k]) n) <;> simp_all
        simp [hpFalse, parityDigitR, pow_succ]
        ring

end Terras

end CollatzEndpointTransport
