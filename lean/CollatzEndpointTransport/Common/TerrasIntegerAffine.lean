/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik
-/
import CollatzEndpointTransport.Common.TerrasAffineIterate

/-!
# Terras Integer Affine

Integer affine correction for the half-Collatz map.

The recursively generated natural number `integerCorrection k n` satisfies

  2^k * T^[k] n = 3^(oddCount k n) * n + integerCorrection k n.

Unlike the normalized real correction, this form can be reduced modulo
`3^s` directly.
-/

namespace CollatzEndpointTransport

namespace Terras

open Nat Finset

/-- Integer correction accumulated through `k` half-Collatz steps. -/
def integerCorrection : ℕ → ℕ → ℕ
  | 0, _ => 0
  | k + 1, n =>
      if parityBit ((T^[k]) n) then
        3 * integerCorrection k n + 2 ^ k
      else
        integerCorrection k n

@[simp]
theorem integerCorrection_zero (n : ℕ) :
    integerCorrection 0 n = 0 := rfl

theorem integerCorrection_succ (k n : ℕ) :
    integerCorrection (k + 1) n =
      if parityBit ((T^[k]) n) then
        3 * integerCorrection k n + 2 ^ k
      else
        integerCorrection k n := rfl

/-- **Exact integer affine iterate identity.** -/
theorem pow_two_mul_iterate_eq_affine (k n : ℕ) :
    2 ^ k * (T^[k]) n =
      3 ^ oddCount k n * n + integerCorrection k n := by
  induction k with
  | zero =>
      simp [integerCorrection, oddCount]
  | succ k ih =>
      rw [integerCorrection_succ, oddCount_succ]
      by_cases hp : parityBit ((T^[k]) n) = true
      · have hmod : (T^[k]) n % 2 = 1 := by
          simpa [parityBit, decide_eq_true_eq] using hp
        have hstep := two_mul_T_of_odd hmod
        rw [Function.iterate_succ_apply', hp]
        simp only [if_true, pow_succ]
        calc
          2 ^ (k + 1) * T ((T^[k]) n)
              = 2 ^ k * (2 * T ((T^[k]) n)) := by ring
          _ = 2 ^ k * (3 * (T^[k]) n + 1) := by rw [hstep]
          _ = 3 * (2 ^ k * (T^[k]) n) + 2 ^ k := by ring
          _ = 3 * (3 ^ oddCount k n * n + integerCorrection k n) +
                2 ^ k := by rw [ih]
          _ = 3 ^ (oddCount k n + 1) * n +
                (3 * integerCorrection k n + 2 ^ k) := by
            rw [pow_succ]
            ring
      · have hpFalse : parityBit ((T^[k]) n) = false := by
          cases h : parityBit ((T^[k]) n) <;> simp_all
        have hmod : (T^[k]) n % 2 = 0 := by
          simp only [parityBit, hpFalse, decide_eq_false_iff_not] at hpFalse
          omega
        have hstep := two_mul_T_of_even hmod
        rw [Function.iterate_succ_apply', hpFalse]
        calc
          2 ^ (k + 1) * T ((T^[k]) n)
              = 2 ^ k * (2 * T ((T^[k]) n)) := by ring
          _ = 2 ^ k * (T^[k]) n := by rw [hstep]
          _ = 3 ^ oddCount k n * n + integerCorrection k n := ih

/-- The integer correction is always smaller than one full affine output
unit at the same odd-count level. -/
theorem integerCorrection_lt_scale (k n : ℕ) :
    integerCorrection k n <
      3 ^ oddCount k n * 2 ^ k := by
  induction k with
  | zero =>
      simp [integerCorrection, oddCount]
  | succ k ih =>
      rw [integerCorrection_succ, oddCount_succ]
      by_cases hp : parityBit ((T^[k]) n) = true
      · rw [hp]
        simp only [if_true, pow_succ]
        have hpow : 0 < 2 ^ k := pow_pos (by norm_num) _
        have hthree : 1 ≤ 3 ^ oddCount k n :=
          one_le_pow₀ (by norm_num)
        nlinarith
      · have hpFalse : parityBit ((T^[k]) n) = false := by
          cases h : parityBit ((T^[k]) n) <;> simp_all
        rw [hpFalse]
        simp only [Bool.false_eq_true, if_false, pow_succ]
        have hscale : 0 < 3 ^ oddCount k n * 2 ^ k := by positivity
        calc
          integerCorrection k n <
              3 ^ oddCount k n * 2 ^ k := ih
          _ < (3 ^ oddCount k n * 2 ^ k) * 2 :=
            lt_mul_of_one_lt_right hscale (by norm_num)
          _ = 3 ^ (oddCount k n + 0) * (2 ^ k * 2) := by
            simp
            ring

/-- A residue below `2^M` stays below its exact multiplicative odd-step
scale after any prefix of the `M`-step window.  At the terminal prefix this
is the sharp canonical-residue endpoint bound

`T^[M] n < 3 ^ oddCount M n`.

The extra factor `2^(M-j)` is the remaining source precision.  Keeping it in
the induction is what makes the estimate uniform in `M`, rather than a
finite-depth calculation. -/
theorem iterate_lt_three_pow_mul_remaining
    {M n j : ℕ} (hjM : j ≤ M) (hn : n < 2 ^ M) :
    (T^[j]) n < 3 ^ oddCount j n * 2 ^ (M - j) := by
  induction j generalizing M n with
  | zero =>
      simpa [oddCount] using hn
  | succ j ih =>
      have hjM' : j ≤ M := by omega
      have hprev := ih hjM' hn
      have hsub : M - j = (M - (j + 1)) + 1 := by omega
      rw [hsub, pow_succ] at hprev
      rw [Function.iterate_succ_apply', oddCount_succ]
      by_cases hp : parityBit ((T^[j]) n) = true
      · have hmod : (T^[j]) n % 2 = 1 := by
          simpa [parityBit, decide_eq_true_eq] using hp
        have hstep := two_mul_T_of_odd hmod
        rw [hp]
        simp only [if_true, pow_succ]
        nlinarith
      · have hpFalse : parityBit ((T^[j]) n) = false := by
          cases h : parityBit ((T^[j]) n) <;> simp_all
        have hmod : (T^[j]) n % 2 = 0 := by
          simp only [parityBit, hpFalse, decide_eq_false_iff_not] at hpFalse
          omega
        have hstep := two_mul_T_of_even hmod
        rw [hpFalse]
        simp only [Bool.false_eq_true, if_false, Nat.add_zero]
        nlinarith

/-- Terminal form of `iterate_lt_three_pow_mul_remaining`. -/
theorem iterate_lt_three_pow_oddCount
    {M n : ℕ} (hn : n < 2 ^ M) :
    (T^[M]) n < 3 ^ oddCount M n := by
  simpa using
    (iterate_lt_three_pow_mul_remaining (M := M) (n := n) (j := M)
      (le_refl M) hn)

/-- Odd counts concatenate exactly across consecutive iterate blocks. -/
theorem oddCount_add (k d n : ℕ) :
    oddCount (k + d) n =
      oddCount k n + oddCount d ((T^[k]) n) := by
  induction d with
  | zero => simp [oddCount]
  | succ d ih =>
      rw [Nat.add_succ, oddCount_succ, ih, oddCount_succ]
      have hcomm :
          (T^[k]) ((T^[d]) n) = (T^[d]) ((T^[k]) n) := by
        rw [← Function.iterate_add_apply,
          ← Function.iterate_add_apply, Nat.add_comm]
      rw [Function.iterate_add_apply]
      rw [hcomm]
      omega

/-- Two ordered inputs with the same odd count and the same `d`-step output
must have started less than one source block-width apart. -/
theorem sub_lt_pow_two_of_equal_iterate_same_oddCount
    {d k n m : ℕ}
    (hnm : n < m)
    (hnk : oddCount d n = k)
    (hmk : oddCount d m = k)
    (hout : (T^[d]) n = (T^[d]) m) :
    m - n < 2 ^ d := by
  have hnAffine := pow_two_mul_iterate_eq_affine d n
  have hmAffine := pow_two_mul_iterate_eq_affine d m
  rw [hnk] at hnAffine
  rw [hmk] at hmAffine
  have hEq :
      3 ^ k * n + integerCorrection d n =
        3 ^ k * m + integerCorrection d m := by
    calc
      3 ^ k * n + integerCorrection d n =
          2 ^ d * (T^[d]) n := hnAffine.symm
      _ = 2 ^ d * (T^[d]) m := by rw [hout]
      _ = 3 ^ k * m + integerCorrection d m := hmAffine
  have hmdecomp : m = n + (m - n) := by omega
  have hEq' :
      3 ^ k * n + integerCorrection d n =
        3 ^ k * n +
          (3 ^ k * (m - n) + integerCorrection d m) := by
    rw [hEq, hmdecomp]
    simp only [Nat.add_sub_cancel_left]
    ring
  have hrest :
      integerCorrection d n =
        3 ^ k * (m - n) + integerCorrection d m :=
    Nat.add_left_cancel hEq'
  have hle : 3 ^ k * (m - n) ≤ integerCorrection d n := by
    omega
  have hcorr : integerCorrection d n < 3 ^ k * 2 ^ d := by
    simpa [hnk] using integerCorrection_lt_scale d n
  have hmul : 3 ^ k * (m - n) < 3 ^ k * 2 ^ d :=
    lt_of_le_of_lt hle hcorr
  exact (Nat.mul_lt_mul_left (pow_pos (by norm_num) k)).mp hmul

/-- Symmetric distance form of
`sub_lt_pow_two_of_equal_iterate_same_oddCount`. -/
theorem dist_lt_pow_two_of_equal_iterate_same_oddCount
    {d k n m : ℕ}
    (hnk : oddCount d n = k)
    (hmk : oddCount d m = k)
    (hout : (T^[d]) n = (T^[d]) m) :
    n.dist m < 2 ^ d := by
  rcases lt_trichotomy n m with hlt | heq | hgt
  · rw [Nat.dist_eq_sub_of_le (Nat.le_of_lt hlt)]
    exact sub_lt_pow_two_of_equal_iterate_same_oddCount
      hlt hnk hmk hout
  · subst m
    simp [Nat.dist, pow_pos (by norm_num : 0 < (2 : ℕ)) d]
  · rw [Nat.dist_comm, Nat.dist_eq_sub_of_le (Nat.le_of_lt hgt)]
    exact sub_lt_pow_two_of_equal_iterate_same_oddCount
      hgt hmk hnk hout.symm

/-- Elementary affine-strip lemma: if the coefficient scale `A` is at
least the target width `D`, translated points with offsets in `[0,A)` can
be `D`-close only at equal or adjacent indices. -/
theorem affine_index_dist_le_one
    {A D q r i j : ℕ}
    (hA : D ≤ A) (hq : q < A) (hr : r < A)
    (hclose : (A * i + q).dist (A * j + r) < D) :
    i.dist j ≤ 1 := by
  by_contra hnot
  have htwo : 2 ≤ i.dist j := by omega
  rcases le_total i j with hij | hji
  · have hgap : i + 2 ≤ j := by
      rw [Nat.dist_eq_sub_of_le hij] at htwo
      omega
    have hsep : A * i + q + A ≤ A * j + r := by
      calc
        A * i + q + A ≤ A * i + A + A := by omega
        _ = A * (i + 2) := by ring
        _ ≤ A * j := Nat.mul_le_mul_left A hgap
        _ ≤ A * j + r := Nat.le_add_right _ _
    have hle : A * i + q ≤ A * j + r :=
      le_trans (Nat.le_add_right _ A) hsep
    have hlower : A ≤ (A * i + q).dist (A * j + r) := by
      rw [Nat.dist_eq_sub_of_le hle]
      exact Nat.le_sub_of_add_le (by
        simpa [add_comm, add_left_comm, add_assoc] using hsep)
    exact (not_lt_of_ge (hA.trans hlower)) hclose
  · have hgap : j + 2 ≤ i := by
      rw [Nat.dist_comm, Nat.dist_eq_sub_of_le hji] at htwo
      omega
    have hsep : A * j + r + A ≤ A * i + q := by
      calc
        A * j + r + A ≤ A * j + A + A := by omega
        _ = A * (j + 2) := by ring
        _ ≤ A * i := Nat.mul_le_mul_left A hgap
        _ ≤ A * i + q := Nat.le_add_right _ _
    have hle : A * j + r ≤ A * i + q :=
      le_trans (Nat.le_add_right _ A) hsep
    have hlower : A ≤ (A * i + q).dist (A * j + r) := by
      rw [Nat.dist_comm, Nat.dist_eq_sub_of_le hle]
      exact Nat.le_sub_of_add_le (by
        simpa [add_comm, add_left_comm, add_assoc] using hsep)
    exact (not_lt_of_ge (hA.trans hlower)) hclose

/-- Equal outputs at a common odd-count level force equal correction
residues modulo the corresponding power of three. -/
theorem correction_modEq_of_equal_output
    {M s n₁ n₂ : ℕ}
    (hs₁ : oddCount M n₁ = s)
    (hs₂ : oddCount M n₂ = s)
    (hout : (T^[M]) n₁ = (T^[M]) n₂) :
    Nat.ModEq (3 ^ s)
      (integerCorrection M n₁) (integerCorrection M n₂) := by
  have h₁ :
      2 ^ M * (T^[M]) n₁ =
        3 ^ s * n₁ + integerCorrection M n₁ := by
    simpa [hs₁] using pow_two_mul_iterate_eq_affine M n₁
  have h₂ :
      2 ^ M * (T^[M]) n₂ =
        3 ^ s * n₂ + integerCorrection M n₂ := by
    simpa [hs₂] using pow_two_mul_iterate_eq_affine M n₂
  have hEq :
      3 ^ s * n₁ + integerCorrection M n₁ =
        3 ^ s * n₂ + integerCorrection M n₂ := by
    calc
      3 ^ s * n₁ + integerCorrection M n₁ =
          2 ^ M * (T^[M]) n₁ := h₁.symm
      _ = 2 ^ M * (T^[M]) n₂ := by rw [hout]
      _ = 3 ^ s * n₂ + integerCorrection M n₂ := h₂
  rw [Nat.ModEq]
  have hmod := congrArg (fun x : ℕ => x % 3 ^ s) hEq
  simpa [Nat.add_mod, Nat.mul_mod] using hmod

end Terras

end CollatzEndpointTransport
