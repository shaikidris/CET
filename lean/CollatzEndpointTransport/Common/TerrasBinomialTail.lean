/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik
-/
import CollatzEndpointTransport.Common.TerrasParityBijection

/-!
# Terras Binomial Tail

Elementary binomial-tail bounds for the Terras parity bijection.

The core estimate is the generating-function inequality

  x^K * sum_{k <= K} choose(H, k) <= (1 + x)^H

for `0 <= x <= 1` and `K <= H`.  It is a finite combinatorial theorem:
no probability space, independence assumption, or asymptotic estimate is
used.  The final declarations transport it to the exact set of Collatz
residues whose first `H` parity bits contain at most `K` odd steps.

The final layer chooses `x = exp (-4t)` and uses Mathlib's
`Real.cosh_le_exp_half_sq` to obtain the explicit Hoeffding exponent
`2^H * exp (-2 t^2 H)`.
-/

namespace CollatzEndpointTransport

namespace Terras

open Nat Finset

/-- The lower binomial tail through weight `K`. -/
def lowerBinomialSum (H K : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (K + 1), H.choose k

/-- The weighted binomial generating function is exactly `(1 + x)^H`. -/
theorem weightedBinomialSum_eq (H : ℕ) (x : ℝ) :
    (∑ k ∈ Finset.range (H + 1), (H.choose k : ℝ) * x ^ k) = (1 + x) ^ H := by
  simpa [add_comm, mul_comm] using (add_pow x 1 H).symm

/-- The elementary lower-tail generating-function bound. -/
theorem pow_mul_lowerBinomialSum_le
    {H K : ℕ} {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hKH : K ≤ H) :
    x ^ K * (lowerBinomialSum H K : ℝ) ≤ (1 + x) ^ H := by
  calc
    x ^ K * (lowerBinomialSum H K : ℝ) =
        ∑ k ∈ Finset.range (K + 1), x ^ K * (H.choose k : ℝ) := by
          simp [lowerBinomialSum, Nat.cast_sum, Finset.mul_sum]
    _ ≤ ∑ k ∈ Finset.range (K + 1), (H.choose k : ℝ) * x ^ k := by
      apply Finset.sum_le_sum
      intro k hk
      have hkK : k ≤ K := by
        exact Nat.le_of_lt_succ (Finset.mem_range.mp hk)
      have hpow : x ^ K ≤ x ^ k :=
        pow_le_pow_of_le_one hx0 hx1 hkK
      simpa [mul_comm] using
        mul_le_mul_of_nonneg_left hpow (Nat.cast_nonneg (H.choose k))
    _ ≤ ∑ k ∈ Finset.range (H + 1), (H.choose k : ℝ) * x ^ k := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.range_mono (Nat.succ_le_succ hKH))
      intro k _ _
      positivity
    _ = (1 + x) ^ H := weightedBinomialSum_eq H x

/-- Division form of `pow_mul_lowerBinomialSum_le`, valid for `x > 0`. -/
theorem lowerBinomialSum_le_div
    {H K : ℕ} {x : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1) (hKH : K ≤ H) :
    (lowerBinomialSum H K : ℝ) ≤ (1 + x) ^ H / x ^ K := by
  apply (le_div_iff₀ (pow_pos hx0 K)).2
  simpa [mul_comm] using
    pow_mul_lowerBinomialSum_le (H := H) (K := K) (x := x) hx0.le hx1 hKH

/-- The scalar inequality behind the explicit Hoeffding optimization. -/
theorem one_add_exp_neg_four_mul_le (t : ℝ) :
    1 + Real.exp (-4 * t) ≤ 2 * Real.exp (-2 * t + 2 * t ^ 2) := by
  have hcosh := Real.cosh_le_exp_half_sq (2 * t)
  have hmul :
      2 * Real.exp (-2 * t) * Real.cosh (2 * t) ≤
        2 * Real.exp (-2 * t) * Real.exp ((2 * t) ^ 2 / 2) :=
    mul_le_mul_of_nonneg_left hcosh (by positivity)
  calc
    1 + Real.exp (-4 * t) =
        2 * Real.exp (-2 * t) * Real.cosh (2 * t) := by
      rw [Real.cosh_eq]
      have hcancel :
          Real.exp (-2 * t) * Real.exp (2 * t) = 1 := by
        rw [← Real.exp_add]
        rw [show -2 * t + 2 * t = 0 by ring, Real.exp_zero]
      have hdouble :
          Real.exp (-2 * t) * Real.exp (-(2 * t)) =
            Real.exp (-4 * t) := by
        rw [← Real.exp_add]
        congr 1
        ring
      rw [show 2 * Real.exp (-2 * t) *
            ((Real.exp (2 * t) + Real.exp (-(2 * t))) / 2) =
          Real.exp (-2 * t) * Real.exp (2 * t) +
            Real.exp (-2 * t) * Real.exp (-(2 * t)) by ring]
      rw [hcancel, hdouble]
    _ ≤ 2 * Real.exp (-2 * t) * Real.exp ((2 * t) ^ 2 / 2) := hmul
    _ = 2 * Real.exp (-2 * t + 2 * t ^ 2) := by
      rw [mul_assoc, ← Real.exp_add]
      congr 2
      ring

/-- Explicit lower binomial-tail estimate with Hoeffding exponent `2t^2H`. -/
theorem lowerBinomialSum_le_hoeffding
    {H K : ℕ} {t : ℝ} (ht : 0 ≤ t)
    (hcut : (K : ℝ) ≤ (1 / 2 - t) * H) :
    (lowerBinomialSum H K : ℝ) ≤
      (2 : ℝ) ^ H * Real.exp (-2 * t ^ 2 * H) := by
  have hKHreal : (K : ℝ) ≤ H := by
    calc
      (K : ℝ) ≤ (1 / 2 - t) * H := hcut
      _ ≤ H := by
        have hH : (0 : ℝ) ≤ H := Nat.cast_nonneg H
        nlinarith
  have hKH : K ≤ H := by exact_mod_cast hKHreal
  let x : ℝ := Real.exp (-4 * t)
  have hx0 : 0 < x := by
    dsimp [x]
    positivity
  have hx1 : x ≤ 1 := by
    dsimp [x]
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (by nlinarith)
  have htail :
      x ^ K * (lowerBinomialSum H K : ℝ) ≤ (1 + x) ^ H :=
    pow_mul_lowerBinomialSum_le hx0.le hx1 hKH
  let z : ℝ := -2 * t + 2 * t ^ 2
  have hbase : 1 + x ≤ 2 * Real.exp z := by
    dsimp [x, z]
    exact one_add_exp_neg_four_mul_le t
  have hpow : (1 + x) ^ H ≤ (2 * Real.exp z) ^ H := by
    exact pow_le_pow_left₀ (by positivity) hbase H
  have hnonpos : -4 * t ≤ 0 := by nlinarith
  have hcutScaled :
      (-4 * t) * ((1 / 2 - t) * H) ≤ (-4 * t) * K :=
    mul_le_mul_of_nonpos_left hcut hnonpos
  have harg :
      (H : ℝ) * z ≤ -2 * t ^ 2 * H + (K : ℝ) * (-4 * t) := by
    dsimp [z]
    nlinarith
  have hexp :
      Real.exp ((H : ℝ) * z) ≤
        Real.exp (-2 * t ^ 2 * H + (K : ℝ) * (-4 * t)) :=
    Real.exp_le_exp.mpr harg
  have htarget :
      (1 + x) ^ H ≤
        ((2 : ℝ) ^ H * Real.exp (-2 * t ^ 2 * H)) * x ^ K := by
    calc
      (1 + x) ^ H ≤ (2 * Real.exp z) ^ H := hpow
      _ = (2 : ℝ) ^ H * Real.exp ((H : ℝ) * z) := by
        rw [mul_pow, ← Real.exp_nat_mul]
      _ ≤ (2 : ℝ) ^ H *
          Real.exp (-2 * t ^ 2 * H + (K : ℝ) * (-4 * t)) :=
        mul_le_mul_of_nonneg_left hexp (by positivity)
      _ = ((2 : ℝ) ^ H * Real.exp (-2 * t ^ 2 * H)) * x ^ K := by
        dsimp [x]
        rw [← Real.exp_nat_mul, Real.exp_add]
        ring
  have hmul :
      x ^ K * (lowerBinomialSum H K : ℝ) ≤
        ((2 : ℝ) ^ H * Real.exp (-2 * t ^ 2 * H)) * x ^ K :=
    htail.trans htarget
  exact (mul_le_mul_right (pow_pos hx0 K)).mp (by
    simpa [mul_comm] using hmul)

/-- Exact count of residues whose first `H` Collatz parity bits contain at
most `K` odd steps. -/
theorem card_residues_with_oddCount_le (H K : ℕ) :
    (Finset.univ.filter
      (fun n : Fin (2 ^ H) => oddCount H (n : ℕ) ≤ K)).card =
      lowerBinomialSum H K := by
  classical
  let s : Finset (Fin (2 ^ H)) :=
    Finset.univ.filter (fun n => oddCount H (n : ℕ) ≤ K)
  have hmap :
      ∀ n ∈ s, oddCount H (n : ℕ) ∈ Finset.range (K + 1) := by
    intro n hn
    have hnK : oddCount H (n : ℕ) ≤ K := by
      simpa [s] using hn
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le hnK)
  calc
    (Finset.univ.filter
      (fun n : Fin (2 ^ H) => oddCount H (n : ℕ) ≤ K)).card = s.card := by
        rfl
    _ = ∑ k ∈ Finset.range (K + 1),
        (s.filter (fun n : Fin (2 ^ H) => oddCount H (n : ℕ) = k)).card :=
      Finset.card_eq_sum_card_fiberwise hmap
    _ = ∑ k ∈ Finset.range (K + 1), H.choose k := by
      apply Finset.sum_congr rfl
      intro k hk
      have hkK : k ≤ K := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
      have hfilter :
          s.filter (fun n : Fin (2 ^ H) => oddCount H (n : ℕ) = k) =
            Finset.univ.filter
              (fun n : Fin (2 ^ H) => oddCount H (n : ℕ) = k) := by
        ext n
        simp only [s, Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · exact And.right
        · intro hweight
          exact ⟨hweight.le.trans hkK, hweight⟩
      rw [hfilter, card_residues_with_oddCount]
    _ = lowerBinomialSum H K := rfl

/-- The exact Collatz residue tail satisfies the same weighted bound as the
abstract binomial tail. -/
theorem pow_mul_card_residues_with_oddCount_le
    {H K : ℕ} {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hKH : K ≤ H) :
    x ^ K *
        ((Finset.univ.filter
          (fun n : Fin (2 ^ H) => oddCount H (n : ℕ) ≤ K)).card : ℝ) ≤
      (1 + x) ^ H := by
  rw [card_residues_with_oddCount_le]
  exact pow_mul_lowerBinomialSum_le hx0 hx1 hKH

/-- Division form of the exact Collatz residue tail bound. -/
theorem card_residues_with_oddCount_le_div
    {H K : ℕ} {x : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1) (hKH : K ≤ H) :
    ((Finset.univ.filter
      (fun n : Fin (2 ^ H) => oddCount H (n : ℕ) ≤ K)).card : ℝ) ≤
      (1 + x) ^ H / x ^ K := by
  rw [card_residues_with_oddCount_le]
  exact lowerBinomialSum_le_div hx0 hx1 hKH

/-- Explicit Hoeffding bound for the lower Collatz parity tail. -/
theorem card_residues_with_oddCount_le_hoeffding
    {H K : ℕ} {t : ℝ} (ht : 0 ≤ t)
    (hcut : (K : ℝ) ≤ (1 / 2 - t) * H) :
    ((Finset.univ.filter
      (fun n : Fin (2 ^ H) => oddCount H (n : ℕ) ≤ K)).card : ℝ) ≤
      (2 : ℝ) ^ H * Real.exp (-2 * t ^ 2 * H) := by
  rw [card_residues_with_oddCount_le]
  exact lowerBinomialSum_le_hoeffding ht hcut

/-- Normalized lower-tail proportion among all `2^H` residues. -/
theorem card_residues_with_oddCount_le_div_pow_le_exp
    {H K : ℕ} {t : ℝ} (ht : 0 ≤ t)
    (hcut : (K : ℝ) ≤ (1 / 2 - t) * H) :
    ((Finset.univ.filter
        (fun n : Fin (2 ^ H) => oddCount H (n : ℕ) ≤ K)).card : ℝ) /
        (2 : ℝ) ^ H ≤
      Real.exp (-2 * t ^ 2 * H) := by
  apply (div_le_iff₀ (pow_pos (by norm_num) H)).2
  simpa [mul_comm] using card_residues_with_oddCount_le_hoeffding ht hcut

/-- The odd-step count cannot exceed the length of the parity word. -/
theorem oddCount_le_length (H n : ℕ) : oddCount H n ≤ H := by
  unfold oddCount
  calc
    (Finset.univ.filter
      (fun i : Fin H => parityVec H n i = true)).card ≤
        (Finset.univ : Finset (Fin H)).card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    _ = H := by simp

/-- Exact count of the symmetric upper tail: at least `H - K` odd steps. -/
theorem card_residues_with_oddCount_ge_sub
    (H K : ℕ) (hKH : K ≤ H) :
    (Finset.univ.filter
      (fun n : Fin (2 ^ H) => H - K ≤ oddCount H (n : ℕ))).card =
      lowerBinomialSum H K := by
  classical
  let s : Finset (Fin (2 ^ H)) :=
    Finset.univ.filter (fun n => H - K ≤ oddCount H (n : ℕ))
  have hmap :
      ∀ n ∈ s, H - oddCount H (n : ℕ) ∈ Finset.range (K + 1) := by
    intro n hn
    have hge : H - K ≤ oddCount H (n : ℕ) := by
      simpa [s] using hn
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (by omega))
  calc
    (Finset.univ.filter
      (fun n : Fin (2 ^ H) => H - K ≤ oddCount H (n : ℕ))).card = s.card := by
        rfl
    _ = ∑ j ∈ Finset.range (K + 1),
        (s.filter
          (fun n : Fin (2 ^ H) => H - oddCount H (n : ℕ) = j)).card :=
      Finset.card_eq_sum_card_fiberwise hmap
    _ = ∑ j ∈ Finset.range (K + 1), H.choose j := by
      apply Finset.sum_congr rfl
      intro j hj
      have hjK : j ≤ K := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
      have hjH : j ≤ H := hjK.trans hKH
      have hfilter :
          s.filter
              (fun n : Fin (2 ^ H) => H - oddCount H (n : ℕ) = j) =
            Finset.univ.filter
              (fun n : Fin (2 ^ H) => oddCount H (n : ℕ) = H - j) := by
        ext n
        have hodd : oddCount H (n : ℕ) ≤ H :=
          oddCount_le_length H (n : ℕ)
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · rintro ⟨hge, hdefect⟩
          omega
        · intro hweight
          constructor
          · show n ∈ s
            simp only [s, Finset.mem_filter, Finset.mem_univ, true_and]
            calc
                H - K ≤ H - j := Nat.sub_le_sub_left hjK H
                _ = oddCount H (n : ℕ) := hweight.symm
          · rw [hweight, Nat.sub_sub_self hjH]
      rw [hfilter, card_residues_with_oddCount, Nat.choose_symm hjH]
    _ = lowerBinomialSum H K := rfl

/-- The symmetric upper Collatz residue tail satisfies the same weighted
generating-function bound. -/
theorem pow_mul_card_residues_with_oddCount_ge_sub
    {H K : ℕ} {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hKH : K ≤ H) :
    x ^ K *
        ((Finset.univ.filter
          (fun n : Fin (2 ^ H) => H - K ≤ oddCount H (n : ℕ))).card : ℝ) ≤
      (1 + x) ^ H := by
  rw [card_residues_with_oddCount_ge_sub H K hKH]
  exact pow_mul_lowerBinomialSum_le hx0 hx1 hKH

/-- Division form of the symmetric upper Collatz residue tail bound. -/
theorem card_residues_with_oddCount_ge_sub_le_div
    {H K : ℕ} {x : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1) (hKH : K ≤ H) :
    ((Finset.univ.filter
      (fun n : Fin (2 ^ H) => H - K ≤ oddCount H (n : ℕ))).card : ℝ) ≤
      (1 + x) ^ H / x ^ K := by
  rw [card_residues_with_oddCount_ge_sub H K hKH]
  exact lowerBinomialSum_le_div hx0 hx1 hKH

/-- Explicit Hoeffding bound for the symmetric upper Collatz parity tail. -/
theorem card_residues_with_oddCount_ge_sub_le_hoeffding
    {H K : ℕ} {t : ℝ} (ht : 0 ≤ t)
    (hcut : (K : ℝ) ≤ (1 / 2 - t) * H) :
    ((Finset.univ.filter
      (fun n : Fin (2 ^ H) => H - K ≤ oddCount H (n : ℕ))).card : ℝ) ≤
      (2 : ℝ) ^ H * Real.exp (-2 * t ^ 2 * H) := by
  have hKHreal : (K : ℝ) ≤ H := by
    calc
      (K : ℝ) ≤ (1 / 2 - t) * H := hcut
      _ ≤ H := by
        have hH : (0 : ℝ) ≤ H := Nat.cast_nonneg H
        nlinarith
  have hKH : K ≤ H := by exact_mod_cast hKHreal
  rw [card_residues_with_oddCount_ge_sub H K hKH]
  exact lowerBinomialSum_le_hoeffding ht hcut

/-- Normalized symmetric upper-tail proportion among all `2^H` residues. -/
theorem card_residues_with_oddCount_ge_sub_div_pow_le_exp
    {H K : ℕ} {t : ℝ} (ht : 0 ≤ t)
    (hcut : (K : ℝ) ≤ (1 / 2 - t) * H) :
    ((Finset.univ.filter
        (fun n : Fin (2 ^ H) => H - K ≤ oddCount H (n : ℕ))).card : ℝ) /
        (2 : ℝ) ^ H ≤
      Real.exp (-2 * t ^ 2 * H) := by
  apply (div_le_iff₀ (pow_pos (by norm_num) H)).2
  simpa [mul_comm] using
    card_residues_with_oddCount_ge_sub_le_hoeffding ht hcut

end Terras

end CollatzEndpointTransport
