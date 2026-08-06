/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik
-/
import CollatzEndpointTransport.QuadraticAppendix.Shared.QuantitativeConeRobustness
import Mathlib.Algebra.Order.Floor.Div

/-!
# Quantitative Base Pullback

Finite-fiber core of the deterministic base-map pullback.

On the dyadic shell `[2^M,2^(M+1))`, write

  A = 3^floor(alpha*M),  B = 2^M,
  Phi(n) = floor(A*n/B).

This file proves:

* `Phi` lands in `[A,2A)`;
* `Phi(n)=y` is exactly the pair of inequalities
  `yB <= An < (y+1)B`;
* every fiber is contained in an explicit ceiling-division interval;
* every fiber has cardinality at most `ceil(B/A)`.

These are the combinatorial facts consumed by Inselmann's Lemma 2.17.  The
remaining layer applies `(C,D)`-density to the bad target values and converts
the resulting dyadic-shell estimate to global density.
-/

namespace CollatzEndpointTransport

namespace QuantitativeDensity

open scoped Real

noncomputable section

/-- Numerator scale `3^floor(alpha*M)` of the deterministic base map. -/
def baseNumeratorScale (alpha : ℝ) (M : ℕ) : ℕ :=
  3 ^ ⌊alpha * M⌋₊

/-- Fiber of the fixed-shell base map over `y`. -/
def baseMapFiber (alpha : ℝ) (M y : ℕ) : Finset ℕ := by
  classical
  exact (dyadicShell M).filter (fun n => baseMapAt alpha M n = y)

theorem baseNumeratorScale_pos (alpha : ℝ) (M : ℕ) :
    0 < baseNumeratorScale alpha M := by
  unfold baseNumeratorScale
  positivity

/-- Ceiling division is subadditive on natural numbers. -/
theorem nat_ceilDiv_add_le {a x y : ℕ} (ha : 0 < a) :
    (x + y) ⌈/⌉ a ≤ x ⌈/⌉ a + y ⌈/⌉ a := by
  rw [ceilDiv_le_iff_le_mul ha]
  have hx : x ≤ a * (x ⌈/⌉ a) :=
    (ceilDiv_le_iff_le_mul ha).1 le_rfl
  have hy : y ≤ a * (y ⌈/⌉ a) :=
    (ceilDiv_le_iff_le_mul ha).1 le_rfl
  calc
    x + y ≤ a * (x ⌈/⌉ a) + a * (y ⌈/⌉ a) :=
      Nat.add_le_add hx hy
    _ = a * (x ⌈/⌉ a + y ⌈/⌉ a) := by
      rw [Nat.mul_add]

/-- Exact quotient dictionary for the base map. -/
theorem baseMapAt_eq_iff
    {alpha : ℝ} {M n y : ℕ} :
    baseMapAt alpha M n = y ↔
      y * 2 ^ M ≤ baseNumeratorScale alpha M * n ∧
      baseNumeratorScale alpha M * n < (y + 1) * 2 ^ M := by
  let A := baseNumeratorScale alpha M
  let B := 2 ^ M
  have hB : 0 < B := by positivity
  have hdef :
      baseMapAt alpha M n = A * n / B := by
    simp [baseMapAt, baseNumeratorScale, A, B]
  rw [hdef]
  constructor
  · intro h
    have hle : y ≤ A * n / B := h.ge
    have hlt : A * n / B < y + 1 := by omega
    exact ⟨(Nat.le_div_iff_mul_le hB).1 hle,
      (Nat.div_lt_iff_lt_mul hB).1 hlt⟩
  · rintro ⟨hle, hlt⟩
    have hyq : y ≤ A * n / B :=
      (Nat.le_div_iff_mul_le hB).2 hle
    have hqy : A * n / B < y + 1 :=
      (Nat.div_lt_iff_lt_mul hB).2 hlt
    omega

/-- The base map sends the `M`-th dyadic shell into
`[3^floor(alpha*M),2*3^floor(alpha*M))`. -/
theorem baseMapAt_range
    {alpha : ℝ} {M n : ℕ} (hn : n ∈ dyadicShell M) :
    baseNumeratorScale alpha M ≤ baseMapAt alpha M n ∧
      baseMapAt alpha M n < 2 * baseNumeratorScale alpha M := by
  let A := baseNumeratorScale alpha M
  let B := 2 ^ M
  have hA : 0 < A := baseNumeratorScale_pos alpha M
  have hB : 0 < B := by positivity
  have hnIco : B ≤ n ∧ n < 2 * B := by
    rw [dyadicShell, Finset.mem_Ico] at hn
    simpa [B, pow_succ, Nat.mul_comm] using hn
  have hdef :
      baseMapAt alpha M n = A * n / B := by
    simp [baseMapAt, baseNumeratorScale, A, B]
  rw [hdef]
  constructor
  · apply (Nat.le_div_iff_mul_le hB).2
    exact Nat.mul_le_mul_left A hnIco.1
  · apply (Nat.div_lt_iff_lt_mul hB).2
    calc
      A * n < A * (2 * B) := (Nat.mul_lt_mul_left hA).2 hnIco.2
      _ = (2 * A) * B := by
        simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]

/-- A base-map fiber lies in its exact ceiling-division interval. -/
theorem baseMapFiber_subset_Ico
    {alpha : ℝ} {M y : ℕ} :
    baseMapFiber alpha M y ⊆
      Finset.Ico
        ((y * 2 ^ M) ⌈/⌉ baseNumeratorScale alpha M)
        (((y + 1) * 2 ^ M) ⌈/⌉ baseNumeratorScale alpha M) := by
  classical
  intro n hn
  rw [baseMapFiber, Finset.mem_filter] at hn
  obtain ⟨_hnShell, hnMap⟩ := hn
  have hA : 0 < baseNumeratorScale alpha M :=
    baseNumeratorScale_pos alpha M
  have hineq := (baseMapAt_eq_iff).1 hnMap
  rw [Finset.mem_Ico]
  constructor
  · exact (ceilDiv_le_iff_le_mul hA).2 hineq.1
  · by_contra hnot
    have hceil :
        ((y + 1) * 2 ^ M) ⌈/⌉ baseNumeratorScale alpha M ≤ n :=
      Nat.le_of_not_gt hnot
    have hmul :
        (y + 1) * 2 ^ M ≤ baseNumeratorScale alpha M * n :=
      (ceilDiv_le_iff_le_mul hA).1 hceil
    omega

/-- Uniform fixed-shell fiber bound. -/
theorem card_baseMapFiber_le
    (alpha : ℝ) (M y : ℕ) :
    (baseMapFiber alpha M y).card ≤
      (2 ^ M) ⌈/⌉ baseNumeratorScale alpha M := by
  let A := baseNumeratorScale alpha M
  let B := 2 ^ M
  let lo := (y * B) ⌈/⌉ A
  let hi := ((y + 1) * B) ⌈/⌉ A
  have hsub :
      baseMapFiber alpha M y ⊆ Finset.Ico lo hi := by
    simpa [A, B, lo, hi] using
      (baseMapFiber_subset_Ico (alpha := alpha) (M := M) (y := y))
  have hhi : hi ≤ lo + (B ⌈/⌉ A) := by
    have hA : 0 < A := baseNumeratorScale_pos alpha M
    have hadd := nat_ceilDiv_add_le
      (a := A) (x := y * B) (y := B) hA
    simpa [lo, hi, Nat.add_mul] using hadd
  calc
    (baseMapFiber alpha M y).card ≤ (Finset.Ico lo hi).card :=
      Finset.card_le_card hsub
    _ = hi - lo := Nat.card_Ico lo hi
    _ ≤ B ⌈/⌉ A := by omega
    _ = (2 ^ M) ⌈/⌉ baseNumeratorScale alpha M := rfl

/-- Union of all shell fibers whose base-map target misses `S`. -/
def baseMapBadFiberUnion
    (S : Set ℕ) (alpha : ℝ) (M : ℕ) : Finset ℕ := by
  classical
  exact (badPrefix S (2 * baseNumeratorScale alpha M)).biUnion
    (baseMapFiber alpha M)

/-- Every failure of the variable-scale base pullback on shell `M` lies in
one of the explicit bad target fibers. -/
theorem shellBad_basePullback_subset_badFiberUnion
    {S : Set ℕ} {alpha : ℝ} {M : ℕ} :
    shellBad (basePullback alpha S) M ⊆
      baseMapBadFiberUnion S alpha M := by
  classical
  intro n hn
  rw [shellBad, Finset.mem_filter] at hn
  obtain ⟨hnShell, hnBad⟩ := hn
  have hlog : Nat.log 2 n = M :=
    Terras.log_two_eq_of_mem_dyadicShell hnShell
  have hyBad :
      baseMapAt alpha M n ∉ S := by
    simpa [basePullback, baseMap, hlog] using hnBad
  have hyrange := baseMapAt_range
    (alpha := alpha) (M := M) (n := n) hnShell
  have hyPos : 0 < baseMapAt alpha M n :=
    lt_of_lt_of_le (baseNumeratorScale_pos alpha M) hyrange.1
  have hyPrefix :
      baseMapAt alpha M n ∈
        badPrefix S (2 * baseNumeratorScale alpha M) := by
    rw [badPrefix, Finset.mem_filter, positivePrefix, Finset.mem_Icc]
    exact ⟨⟨hyPos, hyrange.2.le⟩, hyBad⟩
  rw [baseMapBadFiberUnion, Finset.mem_biUnion]
  refine ⟨baseMapAt alpha M n, hyPrefix, ?_⟩
  rw [baseMapFiber, Finset.mem_filter]
  exact ⟨hnShell, rfl⟩

/-- Complete finite-fiber count for the deterministic base pullback. -/
theorem card_shellBad_basePullback_le
    (S : Set ℕ) (alpha : ℝ) (M : ℕ) :
    (shellBad (basePullback alpha S) M).card ≤
      (badPrefix S (2 * baseNumeratorScale alpha M)).card *
        ((2 ^ M) ⌈/⌉ baseNumeratorScale alpha M) := by
  classical
  calc
    (shellBad (basePullback alpha S) M).card
        ≤ (baseMapBadFiberUnion S alpha M).card :=
      Finset.card_le_card shellBad_basePullback_subset_badFiberUnion
    _ ≤ ∑ y ∈ badPrefix S (2 * baseNumeratorScale alpha M),
          (baseMapFiber alpha M y).card := by
      exact Finset.card_biUnion_le
    _ ≤ ∑ _y ∈ badPrefix S (2 * baseNumeratorScale alpha M),
          ((2 ^ M) ⌈/⌉ baseNumeratorScale alpha M) := by
      apply Finset.sum_le_sum
      intro y _
      exact card_baseMapFiber_le alpha M y
    _ = (badPrefix S (2 * baseNumeratorScale alpha M)).card *
          ((2 ^ M) ⌈/⌉ baseNumeratorScale alpha M) := by
      simp

end

end QuantitativeDensity

end CollatzEndpointTransport
