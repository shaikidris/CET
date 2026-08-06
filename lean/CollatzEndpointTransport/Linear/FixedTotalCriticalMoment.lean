/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik
-/
import CollatzEndpointTransport.Linear.FixedTotalQuotientOrder
import CollatzEndpointTransport.Linear.FixedTotalFirstMoment
import Mathlib.Algebra.Order.Chebyshev

/-!
# Fixed Total Critical Moment

Critical fixed-total moment.

This file combines the quotient-order estimate with the exact aggregate
first moment.  Everything is a finite `Finset` sum.  The resulting critical
average is bounded linearly in the total valuation.
-/

set_option maxHeartbeats 2000000

namespace CollatzEndpointTransport

namespace FixedTotal

open Nat Finset

noncomputable section

local instance compositionDecidableEq (N : ℕ) :
    DecidableEq (Composition N) :=
  Classical.decEq _

/-- Compositions of `N` having exactly `s` parts, as a finite subset of all
compositions. -/
def fixedSet (N s : ℕ) : Finset (Composition N) :=
  (Finset.univ : Finset (Composition N)).filter fun c => c.length = s

theorem syracuseNumerator_injOn_fixedSet
    (N s : ℕ) :
    Set.InjOn syracuseNumerator (↑(fixedSet N s) : Set (Composition N)) := by
  intro c hc d hd hnum
  exact syracuseNumerator_injective_on_length
    (Finset.mem_filter.mp hc).2
    (Finset.mem_filter.mp hd).2
    hnum

/-- Cardinality of one numerator residue fiber. -/
def fixedFiberCard (N s : ℕ) (a : Fin (3 ^ s)) : ℕ :=
  (residueFiber (fixedSet N s) syracuseNumerator (3 ^ s) a).card

/-- The unnormalised critical residue sum at fixed `(N,s)`. -/
def fixedCriticalNumerator (N s : ℕ) : ℝ :=
  Real.sqrt (3 ^ s) *
    ∑ a : Fin (3 ^ s),
      (fixedFiberCard N s a : ℝ) * Real.sqrt (fixedFiberCard N s a)

/-- The contribution after cancelling one factor of the fixed-level
cardinality.  Empty levels contribute zero because real division is total. -/
def fixedCriticalContribution (N s : ℕ) : ℝ :=
  fixedCriticalNumerator N s / Real.sqrt (fixedSet N s).card

/-- Critical average over every nonempty length level. -/
def fixedCriticalAverage (N : ℕ) : ℝ :=
  (∑ s ∈ Finset.Icc 1 N, fixedCriticalContribution N s) /
    (2 ^ (N - 1) : ℝ)

theorem fixedCriticalNumerator_le
    (N s : ℕ) :
    fixedCriticalNumerator N s ≤
      4 * ∑ c ∈ fixedSet N s,
        Real.sqrt (3 ^ s + syracuseNumerator c) := by
  have hm : 0 < 3 ^ s := pow_pos (by norm_num) _
  simpa [fixedCriticalNumerator, fixedFiberCard] using
    residueFibers_critical_bound
      (fixedSet N s) syracuseNumerator (3 ^ s) hm
      (syracuseNumerator_injOn_fixedSet N s)

/-- Finite Cauchy--Schwarz in square-root form. -/
theorem sum_sqrt_div_sqrt_card_le_sqrt_sum
    {α : Type*} [DecidableEq α]
    (W : Finset α) (q : α → ℕ) :
    (∑ x ∈ W, Real.sqrt (q x)) / Real.sqrt W.card ≤
      Real.sqrt (∑ x ∈ W, q x) := by
  by_cases hW : W = ∅
  · simp [hW]
  have hcard : 0 < W.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hW)
  have hcardR : (0 : ℝ) < W.card := by exact_mod_cast hcard
  have hsqrtCard : 0 < Real.sqrt (W.card : ℝ) :=
    Real.sqrt_pos.mpr hcardR
  have hcs :
      (∑ x ∈ W, Real.sqrt (q x)) ^ 2 ≤
        (W.card : ℝ) * ∑ x ∈ W, (q x : ℝ) := by
    have hraw :=
      (sq_sum_le_card_mul_sum_sq
        (s := W) (f := fun x => Real.sqrt (q x)))
    calc
      (∑ x ∈ W, Real.sqrt (q x)) ^ 2
          ≤ (W.card : ℝ) *
              ∑ x ∈ W, (Real.sqrt (q x)) ^ 2 := hraw
      _ = (W.card : ℝ) * ∑ x ∈ W, (q x : ℝ) := by
        apply congrArg (fun z : ℝ => (W.card : ℝ) * z)
        apply Finset.sum_congr rfl
        intro x hx
        exact Real.sq_sqrt (by positivity)
  have hsumNonneg : 0 ≤ ∑ x ∈ W, (q x : ℝ) := by positivity
  have hsumSqrtNonneg :
      0 ≤ ∑ x ∈ W, Real.sqrt (q x) := by positivity
  apply (div_le_iff₀ hsqrtCard).2
  rw [← Real.sqrt_mul hsumNonneg]
  apply (Real.le_sqrt hsumSqrtNonneg
    (mul_nonneg hsumNonneg (by positivity))).2
  nlinarith

theorem fixedCriticalContribution_le
    (N s : ℕ) :
    fixedCriticalContribution N s ≤
      4 * Real.sqrt
        (∑ c ∈ fixedSet N s, (3 ^ s + syracuseNumerator c)) := by
  by_cases hcard : (fixedSet N s).card = 0
  · have hset : fixedSet N s = ∅ := Finset.card_eq_zero.mp hcard
    simp [fixedCriticalContribution, fixedCriticalNumerator,
      fixedFiberCard, hset, residueFiber]
  have hsqrtCard :
      0 < Real.sqrt ((fixedSet N s).card : ℝ) := by
    apply Real.sqrt_pos.mpr
    exact_mod_cast (Nat.pos_of_ne_zero hcard)
  calc
    fixedCriticalContribution N s
        ≤ (4 * ∑ c ∈ fixedSet N s,
            Real.sqrt (3 ^ s + syracuseNumerator c)) /
            Real.sqrt (fixedSet N s).card := by
      exact div_le_div_of_nonneg_right
        (fixedCriticalNumerator_le N s) (Real.sqrt_nonneg _)
    _ = 4 * ((∑ c ∈ fixedSet N s,
            Real.sqrt (3 ^ s + syracuseNumerator c)) /
            Real.sqrt (fixedSet N s).card) := by
      ring
    _ ≤ 4 * Real.sqrt
        (∑ c ∈ fixedSet N s, (3 ^ s + syracuseNumerator c)) := by
      have hsqrt :=
        sum_sqrt_div_sqrt_card_le_sqrt_sum
          (fixedSet N s) (fun c => 3 ^ s + syracuseNumerator c)
      have hmul :=
        mul_le_mul_of_nonneg_left hsqrt (by norm_num : (0 : ℝ) ≤ 4)
      convert hmul using 1 <;>
        norm_num [Nat.cast_add, Nat.cast_pow]

theorem sum_fixedSet
    (N : ℕ) (hN : 0 < N) (f : Composition N → ℕ) :
    (∑ s ∈ Finset.Icc 1 N, ∑ c ∈ fixedSet N s, f c) =
      ∑ c : Composition N, f c := by
  have hmap :
      ∀ c ∈ (Finset.univ : Finset (Composition N)),
        c.length ∈ Finset.Icc 1 N := by
    intro c hc
    exact Finset.mem_Icc.mpr
      ⟨c.length_pos_of_pos hN, c.length_le⟩
  simpa [fixedSet] using
    (Finset.sum_fiberwise_of_maps_to
      (s := (Finset.univ : Finset (Composition N)))
      (t := Finset.Icc 1 N)
      (g := fun c : Composition N => c.length)
      hmap f)

theorem aggregateQ_le
    (N : ℕ) (hN : 0 < N) :
    (∑ s ∈ Finset.Icc 1 N,
        ∑ c ∈ fixedSet N s, (3 ^ s + syracuseNumerator c)) ≤
      4 * N * 4 ^ (N - 1) := by
  have hpartition :
      (∑ s ∈ Finset.Icc 1 N,
          ∑ c ∈ fixedSet N s, (3 ^ s + syracuseNumerator c)) =
        ∑ c : Composition N, (3 ^ c.length + syracuseNumerator c) := by
    have hmap :
        ∀ c ∈ (Finset.univ : Finset (Composition N)),
          c.length ∈ Finset.Icc 1 N := by
      intro c hc
      exact Finset.mem_Icc.mpr
        ⟨c.length_pos_of_pos hN, c.length_le⟩
    calc
      (∑ s ∈ Finset.Icc 1 N,
          ∑ c ∈ fixedSet N s, (3 ^ s + syracuseNumerator c)) =
          ∑ s ∈ Finset.Icc 1 N,
            ∑ c ∈ fixedSet N s,
              (3 ^ c.length + syracuseNumerator c) := by
        apply Finset.sum_congr rfl
        intro s hs
        apply Finset.sum_congr rfl
        intro c hc
        have hlen : c.length = s := (Finset.mem_filter.mp hc).2
        rw [hlen]
      _ = ∑ c : Composition N,
          (3 ^ c.length + syracuseNumerator c) := by
        simpa [fixedSet] using
          (Finset.sum_fiberwise_of_maps_to
            (s := (Finset.univ : Finset (Composition N)))
            (t := Finset.Icc 1 N)
            (g := fun c : Composition N => c.length)
            hmap (fun c => 3 ^ c.length + syracuseNumerator c))
  rw [hpartition]
  let Q := ∑ c : Composition N, (3 ^ c.length + syracuseNumerator c)
  have hExact : 2 * Q = (N + 7) * 4 ^ (N - 1) := by
    exact fixedTotal_firstMoment_exact N hN
  have hN7 : N + 7 ≤ 8 * N := by omega
  have hscaled :=
    Nat.mul_le_mul_right (4 ^ (N - 1)) hN7
  have htwo : 2 * Q ≤ 2 * (4 * N * 4 ^ (N - 1)) := by
    rw [hExact]
    nlinarith
  exact Nat.le_of_mul_le_mul_left htwo (by norm_num)

/-- **Critical fixed-total theorem.**

The averaged normalized residue moment grows at most linearly.  The constant
`8` reflects the deliberately robust quotient-order factor `4`. -/
theorem fixedCriticalAverage_le
    (N : ℕ) (hN : 0 < N) :
    fixedCriticalAverage N ≤ 8 * N := by
  let I := Finset.Icc 1 N
  let Y : ℕ → ℕ := fun s =>
    ∑ c ∈ fixedSet N s, (3 ^ s + syracuseNumerator c)
  have hterm :
      ∑ s ∈ I, fixedCriticalContribution N s ≤
        4 * ∑ s ∈ I, Real.sqrt (Y s) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro s hs
    simpa [Y] using fixedCriticalContribution_le N s
  have hcardI : I.card = N := by
    simp [I, Nat.card_Icc]
  have hcs :
      (∑ s ∈ I, Real.sqrt (Y s)) ^ 2 ≤
        (N : ℝ) * ∑ s ∈ I, (Y s : ℝ) := by
    have hraw :=
      (sq_sum_le_card_mul_sum_sq
        (s := I) (f := fun s => Real.sqrt (Y s)))
    rw [hcardI] at hraw
    calc
      (∑ s ∈ I, Real.sqrt (Y s)) ^ 2
          ≤ (N : ℝ) * ∑ s ∈ I, (Real.sqrt (Y s)) ^ 2 := hraw
      _ = (N : ℝ) * ∑ s ∈ I, (Y s : ℝ) := by
        apply congrArg (fun z : ℝ => (N : ℝ) * z)
        apply Finset.sum_congr rfl
        intro s hs
        exact Real.sq_sqrt (by positivity)
  have hY :
      ∑ s ∈ I, Y s ≤ 4 * N * 4 ^ (N - 1) := by
    exact aggregateQ_le N hN
  have hYReal :
      (∑ s ∈ I, (Y s : ℝ)) ≤
        (4 * N * 4 ^ (N - 1) : ℕ) := by
    exact_mod_cast hY
  have hsumSqrt :
      ∑ s ∈ I, Real.sqrt (Y s) ≤
        2 * N * Real.sqrt (4 ^ (N - 1) : ℕ) := by
    have hnonneg :
        0 ≤ ∑ s ∈ I, Real.sqrt (Y s) := by positivity
    have hrhsNonneg :
        0 ≤ 2 * (N : ℝ) * Real.sqrt (4 ^ (N - 1) : ℕ) := by
      positivity
    have hsq :
        (∑ s ∈ I, Real.sqrt (Y s)) ^ 2 ≤
          (2 * N * Real.sqrt (4 ^ (N - 1) : ℕ)) ^ 2 := by
      calc
        (∑ s ∈ I, Real.sqrt (Y s)) ^ 2
            ≤ (N : ℝ) * ∑ s ∈ I, (Y s : ℝ) := hcs
        _ ≤ (N : ℝ) * (4 * N * 4 ^ (N - 1) : ℕ) := by
          gcongr
        _ = (2 * N * Real.sqrt (4 ^ (N - 1) : ℕ)) ^ 2 := by
          rw [mul_pow]
          rw [Real.sq_sqrt (by positivity)]
          norm_num
          ring
    nlinarith
  have hpowPos : (0 : ℝ) < 2 ^ (N - 1) := by positivity
  have hsqrtPow :
      Real.sqrt (4 ^ (N - 1) : ℕ) = (2 ^ (N - 1) : ℝ) := by
    have hpowNat :
        4 ^ (N - 1) = (2 ^ (N - 1)) ^ 2 := by
      rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul, ← pow_mul]
      congr 1
      omega
    rw [hpowNat]
    rw [Nat.cast_pow]
    rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (by positivity)]
    norm_num [Nat.cast_pow]
  apply (div_le_iff₀ hpowPos).2
  change
    (∑ s ∈ I, fixedCriticalContribution N s) ≤
      8 * N * (2 ^ (N - 1) : ℝ)
  calc
    (∑ s ∈ I, fixedCriticalContribution N s)
        ≤ 4 * ∑ s ∈ I, Real.sqrt (Y s) := hterm
    _ ≤ 4 * (2 * N * Real.sqrt (4 ^ (N - 1) : ℕ)) := by
      gcongr
    _ = 8 * N * (2 ^ (N - 1) : ℝ) := by rw [hsqrtPow]; ring

end

end FixedTotal

end CollatzEndpointTransport
