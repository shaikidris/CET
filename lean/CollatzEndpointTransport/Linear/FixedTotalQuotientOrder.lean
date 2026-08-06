/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik
-/
import CollatzEndpointTransport.Linear.FixedTotalComposition
import Mathlib.Data.Real.Sqrt

/-!
# Fixed Total Quotient Order

Critical quotient-order estimate for the fixed-total offset law.

Distinct integer lifts in one residue class have distinct nonnegative
quotients.  Ordering those quotients shows that at least half are at least
half the fiber cardinality.  This gives the critical square-root moment
bound with an absolute factor `4`.

The paper records the sharper integral constant `3/2`; the factor `4` used
here changes only a hidden prefactor and leaves every density exponent
unchanged.
-/

namespace CollatzEndpointTransport

namespace FixedTotal

open Nat Finset

noncomputable section

/-- At most `h` distinct natural numbers are strictly below `h`. -/
theorem card_filter_lt_le
    (S : Finset ℕ) (h : ℕ) :
    (S.filter fun q => q < h).card ≤ h := by
  have hsub :
      S.filter (fun q => q < h) ⊆ Finset.range h := by
    intro q hq
    exact Finset.mem_range.mpr (Finset.mem_filter.mp hq).2
  simpa using Finset.card_le_card hsub

/-- At least half of a finite set of naturals lies above half its
cardinality. -/
theorem half_card_le_card_filter_half
    (S : Finset ℕ) :
    S.card - S.card / 2 ≤
      (S.filter fun q => S.card / 2 ≤ q).card := by
  let low := S.filter fun q => q < S.card / 2
  let high := S.filter fun q => S.card / 2 ≤ q
  have hlow : low.card ≤ S.card / 2 := by
    exact card_filter_lt_le S (S.card / 2)
  have hdisj : Disjoint low high := by
    refine Finset.disjoint_left.mpr ?_
    intro q hqLow hqHigh
    exact (not_lt_of_ge (Finset.mem_filter.mp hqHigh).2)
      (Finset.mem_filter.mp hqLow).2
  have hunion : low ∪ high = S := by
    ext q
    simp only [low, high, Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro ((⟨hq, _⟩) | (⟨hq, _⟩)) <;> exact hq
    · intro hq
      exact (lt_or_ge q (S.card / 2)).elim
        (fun hlt => Or.inl ⟨hq, hlt⟩)
        (fun hge => Or.inr ⟨hq, hge⟩)
  have hpart : low.card + high.card = S.card := by
    rw [← hunion, Finset.card_union_of_disjoint hdisj]
  change S.card - S.card / 2 ≤ high.card
  omega

/-- A cardinality-vs-square-root estimate for any finite set of distinct
nonnegative integers. -/
theorem card_mul_sqrt_card_le_four_sum_sqrt_succ
    (S : Finset ℕ) :
    (S.card : ℝ) * Real.sqrt S.card ≤
      4 * ∑ q ∈ S, Real.sqrt (q + 1) := by
  let h := S.card / 2
  let high := S.filter fun q => h ≤ q
  have hhigh :
      S.card - S.card / 2 ≤ high.card := by
    simpa [h, high] using half_card_le_card_filter_half S
  have hcard : S.card ≤ 2 * high.card := by omega
  have hscale : S.card ≤ 4 * (h + 1) := by
    dsimp [h]
    omega
  have hsqrt :
      Real.sqrt S.card ≤ 2 * Real.sqrt (h + 1) := by
    have hS0 : (0 : ℝ) ≤ S.card := by positivity
    have hh0 : (0 : ℝ) ≤ h + 1 := by positivity
    have hsS := Real.sq_sqrt hS0
    have hsh := Real.sq_sqrt hh0
    have hsqrtS : 0 ≤ Real.sqrt S.card := Real.sqrt_nonneg _
    have hsqrth : 0 ≤ Real.sqrt (h + 1) := Real.sqrt_nonneg _
    have hscaleR : (S.card : ℝ) ≤ 4 * (h + 1) := by
      exact_mod_cast hscale
    nlinarith
  have hprod :
      (S.card : ℝ) * Real.sqrt S.card ≤
        4 * (high.card : ℝ) * Real.sqrt (h + 1) := by
    have hcardR : (S.card : ℝ) ≤ 2 * high.card := by
      exact_mod_cast hcard
    have hS0 : (0 : ℝ) ≤ S.card := by positivity
    have hhcard0 : (0 : ℝ) ≤ high.card := by positivity
    have hsqrtS : 0 ≤ Real.sqrt S.card := Real.sqrt_nonneg _
    have hsqrth : 0 ≤ Real.sqrt (h + 1) := Real.sqrt_nonneg _
    calc
      (S.card : ℝ) * Real.sqrt S.card
          ≤ (2 * high.card : ℝ) * Real.sqrt S.card :=
        mul_le_mul_of_nonneg_right hcardR hsqrtS
      _ ≤ (2 * high.card : ℝ) * (2 * Real.sqrt (h + 1)) :=
        mul_le_mul_of_nonneg_left hsqrt (by positivity)
      _ = 4 * (high.card : ℝ) * Real.sqrt (h + 1) := by ring
  have hsumHigh :
      (high.card : ℝ) * Real.sqrt (h + 1) ≤
        ∑ q ∈ high, Real.sqrt (q + 1) := by
    calc
      (high.card : ℝ) * Real.sqrt (h + 1)
          = ∑ q ∈ high, Real.sqrt (h + 1) := by simp
      _ ≤ ∑ q ∈ high, Real.sqrt (q + 1) := by
        apply Finset.sum_le_sum
        intro q hq
        have hhq : h ≤ q := (Finset.mem_filter.mp hq).2
        exact Real.sqrt_le_sqrt (by exact_mod_cast Nat.add_le_add_right hhq 1)
  have hsumSubset :
      ∑ q ∈ high, Real.sqrt (q + 1) ≤
        ∑ q ∈ S, Real.sqrt (q + 1) := by
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.filter_subset _ _)
      (fun q _ _ => Real.sqrt_nonneg _)
  calc
    (S.card : ℝ) * Real.sqrt S.card
        ≤ 4 * (high.card : ℝ) * Real.sqrt (h + 1) := hprod
    _ ≤ 4 * ∑ q ∈ high, Real.sqrt (q + 1) := by
      simpa [mul_assoc] using
        mul_le_mul_of_nonneg_left hsumHigh (by norm_num : (0 : ℝ) ≤ 4)
    _ ≤ 4 * ∑ q ∈ S, Real.sqrt (q + 1) :=
      mul_le_mul_of_nonneg_left hsumSubset (by norm_num : (0 : ℝ) ≤ 4)

/-- Elements of `W` carrying a fixed residue modulo `m`. -/
def residueFiber
    {α : Type*} [DecidableEq α]
    (W : Finset α) (A : α → ℕ) (m : ℕ) (a : Fin m) : Finset α :=
  W.filter fun x => A x % m = a

/-- The quotient map is injective inside one residue fiber when the integer
lift itself is injective. -/
theorem quotient_injective_on_residueFiber
    {α : Type*} [DecidableEq α]
    {W : Finset α} {A : α → ℕ} {m : ℕ} {a : Fin m}
    (hA : Set.InjOn A W) :
    Set.InjOn (fun x => A x / m) (residueFiber W A m a) := by
  intro x hx y hy hq
  apply hA
  · exact (Finset.mem_filter.mp hx).1
  · exact (Finset.mem_filter.mp hy).1
  have hrx : A x % m = a := (Finset.mem_filter.mp hx).2
  have hry : A y % m = a := (Finset.mem_filter.mp hy).2
  change A x / m = A y / m at hq
  calc
    A x = A x % m + m * (A x / m) := (Nat.mod_add_div (A x) m).symm
    _ = A y % m + m * (A y / m) := by simp only [hrx, hry, hq]
    _ = A y := Nat.mod_add_div (A y) m

/-- Distinct lifts in a residue fiber obey the critical quotient-order
square-root bound. -/
theorem residueFiber_critical_bound
    {α : Type*} [DecidableEq α]
    (W : Finset α) (A : α → ℕ) (m : ℕ) (a : Fin m)
    (hm : 0 < m) (hA : Set.InjOn A W) :
    Real.sqrt m *
        ((residueFiber W A m a).card : ℝ) *
        Real.sqrt (residueFiber W A m a).card ≤
      4 * ∑ x ∈ residueFiber W A m a,
        Real.sqrt (m + A x) := by
  let F := residueFiber W A m a
  let Q := F.image fun x => A x / m
  have hqinj :
      Set.InjOn (fun x => A x / m) F :=
    quotient_injective_on_residueFiber hA
  have hcardQ : Q.card = F.card := by
    exact Finset.card_image_iff.mpr hqinj
  have hbase :=
    card_mul_sqrt_card_le_four_sum_sqrt_succ Q
  rw [hcardQ] at hbase
  have hscaled :
      Real.sqrt m * (F.card : ℝ) * Real.sqrt F.card ≤
        4 * ∑ q ∈ Q, Real.sqrt ((m * (q + 1) : ℕ) : ℝ) := by
    have hm0 : (0 : ℝ) ≤ m := by positivity
    calc
      Real.sqrt m * (F.card : ℝ) * Real.sqrt F.card
          = Real.sqrt m * ((F.card : ℝ) * Real.sqrt F.card) := by ring
      _ ≤ Real.sqrt m *
          (4 * ∑ q ∈ Q, Real.sqrt (q + 1)) :=
        mul_le_mul_of_nonneg_left hbase (Real.sqrt_nonneg _)
      _ = 4 * ∑ q ∈ Q,
          (Real.sqrt m * Real.sqrt (q + 1)) := by
        calc
          Real.sqrt m * (4 * ∑ q ∈ Q, Real.sqrt (q + 1))
              = 4 * (Real.sqrt m * ∑ q ∈ Q, Real.sqrt (q + 1)) := by ring
          _ = 4 * ∑ q ∈ Q,
              (Real.sqrt m * Real.sqrt (q + 1)) := by
            rw [Finset.mul_sum]
      _ = 4 * ∑ q ∈ Q, Real.sqrt ((m * (q + 1) : ℕ) : ℝ) := by
        apply congrArg (fun x : ℝ => 4 * x)
        apply Finset.sum_congr rfl
        intro q hq
        rw [← Real.sqrt_mul hm0]
        norm_num [Nat.cast_mul, Nat.cast_add]
  have hrewrite :
      ∑ q ∈ Q, Real.sqrt ((m * (q + 1) : ℕ) : ℝ) =
        ∑ x ∈ F,
          Real.sqrt ((m * (A x / m + 1) : ℕ) : ℝ) := by
    rw [show Q = F.image (fun x => A x / m) by rfl]
    rw [Finset.sum_image hqinj]
  rw [hrewrite] at hscaled
  refine hscaled.trans ?_
  apply mul_le_mul_of_nonneg_left ?_ (by norm_num)
  apply Finset.sum_le_sum
  intro x hx
  apply Real.sqrt_le_sqrt
  have hdiv : m * (A x / m) ≤ A x := Nat.mul_div_le (A x) m
  have hnat : m * (A x / m + 1) ≤ m + A x := by
    calc
      m * (A x / m + 1) = m * (A x / m) + m := by
        rw [Nat.mul_add, Nat.mul_one]
      _ ≤ A x + m := Nat.add_le_add_right hdiv m
      _ = m + A x := Nat.add_comm _ _
  exact_mod_cast hnat

/-- Summing a function over all residue fibers recovers the sum over the
source set. -/
theorem sum_residueFiber
    {α β : Type*} [DecidableEq α] [AddCommMonoid β]
    (W : Finset α) (A : α → ℕ) (m : ℕ) (hm : 0 < m) (f : α → β) :
    (∑ a : Fin m, ∑ x ∈ residueFiber W A m a, f x) =
      ∑ x ∈ W, f x := by
  classical
  simp only [residueFiber, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x hx
  let a₀ : Fin m := ⟨A x % m, Nat.mod_lt _ hm⟩
  change
    (∑ a ∈ (Finset.univ : Finset (Fin m)),
      if A x % m = (a : ℕ) then f x else 0) = f x
  change
    (∑ a : Fin m, if A x % m = (a : ℕ) then f x else 0) = f x
  calc
    (∑ a : Fin m, if A x % m = (a : ℕ) then f x else 0) =
        (∑ a : Fin m, if a₀ = a then f x else 0) := by
      apply Fintype.sum_congr
      intro a
      by_cases hres : A x % m = (a : ℕ)
      · have ha : a₀ = a := by
          apply Fin.ext
          change A x % m = (a : ℕ)
          exact hres
        simp [hres, ha]
      · have ha : a₀ ≠ a := by
          intro ha
          apply hres
          change A x % m = (a : ℕ)
          exact congrArg Fin.val ha
        simp [hres, ha]
    _ = f x := by
      simpa using Fintype.sum_ite_eq a₀ (fun _ : Fin m => f x)

/-- Critical quotient-order estimate after summing all residue fibers. -/
theorem residueFibers_critical_bound
    {α : Type*} [DecidableEq α]
    (W : Finset α) (A : α → ℕ) (m : ℕ)
    (hm : 0 < m) (hA : Set.InjOn A W) :
    Real.sqrt m *
        (∑ a : Fin m,
          ((residueFiber W A m a).card : ℝ) *
            Real.sqrt (residueFiber W A m a).card) ≤
      4 * ∑ x ∈ W, Real.sqrt (m + A x) := by
  have hsum :
      (∑ a : Fin m,
          Real.sqrt m *
            ((residueFiber W A m a).card : ℝ) *
            Real.sqrt (residueFiber W A m a).card) ≤
        ∑ a : Fin m,
          4 * ∑ x ∈ residueFiber W A m a,
            Real.sqrt (m + A x) := by
    apply Finset.sum_le_sum
    intro a ha
    exact residueFiber_critical_bound W A m a hm hA
  calc
    Real.sqrt m *
        (∑ a : Fin m,
          ((residueFiber W A m a).card : ℝ) *
            Real.sqrt (residueFiber W A m a).card)
        =
      ∑ a : Fin m,
        Real.sqrt m *
          ((residueFiber W A m a).card : ℝ) *
          Real.sqrt (residueFiber W A m a).card := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a ha
      ring
    _ ≤ ∑ a : Fin m,
        4 * ∑ x ∈ residueFiber W A m a,
          Real.sqrt (m + A x) := hsum
    _ = 4 * ∑ a : Fin m,
        ∑ x ∈ residueFiber W A m a,
          Real.sqrt (m + A x) := by
      rw [Finset.mul_sum]
    _ = 4 * ∑ x ∈ W, Real.sqrt (m + A x) := by
      rw [sum_residueFiber W A m hm]

end

end FixedTotal

end CollatzEndpointTransport
