/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik
-/
import CollatzEndpointTransport.QuadraticAppendix.Shared.QuantitativePullbackParameters

/-!
# Quantitative Cone Robustness

Finite-set core of quantitative cone robustness.

This file formalizes the combinatorial part of Inselmann's Lemma 2.16:

* split the positive integers into base-3 shells;
* express failure of the robust cone as a finite union of affine bad fibers;
* inject every fiber through `n |-> 3^k*n+i` into the original exceptional
  prefix.

No real-power estimate is used yet.  The remaining analytic layer is to sum
the resulting prefix bounds over `(k,i)` and convert the base-3 shell estimate
back to `(C,D)`-density.
-/

namespace CollatzEndpointTransport

namespace QuantitativeDensity

open scoped Real

noncomputable section

/-- Base-3 shell `[3^j,3^(j+1))`. -/
def threeShell (j : ℕ) : Finset ℕ :=
  Finset.Ico (3 ^ j) (3 ^ (j + 1))

/-- Points in one base-3 shell whose `(k,i)` affine descendant misses `S`. -/
def coneBadFiber (S : Set ℕ) (j k i : ℕ) : Finset ℕ := by
  classical
  exact (threeShell j).filter (fun n => 3 ^ k * n + i ∉ S)

/-- The explicit finite union used to cover all cone failures on shell `j`. -/
def coneBadUnion (S : Set ℕ) (K : ℕ) (eta : ℝ) (j : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range (⌊eta * j⌋₊ + 1)).biUnion fun k =>
    (Finset.range (K * 3 ^ k)).biUnion fun i =>
      coneBadFiber S j k i

/-- Actual failures of the nested-floor cone on shell `j`. -/
def coneBadOnThreeShell
    (S : Set ℕ) (K : ℕ) (eta : ℝ) (j : ℕ) : Finset ℕ := by
  classical
  exact (threeShell j).filter (fun n => n ∉ coneCore K eta S)

@[simp]
theorem mem_threeShell {j n : ℕ} :
    n ∈ threeShell j ↔ 3 ^ j ≤ n ∧ n < 3 ^ (j + 1) := by
  simp [threeShell]

theorem threeShell_pos {j n : ℕ} (hn : n ∈ threeShell j) :
    0 < n := by
  have hpow : 0 < 3 ^ j := by positivity
  exact lt_of_lt_of_le hpow (mem_threeShell.mp hn).1

/-- The affine map used by each cone fiber is injective. -/
theorem affineEmbedding_injective (k i : ℕ) :
    Function.Injective (fun n : ℕ => 3 ^ k * n + i) := by
  intro n m h
  have hmul : 3 ^ k * n = 3 ^ k * m := Nat.add_right_cancel h
  exact Nat.eq_of_mul_eq_mul_left (by positivity) hmul

/-- Every affine bad fiber injects into one prefix of the original
exceptional set. -/
theorem card_coneBadFiber_le_badPrefix
    (S : Set ℕ) (j k i : ℕ) :
    (coneBadFiber S j k i).card ≤
      (badPrefix S (3 ^ k * 3 ^ (j + 1) + i)).card := by
  classical
  let f : ℕ → ℕ := fun n => 3 ^ k * n + i
  apply Finset.card_le_card_of_injOn
      (s := coneBadFiber S j k i)
      (t := badPrefix S (3 ^ k * 3 ^ (j + 1) + i))
      (f := f)
  · intro n hn
    rw [coneBadFiber, Finset.mem_filter] at hn
    obtain ⟨hnShell, hnBad⟩ := hn
    have hnRange := (mem_threeShell.mp hnShell).2
    have hfPos : 0 < f n := by
      dsimp [f]
      have hnPos := threeShell_pos hnShell
      positivity
    have hfLe : f n ≤ 3 ^ k * 3 ^ (j + 1) + i := by
      dsimp [f]
      have hmul : 3 ^ k * n < 3 ^ k * 3 ^ (j + 1) :=
        (Nat.mul_lt_mul_left (by positivity : 0 < 3 ^ k)).2 hnRange
      omega
    rw [badPrefix, Finset.mem_filter, positivePrefix, Finset.mem_Icc]
    exact ⟨⟨hfPos, hfLe⟩, hnBad⟩
  · intro n _ m _ h
    exact affineEmbedding_injective k i h

/-- Failure of the nested-floor cone is covered by the explicit `(k,i)`
union. -/
theorem coneBadOnThreeShell_subset_union
    {S : Set ℕ} {K j : ℕ} {eta : ℝ} (_heta : 0 ≤ eta) :
    coneBadOnThreeShell S K eta j ⊆ coneBadUnion S K eta j := by
  classical
  intro n hn
  rw [coneBadOnThreeShell, Finset.mem_filter] at hn
  obtain ⟨hnShell, hnCone⟩ := hn
  have hnPos := threeShell_pos hnShell
  have hnot :
      ¬ ∀ k : ℕ, (k : ℝ) ≤ eta * j →
        ∀ i : ℕ, i < K * 3 ^ k → 3 ^ k * n + i ∈ S := by
    intro h
    apply hnCone
    exact (mem_coneCore_iff_of_mem_three_shell
      (K := K) (eta := eta) (S := S) (mem_threeShell.mp hnShell)).2
      ⟨hnPos, h⟩
  push_neg at hnot
  obtain ⟨k, hk, i, hi, hbad⟩ := hnot
  have hkFloor : k ≤ ⌊eta * j⌋₊ :=
    Nat.le_floor hk
  rw [coneBadUnion, Finset.mem_biUnion]
  refine ⟨k, Finset.mem_range.2 (by omega), ?_⟩
  rw [Finset.mem_biUnion]
  refine ⟨i, Finset.mem_range.2 hi, ?_⟩
  rw [coneBadFiber, Finset.mem_filter]
  exact ⟨hnShell, hbad⟩

/-- Cardinality form of the cone-failure union bound. -/
theorem card_coneBadOnThreeShell_le_sum
    {S : Set ℕ} {K j : ℕ} {eta : ℝ} (heta : 0 ≤ eta) :
    (coneBadOnThreeShell S K eta j).card ≤
      ∑ k ∈ Finset.range (⌊eta * j⌋₊ + 1),
        ∑ i ∈ Finset.range (K * 3 ^ k),
          (coneBadFiber S j k i).card := by
  calc
    (coneBadOnThreeShell S K eta j).card
        ≤ (coneBadUnion S K eta j).card :=
      Finset.card_le_card (coneBadOnThreeShell_subset_union heta)
    _ ≤ ∑ k ∈ Finset.range (⌊eta * j⌋₊ + 1),
          ((Finset.range (K * 3 ^ k)).biUnion fun i =>
            coneBadFiber S j k i).card := by
      simpa only [coneBadUnion] using
        (Finset.card_biUnion_le :
          ((Finset.range (⌊eta * j⌋₊ + 1)).biUnion
            (fun k => (Finset.range (K * 3 ^ k)).biUnion
              (fun i => coneBadFiber S j k i))).card ≤
            ∑ k ∈ Finset.range (⌊eta * j⌋₊ + 1),
              ((Finset.range (K * 3 ^ k)).biUnion
                (fun i => coneBadFiber S j k i)).card)
    _ ≤ ∑ k ∈ Finset.range (⌊eta * j⌋₊ + 1),
          ∑ i ∈ Finset.range (K * 3 ^ k),
            (coneBadFiber S j k i).card := by
      apply Finset.sum_le_sum
      intro k _
      exact Finset.card_biUnion_le

/-- The complete finite combinatorial reduction: every cone failure is
bounded by exceptional-prefix counts of `S`. -/
theorem card_coneBadOnThreeShell_le_badPrefix_sum
    {S : Set ℕ} {K j : ℕ} {eta : ℝ} (heta : 0 ≤ eta) :
    (coneBadOnThreeShell S K eta j).card ≤
      ∑ k ∈ Finset.range (⌊eta * j⌋₊ + 1),
        ∑ i ∈ Finset.range (K * 3 ^ k),
          (badPrefix S (3 ^ k * 3 ^ (j + 1) + i)).card := by
  calc
    (coneBadOnThreeShell S K eta j).card
        ≤ ∑ k ∈ Finset.range (⌊eta * j⌋₊ + 1),
            ∑ i ∈ Finset.range (K * 3 ^ k),
              (coneBadFiber S j k i).card :=
      card_coneBadOnThreeShell_le_sum heta
    _ ≤ ∑ k ∈ Finset.range (⌊eta * j⌋₊ + 1),
          ∑ i ∈ Finset.range (K * 3 ^ k),
            (badPrefix S (3 ^ k * 3 ^ (j + 1) + i)).card := by
      apply Finset.sum_le_sum
      intro k _
      apply Finset.sum_le_sum
      intro i _
      exact card_coneBadFiber_le_badPrefix S j k i

/-! ### Direct prefix reduction

The shell reduction above mirrors the source proof.  For the nested-floor
cone, a shorter route is available: on `[1,N]`, monotonicity of `Nat.log`
places every failing depth below `floor (eta * log_3 N)`.  This avoids a
second shell-to-global conversion in the final quantitative theorem.
-/

/-- One affine cone-failure fiber restricted directly to `[1,N]`. -/
def coneBadPrefixFiber (S : Set ℕ) (N k i : ℕ) : Finset ℕ := by
  classical
  exact (positivePrefix N).filter (fun n => 3 ^ k * n + i ∉ S)

/-- Explicit prefix union covering every failure of the robust cone. -/
def coneBadPrefixUnion
    (S : Set ℕ) (K : ℕ) (eta : ℝ) (N : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range (⌊eta * Nat.log 3 N⌋₊ + 1)).biUnion fun k =>
    (Finset.range (K * 3 ^ k)).biUnion fun i =>
      coneBadPrefixFiber S N k i

/-- Every cone failure in `[1,N]` lies in the direct prefix union. -/
theorem badPrefix_coneCore_subset_prefixUnion
    {S : Set ℕ} {K N : ℕ} {eta : ℝ} (heta : 0 ≤ eta) :
    badPrefix (coneCore K eta S) N ⊆
      coneBadPrefixUnion S K eta N := by
  classical
  intro n hn
  rw [badPrefix, Finset.mem_filter, positivePrefix, Finset.mem_Icc] at hn
  obtain ⟨⟨hnPos, hnN⟩, hnCone⟩ := hn
  have hnot :
      ¬ ∀ k : ℕ, (k : ℝ) ≤ eta * Nat.log 3 n →
        ∀ i : ℕ, i < K * 3 ^ k → 3 ^ k * n + i ∈ S := by
    intro h
    apply hnCone
    exact ⟨hnPos, h⟩
  push_neg at hnot
  obtain ⟨k, hk, i, hi, hbad⟩ := hnot
  have hlog : Nat.log 3 n ≤ Nat.log 3 N :=
    Nat.log_mono_right hnN
  have hkN : (k : ℝ) ≤ eta * Nat.log 3 N :=
    hk.trans (mul_le_mul_of_nonneg_left (by exact_mod_cast hlog) heta)
  have hkFloor : k ≤ ⌊eta * Nat.log 3 N⌋₊ :=
    Nat.le_floor hkN
  rw [coneBadPrefixUnion, Finset.mem_biUnion]
  refine ⟨k, Finset.mem_range.2 (by omega), ?_⟩
  rw [Finset.mem_biUnion]
  refine ⟨i, Finset.mem_range.2 hi, ?_⟩
  rw [coneBadPrefixFiber, Finset.mem_filter, positivePrefix, Finset.mem_Icc]
  exact ⟨⟨hnPos, hnN⟩, hbad⟩

/-- Each direct prefix fiber injects into one exceptional prefix of `S`. -/
theorem card_coneBadPrefixFiber_le_badPrefix
    (S : Set ℕ) (N k i : ℕ) :
    (coneBadPrefixFiber S N k i).card ≤
      (badPrefix S (3 ^ k * N + i)).card := by
  classical
  let f : ℕ → ℕ := fun n => 3 ^ k * n + i
  apply Finset.card_le_card_of_injOn
      (s := coneBadPrefixFiber S N k i)
      (t := badPrefix S (3 ^ k * N + i))
      (f := f)
  · intro n hn
    rw [coneBadPrefixFiber, Finset.mem_filter,
      positivePrefix, Finset.mem_Icc] at hn
    obtain ⟨⟨hnPos, hnN⟩, hnBad⟩ := hn
    rw [badPrefix, Finset.mem_filter, positivePrefix, Finset.mem_Icc]
    refine ⟨⟨?_, ?_⟩, hnBad⟩
    · dsimp [f]
      have hmul : 0 < 3 ^ k * n :=
        Nat.mul_pos (by positivity) hnPos
      omega
    · dsimp [f]
      exact Nat.add_le_add_right (Nat.mul_le_mul_left (3 ^ k) hnN) i
  · intro n _ m _ h
    exact affineEmbedding_injective k i h

/-- Complete direct-prefix combinatorial reduction for cone robustness. -/
theorem card_badPrefix_coneCore_le_badPrefix_sum
    {S : Set ℕ} {K N : ℕ} {eta : ℝ} (heta : 0 ≤ eta) :
    (badPrefix (coneCore K eta S) N).card ≤
      ∑ k ∈ Finset.range (⌊eta * Nat.log 3 N⌋₊ + 1),
        ∑ i ∈ Finset.range (K * 3 ^ k),
          (badPrefix S (3 ^ k * N + i)).card := by
  calc
    (badPrefix (coneCore K eta S) N).card
        ≤ (coneBadPrefixUnion S K eta N).card :=
      Finset.card_le_card (badPrefix_coneCore_subset_prefixUnion heta)
    _ ≤ ∑ k ∈ Finset.range (⌊eta * Nat.log 3 N⌋₊ + 1),
          ((Finset.range (K * 3 ^ k)).biUnion fun i =>
            coneBadPrefixFiber S N k i).card := by
      simpa only [coneBadPrefixUnion] using
        (Finset.card_biUnion_le :
          ((Finset.range (⌊eta * Nat.log 3 N⌋₊ + 1)).biUnion
            (fun k => (Finset.range (K * 3 ^ k)).biUnion
              (fun i => coneBadPrefixFiber S N k i))).card ≤
            ∑ k ∈ Finset.range (⌊eta * Nat.log 3 N⌋₊ + 1),
              ((Finset.range (K * 3 ^ k)).biUnion
                (fun i => coneBadPrefixFiber S N k i)).card)
    _ ≤ ∑ k ∈ Finset.range (⌊eta * Nat.log 3 N⌋₊ + 1),
          ∑ i ∈ Finset.range (K * 3 ^ k),
            (coneBadPrefixFiber S N k i).card := by
      apply Finset.sum_le_sum
      intro k _
      exact Finset.card_biUnion_le
    _ ≤ ∑ k ∈ Finset.range (⌊eta * Nat.log 3 N⌋₊ + 1),
          ∑ i ∈ Finset.range (K * 3 ^ k),
            (badPrefix S (3 ^ k * N + i)).card := by
      apply Finset.sum_le_sum
      intro k _
      apply Finset.sum_le_sum
      intro i _
      exact card_coneBadPrefixFiber_le_badPrefix S N k i

end

end QuantitativeDensity

end CollatzEndpointTransport
