/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik
-/
import Mathlib

/-!
# Quantitative Density

Quantitative `(C,D)`-density definitions used by the paper proof.

Source: Inselmann, arXiv:2402.03276v3, Definition 2.6.

For `C > 0`, `0 < D <= 1`, and a set `S` of positive integers, we encode the
complement-count form

  #(Sᶜ ∩ [1,N]) <= C N^(1-D),

because it is closed transparently under intersections. The file supplies
only the elementary closure properties used by the retained proof.
-/

namespace CollatzEndpointTransport

namespace QuantitativeDensity

open scoped Real

noncomputable section

/-- The positive prefix `[1,N]`. -/
def positivePrefix (N : ℕ) : Finset ℕ :=
  Finset.Icc 1 N

/-- Nonmembers of `S` in `[1,N]`. -/
def badPrefix (S : Set ℕ) (N : ℕ) : Finset ℕ := by
    classical
    exact (positivePrefix N).filter (fun n => n ∉ S)

@[simp]
theorem card_positivePrefix (N : ℕ) :
    (positivePrefix N).card = N := by
  simp [positivePrefix, Nat.card_Icc]

/-- Complement-count form of quantitative `(C,D)`-density. -/
def IsCDDense (S : Set ℕ) (C D : ℝ) : Prop :=
  0 < C ∧ 0 < D ∧ D ≤ 1 ∧
    ∀ N : ℕ, 0 < N →
      ((badPrefix S N).card : ℝ) ≤ C * (N : ℝ) ^ (1 - D)

theorem IsCDDense.C_pos {S : Set ℕ} {C D : ℝ} (h : IsCDDense S C D) :
    0 < C := h.1

theorem IsCDDense.D_pos {S : Set ℕ} {C D : ℝ} (h : IsCDDense S C D) :
    0 < D := h.2.1

theorem IsCDDense.D_le_one {S : Set ℕ} {C D : ℝ} (h : IsCDDense S C D) :
    D ≤ 1 := h.2.2.1

theorem IsCDDense.bad_bound
    {S : Set ℕ} {C D : ℝ} (h : IsCDDense S C D) (N : ℕ) (hN : 0 < N) :
    ((badPrefix S N).card : ℝ) ≤ C * (N : ℝ) ^ (1 - D) :=
  h.2.2.2 N hN

/-- Increasing the prefactor preserves `(C,D)`-density. -/
theorem IsCDDense.mono_constant
    {S : Set ℕ} {C C' D : ℝ} (h : IsCDDense S C D) (hCC' : C ≤ C') :
    IsCDDense S C' D := by
  refine ⟨lt_of_lt_of_le h.C_pos hCC', h.D_pos, h.D_le_one, ?_⟩
  intro N hN
  calc
    ((badPrefix S N).card : ℝ) ≤ C * (N : ℝ) ^ (1 - D) :=
      h.bad_bound N hN
    _ ≤ C' * (N : ℝ) ^ (1 - D) :=
      mul_le_mul_of_nonneg_right hCC' (Real.rpow_nonneg (by positivity) _)

/-- Weakening the exponent preserves quantitative density. -/
theorem IsCDDense.degrade_exponent
    {S : Set ℕ} {C D D' : ℝ} (h : IsCDDense S C D)
    (hD' : 0 < D') (hD'D : D' ≤ D) :
    IsCDDense S C D' := by
  refine ⟨h.C_pos, hD', le_trans hD'D h.D_le_one, ?_⟩
  intro N hN
  have hN1 : 1 ≤ (N : ℝ) := by exact_mod_cast hN
  have hpow :
      (N : ℝ) ^ (1 - D) ≤ (N : ℝ) ^ (1 - D') :=
    Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  calc
    ((badPrefix S N).card : ℝ) ≤ C * (N : ℝ) ^ (1 - D) :=
      h.bad_bound N hN
    _ ≤ C * (N : ℝ) ^ (1 - D') :=
      mul_le_mul_of_nonneg_left hpow (le_of_lt h.C_pos)

/-- Passing to a larger good set preserves quantitative density. -/
theorem IsCDDense.mono_set
    {S T : Set ℕ} {C D : ℝ} (h : IsCDDense S C D) (hST : S ⊆ T) :
    IsCDDense T C D := by
  refine ⟨h.C_pos, h.D_pos, h.D_le_one, ?_⟩
  intro N hN
  have hsub : badPrefix T N ⊆ badPrefix S N := by
    intro n hn
    simp only [badPrefix, Finset.mem_filter] at hn ⊢
    exact ⟨hn.1, fun hnS => hn.2 (hST hnS)⟩
  have hcard : (badPrefix T N).card ≤ (badPrefix S N).card :=
    Finset.card_le_card hsub
  calc
    ((badPrefix T N).card : ℝ) ≤ ((badPrefix S N).card : ℝ) := by
      exact_mod_cast hcard
    _ ≤ C * (N : ℝ) ^ (1 - D) := h.bad_bound N hN

/-- Intersecting two good sets adds their prefactors and preserves a common
exponent. -/
theorem IsCDDense.inter
    {S T : Set ℕ} {C₁ C₂ D : ℝ}
    (hS : IsCDDense S C₁ D) (hT : IsCDDense T C₂ D) :
    IsCDDense (S ∩ T) (C₁ + C₂) D := by
  refine ⟨add_pos hS.C_pos hT.C_pos, hS.D_pos, hS.D_le_one, ?_⟩
  intro N hN
  have hsub :
      badPrefix (S ∩ T) N ⊆ badPrefix S N ∪ badPrefix T N := by
    intro n hn
    simp only [badPrefix, Finset.mem_filter, Finset.mem_union] at hn ⊢
    rcases hn with ⟨hnPrefix, hnInter⟩
    by_cases hnS : n ∈ S
    · exact Or.inr ⟨hnPrefix, fun hnT => hnInter ⟨hnS, hnT⟩⟩
    · exact Or.inl ⟨hnPrefix, hnS⟩
  have hcard :
      (badPrefix (S ∩ T) N).card ≤
        (badPrefix S N).card + (badPrefix T N).card :=
    le_trans (Finset.card_le_card hsub)
      (Finset.card_union_le (badPrefix S N) (badPrefix T N))
  have hcardReal :
      ((badPrefix (S ∩ T) N).card : ℝ) ≤
        (badPrefix S N).card + (badPrefix T N).card := by
    exact_mod_cast hcard
  calc
    ((badPrefix (S ∩ T) N).card : ℝ)
        ≤ (badPrefix S N).card + (badPrefix T N).card := hcardReal
    _ ≤ C₁ * (N : ℝ) ^ (1 - D) + C₂ * (N : ℝ) ^ (1 - D) :=
      add_le_add (hS.bad_bound N hN) (hT.bad_bound N hN)
    _ = (C₁ + C₂) * (N : ℝ) ^ (1 - D) := by ring

end

end QuantitativeDensity

end CollatzEndpointTransport
