/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik
-/
import CollatzEndpointTransport.QuadraticAppendix.QuantitativeQuadraticTheoremB
import CollatzEndpointTransport.Common.TerrasOrbitMinimum

/-!
# Quantitative Quadratic Corollaries

Literal corollaries of the end-to-end quadratic theorem.

No result in this file is an input to Theorem B.  The purpose is to align
the exported Lean surface with the paper's `T_min` notation and its
qualitative Proposition A.
-/

namespace CollatzEndpointTransport

namespace QuantitativeDensity

open scoped Real Topology

noncomputable section

theorem hasNaturalDensityOne_inter_Ici
    {S : Set ℕ} (hS : HasNaturalDensityOne S) (N₀ : ℕ) :
    HasNaturalDensityOne (S ∩ Set.Ici N₀) := by
  have hbound :
      ∀ N,
        ((badPrefix (S ∩ Set.Ici N₀) N).card : ℝ) / N ≤
          ((badPrefix S N).card : ℝ) / N + N₀ / N := by
    intro N
    have hsub :
        badPrefix (S ∩ Set.Ici N₀) N ⊆
          badPrefix S N ∪ Finset.range N₀ := by
      intro n hn
      simp only [badPrefix, Finset.mem_filter, Set.mem_inter_iff,
        Set.mem_Ici] at hn
      by_cases hnS : n ∈ S
      · have hnlt : n < N₀ := by
          by_contra hnot
          exact hn.2 ⟨hnS, le_of_not_gt hnot⟩
        exact Finset.mem_union_right _ (Finset.mem_range.2 hnlt)
      · have hnBad : n ∈ badPrefix S N := by
          simp only [badPrefix, Finset.mem_filter]
          exact ⟨hn.1, hnS⟩
        exact Finset.mem_union_left _ hnBad
    have hcardNat :
        (badPrefix (S ∩ Set.Ici N₀) N).card ≤
          (badPrefix S N).card + N₀ := by
      calc
        (badPrefix (S ∩ Set.Ici N₀) N).card
            ≤ (badPrefix S N ∪ Finset.range N₀).card :=
          Finset.card_le_card hsub
        _ ≤ (badPrefix S N).card + (Finset.range N₀).card :=
          Finset.card_union_le _ _
        _ = (badPrefix S N).card + N₀ := by simp
    have hcard :
        ((badPrefix (S ∩ Set.Ici N₀) N).card : ℝ) ≤
          (badPrefix S N).card + N₀ := by
      exact_mod_cast hcardNat
    calc
      ((badPrefix (S ∩ Set.Ici N₀) N).card : ℝ) / N
          ≤ (((badPrefix S N).card : ℝ) + N₀) / N :=
        div_le_div_of_nonneg_right hcard (Nat.cast_nonneg N)
      _ = ((badPrefix S N).card : ℝ) / N + N₀ / N := by ring
  have hsum :
      Filter.Tendsto
        (fun N : ℕ =>
          ((badPrefix S N).card : ℝ) / N + N₀ / N)
        Filter.atTop (nhds 0) := by
    simpa only [add_zero] using
      hS.add (tendsto_const_div_atTop_nhds_zero_nat N₀)
  exact squeeze_zero (fun N => by positivity) hbound hsum

def propositionAEpsilon (a C : ℝ) (n : ℕ) : ℝ :=
  C / (Real.log (Real.log (((max n 4 : ℕ) : ℝ)))) ^ a

def propositionASet (eps : ℕ → ℝ) : Set ℕ :=
  {n | (Terras.Tmin n : ℝ) ≤ (n : ℝ) ^ eps n}

def PropositionAStatement : Prop :=
  ∃ eps : ℕ → ℝ,
    (∀ n, 0 < eps n) ∧
      Antitone eps ∧
      Filter.Tendsto eps Filter.atTop (nhds 0) ∧
      HasNaturalDensityOne (propositionASet eps)

theorem log_log_max_four_pos (n : ℕ) :
    0 < Real.log (Real.log (((max n 4 : ℕ) : ℝ))) := by
  have hfour : (4 : ℝ) ≤ ((max n 4 : ℕ) : ℝ) := by
    exact_mod_cast Nat.le_max_right n 4
  have hmax0 : 0 < ((max n 4 : ℕ) : ℝ) := by positivity
  have hlogFour :
      1 < Real.log 4 := by
    rw [show (4 : ℝ) = 2 * 2 by norm_num,
      Real.log_mul (by norm_num) (by norm_num)]
    nlinarith [Real.log_two_gt_d9]
  have hlog :
      Real.log 4 ≤ Real.log (((max n 4 : ℕ) : ℝ)) :=
    Real.strictMonoOn_log.monotoneOn
      (Set.mem_Ioi.mpr (by norm_num))
      (Set.mem_Ioi.mpr hmax0)
      hfour
  exact Real.log_pos (hlogFour.trans_le hlog)

theorem propositionAEpsilon_pos
    {a C : ℝ} (hC : 0 < C) (n : ℕ) :
    0 < propositionAEpsilon a C n := by
  unfold propositionAEpsilon
  exact div_pos hC
    (Real.rpow_pos_of_pos (log_log_max_four_pos n) a)

theorem propositionAEpsilon_antitone
    {a C : ℝ} (ha : 0 < a) (hC : 0 < C) :
    Antitone (propositionAEpsilon a C) := by
  intro n m hnm
  have hmaxNat : max n 4 ≤ max m 4 :=
    max_le_max hnm le_rfl
  have hmax :
      ((max n 4 : ℕ) : ℝ) ≤ ((max m 4 : ℕ) : ℝ) := by
    exact_mod_cast hmaxNat
  have hn0 : 0 < ((max n 4 : ℕ) : ℝ) := by positivity
  have hm0 : 0 < ((max m 4 : ℕ) : ℝ) := by positivity
  have hlog :
      Real.log (((max n 4 : ℕ) : ℝ)) ≤
        Real.log (((max m 4 : ℕ) : ℝ)) :=
    Real.strictMonoOn_log.monotoneOn
      (Set.mem_Ioi.mpr hn0) (Set.mem_Ioi.mpr hm0) hmax
  have hlogn0 : 0 < Real.log (((max n 4 : ℕ) : ℝ)) := by
    exact Real.log_pos (by
      have hfour : (4 : ℝ) ≤ ((max n 4 : ℕ) : ℝ) := by
        exact_mod_cast Nat.le_max_right n 4
      exact lt_of_lt_of_le (by norm_num) hfour)
  have hlogm0 : 0 < Real.log (((max m 4 : ℕ) : ℝ)) := by
    exact Real.log_pos (by
      have hfour : (4 : ℝ) ≤ ((max m 4 : ℕ) : ℝ) := by
        exact_mod_cast Nat.le_max_right m 4
      exact lt_of_lt_of_le (by norm_num) hfour)
  have hloglog :
      Real.log (Real.log (((max n 4 : ℕ) : ℝ))) ≤
        Real.log (Real.log (((max m 4 : ℕ) : ℝ))) :=
    Real.strictMonoOn_log.monotoneOn
      (Set.mem_Ioi.mpr hlogn0) (Set.mem_Ioi.mpr hlogm0) hlog
  have hpow :
      (Real.log (Real.log (((max n 4 : ℕ) : ℝ)))) ^ a ≤
        (Real.log (Real.log (((max m 4 : ℕ) : ℝ)))) ^ a :=
    Real.rpow_le_rpow (log_log_max_four_pos n).le hloglog ha.le
  unfold propositionAEpsilon
  exact div_le_div_of_nonneg_left hC.le
    (Real.rpow_pos_of_pos (log_log_max_four_pos n) a) hpow

theorem propositionAEpsilon_tendsto_zero
    {a C : ℝ} (ha : 0 < a) :
    Filter.Tendsto (propositionAEpsilon a C)
      Filter.atTop (nhds 0) := by
  have hmax :
      Filter.Tendsto (fun n : ℕ => ((max n 4 : ℕ) : ℝ))
        Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_mono' Filter.atTop
      (Filter.Eventually.of_forall fun n => by
        exact Nat.cast_le.2 (Nat.le_max_left n 4))
      tendsto_natCast_atTop_atTop
  have hlog := Real.tendsto_log_atTop.comp hmax
  have hloglog := Real.tendsto_log_atTop.comp hlog
  have hpow := (tendsto_rpow_atTop ha).comp hloglog
  exact hpow.const_div_atTop C

theorem quantitativeTheoremBSet_inter_subset_propositionASet
    {a C : ℝ} :
    quantitativeTheoremBSet a C ∩ Set.Ici 4 ⊆
      propositionASet (propositionAEpsilon a C) := by
  intro n hn
  obtain ⟨hquant, hn4⟩ := hn
  obtain ⟨k, hk⟩ := hquant
  have hn4' : 4 ≤ n := hn4
  have hn0 : 0 < n := by omega
  have hmin :
      (Terras.Tmin n : ℝ) ≤
        Real.exp
          (C * Real.log n /
            (Real.log (Real.log n)) ^ a) :=
    Terras.cast_Tmin_le_of_exists_iterate_cast_le ⟨k, hk⟩
  have hmax : max n 4 = n := max_eq_left hn4
  have heq :
      Real.exp
          (C * Real.log n /
            (Real.log (Real.log n)) ^ a) =
        (n : ℝ) ^ propositionAEpsilon a C n := by
    calc
      Real.exp
          (C * Real.log n /
            (Real.log (Real.log n)) ^ a) =
          Real.exp
            (Real.log n * propositionAEpsilon a C n) := by
        rw [propositionAEpsilon, hmax]
        congr 1
        ring
      _ = (n : ℝ) ^ propositionAEpsilon a C n :=
        (Real.rpow_def_of_pos (by exact_mod_cast hn0)
          (propositionAEpsilon a C n)).symm
  exact hmin.trans_eq heq

/-- **Proposition A.**  A positive non-increasing exponent tending to zero
controls the literal orbit minimum on a natural-density-one set.  This is a
corollary of Theorem B, not an invocation of Inselmann's fixed-exponent
theorem. -/
theorem quantitativeQuadraticPropositionA :
    PropositionAStatement := by
  have hheadline :
      0 < quadraticHeadlineExponent := by
    unfold quadraticHeadlineExponent
    exact quadraticAdmissibleExponent_pos a0_pos a0_lt_one
  let a := quadraticHeadlineExponent / 2
  have ha0 : 0 < a := by
    dsimp [a]
    linarith
  have ha : a < quadraticHeadlineExponent := by
    dsimp [a]
    linarith
  have hB := quantitativeQuadraticTheoremB_one ha0 ha
  refine ⟨propositionAEpsilon a 1,
    propositionAEpsilon_pos zero_lt_one,
    propositionAEpsilon_antitone ha0 zero_lt_one,
    propositionAEpsilon_tendsto_zero ha0, ?_⟩
  apply hasNaturalDensityOne_mono
    quantitativeTheoremBSet_inter_subset_propositionASet
  exact hasNaturalDensityOne_inter_Ici hB 4

end

end QuantitativeDensity

end CollatzEndpointTransport
