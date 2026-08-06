/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik
-/
import CollatzEndpointTransport.QuadraticAppendix.QuantitativeQuadraticStoppingTime
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# Quantitative Quadratic Exceptional Count

Quantitative exceptional-count corollary for the quadratic schedule.

The shell analysis already supplies a stretched-exponential majorant with
power `3/4`.  This file first degrades it to a square-root majorant and then
sums the shell bounds.  No new Collatz input is introduced.
-/

set_option maxHeartbeats 800000

namespace CollatzEndpointTransport

namespace QuantitativeDensity

open scoped Real Topology BigOperators

noncomputable section

/-- The explicit `3/4`-power shell model is eventually bounded by a simpler
square-root stretched exponential. -/
theorem modelShellDecay_eventually_le_sqrt :
    ∀ᶠ M : ℕ in Filter.atTop,
      2 * (shiftedShellSize M) ^ ((1 : ℝ) / 4) *
          Real.exp
            (-(Real.log 2 / 2) *
              (shiftedShellSize M) ^ ((3 : ℝ) / 4)) ≤
        2 * Real.exp
          (-(1 / 2 : ℝ) *
            (shiftedShellSize M) ^ ((1 : ℝ) / 2)) := by
  have hb : 0 < Real.log 2 / 2 :=
    div_pos log_two_pos (by norm_num)
  have hp : (1 : ℝ) < 3 / 2 := by norm_num
  have hlittle :=
    rpow_mul_exp_neg_mul_rpow_isLittleO_exp_neg
      ((1 : ℝ) / 2) hp hb
  have hy :
      Filter.Tendsto
        (fun M : ℕ =>
          (shiftedShellSize M) ^ ((1 : ℝ) / 2))
        Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp
      shiftedShellSize_tendsto_atTop
  have hbound := (hlittle.comp_tendsto hy).bound zero_lt_one
  filter_upwards [hbound] with M hM
  have hx := shiftedShellSize_pos M
  have hy0 :
      0 < (shiftedShellSize M) ^ ((1 : ℝ) / 2) :=
    Real.rpow_pos_of_pos hx _
  have hquarter :
      ((shiftedShellSize M) ^ ((1 : ℝ) / 2)) ^
          ((1 : ℝ) / 2) =
        (shiftedShellSize M) ^ ((1 : ℝ) / 4) := by
    rw [← Real.rpow_mul hx.le]
    norm_num
  have hthreequarter :
      ((shiftedShellSize M) ^ ((1 : ℝ) / 2)) ^
          ((3 : ℝ) / 2) =
        (shiftedShellSize M) ^ ((3 : ℝ) / 4) := by
    rw [← Real.rpow_mul hx.le]
    norm_num
  simp only [Function.comp_apply, Real.norm_eq_abs,
    abs_of_pos hy0, abs_of_pos (Real.exp_pos _),
    abs_of_pos (mul_pos
      (Real.rpow_pos_of_pos hy0 _)
      (Real.exp_pos _))] at hM
  rw [hquarter, hthreequarter] at hM
  nlinarith [Real.exp_pos
    (-(1 / 2 : ℝ) *
      shiftedShellSize M ^ ((1 : ℝ) / 2))]

/-- Quantitative dyadic summation at the square-root rate.  The assumptions
are deliberately finite and explicit, so this theorem is reusable without
any filter-level interpretation. -/
theorem card_badPrefix_assembleDyadic_le_sqrt_rate
    (S : ℕ → Set ℕ) (M₀ N : ℕ)
    (hshell :
      ∀ M, M₀ ≤ M →
        shellExceptionalRatio (S M) M ≤
          2 * Real.exp
            (-(1 / 2 : ℝ) * Real.sqrt (shiftedShellSize M)))
    (hN : 0 < N)
    (hL1 : 1 ≤ Nat.log 2 N)
    (hM₀ : M₀ ≤ (Nat.log 2 N) / 2) :
    ((badPrefix (assembleDyadic S) N).card : ℝ) ≤
      6 * N *
        Real.exp
          (-(1 / 8 : ℝ) *
            Real.sqrt (Nat.log 2 N : ℝ)) := by
  classical
  let L := Nat.log 2 N
  let K := L / 2
  have hKL : K ≤ L + 1 := by
    dsimp [K]
    omega
  have hprefix := card_badPrefix_le_sum (assembleDyadic S) N
  have hprefixR :
      ((badPrefix (assembleDyadic S) N).card : ℝ) ≤
        ∑ M ∈ Finset.range (L + 1),
          ((shellBad (assembleDyadic S) M).card : ℝ) := by
    dsimp [L]
    exact_mod_cast hprefix
  rw [← Finset.sum_range_add_sum_Ico
    (fun M => ((shellBad (assembleDyadic S) M).card : ℝ)) hKL] at hprefixR
  have hearly :
      ∑ M ∈ Finset.range K,
          ((shellBad (assembleDyadic S) M).card : ℝ) ≤
        (2 : ℝ) ^ K := by
    calc
      ∑ M ∈ Finset.range K,
          ((shellBad (assembleDyadic S) M).card : ℝ)
          ≤ ∑ M ∈ Finset.range K, (2 : ℝ) ^ M := by
            apply Finset.sum_le_sum
            intro M hMr
            have hcard :
                (shellBad (assembleDyadic S) M).card ≤ 2 ^ M := by
              calc
                (shellBad (assembleDyadic S) M).card
                    ≤ (dyadicShell M).card := by
                      apply Finset.card_le_card
                      intro x hx
                      exact (Finset.mem_filter.mp hx).1
                _ = 2 ^ M := by
                  simp [dyadicShell, Nat.card_Ico, pow_succ] <;> omega
            exact_mod_cast hcard
      _ = (2 : ℝ) ^ K - 1 := sum_two_pow_range K
      _ ≤ (2 : ℝ) ^ K := by linarith
  have hshiftMono :
      ∀ M, K ≤ M →
        Real.exp
            (-(1 / 2 : ℝ) * Real.sqrt (shiftedShellSize M)) ≤
          Real.exp
            (-(1 / 2 : ℝ) * Real.sqrt (shiftedShellSize K)) := by
    intro M hKM
    apply Real.exp_le_exp.2
    have hshift :
        shiftedShellSize K ≤ shiftedShellSize M := by
      unfold shiftedShellSize
      exact_mod_cast Nat.add_le_add_right hKM 4
    have hsqrt :
        Real.sqrt (shiftedShellSize K) ≤
          Real.sqrt (shiftedShellSize M) :=
      Real.sqrt_le_sqrt hshift
    nlinarith
  have hlate :
      ∑ M ∈ Finset.Ico K (L + 1),
          ((shellBad (assembleDyadic S) M).card : ℝ) ≤
        2 * Real.exp
            (-(1 / 2 : ℝ) * Real.sqrt (shiftedShellSize K)) *
          (2 : ℝ) ^ (L + 1) := by
    calc
      ∑ M ∈ Finset.Ico K (L + 1),
          ((shellBad (assembleDyadic S) M).card : ℝ)
          ≤ ∑ M ∈ Finset.Ico K (L + 1),
              (2 * Real.exp
                  (-(1 / 2 : ℝ) *
                    Real.sqrt (shiftedShellSize K))) *
                (2 : ℝ) ^ M := by
            apply Finset.sum_le_sum
            intro M hM
            rw [shellBad_assembleDyadic, shellBad_card_eq_ratio_mul]
            have hKM := (Finset.mem_Ico.mp hM).1
            have hM₀M : M₀ ≤ M :=
              hM₀.trans hKM
            exact mul_le_mul_of_nonneg_right
              ((hshell M hM₀M).trans
                (mul_le_mul_of_nonneg_left
                  (hshiftMono M hKM) (by norm_num)))
              (by positivity)
      _ ≤ (2 * Real.exp
              (-(1 / 2 : ℝ) *
                Real.sqrt (shiftedShellSize K))) *
            (∑ M ∈ Finset.range (L + 1), (2 : ℝ) ^ M) := by
          rw [Finset.mul_sum]
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro x hx
            exact Finset.mem_range.2 (Finset.mem_Ico.mp hx).2
          · intro i _ _
            positivity
      _ = (2 * Real.exp
              (-(1 / 2 : ℝ) *
                Real.sqrt (shiftedShellSize K))) *
            ((2 : ℝ) ^ (L + 1) - 1) := by
          rw [sum_two_pow_range]
      _ ≤ 2 * Real.exp
              (-(1 / 2 : ℝ) *
                Real.sqrt (shiftedShellSize K)) *
            (2 : ℝ) ^ (L + 1) := by
          have hcoef :
              0 ≤ 2 * Real.exp
                (-(1 / 2 : ℝ) *
                  Real.sqrt (shiftedShellSize K)) := by positivity
          nlinarith [show 0 ≤ (2 : ℝ) ^ (L + 1) by positivity]
  have hpowN : (2 : ℝ) ^ L ≤ N := by
    dsimp [L]
    exact_mod_cast Nat.pow_log_le_self 2 hN.ne'
  have hpowSuccN : (2 : ℝ) ^ (L + 1) ≤ 2 * N := by
    rw [pow_succ]
    nlinarith
  have hLK : L ≤ 2 * K + 1 := by
    dsimp [K]
    omega
  have hquarter :
      (L : ℝ) / 4 ≤ shiftedShellSize K := by
    have hcast : (L : ℝ) ≤ 2 * K + 1 := by exact_mod_cast hLK
    unfold shiftedShellSize
    nlinarith
  have hsqrtQuarter :
      Real.sqrt (L : ℝ) / 2 ≤
        Real.sqrt (shiftedShellSize K) := by
    have hL0 : 0 ≤ (L : ℝ) := Nat.cast_nonneg L
    have hsqrt :=
      Real.sqrt_le_sqrt hquarter
    rw [Real.sqrt_div hL0] at hsqrt
    have hsqrtFour : Real.sqrt (4 : ℝ) = 2 := by
      have hsquare := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 4)
      have hnonneg := Real.sqrt_nonneg (4 : ℝ)
      nlinarith
    simpa [hsqrtFour] using hsqrt
  have hhighRate :
      Real.exp
          (-(1 / 2 : ℝ) * Real.sqrt (shiftedShellSize K)) ≤
        Real.exp
          (-(1 / 4 : ℝ) * Real.sqrt (L : ℝ)) := by
    apply Real.exp_le_exp.2
    nlinarith
  have hsqrtLeL :
      Real.sqrt (L : ℝ) ≤ (L : ℝ) := by
    rw [Real.sqrt_le_iff]
    constructor
    · exact Nat.cast_nonneg L
    · have hLR : (1 : ℝ) ≤ L := by exact_mod_cast hL1
      nlinarith
  have hlogLinear :
      (1 / 8 : ℝ) * Real.sqrt (L : ℝ) ≤
        Real.log 2 * (L : ℝ) / 2 := by
    have hcoef : (1 / 8 : ℝ) ≤ Real.log 2 / 2 := by
      linarith [Real.log_two_gt_d9]
    calc
      (1 / 8 : ℝ) * Real.sqrt (L : ℝ)
          ≤ (1 / 8 : ℝ) * L :=
        mul_le_mul_of_nonneg_left hsqrtLeL (by norm_num)
      _ ≤ (Real.log 2 / 2) * L :=
        mul_le_mul_of_nonneg_right hcoef (Nat.cast_nonneg L)
      _ = Real.log 2 * L / 2 := by ring
  have hearlyRate :
      (2 : ℝ) ^ K ≤
        2 * N *
          Real.exp
            (-(1 / 8 : ℝ) * Real.sqrt (L : ℝ)) := by
    have hKLhalf : (K : ℝ) ≤ (L : ℝ) / 2 := by
      have htwo : 2 * K ≤ L := by
        dsimp [K]
        exact Nat.mul_div_le L 2
      have htwoR : (2 : ℝ) * K ≤ L := by
        exact_mod_cast htwo
      linarith
    have hpowK :
        (2 : ℝ) ^ K ≤
          (2 : ℝ) ^ ((L : ℝ) / 2) := by
        simpa only [Real.rpow_natCast] using
          Real.rpow_le_rpow_of_exponent_le
            (x := (2 : ℝ)) (by norm_num) hKLhalf
    have hexpIdentity :
        (2 : ℝ) ^ ((L : ℝ) / 2) =
          (2 : ℝ) ^ L *
            Real.exp (-(Real.log 2 * L / 2)) := by
      have hpowL :
          (2 : ℝ) ^ L = Real.exp (Real.log 2 * L) := by
        rw [← Real.rpow_natCast,
          Real.rpow_def_of_pos (by norm_num)]
      rw [Real.rpow_def_of_pos (by norm_num), hpowL]
      rw [← Real.exp_add]
      congr 1
      ring
    have hexpCompare :
        Real.exp (-(Real.log 2 * L / 2)) ≤
          Real.exp
            (-(1 / 8 : ℝ) * Real.sqrt (L : ℝ)) :=
      Real.exp_le_exp.2 (by linarith)
    calc
      (2 : ℝ) ^ K
          ≤ (2 : ℝ) ^ ((L : ℝ) / 2) := hpowK
      _ = (2 : ℝ) ^ L *
            Real.exp (-(Real.log 2 * L / 2)) := hexpIdentity
      _ ≤ N *
            Real.exp
              (-(1 / 8 : ℝ) * Real.sqrt (L : ℝ)) :=
        mul_le_mul hpowN hexpCompare
          (Real.exp_nonneg _) (by positivity)
      _ ≤ 2 * N *
            Real.exp
              (-(1 / 8 : ℝ) * Real.sqrt (L : ℝ)) := by
        have hnonneg :
            0 ≤ (N : ℝ) *
              Real.exp
                (-(1 / 8 : ℝ) * Real.sqrt (L : ℝ)) := by
          positivity
        nlinarith
  have hlateRate :
      2 * Real.exp
            (-(1 / 2 : ℝ) * Real.sqrt (shiftedShellSize K)) *
          (2 : ℝ) ^ (L + 1) ≤
        4 * N *
          Real.exp
            (-(1 / 8 : ℝ) * Real.sqrt (L : ℝ)) := by
    have hquarterE :
        Real.exp
            (-(1 / 4 : ℝ) * Real.sqrt (L : ℝ)) ≤
          Real.exp
            (-(1 / 8 : ℝ) * Real.sqrt (L : ℝ)) := by
      apply Real.exp_le_exp.2
      nlinarith [Real.sqrt_nonneg (L : ℝ)]
    calc
      2 * Real.exp
              (-(1 / 2 : ℝ) * Real.sqrt (shiftedShellSize K)) *
            (2 : ℝ) ^ (L + 1)
          ≤ 2 * Real.exp
              (-(1 / 4 : ℝ) * Real.sqrt (L : ℝ)) *
            (2 : ℝ) ^ (L + 1) := by
        gcongr
      _ ≤ 2 * Real.exp
              (-(1 / 8 : ℝ) * Real.sqrt (L : ℝ)) *
            (2 * N) := by
        gcongr
      _ = 4 * N *
            Real.exp
              (-(1 / 8 : ℝ) * Real.sqrt (L : ℝ)) := by ring
  calc
    ((badPrefix (assembleDyadic S) N).card : ℝ)
        ≤ (∑ M ∈ Finset.range K,
            ((shellBad (assembleDyadic S) M).card : ℝ)) +
          ∑ M ∈ Finset.Ico K (L + 1),
            ((shellBad (assembleDyadic S) M).card : ℝ) := hprefixR
    _ ≤ (2 : ℝ) ^ K +
          2 * Real.exp
              (-(1 / 2 : ℝ) * Real.sqrt (shiftedShellSize K)) *
            (2 : ℝ) ^ (L + 1) :=
      add_le_add hearly hlate
    _ ≤ 2 * N *
            Real.exp
              (-(1 / 8 : ℝ) * Real.sqrt (L : ℝ)) +
          4 * N *
            Real.exp
              (-(1 / 8 : ℝ) * Real.sqrt (L : ℝ)) :=
      add_le_add hearlyRate hlateRate
    _ = _ := by ring

/-- The shell family used by Theorem B satisfies the square-root shell
majorant eventually. -/
theorem theoremBShell_eventually_le_sqrt_rate
    {q s a : ℝ}
    (hq0 : 0 < q) (hqa : a0 < q) (hq1 : q < 1)
    (hs : 0 < s) (hv : scheduleV s < 1)
    (hua : a < scheduleU q s) :
    ∀ᶠ M : ℕ in Filter.atTop,
      shellExceptionalRatio (theoremBShell q s a M) M ≤
        2 * Real.exp
          (-(1 / 2 : ℝ) * Real.sqrt (shiftedShellSize M)) := by
  have hbudget :=
    theoremBShellBudget_eventually hq0 hqa hq1 hs hua
  have heq :=
    theoremBShell_ratio_eventually_eq hbudget
  have hmodel :=
    explicitShellExceptionalRatio_eventually_le_model
      hq0 hqa hq1 hs hv
  filter_upwards [heq, hmodel, modelShellDecay_eventually_le_sqrt]
    with M heqM hmodelM hsqrtM
  rw [heqM]
  exact hmodelM.trans (by
    simpa [Real.sqrt_eq_rpow] using hsqrtM)

/-- Quantitative exceptional-count estimate in the natural dyadic shell
coordinate `log₂ N`. -/
theorem theoremBSet_badPrefix_eventually_le_logTwo_sqrt
    {q s a : ℝ}
    (hq0 : 0 < q) (hqa : a0 < q) (hq1 : q < 1)
    (hs : 0 < s) (hv : scheduleV s < 1)
    (hua : a < scheduleU q s) :
    ∀ᶠ N : ℕ in Filter.atTop,
      ((badPrefix (theoremBSet q s a) N).card : ℝ) ≤
        6 * N *
          Real.exp
            (-(1 / 8 : ℝ) *
              Real.sqrt (Nat.log 2 N : ℝ)) := by
  obtain ⟨M₀, hM₀⟩ :=
    Filter.eventually_atTop.1
      (theoremBShell_eventually_le_sqrt_rate
        hq0 hqa hq1 hs hv hua)
  let N₀ := 2 ^ (2 * M₀ + 2)
  filter_upwards [Filter.eventually_ge_atTop N₀] with N hN₀
  have hN0 : 0 < N := by
    have hpow0 : 0 < N₀ := by
      dsimp [N₀]
      positivity
    omega
  have hlogLower :
      2 * M₀ + 2 ≤ Nat.log 2 N := by
    apply Nat.le_log_of_pow_le (by norm_num)
    exact hN₀
  have hlogOne : 1 ≤ Nat.log 2 N := by omega
  have hMhalf : M₀ ≤ Nat.log 2 N / 2 := by
    apply (Nat.le_div_iff_mul_le (by norm_num : 0 < 2)).2
    omega
  exact card_badPrefix_assembleDyadic_le_sqrt_rate
    (theoremBShell q s a) M₀ N
    (fun M hM => hM₀ M hM)
    hN0 hlogOne hMhalf

/-- The same estimate in natural-log coordinates, matching Corollary B.2. -/
theorem theoremBSet_badPrefix_eventually_le_sqrt_log
    {q s a : ℝ}
    (hq0 : 0 < q) (hqa : a0 < q) (hq1 : q < 1)
    (hs : 0 < s) (hv : scheduleV s < 1)
    (hua : a < scheduleU q s) :
    ∀ᶠ N : ℕ in Filter.atTop,
      ((badPrefix (theoremBSet q s a) N).card : ℝ) ≤
        6 * N *
          Real.exp
            (-(1 / 16 : ℝ) *
              Real.sqrt (Real.log N)) := by
  have hbase :=
    theoremBSet_badPrefix_eventually_le_logTwo_sqrt
      hq0 hqa hq1 hs hv hua
  filter_upwards [hbase, Filter.eventually_ge_atTop 4] with N hbad hN4
  let L := Nat.log 2 N
  have hN0 : 0 < N := by omega
  have hL2 : 2 ≤ L := by
    apply Nat.le_log_of_pow_le (by norm_num)
    simpa [L] using hN4
  have hNupperNat : N < 2 ^ (L + 1) := by
    dsimp [L]
    exact Nat.lt_pow_succ_log_self (by norm_num) N
  have hNupper : (N : ℝ) ≤ (2 : ℝ) ^ (L + 1) := by
    exact_mod_cast hNupperNat.le
  have hNR0 : (0 : ℝ) < N := by exact_mod_cast hN0
  have hlogUpper :
      Real.log N ≤ ((L : ℝ) + 1) * Real.log 2 := by
    have h :=
      Real.strictMonoOn_log.monotoneOn
        (Set.mem_Ioi.mpr hNR0)
        (Set.mem_Ioi.mpr
          (by positivity : 0 < (2 : ℝ) ^ (L + 1)))
        hNupper
    rw [Real.log_pow] at h
    push_cast at h
    simpa [mul_comm] using h
  have hlogTwoLt : Real.log 2 < 1 :=
    Real.log_two_lt_d9.trans (by norm_num)
  have hlogFourL :
      Real.log N ≤ 4 * (L : ℝ) := by
    have hLR : (2 : ℝ) ≤ L := by exact_mod_cast hL2
    have hlogNonneg := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)
    nlinarith
  have hsqrtCompare :
      Real.sqrt (Real.log N) ≤
        2 * Real.sqrt (L : ℝ) := by
    rw [Real.sqrt_le_iff]
    constructor
    · positivity
    · have hL0 : 0 ≤ (L : ℝ) := Nat.cast_nonneg L
      rw [mul_pow, Real.sq_sqrt hL0]
      norm_num
      exact hlogFourL
  have hexpCompare :
      Real.exp
          (-(1 / 8 : ℝ) * Real.sqrt (L : ℝ)) ≤
        Real.exp
          (-(1 / 16 : ℝ) * Real.sqrt (Real.log N)) := by
    apply Real.exp_le_exp.2
    nlinarith
  exact hbad.trans
    (mul_le_mul_of_nonneg_left hexpCompare
      (mul_nonneg (by norm_num) (Nat.cast_nonneg N)))

/-- Corollary B.2 for the literal existential-iterate event. -/
theorem quantitativeQuadraticTheoremB_exceptional_count
    {a : ℝ} (ha0 : 0 < a)
    (ha : a < quadraticHeadlineExponent) :
    ∀ᶠ N : ℕ in Filter.atTop,
      ((badPrefix (quantitativeTheoremBSet a 1) N).card : ℝ) ≤
        6 * N *
          Real.exp
            (-(1 / 16 : ℝ) *
              Real.sqrt (Real.log N)) := by
  let q := theoremBChoiceQ a
  let s := theoremBChoiceS a q
  have hq := theoremBChoiceQ_properties ha0 ha
  have hs := theoremBChoiceS_properties ha0 hq.1 hq.2.2.1 hq.2.2.2
  have hgenerated :=
    theoremBSet_badPrefix_eventually_le_sqrt_log
      hq.1 hq.2.1 hq.2.2.1 hs.1 hs.2.2 hs.2.1
  filter_upwards [hgenerated] with N hN
  have hsub :
      badPrefix (quantitativeTheoremBSet a 1) N ⊆
        badPrefix (theoremBSet q s a) N := by
    intro n hn
    simp only [badPrefix, Finset.mem_filter] at hn ⊢
    exact ⟨hn.1, fun hgood =>
      hn.2 (theoremBSet_subset_quantitativeTheoremBSet
        hq.1 hq.2.1 ha0 hgood)⟩
  have hcard :
      ((badPrefix (quantitativeTheoremBSet a 1) N).card : ℝ) ≤
        ((badPrefix (theoremBSet q s a) N).card : ℝ) := by
    exact_mod_cast Finset.card_le_card hsub
  exact hcard.trans hN

/-- The lower-envelope survival corollary has the same explicit exceptional
count as Theorem B because both are consequences of the scheduled shell
envelope. -/
theorem quantitativeQuadraticSurvival_exceptional_count
    {a : ℝ} (ha0 : 0 < a)
    (ha : a < quadraticHeadlineExponent) :
    ∀ᶠ N : ℕ in Filter.atTop,
      ((badPrefix (quantitativeSurvivalSet a) N).card : ℝ) ≤
        6 * N *
          Real.exp
            (-(1 / 16 : ℝ) *
              Real.sqrt (Real.log N)) := by
  let q := theoremBChoiceQ a
  let s := theoremBChoiceS a q
  have hq := theoremBChoiceQ_properties ha0 ha
  have hs := theoremBChoiceS_properties ha0 hq.1 hq.2.2.1 hq.2.2.2
  have hgenerated :=
    theoremBSet_badPrefix_eventually_le_sqrt_log
      hq.1 hq.2.1 hq.2.2.1 hs.1 hs.2.2 hs.2.1
  filter_upwards [hgenerated] with N hN
  have hsub :
      badPrefix (quantitativeSurvivalSet a) N ⊆
        badPrefix (theoremBSet q s a) N := by
    intro n hn
    simp only [badPrefix, Finset.mem_filter] at hn ⊢
    exact ⟨hn.1, fun hgood =>
      hn.2 (theoremBSet_subset_survival
        hq.1 hq.2.1 hq.2.2.1 ha0 hgood)⟩
  have hcard :
      ((badPrefix (quantitativeSurvivalSet a) N).card : ℝ) ≤
        ((badPrefix (theoremBSet q s a) N).card : ℝ) := by
    exact_mod_cast Finset.card_le_card hsub
  exact hcard.trans hN

end

end QuantitativeDensity

end CollatzEndpointTransport
