/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik
-/
import CollatzEndpointTransport.QuadraticAppendix.QuantitativeQuadraticShellVanishing
import CollatzEndpointTransport.Common.QuantitativeEndpoint

/-!
# Quantitative Quadratic Theorem B

End-to-end quantitative quadratic theorem.

The shell schedule is explicit:

  R_M = ceil (s * log (log (M + 4))),

where `a / log(1/q) < s < 1 / log 2`.  The first inequality makes the
terminal envelope exponent smaller than `(log M)^{-a}`; the second makes
the concrete quadratic stage cost `o(log M)`.
-/

namespace CollatzEndpointTransport

namespace QuantitativeDensity

open scoped Real Topology

noncomputable section

def theoremBShellExponent (a : ℝ) (M : ℕ) : ℝ :=
  (finalShellLog M) ^ (-a)

def theoremBShellLambda (q s : ℝ) (M : ℕ) : ℝ :=
  stageLambda q (explicitStageCount s M)

def theoremBShellTolerance (q s : ℝ) (M : ℕ) : ℝ :=
  explicitTerminalTolerance q (explicitStageCount s M)

def theoremBShellBudget (q s a : ℝ) (M : ℕ) : Prop :=
  (M : ℝ) *
        (theoremBShellLambda q s M + theoremBShellTolerance q s M) +
      bConst + 1 + theoremBShellTolerance q s M ≤
    (M : ℝ) * theoremBShellExponent a M

def theoremBShell (q s a : ℝ) (M : ℕ) : Set ℕ := by
  classical
  exact if theoremBShellBudget q s a M ∧ 4 ≤ M then
    explicitShellEnvelope q s M
  else
    ∅

def theoremBSet (q s a : ℝ) : Set ℕ :=
  assembleDyadic (theoremBShell q s a)

theorem theoremBShellExponent_pos (a : ℝ) (M : ℕ) :
    0 < theoremBShellExponent a M :=
  Real.rpow_pos_of_pos (finalShellLog_pos M) _

theorem theoremBShellLambda_pos
    {q : ℝ} (hq0 : 0 < q) (s : ℝ) (M : ℕ) :
    0 < theoremBShellLambda q s M :=
  stageLambda_pos hq0 _

theorem theoremBShellTolerance_pos
    {q : ℝ} (hq0 : 0 < q) (hqa : a0 < q)
    (s : ℝ) (M : ℕ) :
    0 < theoremBShellTolerance q s M :=
  explicitTerminalTolerance_pos hq0 hqa _

theorem theoremBShellLambda_le
    {q s : ℝ}
    (hq0 : 0 < q) (hq1 : q < 1) (hs : 0 < s) (M : ℕ) :
    theoremBShellLambda q s M ≤
      a0 * (finalShellLog M) ^ (-scheduleU q s) := by
  unfold theoremBShellLambda stageLambda
  simpa [scheduleU] using mul_le_mul_of_nonneg_left
    (explicit_q_pow_upper hq0 hq1 hs M) a0_pos.le

theorem terminalDriftRatio_tendsto_zero
    {q s a : ℝ}
    (hq0 : 0 < q) (hqa : a0 < q) (hq1 : q < 1)
    (hs : 0 < s) (hua : a < scheduleU q s) :
    Filter.Tendsto
      (fun M =>
        (theoremBShellLambda q s M + theoremBShellTolerance q s M) /
          theoremBShellExponent a M)
      Filter.atTop (nhds 0) := by
  have hgap : 0 < scheduleU q s - a := sub_pos.mpr hua
  have hmodel :
      Filter.Tendsto
        (fun M =>
          ((1 + cq q) * a0) *
            (finalShellLog M) ^ (-(scheduleU q s - a)))
        Filter.atTop (nhds 0) := by
      simpa [Function.comp_apply] using
        ((tendsto_rpow_neg_atTop hgap).comp
          finalShellLog_tendsto_atTop).const_mul ((1 + cq q) * a0)
  have hnonneg :
      ∀ M,
        0 ≤
          (theoremBShellLambda q s M +
              theoremBShellTolerance q s M) /
            theoremBShellExponent a M := by
    intro M
    exact div_nonneg
      (add_nonneg
        (theoremBShellLambda_pos hq0 s M).le
        (theoremBShellTolerance_pos hq0 hqa s M).le)
      (theoremBShellExponent_pos a M).le
  have hupper :
      ∀ M,
        (theoremBShellLambda q s M +
              theoremBShellTolerance q s M) /
            theoremBShellExponent a M ≤
          ((1 + cq q) * a0) *
            (finalShellLog M) ^ (-(scheduleU q s - a)) := by
    intro M
    have hlam := theoremBShellLambda_le hq0 hq1 hs M
    have htcap :=
      explicitTerminalTolerance_le_cap hq0 hqa
        (explicitStageCount s M)
    have hsum :
        theoremBShellLambda q s M +
            theoremBShellTolerance q s M ≤
          (1 + cq q) * a0 *
            (finalShellLog M) ^ (-scheduleU q s) := by
      have hlam0 := (theoremBShellLambda_pos hq0 s M).le
      unfold theoremBShellTolerance at htcap
      unfold theoremBShellTolerance theoremBShellLambda
      calc
        stageLambda q (explicitStageCount s M) +
              explicitTerminalTolerance q (explicitStageCount s M)
            ≤ (1 + cq q) *
                stageLambda q (explicitStageCount s M) := by
              nlinarith [htcap]
        _ ≤ (1 + cq q) *
              (a0 * finalShellLog M ^ (-scheduleU q s)) :=
            mul_le_mul_of_nonneg_left hlam
              (by linarith [cq_pos hq0 hqa])
        _ = _ := by ring
    have hL := finalShellLog_pos M
    have heps := theoremBShellExponent_pos a M
    have hdiv :=
      div_le_div_of_nonneg_right hsum heps.le
    have hratio :
        ((1 + cq q) * a0 *
              finalShellLog M ^ (-scheduleU q s)) /
            theoremBShellExponent a M =
          ((1 + cq q) * a0) *
            finalShellLog M ^ (-(scheduleU q s - a)) := by
      unfold theoremBShellExponent
      calc
        ((1 + cq q) * a0 *
              finalShellLog M ^ (-scheduleU q s)) /
              finalShellLog M ^ (-a)
            = ((1 + cq q) * a0) *
                (finalShellLog M ^ (-scheduleU q s) /
                  finalShellLog M ^ (-a)) := by ring
        _ = ((1 + cq q) * a0) *
              finalShellLog M ^
                ((-scheduleU q s) - (-a)) := by
              rw [← Real.rpow_sub hL]
        _ = _ := by congr 2 <;> ring
    exact hdiv.trans_eq hratio
  exact squeeze_zero hnonneg hupper hmodel

theorem terminalFloorRatio_tendsto_zero
    {q s a : ℝ}
    (hq0 : 0 < q) (hqa : a0 < q) :
    Filter.Tendsto
      (fun M =>
        (bConst + 1 + theoremBShellTolerance q s M) /
          ((M : ℝ) * theoremBShellExponent a M))
      Filter.atTop (nhds 0) := by
  have hbase :
      Filter.Tendsto
        (fun M : ℕ =>
          (finalShellLog M) ^ a / shiftedShellSize M)
        Filter.atTop (nhds 0) := by
    have hreal :=
      (isLittleO_log_rpow_rpow_atTop a
        (by norm_num : (0 : ℝ) < 1)).tendsto_div_nhds_zero
    have hcomp := hreal.comp shiftedShellSize_tendsto_atTop
    convert hcomp using 1
    funext M
    simp [Function.comp_apply, finalShellLog_eq_log_shifted,
      Real.rpow_one]
  have hmodel :=
    hbase.const_mul (2 * (bConst + 2))
  have hMlarge : ∀ᶠ M : ℕ in Filter.atTop, 4 ≤ M :=
    Filter.eventually_atTop.2 ⟨4, fun _ h => h⟩
  have hnonneg :
      ∀ᶠ M : ℕ in Filter.atTop,
        0 ≤
          (bConst + 1 + theoremBShellTolerance q s M) /
            ((M : ℝ) * theoremBShellExponent a M) := by
    filter_upwards [hMlarge] with M hM
    exact div_nonneg
      (by
        have ht := theoremBShellTolerance_pos hq0 hqa s M
        linarith [bConst_pos])
      (mul_nonneg (Nat.cast_nonneg M)
        (theoremBShellExponent_pos a M).le)
  have hupper :
      ∀ᶠ M : ℕ in Filter.atTop,
        (bConst + 1 + theoremBShellTolerance q s M) /
            ((M : ℝ) * theoremBShellExponent a M) ≤
          2 * (bConst + 2) *
            ((finalShellLog M) ^ a / shiftedShellSize M) := by
    filter_upwards [hMlarge] with M hM4
    have ht1 :=
      explicitTerminalTolerance_le_one hq0 hqa
        (explicitStageCount s M)
    have hM0 : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
    have hshift0 := shiftedShellSize_pos M
    have hMhalf :
        shiftedShellSize M / 2 ≤ (M : ℝ) := by
      have hM4R : (4 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM4
      unfold shiftedShellSize
      linarith
    have hepsInv :
        (theoremBShellExponent a M)⁻¹ =
          (finalShellLog M) ^ a := by
      unfold theoremBShellExponent
      rw [Real.rpow_neg (finalShellLog_pos M).le, inv_inv]
    have hnum :
        bConst + 1 + theoremBShellTolerance q s M ≤ bConst + 2 := by
      unfold theoremBShellTolerance
      linarith
    have hden :
        1 / (M : ℝ) ≤ 2 / shiftedShellSize M := by
      have h := one_div_le_one_div_of_le
        (by positivity : 0 < shiftedShellSize M / 2) hMhalf
      simpa [one_div_div] using h
    have horiginal :
        (bConst + 1 + theoremBShellTolerance q s M) /
            ((M : ℝ) * theoremBShellExponent a M) =
          (bConst + 1 + theoremBShellTolerance q s M) *
            ((finalShellLog M) ^ a * (M : ℝ)⁻¹) := by
      rw [div_eq_mul_inv, mul_inv_rev, hepsInv]
    rw [horiginal]
    have hnum0 : 0 ≤ bConst + 1 +
        theoremBShellTolerance q s M := by
      linarith [bConst_pos, theoremBShellTolerance_pos hq0 hqa s M]
    calc
      (bConst + 1 + theoremBShellTolerance q s M) *
            ((finalShellLog M) ^ a * (M : ℝ)⁻¹)
          ≤ (bConst + 2) *
            ((finalShellLog M) ^ a * (M : ℝ)⁻¹) := by
              exact mul_le_mul_of_nonneg_right hnum
                (mul_nonneg
                  (Real.rpow_nonneg (finalShellLog_pos M).le _)
                  (inv_nonneg.mpr hM0.le))
      _ ≤ (bConst + 2) *
            ((finalShellLog M) ^ a *
              (2 / shiftedShellSize M)) := by
              exact mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_left
                  (by simpa [one_div] using hden)
                  (Real.rpow_nonneg
                    (finalShellLog_pos M).le _))
                (by linarith [bConst_pos])
      _ = 2 * (bConst + 2) *
            ((finalShellLog M) ^ a / shiftedShellSize M) := by ring
  exact squeeze_zero' hnonneg hupper (by simpa using hmodel)

theorem theoremBShellBudget_eventually
    {q s a : ℝ}
    (hq0 : 0 < q) (hqa : a0 < q) (hq1 : q < 1)
    (hs : 0 < s) (hua : a < scheduleU q s) :
    ∀ᶠ M : ℕ in Filter.atTop, theoremBShellBudget q s a M := by
  have hdrift :=
    terminalDriftRatio_tendsto_zero hq0 hqa hq1 hs hua
  have hfloor :=
    terminalFloorRatio_tendsto_zero (q := q) (s := s) (a := a) hq0 hqa
  have hsum := hdrift.add hfloor
  have hone :
      ∀ᶠ M : ℕ in Filter.atTop,
        (theoremBShellLambda q s M + theoremBShellTolerance q s M) /
              theoremBShellExponent a M +
            (bConst + 1 + theoremBShellTolerance q s M) /
              ((M : ℝ) * theoremBShellExponent a M) < 1 := by
    have hdist := (Metric.tendsto_atTop.1 hsum) 1 zero_lt_one
    filter_upwards [Filter.eventually_atTop.2 hdist] with M hM
    rw [Real.dist_eq] at hM
    simpa using lt_of_le_of_lt (le_abs_self _) hM
  have hMpos : ∀ᶠ M : ℕ in Filter.atTop, 0 < M :=
    Filter.eventually_atTop.2 ⟨1, fun _ h => by omega⟩
  filter_upwards [hone, hMpos] with M hratio hM
  have heps := theoremBShellExponent_pos a M
  unfold theoremBShellBudget
  have hden : 0 < (M : ℝ) * theoremBShellExponent a M :=
    mul_pos (by exact_mod_cast hM) heps
  have hid :
      ((M : ℝ) *
            (theoremBShellLambda q s M + theoremBShellTolerance q s M) +
          bConst + 1 + theoremBShellTolerance q s M) /
          ((M : ℝ) * theoremBShellExponent a M) =
        (theoremBShellLambda q s M + theoremBShellTolerance q s M) /
            theoremBShellExponent a M +
          (bConst + 1 + theoremBShellTolerance q s M) /
            ((M : ℝ) * theoremBShellExponent a M) := by
    field_simp
    ring
  rw [← hid] at hratio
  exact (div_le_one hden).mp hratio.le

theorem theoremBShell_ratio_eventually_eq
    {q s a : ℝ}
    (hbudget : ∀ᶠ M : ℕ in Filter.atTop, theoremBShellBudget q s a M) :
    (fun M => shellExceptionalRatio (theoremBShell q s a M) M) =ᶠ[Filter.atTop]
      (fun M => shellExceptionalRatio (explicitShellEnvelope q s M) M) := by
  have hMlarge : ∀ᶠ M : ℕ in Filter.atTop, 4 ≤ M :=
    Filter.eventually_atTop.2 ⟨4, fun _ h => h⟩
  filter_upwards [hbudget, hMlarge] with M hM hM4
  simp [theoremBShell, hM, hM4]

theorem theoremBSet_hasNaturalDensityOne
    {q s a : ℝ}
    (hq0 : 0 < q) (hqa : a0 < q) (hq1 : q < 1)
    (hs : 0 < s) (hv : scheduleV s < 1)
    (hua : a < scheduleU q s) :
    HasNaturalDensityOne (theoremBSet q s a) := by
  have hbudget :=
    theoremBShellBudget_eventually hq0 hqa hq1 hs hua
  have hratio :=
    explicitShellExceptionalRatio_tendsto_zero hq0 hqa hq1 hs hv
  have hratio' :=
    hratio.congr' (theoremBShell_ratio_eventually_eq hbudget).symm
  exact hasNaturalDensityOne_assembleDyadic _ hratio'

def quantitativeTheoremBSet (a C : ℝ) : Set ℕ :=
  {n | ∃ k : ℕ,
    (((Terras.T^[k]) n : ℕ) : ℝ) ≤
      Real.exp
        (C * Real.log n /
          (Real.log (Real.log n)) ^ a)}

/-- The quantitative Theorem B event with the explicit witness-time bound
used in the paper. -/
def quantitativeTimedTheoremBSet (a C : ℝ) : Set ℕ :=
  {n | ∃ k : ℕ,
    (k : ℝ) ≤ Real.log n / (bConst * Real.log 2) ∧
      (k : ℝ) < (6953 / 1000 : ℝ) * Real.log n ∧
      (((Terras.T^[k]) n : ℕ) : ℝ) ≤
        Real.exp
          (C * Real.log n /
            (Real.log (Real.log n)) ^ a)}

theorem hasNaturalDensityOne_mono
    {S U : Set ℕ} (hSU : S ⊆ U)
    (hS : HasNaturalDensityOne S) :
    HasNaturalDensityOne U := by
  have hbad :
      ∀ N,
        ((badPrefix U N).card : ℝ) / N ≤
          ((badPrefix S N).card : ℝ) / N := by
    intro N
    have hsub : badPrefix U N ⊆ badPrefix S N := by
      intro n hn
      simp only [badPrefix, Finset.mem_filter] at hn ⊢
      exact ⟨hn.1, fun hnS => hn.2 (hSU hnS)⟩
    exact div_le_div_of_nonneg_right
      (by exact_mod_cast Finset.card_le_card hsub)
      (Nat.cast_nonneg N)
  exact squeeze_zero
    (fun N => by positivity)
    hbad
    hS

theorem mem_theoremBSet_data
    {q s a : ℝ} {n : ℕ}
    (hn : n ∈ theoremBSet q s a) :
    let M := Nat.log 2 n
    theoremBShellBudget q s a M ∧
      4 ≤ M ∧
      n ∈ explicitShellEnvelope q s M := by
  classical
  let M := Nat.log 2 n
  have hshell :
      n ∈ theoremBShell q s a M := by
    simpa [theoremBSet, assembleDyadic, M] using hn
  by_cases hcond : theoremBShellBudget q s a M ∧ 4 ≤ M
  · simpa [theoremBShell, hcond] using
      And.intro hcond hshell
  · simp [theoremBShell, hcond] at hshell

theorem log_log_le_finalShellLog
    {n M : ℕ}
    (hM : M = Nat.log 2 n) (hM4 : 4 ≤ M) :
    0 < Real.log (Real.log n) ∧
      Real.log (Real.log n) ≤ finalShellLog M := by
  have hn0 : 0 < n := by
    by_contra hn
    have hnz : n = 0 := Nat.eq_zero_of_not_pos hn
    subst n
    simp at hM
    omega
  have hnLowerNat : 2 ^ M ≤ n := by
    subst M
    exact Nat.pow_log_le_self 2 hn0.ne'
  have hnUpperNat : n < 2 ^ (M + 1) := by
    subst M
    exact Nat.lt_pow_succ_log_self (by norm_num) n
  have hnLower : (2 : ℝ) ^ M ≤ (n : ℝ) := by
    exact_mod_cast hnLowerNat
  have hnUpper : (n : ℝ) ≤ (2 : ℝ) ^ (M + 1) := by
    exact_mod_cast hnUpperNat.le
  have hpowM0 : 0 < (2 : ℝ) ^ M := by positivity
  have hnR0 : 0 < (n : ℝ) := by exact_mod_cast hn0
  have hlogLower :
      (M : ℝ) * Real.log 2 ≤ Real.log n := by
    have h :=
      Real.strictMonoOn_log.monotoneOn
        (Set.mem_Ioi.mpr hpowM0)
        (Set.mem_Ioi.mpr hnR0)
        hnLower
    rw [Real.log_pow] at h
    simpa [mul_comm] using h
  have hlognOne : 1 < Real.log n := by
    have hM4R : (4 : ℝ) ≤ M := by exact_mod_cast hM4
    nlinarith [Real.log_two_gt_d9]
  have hlogUpper :
      Real.log n ≤ ((M : ℝ) + 1) * Real.log 2 := by
    have h :=
      Real.strictMonoOn_log.monotoneOn
        (Set.mem_Ioi.mpr hnR0)
        (Set.mem_Ioi.mpr (by positivity : 0 < (2 : ℝ) ^ (M + 1)))
        hnUpper
    rw [Real.log_pow] at h
    push_cast at h
    simpa [mul_comm] using h
  have hlogShift :
      Real.log n ≤ (M : ℝ) + 4 := by
    have hlog2lt : Real.log 2 < 1 :=
      Real.log_two_lt_d9.trans (by norm_num)
    have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg M
    nlinarith
  have hloglog0 : 0 < Real.log (Real.log n) :=
    Real.log_pos hlognOne
  have hshift0 : 0 < (M : ℝ) + 4 := by positivity
  have hloglogUpper :
      Real.log (Real.log n) ≤ Real.log ((M : ℝ) + 4) :=
    Real.strictMonoOn_log.monotoneOn
      (Set.mem_Ioi.mpr (by linarith))
      (Set.mem_Ioi.mpr hshift0)
      hlogShift
  exact ⟨hloglog0, by simpa [finalShellLog] using hloglogUpper⟩

theorem shellExponent_le_logLogExponent
    {a : ℝ} {n M : ℕ}
    (ha : 0 < a)
    (hM : M = Nat.log 2 n) (hM4 : 4 ≤ M) :
    theoremBShellExponent a M ≤
      1 / (Real.log (Real.log n)) ^ a := by
  have hlog := log_log_le_finalShellLog hM hM4
  have hpow :
      (Real.log (Real.log n)) ^ a ≤
        (finalShellLog M) ^ a :=
    Real.rpow_le_rpow hlog.1.le hlog.2 ha.le
  have hleft0 :
      0 < (Real.log (Real.log n)) ^ a :=
    Real.rpow_pos_of_pos hlog.1 a
  have hright0 :
      0 < (finalShellLog M) ^ a :=
    Real.rpow_pos_of_pos (finalShellLog_pos M) a
  unfold theoremBShellExponent
  rw [Real.rpow_neg (finalShellLog_pos M).le]
  simpa [one_div] using one_div_le_one_div_of_le hleft0 hpow

theorem theoremBSet_subset_quantitativeTheoremBSet
    {q s a : ℝ}
    (hq0 : 0 < q) (hqa : a0 < q) (ha : 0 < a) :
    theoremBSet q s a ⊆ quantitativeTheoremBSet a 1 := by
  intro n hn
  obtain ⟨hbudget, hM4, hgood⟩ := mem_theoremBSet_data hn
  let M := Nat.log 2 n
  have hn0 : 0 < n := by
    by_contra hn
    have hnz : n = 0 := Nat.eq_zero_of_not_pos hn
    subst n
    simp [M] at hM4
  have ht0 :
      0 ≤ theoremBShellTolerance q s M :=
    (theoremBShellTolerance_pos hq0 hqa s M).le
  have heps0 := (theoremBShellExponent_pos a M).le
  have hiterate :=
    exists_iterate_le_rpow_of_mem_terminal_envelope
      hn0 rfl ht0 heps0 hbudget (by
        simpa [explicitShellEnvelope, theoremBShellLambda,
          theoremBShellTolerance, M, stageTolerance] using hgood)
  obtain ⟨k, hk⟩ := hiterate
  refine ⟨k, hk.trans ?_⟩
  have heps :=
    shellExponent_le_logLogExponent ha (M := M) rfl hM4
  have hlogn0 : 0 ≤ Real.log n :=
    Real.log_nonneg (by exact_mod_cast hn0)
  rw [Real.rpow_def_of_pos (by exact_mod_cast hn0)]
  apply Real.exp_le_exp.2
  calc
    Real.log (n : ℝ) * theoremBShellExponent a M
        ≤ Real.log n *
            (1 / (Real.log (Real.log n)) ^ a) :=
      mul_le_mul_of_nonneg_left heps hlogn0
    _ = 1 * Real.log n /
          (Real.log (Real.log n)) ^ a := by ring

/-- The generated shell set also supplies the explicit logarithmic-time
witness used by Corollary B.1. -/
theorem theoremBSet_subset_quantitativeTimedTheoremBSet
    {q s a : ℝ}
    (hq0 : 0 < q) (hqa : a0 < q) (hq1 : q < 1) (ha : 0 < a) :
    theoremBSet q s a ⊆ quantitativeTimedTheoremBSet a 1 := by
  intro n hn
  obtain ⟨hbudget, hM4, hgood⟩ := mem_theoremBSet_data hn
  let M := Nat.log 2 n
  have hn0 : 0 < n := by
    by_contra hn
    have hnz : n = 0 := Nat.eq_zero_of_not_pos hn
    subst n
    simp [M] at hM4
  have ht0 :
      0 ≤ theoremBShellTolerance q s M :=
    (theoremBShellTolerance_pos hq0 hqa s M).le
  have heps0 := (theoremBShellExponent_pos a M).le
  let k := envelopeHorizon (theoremBShellLambda q s M) n
  have hgood' :
      n ∈ EnvelopeGood
        (theoremBShellLambda q s M)
        (theoremBShellTolerance q s M) := by
    simpa [explicitShellEnvelope, theoremBShellLambda,
      theoremBShellTolerance, M, stageTolerance] using hgood
  have hvalue :
      (((Terras.T^[k]) n : ℕ) : ℝ) ≤
        (n : ℝ) ^ theoremBShellExponent a M := by
    simpa [k] using
      iterate_at_horizon_le_rpow_of_mem_terminal_envelope
        hn0 rfl ht0 heps0 hbudget hgood'
  have hlambda0 :
      0 ≤ theoremBShellLambda q s M :=
    (theoremBShellLambda_pos hq0 s M).le
  have hlambda1 :
      theoremBShellLambda q s M ≤ 1 := by
    exact (stageLambda_lt_one hq0 hq1
      (explicitStageCount s M)).le
  have htime :
      (k : ℝ) ≤ Real.log n / (bConst * Real.log 2) := by
    simpa [k] using
      envelopeHorizon_le_natural_log_time
        hn0 hlambda0 hlambda1
  have hnOne : 1 < n := by
    have hpow := Nat.pow_log_le_self 2 hn0.ne'
    have hpowFour : 2 ^ 4 ≤ n := (Nat.pow_le_pow_right (by norm_num) hM4).trans hpow
    omega
  have htimeDecimal :
      (k : ℝ) < (6953 / 1000 : ℝ) * Real.log n := by
    simpa [k] using
      envelopeHorizon_lt_6953_log hnOne hlambda0 hlambda1
  refine ⟨k, htime, htimeDecimal, hvalue.trans ?_⟩
  have heps :=
    shellExponent_le_logLogExponent ha (M := M) rfl hM4
  have hlogn0 : 0 ≤ Real.log n :=
    Real.log_nonneg (by exact_mod_cast hn0)
  rw [Real.rpow_def_of_pos (by exact_mod_cast hn0)]
  apply Real.exp_le_exp.2
  calc
    Real.log (n : ℝ) * theoremBShellExponent a M
        ≤ Real.log n *
            (1 / (Real.log (Real.log n)) ^ a) :=
      mul_le_mul_of_nonneg_left heps hlogn0
    _ = 1 * Real.log n /
          (Real.log (Real.log n)) ^ a := by ring

def theoremBChoiceQ (a : ℝ) : ℝ :=
  (a0 + Real.exp (-a * Real.log 2)) / 2

def theoremBChoiceS (a q : ℝ) : ℝ :=
  (a / Real.log (1 / q) + 1 / Real.log 2) / 2

theorem theoremBChoiceQ_properties
    {a : ℝ} (ha0 : 0 < a)
    (ha : a < quadraticHeadlineExponent) :
    0 < theoremBChoiceQ a ∧
      a0 < theoremBChoiceQ a ∧
      theoremBChoiceQ a < 1 ∧
      a < quadraticAdmissibleExponent (theoremBChoiceQ a) := by
  have hlog2 := log_two_pos
  have haMul :
      a * Real.log 2 < Real.log (1 / a0) := by
    unfold quadraticHeadlineExponent quadraticAdmissibleExponent at ha
    exact (lt_div_iff₀ hlog2).mp ha
  let r := Real.exp (-a * Real.log 2)
  have hr0 : 0 < r := Real.exp_pos _
  have hr1 : r < 1 := by
    dsimp [r]
    rw [← Real.exp_zero]
    exact Real.exp_lt_exp.2 (by nlinarith)
  have hra : a0 < r := by
    have hexp :
        Real.exp (-Real.log (1 / a0)) = a0 := by
      rw [Real.exp_neg, Real.exp_log (one_div_pos.mpr a0_pos)]
      field_simp [a0_pos.ne']
    rw [← hexp]
    exact Real.exp_lt_exp.2 (by linarith)
  have hq0 : 0 < theoremBChoiceQ a := by
    unfold theoremBChoiceQ
    dsimp [r] at hr0
    nlinarith [a0_pos]
  have hqa : a0 < theoremBChoiceQ a := by
    unfold theoremBChoiceQ
    dsimp [r] at hra
    linarith
  have hq1 : theoremBChoiceQ a < 1 := by
    unfold theoremBChoiceQ
    have ha01 := a0_lt_one
    dsimp [r] at hr1
    linarith
  have hqr : theoremBChoiceQ a < r := by
    unfold theoremBChoiceQ
    dsimp [r] at hra
    linarith
  have hlogq :
      Real.log (theoremBChoiceQ a) <
        Real.log r :=
    Real.strictMonoOn_log
      (Set.mem_Ioi.mpr hq0) (Set.mem_Ioi.mpr hr0) hqr
  have hlogr : Real.log r = -a * Real.log 2 := by
    dsimp [r]
    rw [Real.log_exp]
  have hlogInv :
      a * Real.log 2 <
        Real.log (1 / theoremBChoiceQ a) := by
    rw [log_one_div_eq_neg_log hq0]
    rw [hlogr] at hlogq
    linarith
  have hadm :
      a < quadraticAdmissibleExponent (theoremBChoiceQ a) := by
    unfold quadraticAdmissibleExponent
    exact (lt_div_iff₀ hlog2).2 hlogInv
  exact ⟨hq0, hqa, hq1, hadm⟩

theorem theoremBChoiceS_properties
    {a q : ℝ} (ha0 : 0 < a)
    (hq0 : 0 < q) (hq1 : q < 1)
    (ha : a < quadraticAdmissibleExponent q) :
    0 < theoremBChoiceS a q ∧
      a < scheduleU q (theoremBChoiceS a q) ∧
      scheduleV (theoremBChoiceS a q) < 1 := by
  have hLq := log_one_div_pos hq0 hq1
  have hlog2 := log_two_pos
  have hleft :
      a / Real.log (1 / q) < 1 / Real.log 2 := by
    unfold quadraticAdmissibleExponent at ha
    rw [div_lt_div_iff₀ hLq hlog2]
    simpa using (lt_div_iff₀ hlog2).mp ha
  have hsLower :
      a / Real.log (1 / q) < theoremBChoiceS a q := by
    unfold theoremBChoiceS
    linarith
  have hsUpper :
      theoremBChoiceS a q < 1 / Real.log 2 := by
    unfold theoremBChoiceS
    linarith
  have hs0 : 0 < theoremBChoiceS a q := by
    have : 0 < a / Real.log (1 / q) := div_pos ha0 hLq
    linarith
  have hu :
      a < scheduleU q (theoremBChoiceS a q) := by
    unfold scheduleU
    have := mul_lt_mul_of_pos_right hsLower hLq
    field_simp [hLq.ne'] at this
    simpa using this
  have hv :
      scheduleV (theoremBChoiceS a q) < 1 := by
    unfold scheduleV
    have := mul_lt_mul_of_pos_right hsUpper hlog2
    field_simp [hlog2.ne'] at this
    simpa using this
  exact ⟨hs0, hu, hv⟩

/-- **Theorem B with its explicit threshold coefficient.**

For every exponent below the quadratic endpoint, the set of integers with
an iterate below the displayed `(log log n)^{-a}` threshold has natural
density one with coefficient exactly `1`. The large bookkeeping constants
affect the rate at which the exceptional density vanishes, not this orbit
threshold. -/
theorem quantitativeQuadraticTheoremB_one
    {a : ℝ} (ha0 : 0 < a)
    (ha : a < quadraticHeadlineExponent) :
    HasNaturalDensityOne (quantitativeTheoremBSet a 1) := by
  let q := theoremBChoiceQ a
  let s := theoremBChoiceS a q
  have hq := theoremBChoiceQ_properties ha0 ha
  have hs := theoremBChoiceS_properties ha0 hq.1 hq.2.2.1 hq.2.2.2
  apply hasNaturalDensityOne_mono
    (theoremBSet_subset_quantitativeTheoremBSet hq.1 hq.2.1 ha0)
  exact theoremBSet_hasNaturalDensityOne
    hq.1 hq.2.1 hq.2.2.1 hs.1 hs.2.2 hs.2.1

/-- **Theorem B with an explicit logarithmic witness time.** -/
theorem quantitativeQuadraticTheoremB_timed
    {a : ℝ} (ha0 : 0 < a)
    (ha : a < quadraticHeadlineExponent) :
    HasNaturalDensityOne (quantitativeTimedTheoremBSet a 1) := by
  let q := theoremBChoiceQ a
  let s := theoremBChoiceS a q
  have hq := theoremBChoiceQ_properties ha0 ha
  have hs := theoremBChoiceS_properties ha0 hq.1 hq.2.2.1 hq.2.2.2
  apply hasNaturalDensityOne_mono
    (theoremBSet_subset_quantitativeTimedTheoremBSet
      hq.1 hq.2.1 hq.2.2.1 ha0)
  exact theoremBSet_hasNaturalDensityOne
    hq.1 hq.2.1 hq.2.2.1 hs.1 hs.2.2 hs.2.1

/-- Existential-coefficient compatibility form of Theorem B. -/
theorem quantitativeQuadraticTheoremB
    {a : ℝ} (ha0 : 0 < a)
    (ha : a < quadraticHeadlineExponent) :
    ∃ C : ℝ, 0 < C ∧
      HasNaturalDensityOne (quantitativeTheoremBSet a C) :=
  ⟨1, zero_lt_one, quantitativeQuadraticTheoremB_one ha0 ha⟩

end

end QuantitativeDensity

end CollatzEndpointTransport
