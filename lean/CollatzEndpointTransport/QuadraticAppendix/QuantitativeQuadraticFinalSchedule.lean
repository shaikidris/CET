/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik
-/
import CollatzEndpointTransport.QuadraticAppendix.QuantitativeQuadraticRecurrenceBound
import CollatzEndpointTransport.Common.VaryingShellDensity

/-!
# Quantitative Quadratic Final Schedule

An explicit shell-dependent terminal schedule.

Instead of using a `Nat.find` first-crossing index, choose a slope `s` with

  a / log(1/q) < s < 1 / log 2

and set

  R_M = ceil (s * log (log (M + 4))).

This is equivalent for the final theorem but gives direct two-sided bounds
on `q ^ R_M` and the required upper bound on `2 ^ R_M`.
-/

namespace CollatzEndpointTransport

namespace QuantitativeDensity

open scoped Real Topology

noncomputable section

def finalShellLog (M : ℕ) : ℝ :=
  Real.log ((M : ℝ) + 4)

def finalShellLogLog (M : ℕ) : ℝ :=
  Real.log (finalShellLog M)

def explicitStageCount (s : ℝ) (M : ℕ) : ℕ :=
  ⌈s * finalShellLogLog M⌉₊

def explicitTerminalTolerance (q : ℝ) (R : ℕ) : ℝ :=
  let x := cq q * stageLambda q R
  x / (2 * (1 + x))

def explicitShellEnvelope (q s : ℝ) (M : ℕ) : Set ℕ :=
  let R := explicitStageCount s M
  EnvelopeGood (stageLambda q R)
    (stageTolerance R (explicitTerminalTolerance q R) R)

def scheduleU (q s : ℝ) : ℝ :=
  s * Real.log (1 / q)

def scheduleV (s : ℝ) : ℝ :=
  s * Real.log 2

def scheduleToleranceConstant (q : ℝ) : ℝ :=
  cq q / (2 * (1 + cq q)) * a0 * q

def scheduleLogEnvelope (q s : ℝ) (M : ℕ) : ℝ :=
  let L := finalShellLog M
  let u := scheduleU q s
  let v := scheduleV s
  let B := 2 + |Real.log (1 / scheduleToleranceConstant q)|
  2 * lemmaSevenTwoConstant q * L ^ v *
    (B + (s + u) * Real.log L)

theorem finalShellLog_gt_one (M : ℕ) :
    1 < finalShellLog M := by
  unfold finalShellLog
  have h4 : (4 : ℝ) ≤ (M : ℝ) + 4 := by
    have hM : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg M
    linarith
  have hlog4 :
      Real.log 4 ≤ Real.log ((M : ℝ) + 4) :=
    Real.strictMonoOn_log.monotoneOn
      (Set.mem_Ioi.mpr (by norm_num))
      (Set.mem_Ioi.mpr (by positivity))
      h4
  have hone4 : 1 < Real.log 4 := by
    rw [show (4 : ℝ) = 2 * 2 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
    nlinarith [Real.log_two_gt_d9]
  exact hone4.trans_le hlog4

theorem finalShellLog_pos (M : ℕ) :
    0 < finalShellLog M :=
  zero_lt_one.trans (finalShellLog_gt_one M)

theorem finalShellLogLog_pos (M : ℕ) :
    0 < finalShellLogLog M := by
  unfold finalShellLogLog
  exact Real.log_pos (finalShellLog_gt_one M)

theorem finalShellLog_tendsto_atTop :
    Filter.Tendsto finalShellLog Filter.atTop Filter.atTop := by
  have hshift :
      Filter.Tendsto (fun M : ℕ => (M : ℝ) + 4)
        Filter.atTop Filter.atTop :=
    tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
  exact Real.tendsto_log_atTop.comp hshift

theorem explicitStageCount_bounds
    {s : ℝ} (hs : 0 < s) (M : ℕ) :
    s * finalShellLogLog M ≤ explicitStageCount s M ∧
      (explicitStageCount s M : ℝ) <
        s * finalShellLogLog M + 1 := by
  have hx0 : 0 ≤ s * finalShellLogLog M :=
    mul_nonneg hs.le (finalShellLogLog_pos M).le
  exact ⟨Nat.le_ceil _, Nat.ceil_lt_add_one hx0⟩

theorem log_one_div_eq_neg_log
    {q : ℝ} (hq : 0 < q) :
    Real.log (1 / q) = -Real.log q := by
  rw [one_div, Real.log_inv]

theorem q_rpow_shell_identity
    {q s : ℝ} (hq : 0 < q) (M : ℕ) :
    q ^ (s * finalShellLogLog M) =
      (finalShellLog M) ^ (-s * Real.log (1 / q)) := by
  rw [Real.rpow_def_of_pos hq,
    Real.rpow_def_of_pos (finalShellLog_pos M)]
  rw [log_one_div_eq_neg_log hq]
  unfold finalShellLogLog
  congr 1
  ring

theorem two_rpow_shell_identity
    (s : ℝ) (M : ℕ) :
    (2 : ℝ) ^ (s * finalShellLogLog M) =
      (finalShellLog M) ^ (s * Real.log 2) := by
  rw [Real.rpow_def_of_pos (by norm_num),
    Real.rpow_def_of_pos (finalShellLog_pos M)]
  unfold finalShellLogLog
  congr 1
  ring

theorem explicit_q_pow_upper
    {q s : ℝ}
    (hq0 : 0 < q) (hq1 : q < 1) (hs : 0 < s) (M : ℕ) :
    q ^ explicitStageCount s M ≤
      (finalShellLog M) ^ (-s * Real.log (1 / q)) := by
  have hR := (explicitStageCount_bounds hs M).1
  rw [← Real.rpow_natCast, ← q_rpow_shell_identity hq0 M]
  exact Real.rpow_le_rpow_of_exponent_ge hq0 hq1.le hR

theorem explicit_q_pow_lower
    {q s : ℝ}
    (hq0 : 0 < q) (hq1 : q < 1) (hs : 0 < s) (M : ℕ) :
    q * (finalShellLog M) ^ (-s * Real.log (1 / q)) ≤
      q ^ explicitStageCount s M := by
  have hR := (explicitStageCount_bounds hs M).2.le
  rw [← Real.rpow_natCast, ← q_rpow_shell_identity hq0 M]
  have hpow :
      q ^ (s * finalShellLogLog M + 1) ≤
        q ^ (explicitStageCount s M : ℝ) :=
    Real.rpow_le_rpow_of_exponent_ge hq0 hq1.le hR
  rw [Real.rpow_add hq0, Real.rpow_one] at hpow
  simpa [mul_comm] using hpow

theorem explicit_two_pow_upper
    {s : ℝ} (hs : 0 < s) (M : ℕ) :
    (2 : ℝ) ^ explicitStageCount s M ≤
      2 * (finalShellLog M) ^ (s * Real.log 2) := by
  have hR := (explicitStageCount_bounds hs M).2.le
  rw [← Real.rpow_natCast, ← two_rpow_shell_identity s M]
  calc
    (2 : ℝ) ^ (explicitStageCount s M : ℝ)
        ≤ (2 : ℝ) ^ (s * finalShellLogLog M + 1) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) hR
    _ = 2 * (2 : ℝ) ^ (s * finalShellLogLog M) := by
      rw [Real.rpow_add (by norm_num), Real.rpow_one]
      ring

theorem explicitTerminalTolerance_pos
    {q : ℝ} (hq0 : 0 < q) (hqa : a0 < q) (R : ℕ) :
    0 < explicitTerminalTolerance q R := by
  unfold explicitTerminalTolerance
  have hx :
      0 < cq q * stageLambda q R :=
    mul_pos (cq_pos hq0 hqa) (stageLambda_pos hq0 R)
  positivity

theorem explicitTerminalTolerance_le_one
    {q : ℝ} (hq0 : 0 < q) (hqa : a0 < q) (R : ℕ) :
    explicitTerminalTolerance q R ≤ 1 := by
  unfold explicitTerminalTolerance
  have hx :
      0 < cq q * stageLambda q R :=
    mul_pos (cq_pos hq0 hqa) (stageLambda_pos hq0 R)
  have hden : 0 < 2 * (1 + cq q * stageLambda q R) := by positivity
  rw [div_le_iff₀ hden]
  nlinarith

theorem explicitTerminalTolerance_le_cap
    {q : ℝ} (hq0 : 0 < q) (hqa : a0 < q) (R : ℕ) :
    explicitTerminalTolerance q R ≤ cq q * stageLambda q R := by
  unfold explicitTerminalTolerance
  have hx :
      0 < cq q * stageLambda q R :=
    mul_pos (cq_pos hq0 hqa) (stageLambda_pos hq0 R)
  have hden : 0 < 2 * (1 + cq q * stageLambda q R) := by positivity
  rw [div_le_iff₀ hden]
  nlinarith [sq_nonneg (cq q * stageLambda q R)]

theorem explicitTerminalTolerance_lower
    {q : ℝ}
    (hq0 : 0 < q) (hqa : a0 < q) (hq1 : q < 1) (R : ℕ) :
    cq q / (2 * (1 + cq q)) * stageLambda q R ≤
      explicitTerminalTolerance q R := by
  have hcq0 := cq_pos hq0 hqa
  have hlam0 := stageLambda_pos hq0 R
  have hlam1 := (stageLambda_lt_one hq0 hq1 R).le
  unfold explicitTerminalTolerance
  have hden0 : 0 < 2 * (1 + cq q) := by positivity
  have hdenR0 :
      0 < 2 * (1 + cq q * stageLambda q R) := by positivity
  rw [div_mul_eq_mul_div, div_le_div_iff₀ hden0 hdenR0]
  have hmul :
      cq q * stageLambda q R ≤ cq q :=
    (mul_le_mul_of_nonneg_left hlam1 hcq0.le).trans_eq (mul_one _)
  nlinarith [mul_pos hcq0 hlam0]

theorem scheduleU_pos
    {q s : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (hs : 0 < s) :
    0 < scheduleU q s := by
  unfold scheduleU
  exact mul_pos hs (log_one_div_pos hq0 hq1)

theorem scheduleV_pos
    {s : ℝ} (hs : 0 < s) :
    0 < scheduleV s := by
  exact mul_pos hs log_two_pos

theorem scheduleToleranceConstant_pos
    {q : ℝ} (hq0 : 0 < q) (hqa : a0 < q) :
    0 < scheduleToleranceConstant q := by
  unfold scheduleToleranceConstant
  have hcq0 := cq_pos hq0 hqa
  have hden : 0 < 2 * (1 + cq q) := by positivity
  exact mul_pos (mul_pos (div_pos hcq0 hden) a0_pos) hq0

theorem explicitTerminalTolerance_schedule_lower
    {q s : ℝ}
    (hq0 : 0 < q) (hqa : a0 < q) (hq1 : q < 1)
    (hs : 0 < s) (M : ℕ) :
    scheduleToleranceConstant q *
        (finalShellLog M) ^ (-scheduleU q s) ≤
      explicitTerminalTolerance q (explicitStageCount s M) := by
  let R := explicitStageCount s M
  have ht :=
    explicitTerminalTolerance_lower hq0 hqa hq1 R
  have hqpow :=
    explicit_q_pow_lower hq0 hq1 hs M
  have hcoef0 :
      0 ≤ cq q / (2 * (1 + cq q)) * a0 :=
    (mul_nonneg
      (div_nonneg (cq_pos hq0 hqa).le
        (mul_nonneg (by norm_num) (by linarith [cq_pos hq0 hqa])))
      a0_pos.le)
  have hscaled :=
    mul_le_mul_of_nonneg_left hqpow hcoef0
  unfold stageLambda at ht
  dsimp [R] at ht
  unfold scheduleToleranceConstant scheduleU
  calc
    cq q / (2 * (1 + cq q)) * a0 * q *
          finalShellLog M ^ (-(s * Real.log (1 / q)))
        = (cq q / (2 * (1 + cq q)) * a0) *
            (q * finalShellLog M ^ (-s * Real.log (1 / q))) := by ring
    _ ≤ (cq q / (2 * (1 + cq q)) * a0) *
          q ^ explicitStageCount s M := hscaled
    _ ≤ explicitTerminalTolerance q (explicitStageCount s M) := by
      simpa [mul_assoc] using ht

theorem explicitTerminalTolerance_log_inv_le
    {q s : ℝ}
    (hq0 : 0 < q) (hqa : a0 < q) (hq1 : q < 1)
    (hs : 0 < s) (M : ℕ) :
    Real.log
        (1 / explicitTerminalTolerance q (explicitStageCount s M)) ≤
      |Real.log (1 / scheduleToleranceConstant q)| +
        scheduleU q s * Real.log (finalShellLog M) := by
  have hK0 := scheduleToleranceConstant_pos hq0 hqa
  have hL0 := finalShellLog_pos M
  have hu0 := scheduleU_pos hq0 hq1 hs
  have ht0 :=
    explicitTerminalTolerance_pos hq0 hqa (explicitStageCount s M)
  have hlower :=
    explicitTerminalTolerance_schedule_lower hq0 hqa hq1 hs M
  have hbase0 :
      0 <
        scheduleToleranceConstant q *
          (finalShellLog M) ^ (-scheduleU q s) :=
    mul_pos hK0 (Real.rpow_pos_of_pos hL0 _)
  have hinv :
      1 / explicitTerminalTolerance q (explicitStageCount s M) ≤
        1 /
          (scheduleToleranceConstant q *
            (finalShellLog M) ^ (-scheduleU q s)) :=
    one_div_le_one_div_of_le hbase0 hlower
  have hlog :
      Real.log
          (1 / explicitTerminalTolerance q (explicitStageCount s M)) ≤
        Real.log
          (1 /
            (scheduleToleranceConstant q *
              (finalShellLog M) ^ (-scheduleU q s))) :=
    Real.strictMonoOn_log.monotoneOn
      (Set.mem_Ioi.mpr (one_div_pos.mpr ht0))
      (Set.mem_Ioi.mpr (one_div_pos.mpr hbase0))
      hinv
  have hexact :
      Real.log
          (1 /
            (scheduleToleranceConstant q *
              (finalShellLog M) ^ (-scheduleU q s))) =
        Real.log (1 / scheduleToleranceConstant q) +
          scheduleU q s * Real.log (finalShellLog M) := by
    rw [one_div, mul_inv_rev, Real.log_mul
      (inv_ne_zero (Real.rpow_pos_of_pos hL0 _).ne')
      (inv_ne_zero hK0.ne'),
      Real.log_inv, Real.log_rpow hL0, Real.log_inv]
    rw [show 1 / scheduleToleranceConstant q =
      (scheduleToleranceConstant q)⁻¹ by rw [one_div], Real.log_inv]
    ring
  rw [hexact] at hlog
  exact hlog.trans (add_le_add_right (le_abs_self _) _)

theorem concreteScheduleCost_le_logEnvelope
    {q s : ℝ}
    (hq0 : 0 < q) (hqa : a0 < q) (hq1 : q < 1)
    (hs : 0 < s) (M : ℕ) :
    Real.log
          (1 /
            stageD (explicitStageCount s M)
              (explicitTerminalTolerance q (explicitStageCount s M))
              (explicitStageCount s M)) +
        Real.log (stageC q (explicitStageCount s M) + 2) ≤
      scheduleLogEnvelope q s M := by
  let R := explicitStageCount s M
  let tR := explicitTerminalTolerance q R
  have ht0 := explicitTerminalTolerance_pos hq0 hqa R
  have ht1 := explicitTerminalTolerance_le_one hq0 hqa R
  have hboot :=
    concrete_quadratic_bootstrap_bound
      (q := q) (tR := tR) (R := R) hqa hq1 ht0 ht1
  have htwo := explicit_two_pow_upper hs M
  have hR := (explicitStageCount_bounds hs M).2.le
  have hlogt :=
    explicitTerminalTolerance_log_inv_le hq0 hqa hq1 hs M
  have hK0 := (lemmaSevenTwoConstant_pos hqa).le
  have hLpow0 :
      0 ≤ (finalShellLog M) ^ scheduleV s :=
    Real.rpow_nonneg (finalShellLog_pos M).le _
  have hfactor0 :
      0 ≤ 1 + (R : ℝ) + Real.log (1 / tR) := by
    have ht1' : 1 ≤ 1 / tR := by
      rw [one_div]
      exact (one_le_inv₀ ht0).2 ht1
    have hlog0 := Real.log_nonneg ht1'
    positivity
  have hpowScaled :
      lemmaSevenTwoConstant q * (2 : ℝ) ^ R *
          (1 + R + Real.log (1 / tR)) ≤
        lemmaSevenTwoConstant q *
          (2 * (finalShellLog M) ^ scheduleV s) *
          (1 + R + Real.log (1 / tR)) := by
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left htwo hK0) hfactor0
  have hRlog :
      1 + (R : ℝ) + Real.log (1 / tR) ≤
        (2 + |Real.log (1 / scheduleToleranceConstant q)|) +
          (s + scheduleU q s) * Real.log (finalShellLog M) := by
    dsimp [R, tR]
    have hlogL0 : 0 ≤ Real.log (finalShellLog M) :=
      (finalShellLogLog_pos M).le
    have hR' :
        (explicitStageCount s M : ℝ) ≤
          s * Real.log (finalShellLog M) + 1 := by
      simpa [finalShellLogLog] using hR
    have hlogt' := hlogt
    nlinarith [abs_nonneg
      (Real.log (1 / scheduleToleranceConstant q))]
  have hfactorScaled :
      lemmaSevenTwoConstant q *
          (2 * (finalShellLog M) ^ scheduleV s) *
          (1 + R + Real.log (1 / tR)) ≤
        lemmaSevenTwoConstant q *
          (2 * (finalShellLog M) ^ scheduleV s) *
          ((2 + |Real.log (1 / scheduleToleranceConstant q)|) +
            (s + scheduleU q s) * Real.log (finalShellLog M)) := by
    exact mul_le_mul_of_nonneg_left hRlog
      (mul_nonneg hK0 (mul_nonneg (by norm_num) hLpow0))
  exact hboot.trans (hpowScaled.trans (by
    simpa [scheduleLogEnvelope, mul_assoc, mul_left_comm, mul_comm]
      using hfactorScaled))

theorem scheduleLogEnvelope_div_eq
    (q s : ℝ) (M : ℕ) :
    scheduleLogEnvelope q s M / finalShellLog M =
      2 * lemmaSevenTwoConstant q *
        ((2 + |Real.log (1 / scheduleToleranceConstant q)|) *
            (finalShellLog M) ^ (-(1 - scheduleV s)) +
          (s + scheduleU q s) *
            (Real.log (finalShellLog M) /
              (finalShellLog M) ^ (1 - scheduleV s))) := by
  have hL := finalShellLog_pos M
  have hpowRatio :
      (finalShellLog M) ^ scheduleV s / finalShellLog M =
        (finalShellLog M) ^ (-(1 - scheduleV s)) := by
    calc
      (finalShellLog M) ^ scheduleV s / finalShellLog M
          = (finalShellLog M) ^ scheduleV s /
              (finalShellLog M) ^ (1 : ℝ) := by
            rw [Real.rpow_one]
      _ = (finalShellLog M) ^ (scheduleV s - 1) :=
        (Real.rpow_sub hL _ _).symm
      _ = (finalShellLog M) ^ (-(1 - scheduleV s)) := by ring_nf
  have hlogRatio :
      (finalShellLog M) ^ scheduleV s *
            Real.log (finalShellLog M) / finalShellLog M =
        Real.log (finalShellLog M) /
          (finalShellLog M) ^ (1 - scheduleV s) := by
    have hneg :
        (finalShellLog M) ^ (-(1 - scheduleV s)) =
          ((finalShellLog M) ^ (1 - scheduleV s))⁻¹ :=
      Real.rpow_neg hL.le _
    calc
      (finalShellLog M) ^ scheduleV s *
            Real.log (finalShellLog M) / finalShellLog M
          = ((finalShellLog M) ^ scheduleV s / finalShellLog M) *
              Real.log (finalShellLog M) := by ring
      _ = (finalShellLog M) ^ (-(1 - scheduleV s)) *
              Real.log (finalShellLog M) := by rw [hpowRatio]
      _ = Real.log (finalShellLog M) /
              (finalShellLog M) ^ (1 - scheduleV s) := by
            rw [hneg, div_eq_mul_inv]
            ring
  unfold scheduleLogEnvelope
  dsimp only
  calc
    (2 * lemmaSevenTwoConstant q *
          (finalShellLog M) ^ scheduleV s *
          ((2 + |Real.log (1 / scheduleToleranceConstant q)|) +
            (s + scheduleU q s) * Real.log (finalShellLog M))) /
        finalShellLog M
        =
      2 * lemmaSevenTwoConstant q *
        ((2 + |Real.log (1 / scheduleToleranceConstant q)|) *
            ((finalShellLog M) ^ scheduleV s / finalShellLog M) +
          (s + scheduleU q s) *
            ((finalShellLog M) ^ scheduleV s *
              Real.log (finalShellLog M) / finalShellLog M)) := by ring
    _ = _ := by rw [hpowRatio, hlogRatio]

theorem scheduleLogEnvelope_div_tendsto_zero
    {q s : ℝ}
    (hs : 0 < s) (hv : scheduleV s < 1) :
    Filter.Tendsto
      (fun M =>
        scheduleLogEnvelope q s M / finalShellLog M)
      Filter.atTop (nhds 0) := by
  have hgap : 0 < 1 - scheduleV s := sub_pos.mpr hv
  have hpow :
      Filter.Tendsto
        (fun M =>
          (finalShellLog M) ^ (-(1 - scheduleV s)))
        Filter.atTop (nhds 0) :=
    (tendsto_rpow_neg_atTop hgap).comp finalShellLog_tendsto_atTop
  have hlog :
      Filter.Tendsto
        (fun M =>
          Real.log (finalShellLog M) /
            (finalShellLog M) ^ (1 - scheduleV s))
        Filter.atTop (nhds 0) :=
    ((isLittleO_log_rpow_atTop hgap).tendsto_div_nhds_zero).comp
      finalShellLog_tendsto_atTop
  have hsum :=
    (hpow.const_mul
      (2 + |Real.log (1 / scheduleToleranceConstant q)|)).add
      (hlog.const_mul (s + scheduleU q s))
  have hscaled :=
    hsum.const_mul (2 * lemmaSevenTwoConstant q)
  convert hscaled using 1
  · funext M
    exact scheduleLogEnvelope_div_eq q s M
  · ring

theorem concreteScheduleLogCost_div_tendsto_zero
    {q s : ℝ}
    (hq0 : 0 < q) (hqa : a0 < q) (hq1 : q < 1)
    (hs : 0 < s) (hv : scheduleV s < 1) :
    Filter.Tendsto
      (fun M =>
        (Real.log
            (1 /
              stageD (explicitStageCount s M)
                (explicitTerminalTolerance q (explicitStageCount s M))
                (explicitStageCount s M)) +
          Real.log (stageC q (explicitStageCount s M) + 2)) /
          finalShellLog M)
      Filter.atTop (nhds 0) := by
  let R : ℕ → ℕ := fun M => explicitStageCount s M
  let tR : ℕ → ℝ := fun M => explicitTerminalTolerance q (R M)
  have hnonneg :
      ∀ M,
        0 ≤
          (Real.log
              (1 / stageD (R M) (tR M) (R M)) +
            Real.log (stageC q (R M) + 2)) /
            finalShellLog M := by
    intro M
    have ht0 := explicitTerminalTolerance_pos hq0 hqa (R M)
    have ht1 := explicitTerminalTolerance_le_one hq0 hqa (R M)
    have hD :=
      stageD_invariants (R := R M) ht0 ht1 (R M) le_rfl
    have hDinv : 1 ≤ 1 / stageD (R M) (tR M) (R M) := by
      rw [one_div]
      exact (one_le_inv₀ hD.1).2 hD.2.2
    have hlogD := Real.log_nonneg hDinv
    have hC : 1 ≤ stageC q (R M) + 2 := by
      linarith [stageC_pos q (R M)]
    have hlogC := Real.log_nonneg hC
    exact div_nonneg (add_nonneg hlogD hlogC)
      (finalShellLog_pos M).le
  have hupper :
      ∀ M,
        (Real.log
              (1 / stageD (R M) (tR M) (R M)) +
            Real.log (stageC q (R M) + 2)) /
            finalShellLog M ≤
          scheduleLogEnvelope q s M / finalShellLog M := by
    intro M
    exact div_le_div_of_nonneg_right
      (by
        simpa [R, tR] using
          concreteScheduleCost_le_logEnvelope hq0 hqa hq1 hs M)
      (finalShellLog_pos M).le
  exact squeeze_zero hnonneg hupper
    (scheduleLogEnvelope_div_tendsto_zero hs hv)

/-- Every explicit shell envelope has the concrete stage certificate. -/
theorem explicitShellEnvelope_dense
    {q s : ℝ}
    (hq0 : 0 < q) (hqa : a0 < q) (hq1 : q < 1)
    (M : ℕ) :
    IsCDDense (explicitShellEnvelope q s M)
      (stageC q (explicitStageCount s M))
      (stageD (explicitStageCount s M)
        (explicitTerminalTolerance q (explicitStageCount s M))
        (explicitStageCount s M)) := by
  let R := explicitStageCount s M
  have ht0 := explicitTerminalTolerance_pos hq0 hqa R
  have ht1 := explicitTerminalTolerance_le_one hq0 hqa R
  have hcap := explicitTerminalTolerance_le_cap hq0 hqa R
  have hstage :=
    envelopeGood_dense_stage hq0 hqa hq1 ht0 ht1 hcap R le_rfl
  simpa [explicitShellEnvelope, R, stageTolerance] using hstage

end

end QuantitativeDensity

end CollatzEndpointTransport
