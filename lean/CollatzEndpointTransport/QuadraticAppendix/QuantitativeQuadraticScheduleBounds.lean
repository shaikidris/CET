/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik
-/
import CollatzEndpointTransport.QuadraticAppendix.QuantitativeQuadraticSchedule

/-!
# Quantitative Quadratic Schedule Bounds

Scalar bounds for the concrete stage recurrence.

These are the quantitative estimates behind the quadratic stage induction. They are stated on
the actual `stageC`, `stageD`, `stageLambda`, and `stageTolerance`
definitions from `QuantitativeQuadraticSchedule`, rather than on an
unrelated generic majorant.
-/

namespace CollatzEndpointTransport

namespace QuantitativeDensity

open scoped Real BigOperators

noncomputable section

def stageStartupB (q : ℝ) : ℝ :=
  (stageStartupA q + 1) * Real.log 2

def stagePrefactorK : ℝ :=
  quadraticPullbackGlobalConstant +
    Terras.quadraticWindowFixedGlobalConstant + 2

theorem stageStartupA_pos {q : ℝ} (hqa : a0 < q) :
    0 < stageStartupA q := by
  unfold stageStartupA
  exact div_pos (mul_pos (by norm_num) (by linarith [bConst_pos]))
    (mul_pos (by norm_num) (sub_pos.mpr hqa))

theorem quadraticPullbackGlobalConstant_pos' :
    0 < quadraticPullbackGlobalConstant := by
  unfold quadraticPullbackGlobalConstant
  exact div_pos (mul_pos (by norm_num) quadraticPullbackStartupConstant_pos)
    quadraticPullbackFixedDenominator_pos

theorem quadraticWindowFixedGlobalConstant_pos' :
    0 < Terras.quadraticWindowFixedGlobalConstant := by
  have hhalf : (1 : ℝ) / 2 <
      Real.exp (-Terras.maximalBarrierC0) := by
    have hExpLog : Real.exp (-Real.log 2) = (1 : ℝ) / 2 := by
      rw [Real.exp_neg, Real.exp_log (by norm_num)]
      norm_num
    rw [← hExpLog]
    exact Real.exp_lt_exp.2
      (by linarith [Terras.maximalBarrierC0_lt_log_two])
  unfold Terras.quadraticWindowFixedGlobalConstant
  exact div_pos (mul_pos (by norm_num) Terras.quadraticWindowShellConstant_pos)
    (by linarith)

theorem stageStartupB_pos {q : ℝ} (hqa : a0 < q) :
    0 < stageStartupB q := by
  unfold stageStartupB
  exact mul_pos (by linarith [stageStartupA_pos hqa]) log_two_pos

theorem stagePrefactorK_pos : 0 < stagePrefactorK := by
  unfold stagePrefactorK
  linarith [quadraticPullbackGlobalConstant_pos',
    quadraticWindowFixedGlobalConstant_pos']

theorem stagePrefactorK_ge_one : 1 ≤ stagePrefactorK := by
  unfold stagePrefactorK
  linarith [quadraticPullbackGlobalConstant_pos',
    quadraticWindowFixedGlobalConstant_pos']

theorem startup_pow_le_exp
    {q lambda : ℝ}
    (hqa : a0 < q) (hlambda0 : 0 < lambda) (hlambda1 : lambda ≤ 1) :
    (2 : ℝ) ^ stageStartupIndex q lambda ≤
      Real.exp (stageStartupB q / lambda) := by
  have hA0 := stageStartupA_pos hqa
  have hx0 : 0 ≤ stageStartupA q / lambda :=
    (div_pos hA0 hlambda0).le
  have hceil :
      (stageStartupIndex q lambda : ℝ) <
        stageStartupA q / lambda + 1 := by
    exact Nat.ceil_lt_add_one hx0
  have hexpArg :
      Real.log 2 * (stageStartupIndex q lambda : ℝ) ≤
        stageStartupB q / lambda := by
    unfold stageStartupB
    have hlog := log_two_pos
    have hinv : 1 ≤ lambda⁻¹ := (one_le_inv₀ hlambda0).2 hlambda1
    have hone :
        stageStartupA q / lambda + 1 ≤
          (stageStartupA q + 1) / lambda := by
      rw [div_eq_mul_inv, div_eq_mul_inv]
      nlinarith [hA0, inv_pos.mpr hlambda0]
    calc
      Real.log 2 * (stageStartupIndex q lambda : ℝ)
          ≤ Real.log 2 * (stageStartupA q / lambda + 1) :=
        mul_le_mul_of_nonneg_left hceil.le hlog.le
      _ ≤ Real.log 2 * ((stageStartupA q + 1) / lambda) :=
        mul_le_mul_of_nonneg_left hone hlog.le
      _ = (stageStartupA q + 1) * Real.log 2 / lambda := by ring
  rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by norm_num)]
  exact Real.exp_le_exp.2 hexpArg

theorem stageLambda_anti
    {q : ℝ} {i j : ℕ}
    (hq0 : 0 < q) (hq1 : q < 1) (hij : i ≤ j) :
    stageLambda q j ≤ stageLambda q i :=
  stageLambda_terminal_le hq0 hq1 hij

theorem startup_exp_mono
    {q : ℝ} {i j : ℕ}
    (hq0 : 0 < q) (hqa : a0 < q) (hq1 : q < 1) (hij : i ≤ j) :
    Real.exp (stageStartupB q / stageLambda q i) ≤
      Real.exp (stageStartupB q / stageLambda q j) := by
  apply Real.exp_le_exp.2
  have hli := stageLambda_pos hq0 i
  have hlj := stageLambda_pos hq0 j
  have hlam := stageLambda_anti hq0 hq1 hij
  exact div_le_div_of_nonneg_left (stageStartupB_pos hqa).le hlj hlam

theorem stageC_pos (q : ℝ) : ∀ j, 0 < stageC q j := by
  intro j
  induction j with
  | zero =>
      rw [stageC_zero]
      exact quadraticWindowFixedGlobalConstant_pos'
  | succ j ih =>
      rw [stageC_succ]
      exact add_pos
        (add_pos
          (mul_pos quadraticPullbackGlobalConstant_pos' (by linarith))
          quadraticWindowFixedGlobalConstant_pos')
        (pow_pos (by norm_num) _)

/-- A terminal-stage bound for the exact prefactor recurrence. -/
theorem stageC_terminal_bound
    {q : ℝ} {R : ℕ}
    (hq0 : 0 < q) (hqa : a0 < q) (hq1 : q < 1) :
    stageC q R + 1 ≤
      (stagePrefactorK *
          Real.exp (stageStartupB q / stageLambda q R)) ^ R *
        (Terras.quadraticWindowFixedGlobalConstant + 1) := by
  induction R with
  | zero => simp [stageC_zero]
  | succ R ih =>
      let E := Real.exp (stageStartupB q / stageLambda q (R + 1))
      have hE1 : 1 ≤ E := by
        dsimp [E]
        exact Real.one_le_exp
          (div_nonneg (stageStartupB_pos hqa).le
            (stageLambda_pos hq0 (R + 1)).le)
      have hEpos : 0 < E := lt_of_lt_of_le zero_lt_one hE1
      have hstartup :
          (2 : ℝ) ^ stageStartupIndex q (stageLambda q R) ≤ E := by
        have hpow := startup_pow_le_exp hqa
          (stageLambda_pos hq0 R)
          (stageLambda_lt_one hq0 hq1 R).le
        exact hpow.trans (startup_exp_mono hq0 hqa hq1 (Nat.le_succ R))
      have hEprev :
          Real.exp (stageStartupB q / stageLambda q R) ≤ E :=
        startup_exp_mono hq0 hqa hq1 (Nat.le_succ R)
      have hbase0 :
          0 ≤ Terras.quadraticWindowFixedGlobalConstant + 1 := by
        linarith [quadraticWindowFixedGlobalConstant_pos']
      have hmulBase :
          stagePrefactorK *
              Real.exp (stageStartupB q / stageLambda q R) ≤
            stagePrefactorK * E :=
        mul_le_mul_of_nonneg_left hEprev stagePrefactorK_pos.le
      have ihE :
          stageC q R + 1 ≤
            (stagePrefactorK * E) ^ R *
              (Terras.quadraticWindowFixedGlobalConstant + 1) :=
        ih.trans
          (mul_le_mul_of_nonneg_right
            (pow_le_pow_left₀
              (mul_nonneg stagePrefactorK_pos.le (Real.exp_pos _).le)
              hmulBase R)
            hbase0)
      rw [stageC_succ, pow_succ]
      have hC1 : 1 ≤ stageC q R + 1 := by
        linarith [stageC_pos q R]
      have hfactor :
          quadraticPullbackGlobalConstant * (stageC q R + 1) +
                Terras.quadraticWindowFixedGlobalConstant +
                (2 : ℝ) ^ stageStartupIndex q (stageLambda q R) + 1
            ≤ stagePrefactorK * E * (stageC q R + 1) := by
        have hEC :
            stageC q R + 1 ≤ E * (stageC q R + 1) := by
            have h := mul_le_mul_of_nonneg_right hE1 (zero_le_one.trans hC1)
            simpa using h
        have hEC1 : 1 ≤ E * (stageC q R + 1) := hC1.trans hEC
        have hpterm :
            quadraticPullbackGlobalConstant * (stageC q R + 1) ≤
              quadraticPullbackGlobalConstant *
                (E * (stageC q R + 1)) :=
          mul_le_mul_of_nonneg_left hEC
            quadraticPullbackGlobalConstant_pos'.le
        have hwterm :
            Terras.quadraticWindowFixedGlobalConstant ≤
              Terras.quadraticWindowFixedGlobalConstant *
                (E * (stageC q R + 1)) := by
          calc
            Terras.quadraticWindowFixedGlobalConstant
                = Terras.quadraticWindowFixedGlobalConstant * 1 := by ring
            _ ≤ _ := mul_le_mul_of_nonneg_left hEC1
              quadraticWindowFixedGlobalConstant_pos'.le
        have hstartupTerm :
            (2 : ℝ) ^ stageStartupIndex q (stageLambda q R) + 1 ≤
              2 * (E * (stageC q R + 1)) := by
          have hEle : E ≤ E * (stageC q R + 1) := by
              have h := mul_le_mul_of_nonneg_left hC1 hEpos.le
              simpa using h
          linarith
        unfold stagePrefactorK
        nlinarith [hpterm, hwterm, hstartupTerm]
      calc
        quadraticPullbackGlobalConstant * (stageC q R + 1) +
              Terras.quadraticWindowFixedGlobalConstant +
              (2 : ℝ) ^ stageStartupIndex q (stageLambda q R) + 1
            ≤ stagePrefactorK * E * (stageC q R + 1) := hfactor
        _ ≤ stagePrefactorK * E *
              ((stagePrefactorK * E) ^ R *
                (Terras.quadraticWindowFixedGlobalConstant + 1)) := by
              exact mul_le_mul_of_nonneg_left ihE
                (mul_nonneg stagePrefactorK_pos.le (Real.exp_pos _).le)
        _ = (stagePrefactorK * E) ^ (R + 1) *
              (Terras.quadraticWindowFixedGlobalConstant + 1) := by ring

/-- Exact formula for the actual density-exponent recurrence. -/
theorem stageD_exact (R : ℕ) (tR : ℝ) (j : ℕ) :
    stageD R tR j =
      quadraticStageExponentConstant ^ quadraticWeight j *
        (stageD R tR 0) ^ (2 ^ j) := by
  exact quadraticRecurrence_exact
    quadraticStageExponentConstant (stageD R tR 0)
    (stageD R tR) rfl (fun n => stageD_succ R tR n) j

end

end QuantitativeDensity

end CollatzEndpointTransport
