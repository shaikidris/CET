/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik
-/
import CollatzEndpointTransport.QuadraticAppendix.QuantitativeQuadraticFinalSchedule

/-!
# Quantitative Quadratic Shell Vanishing

Vanishing shell mass from the concrete quadratic schedule.

The key interface is deliberately logarithmic.  If the combined cost

  log (1 / D_M) + log (C_M + 2)

is `o(log M)`, then `C_M = M^{o(1)}` and `D_M = M^{-o(1)}`.  The resulting
shell exceptional proportion is bounded by `exp (-M^{1-o(1)})`.
-/

namespace CollatzEndpointTransport

namespace QuantitativeDensity

open scoped Real Topology

noncomputable section

def shiftedShellSize (M : ℕ) : ℝ :=
  (M : ℝ) + 4

theorem shiftedShellSize_pos (M : ℕ) :
    0 < shiftedShellSize M := by
  unfold shiftedShellSize
  positivity

theorem shiftedShellSize_tendsto_atTop :
    Filter.Tendsto shiftedShellSize Filter.atTop Filter.atTop :=
  tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds

theorem finalShellLog_eq_log_shifted (M : ℕ) :
    finalShellLog M = Real.log (shiftedShellSize M) := rfl

theorem modelShellDecay_tendsto_zero :
    Filter.Tendsto
      (fun M : ℕ =>
        2 * (shiftedShellSize M) ^ ((1 : ℝ) / 4) *
          Real.exp
            (-(Real.log 2 / 2) *
              (shiftedShellSize M) ^ ((3 : ℝ) / 4)))
      Filter.atTop (nhds 0) := by
  have hb : 0 < Real.log 2 / 2 := div_pos log_two_pos (by norm_num)
  have hy :
      Filter.Tendsto
        (fun M : ℕ =>
          (shiftedShellSize M) ^ ((3 : ℝ) / 4))
        Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 3 / 4)).comp
      shiftedShellSize_tendsto_atTop
  have hbase :=
    (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
      ((1 : ℝ) / 3) (Real.log 2 / 2) hb).comp hy
  have hscaled := hbase.const_mul 2
  have heq :
      (fun M : ℕ =>
        2 * (((fun x : ℝ =>
          x ^ ((1 : ℝ) / 3) *
            Real.exp (-(Real.log 2 / 2) * x)) ∘
              fun M : ℕ =>
                (shiftedShellSize M) ^ ((3 : ℝ) / 4)) M)) =ᶠ[Filter.atTop]
        (fun M : ℕ =>
          2 * (shiftedShellSize M) ^ ((1 : ℝ) / 4) *
            Real.exp
              (-(Real.log 2 / 2) *
                (shiftedShellSize M) ^ ((3 : ℝ) / 4))) :=
    Filter.Eventually.of_forall fun M => by
      have hx := shiftedShellSize_pos M
      have hpow :
          ((shiftedShellSize M) ^ ((3 : ℝ) / 4)) ^ ((1 : ℝ) / 3) =
            (shiftedShellSize M) ^ ((1 : ℝ) / 4) := by
        rw [← Real.rpow_mul hx.le]
        congr 1
        norm_num
      simp only [Function.comp_apply, hpow]
      ring
  simpa using hscaled.congr' heq

/-- The explicit majorant used inside the shell-vanishing proof.  Exporting
it makes the quantitative exceptional-count corollary available without
repeating the schedule analysis. -/
theorem shellExceptionalRatio_eventually_le_model_of_log_cost
    (S : ℕ → Set ℕ) (C D : ℕ → ℝ)
    (hdense : ∀ M, IsCDDense (S M) (C M) (D M))
    (hcost :
      Filter.Tendsto
        (fun M =>
          (Real.log (1 / D M) + Real.log (C M + 2)) /
            finalShellLog M)
        Filter.atTop (nhds 0)) :
    ∀ᶠ M in Filter.atTop,
      shellExceptionalRatio (S M) M ≤
        2 * (shiftedShellSize M) ^ ((1 : ℝ) / 4) *
          Real.exp
            (-(Real.log 2 / 2) *
              (shiftedShellSize M) ^ ((3 : ℝ) / 4)) := by
  have hquarter :
      ∀ᶠ M in Filter.atTop,
        (Real.log (1 / D M) + Real.log (C M + 2)) /
            finalShellLog M < (1 : ℝ) / 4 := by
    have hdist :=
      (Metric.tendsto_atTop.1 hcost) ((1 : ℝ) / 4) (by norm_num)
    filter_upwards [Filter.eventually_atTop.2 hdist] with M hM
    rw [Real.dist_eq] at hM
    simpa using lt_of_le_of_lt (le_abs_self _) hM
  have hMlarge : ∀ᶠ M : ℕ in Filter.atTop, 4 ≤ M :=
    Filter.eventually_atTop.2 ⟨4, fun _ h => h⟩
  filter_upwards [hquarter, hMlarge] with M hsmall hM4
  have hcert := hdense M
  have hL0 := finalShellLog_pos M
  have hcostRaw :
      Real.log (1 / D M) + Real.log (C M + 2) <
        finalShellLog M / 4 := by
    have := (div_lt_iff₀ hL0).mp hsmall
    nlinarith
  have hDinv : 1 ≤ 1 / D M := by
    rw [one_div]
    exact (one_le_inv₀ hcert.D_pos).2 hcert.D_le_one
  have hlogD0 : 0 ≤ Real.log (1 / D M) :=
    Real.log_nonneg hDinv
  have hCtwo : 1 ≤ C M + 2 := by
    linarith [hcert.C_pos]
  have hlogC0 : 0 ≤ Real.log (C M + 2) :=
    Real.log_nonneg hCtwo
  have hlogC :
      Real.log (C M + 2) < finalShellLog M / 4 := by
    linarith
  have hlogD :
      Real.log (1 / D M) < finalShellLog M / 4 := by
    linarith
  let X := (shiftedShellSize M) ^ ((1 : ℝ) / 4)
  have hX0 : 0 < X :=
    Real.rpow_pos_of_pos (shiftedShellSize_pos M) _
  have hexp :
      Real.exp (finalShellLog M / 4) = X := by
    dsimp [X]
    rw [finalShellLog_eq_log_shifted,
      Real.rpow_def_of_pos (shiftedShellSize_pos M)]
    congr 1
    ring
  have hCexp :
      C M + 2 < Real.exp (finalShellLog M / 4) := by
    rw [← Real.exp_log (by linarith [hcert.C_pos] : 0 < C M + 2)]
    exact Real.exp_lt_exp.2 hlogC
  have hCle : C M ≤ X := by
    rw [hexp] at hCexp
    linarith
  have hDexp :
      1 / D M < Real.exp (finalShellLog M / 4) := by
    rw [← Real.exp_log (one_div_pos.mpr hcert.D_pos)]
    exact Real.exp_lt_exp.2 hlogD
  have hDlower : 1 / X < D M := by
    rw [hexp] at hDexp
    exact (one_div_lt hcert.D_pos hX0).mp hDexp
  have hshiftEq : shiftedShellSize M = (M : ℝ) + 4 := rfl
  have hMhalf :
      shiftedShellSize M / 2 ≤ (M : ℝ) := by
    have hM4R : (4 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM4
    rw [hshiftEq]
    linarith
  have hXformula :
      shiftedShellSize M / X =
        (shiftedShellSize M) ^ ((3 : ℝ) / 4) := by
    dsimp [X]
    calc
      shiftedShellSize M /
            shiftedShellSize M ^ ((1 : ℝ) / 4)
          = shiftedShellSize M ^ (1 : ℝ) /
              shiftedShellSize M ^ ((1 : ℝ) / 4) := by
            rw [Real.rpow_one]
      _ = shiftedShellSize M ^
              ((1 : ℝ) - (1 : ℝ) / 4) :=
            (Real.rpow_sub (shiftedShellSize_pos M)
              (1 : ℝ) ((1 : ℝ) / 4)).symm
      _ = shiftedShellSize M ^ ((3 : ℝ) / 4) := by norm_num
  have hDM :
      (shiftedShellSize M) ^ ((3 : ℝ) / 4) / 2 ≤
        D M * (M : ℝ) := by
    have hleft :
        shiftedShellSize M / (2 * X) ≤ (M : ℝ) / X := by
      have h := div_le_div_of_nonneg_right hMhalf hX0.le
      calc
        shiftedShellSize M / (2 * X)
            = (shiftedShellSize M / 2) / X := by field_simp
        _ ≤ (M : ℝ) / X := h
    have hright :
        (M : ℝ) / X ≤ D M * (M : ℝ) := by
      have hM0 : 0 ≤ (M : ℝ) := Nat.cast_nonneg M
      have hmul := mul_le_mul_of_nonneg_right hDlower.le hM0
      simpa [div_eq_mul_inv, mul_comm] using hmul
    calc
      (shiftedShellSize M) ^ ((3 : ℝ) / 4) / 2
          = shiftedShellSize M / (2 * X) := by
            rw [← hXformula]
            ring
      _ ≤ (M : ℝ) / X := hleft
      _ ≤ D M * (M : ℝ) := hright
  have hexpBound :
      Real.exp (-(Real.log 2 * D M * M)) ≤
        Real.exp
          (-(Real.log 2 / 2) *
            (shiftedShellSize M) ^ ((3 : ℝ) / 4)) := by
    apply Real.exp_le_exp.2
    have hlog2 := log_two_pos
    push_cast
    nlinarith
  calc
    shellExceptionalRatio (S M) M
        ≤ 2 * C M * Real.exp (-(Real.log 2 * D M * M)) :=
      shellExceptionalRatio_le_of_isCDDense hcert M
    _ ≤ 2 * X *
          Real.exp
            (-(Real.log 2 / 2) *
              (shiftedShellSize M) ^ ((3 : ℝ) / 4)) :=
      mul_le_mul
        (mul_le_mul_of_nonneg_left hCle (by norm_num))
        hexpBound
        (Real.exp_nonneg _)
        (mul_nonneg (by norm_num) hX0.le)
    _ = _ := rfl

/-- A logarithmic `o(log M)` certificate forces vanishing exceptional
mass for a shell-dependent family of `(C_M,D_M)`-dense sets. -/
theorem shellExceptionalRatio_tendsto_zero_of_log_cost
    (S : ℕ → Set ℕ) (C D : ℕ → ℝ)
    (hdense : ∀ M, IsCDDense (S M) (C M) (D M))
    (hcost :
      Filter.Tendsto
        (fun M =>
          (Real.log (1 / D M) + Real.log (C M + 2)) /
            finalShellLog M)
        Filter.atTop (nhds 0)) :
    Filter.Tendsto
      (fun M => shellExceptionalRatio (S M) M)
      Filter.atTop (nhds 0) := by
  have hquarter :
      ∀ᶠ M in Filter.atTop,
        (Real.log (1 / D M) + Real.log (C M + 2)) /
            finalShellLog M < (1 : ℝ) / 4 := by
    have hdist :=
      (Metric.tendsto_atTop.1 hcost) ((1 : ℝ) / 4) (by norm_num)
    filter_upwards [Filter.eventually_atTop.2 hdist] with M hM
    rw [Real.dist_eq] at hM
    simpa using lt_of_le_of_lt (le_abs_self _) hM
  have hMlarge : ∀ᶠ M : ℕ in Filter.atTop, 4 ≤ M :=
    Filter.eventually_atTop.2 ⟨4, fun _ h => h⟩
  have hbound :
      ∀ᶠ M in Filter.atTop,
        shellExceptionalRatio (S M) M ≤
          2 * (shiftedShellSize M) ^ ((1 : ℝ) / 4) *
            Real.exp
              (-(Real.log 2 / 2) *
                (shiftedShellSize M) ^ ((3 : ℝ) / 4)) := by
    filter_upwards [hquarter, hMlarge] with M hsmall hM4
    have hcert := hdense M
    have hL0 := finalShellLog_pos M
    have hcostRaw :
        Real.log (1 / D M) + Real.log (C M + 2) <
          finalShellLog M / 4 := by
      have := (div_lt_iff₀ hL0).mp hsmall
      nlinarith
    have hDinv : 1 ≤ 1 / D M := by
      rw [one_div]
      exact (one_le_inv₀ hcert.D_pos).2 hcert.D_le_one
    have hlogD0 : 0 ≤ Real.log (1 / D M) :=
      Real.log_nonneg hDinv
    have hCtwo : 1 ≤ C M + 2 := by
      linarith [hcert.C_pos]
    have hlogC0 : 0 ≤ Real.log (C M + 2) :=
      Real.log_nonneg hCtwo
    have hlogC :
        Real.log (C M + 2) < finalShellLog M / 4 := by
      linarith
    have hlogD :
        Real.log (1 / D M) < finalShellLog M / 4 := by
      linarith
    let X := (shiftedShellSize M) ^ ((1 : ℝ) / 4)
    have hX0 : 0 < X :=
      Real.rpow_pos_of_pos (shiftedShellSize_pos M) _
    have hexp :
        Real.exp (finalShellLog M / 4) = X := by
      dsimp [X]
      rw [finalShellLog_eq_log_shifted,
        Real.rpow_def_of_pos (shiftedShellSize_pos M)]
      congr 1
      ring
    have hCexp :
        C M + 2 < Real.exp (finalShellLog M / 4) := by
      rw [← Real.exp_log (by linarith [hcert.C_pos] : 0 < C M + 2)]
      exact Real.exp_lt_exp.2 hlogC
    have hCle : C M ≤ X := by
      rw [hexp] at hCexp
      linarith
    have hDexp :
        1 / D M < Real.exp (finalShellLog M / 4) := by
      rw [← Real.exp_log (one_div_pos.mpr hcert.D_pos)]
      exact Real.exp_lt_exp.2 hlogD
    have hDlower : 1 / X < D M := by
      rw [hexp] at hDexp
      exact (one_div_lt hcert.D_pos hX0).mp hDexp
    have hshiftEq : shiftedShellSize M = (M : ℝ) + 4 := rfl
    have hMhalf :
        shiftedShellSize M / 2 ≤ (M : ℝ) := by
      have hM4R : (4 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM4
      rw [hshiftEq]
      linarith
    have hXformula :
        shiftedShellSize M / X =
          (shiftedShellSize M) ^ ((3 : ℝ) / 4) := by
      dsimp [X]
      calc
        shiftedShellSize M /
              shiftedShellSize M ^ ((1 : ℝ) / 4)
            = shiftedShellSize M ^ (1 : ℝ) /
                shiftedShellSize M ^ ((1 : ℝ) / 4) := by
              rw [Real.rpow_one]
        _ = shiftedShellSize M ^
                ((1 : ℝ) - (1 : ℝ) / 4) :=
              (Real.rpow_sub (shiftedShellSize_pos M)
                (1 : ℝ) ((1 : ℝ) / 4)).symm
        _ = shiftedShellSize M ^ ((3 : ℝ) / 4) := by norm_num
    have hDM :
        (shiftedShellSize M) ^ ((3 : ℝ) / 4) / 2 ≤
          D M * (M : ℝ) := by
      have hleft :
          shiftedShellSize M / (2 * X) ≤ (M : ℝ) / X := by
        have h := div_le_div_of_nonneg_right hMhalf hX0.le
        calc
          shiftedShellSize M / (2 * X)
              = (shiftedShellSize M / 2) / X := by field_simp
          _ ≤ (M : ℝ) / X := h
      have hright :
          (M : ℝ) / X ≤ D M * (M : ℝ) := by
        have hM0 : 0 ≤ (M : ℝ) := Nat.cast_nonneg M
        have hmul := mul_le_mul_of_nonneg_right hDlower.le hM0
        simpa [div_eq_mul_inv, mul_comm] using hmul
      calc
        (shiftedShellSize M) ^ ((3 : ℝ) / 4) / 2
            = shiftedShellSize M / (2 * X) := by
              rw [← hXformula]
              ring
        _ ≤ (M : ℝ) / X := hleft
        _ ≤ D M * (M : ℝ) := hright
    have hexpBound :
        Real.exp (-(Real.log 2 * D M * M)) ≤
          Real.exp
            (-(Real.log 2 / 2) *
              (shiftedShellSize M) ^ ((3 : ℝ) / 4)) := by
      apply Real.exp_le_exp.2
      have hlog2 := log_two_pos
      push_cast
      nlinarith
    calc
      shellExceptionalRatio (S M) M
          ≤ 2 * C M * Real.exp (-(Real.log 2 * D M * M)) :=
        shellExceptionalRatio_le_of_isCDDense hcert M
      _ ≤ 2 * X *
            Real.exp
              (-(Real.log 2 / 2) *
                (shiftedShellSize M) ^ ((3 : ℝ) / 4)) :=
        mul_le_mul
          (mul_le_mul_of_nonneg_left hCle (by norm_num))
          hexpBound
          (Real.exp_nonneg _)
          (mul_nonneg (by norm_num) hX0.le)
      _ = _ := rfl
  exact squeeze_zero'
    (Filter.Eventually.of_forall fun M =>
      shellExceptionalRatio_nonneg (S M) M)
    hbound
    modelShellDecay_tendsto_zero

/-- The explicit quadratic schedule has vanishing shell exceptional mass. -/
theorem explicitShellExceptionalRatio_tendsto_zero
    {q s : ℝ}
    (hq0 : 0 < q) (hqa : a0 < q) (hq1 : q < 1)
    (hs : 0 < s) (hv : scheduleV s < 1) :
    Filter.Tendsto
      (fun M =>
        shellExceptionalRatio (explicitShellEnvelope q s M) M)
      Filter.atTop (nhds 0) := by
  apply shellExceptionalRatio_tendsto_zero_of_log_cost
    (explicitShellEnvelope q s)
    (fun M => stageC q (explicitStageCount s M))
    (fun M =>
      stageD (explicitStageCount s M)
        (explicitTerminalTolerance q (explicitStageCount s M))
        (explicitStageCount s M))
  · exact explicitShellEnvelope_dense hq0 hqa hq1
  · exact concreteScheduleLogCost_div_tendsto_zero
      hq0 hqa hq1 hs hv

/-- The explicit schedule satisfies the concrete shell majorant, not merely
its limiting consequence. -/
theorem explicitShellExceptionalRatio_eventually_le_model
    {q s : ℝ}
    (hq0 : 0 < q) (hqa : a0 < q) (hq1 : q < 1)
    (hs : 0 < s) (hv : scheduleV s < 1) :
    ∀ᶠ M in Filter.atTop,
      shellExceptionalRatio (explicitShellEnvelope q s M) M ≤
        2 * (shiftedShellSize M) ^ ((1 : ℝ) / 4) *
          Real.exp
            (-(Real.log 2 / 2) *
              (shiftedShellSize M) ^ ((3 : ℝ) / 4)) := by
  exact shellExceptionalRatio_eventually_le_model_of_log_cost
    (explicitShellEnvelope q s)
    (fun M => stageC q (explicitStageCount s M))
    (fun M =>
      stageD (explicitStageCount s M)
        (explicitTerminalTolerance q (explicitStageCount s M))
        (explicitStageCount s M))
    (explicitShellEnvelope_dense hq0 hqa hq1)
    (concreteScheduleLogCost_div_tendsto_zero
      hq0 hqa hq1 hs hv)

/-- The union of the explicit shell envelopes has natural density one. -/
theorem explicitShellEnvelope_hasNaturalDensityOne
    {q s : ℝ}
    (hq0 : 0 < q) (hqa : a0 < q) (hq1 : q < 1)
    (hs : 0 < s) (hv : scheduleV s < 1) :
    HasNaturalDensityOne
      (assembleDyadic (explicitShellEnvelope q s)) :=
  hasNaturalDensityOne_assembleDyadic _
    (explicitShellExceptionalRatio_tendsto_zero
      hq0 hqa hq1 hs hv)

end

end QuantitativeDensity

end CollatzEndpointTransport
