/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik
-/
import CollatzEndpointTransport.Linear.CentralRenyiPullback
import CollatzEndpointTransport.Linear.EndpointOnlyAbstract
import CollatzEndpointTransport.Linear.EndpointOnlyAsymptotic
import CollatzEndpointTransport.Linear.EndpointOnlyParameterChoice
import CollatzEndpointTransport.Common.StretchedExceptionalCount
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Central Renyi Endpoint Only

Endpoint-only bootstrap driven by the central higher-Renyi pullback.

The orbit recursion and logarithmic schedule are the existing endpoint-only
ones.  This module supplies only the new one-stage density socket and the
fixed inverse-sixth-power prefactor estimate.
-/

namespace CollatzEndpointTransport

namespace OptimizedLinearPullback

open scoped Real Topology

noncomputable section

open QuantitativeDensity

/-- One endpoint-density stage supplied by the central higher-Renyi
pullback. -/
theorem centralRenyiEndpointDensityStep
    {theta eta transport t Dcut : ℝ}
    (htheta0 : 0 < theta) (htheta1 : theta < 1)
    (heta0 : 0 < eta)
    (heta1 : eta < FixedTotal.centralRenyiAlpha theta - 1 / 2)
    (htransport0 : 0 < transport)
    (htransport : transport < FixedTotal.centralRenyiAsymptoticRate theta)
    (htransport1 : transport ≤ 1)
    (ht0 : 0 < t) (ht1 : t ≤ 1)
    (hDcut0 : 0 < Dcut)
    (hcut : ∀ D : ℝ, 0 < D → D ≤ Dcut →
      transport * D ≤
          FixedTotal.centralRenyiShellRate theta transport D / Real.log 2 ∧
      FixedTotal.centralRenyiShellRate theta transport D ≤
          eta * Real.log 2 / 16 ∧
      FixedTotal.centralRenyiShellRate theta transport D ≤ eta ^ 2 / 8)
    (hwindowCut : transport * Dcut ≤
      Terras.quadraticWindowDensityRate t) :
    EndpointDensityStep t transport
      (FixedTotal.centralRenyiStageConstant theta eta transport)
      Terras.quadraticWindowFixedGlobalConstant Dcut 6 := by
  refine ⟨htransport0, htransport1,
    FixedTotal.centralRenyiStageConstant_pos
      htheta0 htheta1 heta0 heta1 htransport0 htransport,
    (Terras.initialWindowGood_dense_quadratic_fixed ht0 ht1).C_pos,
    hDcut0, ?_⟩
  intro S C D hS hDcut
  obtain ⟨hlinear, hlate, hparity⟩ := hcut D hS.D_pos hDcut
  have hnext0 : 0 < transport * D := mul_pos htransport0 hS.D_pos
  have hPullRaw := FixedTotal.collatzPullback_dense_centralRenyi
    hS htheta0 htheta1 heta0 heta1 htransport0 htransport hlate hparity
  have hPullExp := hPullRaw.degrade_exponent hnext0 hlinear
  have hPull := hPullExp.mono_constant
    (FixedTotal.centralRenyiPullbackConstant_le_stage
      hS.C_pos hS.D_pos hS.D_le_one htheta0 htheta1 heta0 heta1
      htransport0 htransport hlinear hparity)
  have hWindowRaw :=
    Terras.initialWindowGood_dense_quadratic_fixed ht0 ht1
  have hwindow : transport * D ≤
      Terras.quadraticWindowDensityRate t := by
    exact (mul_le_mul_of_nonneg_left hDcut htransport0.le).trans hwindowCut
  have hWindow := hWindowRaw.degrade_exponent hnext0 hwindow
  simpa [add_comm] using hWindow.inter hPull

/-- Scheduled abstract prefactor for the central endpoint chain. -/
def centralRenyiEndpointScheduledC
    (theta eta transport D0 omega : ℝ) (M : ℕ) : ℝ :=
  endpointAbstractC
    (FixedTotal.centralRenyiStageConstant theta eta transport)
    Terras.quadraticWindowFixedGlobalConstant transport D0 6
    (endpointStageCount omega M)

/-- Exact scheduled density theorem obtained from the existing abstract
endpoint recursion. -/
theorem centralRenyiEndpointScheduledChain_dense
    {theta eta transport t D0 Dcut omega : ℝ}
    (hstep : EndpointDensityStep t transport
      (FixedTotal.centralRenyiStageConstant theta eta transport)
      Terras.quadraticWindowFixedGlobalConstant Dcut 6)
    (hD00 : 0 < D0) (hD01 : D0 ≤ 1) (hD0cut : D0 ≤ Dcut)
    (M : ℕ) :
    IsCDDense
      (endpointChain t (endpointStageCount omega M))
      (centralRenyiEndpointScheduledC theta eta transport D0 omega M)
      (endpointScheduledD transport D0 omega M) := by
  simpa [centralRenyiEndpointScheduledC, endpointScheduledD] using
    endpointChain_dense_of_abstract_step hstep hD00 hD01 hD0cut
      (endpointStageCount omega M)

/-- Coarse fixed stage constant entering the terminal prefactor bound. -/
def centralRenyiEndpointStageK
    (theta eta transport : ℝ) : ℝ :=
  endpointAbstractStageK
    (FixedTotal.centralRenyiStageConstant theta eta transport)
    Terras.quadraticWindowFixedGlobalConstant

/-- Fixed part of the logarithmic terminal-prefactor cost. -/
def centralRenyiEndpointCostConstant
    (theta eta transport D0 : ℝ) : ℝ :=
  |Real.log (centralRenyiEndpointStageK theta eta transport)| +
    6 * |Real.log ((endpointDensityConstant transport D0)⁻¹)| + 1

/-- Explicit quadratic-in-log envelope for the central endpoint
prefactor. -/
def centralRenyiEndpointLogCostEnvelope
    (theta eta transport D0 omega : ℝ) (M : ℕ) : ℝ :=
  (omega * powerShellLog M + 1) *
      (centralRenyiEndpointCostConstant theta eta transport D0 +
        6 * endpointDensityPower transport omega * powerShellLog M) +
    |Real.log 3|

theorem centralRenyiEndpointScheduledLogC_le_raw
    {theta eta transport D0 omega : ℝ}
    (htheta0 : 0 < theta) (htheta1 : theta < 1)
    (heta0 : 0 < eta)
    (heta1 : eta < FixedTotal.centralRenyiAlpha theta - 1 / 2)
    (htransport0 : 0 < transport)
    (htransport : transport < FixedTotal.centralRenyiAsymptoticRate theta)
    (htransport1 : transport ≤ 1)
    (hD00 : 0 < D0) (hD01 : D0 ≤ 1)
    (M : ℕ) :
    Real.log
        (centralRenyiEndpointScheduledC
          theta eta transport D0 omega M + 2) ≤
      (endpointStageCount omega M : ℝ) *
        (Real.log (centralRenyiEndpointStageK theta eta transport) +
          6 * Real.log
            ((endpointScheduledD transport D0 omega M)⁻¹)) +
        Real.log 3 := by
  let K := FixedTotal.centralRenyiStageConstant theta eta transport
  let W := Terras.quadraticWindowFixedGlobalConstant
  let F := centralRenyiEndpointStageK theta eta transport *
    ((endpointScheduledD transport D0 omega M)⁻¹) ^ 6
  have hK0 : 0 < K := FixedTotal.centralRenyiStageConstant_pos
    htheta0 htheta1 heta0 heta1 htransport0 htransport
  have hW0 : 0 < W := by
    dsimp [W]
    exact linearWindowConstant_pos
  have hDterminal : endpointScheduledD transport D0 omega M ≤ 1 :=
    (endpointScheduledD_le_D0 htransport0 htransport1 hD00 M).trans hD01
  have hbound := endpointAbstractC_terminal_bound
    hK0 hW0 htransport0 htransport1 hD00 hDterminal
    (B := 6) (R := endpointStageCount omega M)
  have hC0 : 0 < centralRenyiEndpointScheduledC
      theta eta transport D0 omega M + 2 := by
    have hC := endpointAbstractC_pos
      hK0 hW0 htransport0 hD00 (B := 6) (endpointStageCount omega M)
    simpa [centralRenyiEndpointScheduledC, K, W] using (by linarith :
      0 < endpointAbstractC K W transport D0 6
        (endpointStageCount omega M) + 2)
  have hD0 : 0 < endpointScheduledD transport D0 omega M :=
    endpointScheduledD_pos htransport0 hD00 M
  have hstage0 : 0 < centralRenyiEndpointStageK theta eta transport := by
    unfold centralRenyiEndpointStageK
    exact zero_lt_one.trans_le (endpointAbstractStageK_ge_one hK0 hW0)
  have hF0 : 0 < F := by dsimp [F]; positivity
  have hright0 : 0 < 3 * F ^ endpointStageCount omega M :=
    mul_pos (by norm_num) (pow_pos hF0 _)
  have hlogMono :
      Real.log (centralRenyiEndpointScheduledC
          theta eta transport D0 omega M + 2) ≤
        Real.log (3 * F ^ endpointStageCount omega M) :=
    Real.strictMonoOn_log.monotoneOn
      (Set.mem_Ioi.mpr hC0) (Set.mem_Ioi.mpr hright0)
      (by simpa [centralRenyiEndpointScheduledC, K, W, F,
          centralRenyiEndpointStageK] using hbound)
  calc
    Real.log (centralRenyiEndpointScheduledC
          theta eta transport D0 omega M + 2)
        ≤ Real.log (3 * F ^ endpointStageCount omega M) := hlogMono
    _ = (endpointStageCount omega M : ℝ) * Real.log F +
          Real.log 3 := by
      rw [Real.log_mul (by norm_num : (3 : ℝ) ≠ 0)
          (pow_ne_zero _ hF0.ne'), Real.log_pow]
      ring
    _ = (endpointStageCount omega M : ℝ) *
          (Real.log (centralRenyiEndpointStageK theta eta transport) +
            6 * Real.log
              ((endpointScheduledD transport D0 omega M)⁻¹)) +
          Real.log 3 := by
      dsimp [F]
      rw [Real.log_mul hstage0.ne'
          (pow_ne_zero 6 (inv_ne_zero hD0.ne')), Real.log_pow]
      norm_num

/-- Explicit quadratic-in-`log X` upper bound for the central terminal
prefactor.  The coefficient six is the conservative inverse-power loss in
the central pullback socket; it does not alter the endpoint exponent. -/
theorem centralRenyiEndpointScheduledLogC_le
    {theta eta transport D0 omega : ℝ}
    (htheta0 : 0 < theta) (htheta1 : theta < 1)
    (heta0 : 0 < eta)
    (heta1 : eta < FixedTotal.centralRenyiAlpha theta - 1 / 2)
    (htransport0 : 0 < transport)
    (htransport : transport < FixedTotal.centralRenyiAsymptoticRate theta)
    (htransport1 : transport < 1)
    (hD00 : 0 < D0) (hD01 : D0 ≤ 1)
    (homega : 0 < omega)
    (M : ℕ) :
    Real.log
        (centralRenyiEndpointScheduledC
          theta eta transport D0 omega M + 2) ≤
      centralRenyiEndpointLogCostEnvelope
        theta eta transport D0 omega M := by
  have hraw :=
    centralRenyiEndpointScheduledLogC_le_raw
      htheta0 htheta1 heta0 heta1 htransport0 htransport
      htransport1.le hD00 hD01 (omega := omega) M
  have hR := (endpointStageCount_bounds homega M).2.le
  have hlogD :=
    endpointScheduledLogDInv_le
      htransport0 htransport1 hD00 homega M
  have hKabs :
      Real.log (centralRenyiEndpointStageK theta eta transport) ≤
        |Real.log (centralRenyiEndpointStageK theta eta transport)| :=
    le_abs_self _
  have hinner :
      Real.log (centralRenyiEndpointStageK theta eta transport) +
            6 * Real.log
              ((endpointScheduledD transport D0 omega M)⁻¹)
          ≤
        centralRenyiEndpointCostConstant theta eta transport D0 +
          6 * endpointDensityPower transport omega * powerShellLog M := by
    unfold centralRenyiEndpointCostConstant
    nlinarith
  have hinner0 :
      0 ≤
        centralRenyiEndpointCostConstant theta eta transport D0 +
          6 * endpointDensityPower transport omega * powerShellLog M := by
    unfold centralRenyiEndpointCostConstant
    have hw0 :
        0 ≤ endpointDensityPower transport omega :=
      (endpointDensityPower_pos htransport0 htransport1 homega).le
    have hlogX0 := (powerShellLog_pos M).le
    positivity
  have hrawInner0 :
      0 ≤
        Real.log (centralRenyiEndpointStageK theta eta transport) +
          6 * Real.log
            ((endpointScheduledD transport D0 omega M)⁻¹) := by
    have hK0 :
        0 < FixedTotal.centralRenyiStageConstant theta eta transport :=
      FixedTotal.centralRenyiStageConstant_pos
        htheta0 htheta1 heta0 heta1 htransport0 htransport
    have hW0 :
        0 < Terras.quadraticWindowFixedGlobalConstant :=
      linearWindowConstant_pos
    have hlogK0 :
        0 ≤ Real.log
          (centralRenyiEndpointStageK theta eta transport) :=
      Real.log_nonneg (by
        unfold centralRenyiEndpointStageK
        exact endpointAbstractStageK_ge_one hK0 hW0)
    have hDM0 :=
      endpointScheduledD_pos (omega := omega) htransport0 hD00 M
    have hDM1 :
        endpointScheduledD transport D0 omega M ≤ 1 :=
      (endpointScheduledD_le_D0 (omega := omega)
        htransport0 htransport1.le hD00 M).trans hD01
    have hinv1 :
        1 ≤ (endpointScheduledD transport D0 omega M)⁻¹ :=
      (one_le_inv₀ hDM0).2 hDM1
    have hlogInv0 :
        0 ≤ Real.log
          ((endpointScheduledD transport D0 omega M)⁻¹) :=
      Real.log_nonneg hinv1
    linarith
  have hRright0 :
      0 ≤ omega * powerShellLog M + 1 := by
    have hlogX0 := (powerShellLog_pos M).le
    nlinarith [mul_nonneg homega.le hlogX0]
  have hmul :
      (endpointStageCount omega M : ℝ) *
          (Real.log (centralRenyiEndpointStageK theta eta transport) +
            6 * Real.log
              ((endpointScheduledD transport D0 omega M)⁻¹))
        ≤
      (omega * powerShellLog M + 1) *
        (centralRenyiEndpointCostConstant theta eta transport D0 +
          6 * endpointDensityPower transport omega * powerShellLog M) := by
    exact mul_le_mul hR hinner hrawInner0 hRright0
  unfold centralRenyiEndpointLogCostEnvelope
  exact hraw.trans (add_le_add hmul (le_abs_self _))

theorem centralRenyiEndpointLogCostEnvelope_eq
    (theta eta transport D0 omega : ℝ) (M : ℕ) :
    centralRenyiEndpointLogCostEnvelope
        theta eta transport D0 omega M =
      (6 * omega * endpointDensityPower transport omega) *
          (powerShellLog M) ^ (2 : ℝ) +
        (omega * centralRenyiEndpointCostConstant
              theta eta transport D0 +
            6 * endpointDensityPower transport omega) *
          powerShellLog M +
        (centralRenyiEndpointCostConstant theta eta transport D0 +
          |Real.log 3|) := by
  unfold centralRenyiEndpointLogCostEnvelope
  rw [Real.rpow_two]
  ring

/-- The central higher-Renyi prefactor remains negligible against the
retained shell-density power. -/
theorem centralRenyiEndpointLogCostEnvelope_ratio_tendsto_zero
    {theta eta transport D0 omega : ℝ}
    (htransport0 : 0 < transport)
    (htransport1 : transport < 1)
    (homega : 0 < omega)
    (hw : endpointDensityPower transport omega < 1) :
    Filter.Tendsto
      (fun M =>
        centralRenyiEndpointLogCostEnvelope
            theta eta transport D0 omega M /
          powerShellScale M ^
            (1 - endpointDensityPower transport omega))
      Filter.atTop (nhds 0) := by
  have hgap :
      0 < 1 - endpointDensityPower transport omega := by
    linarith
  have hlogGap :
      Filter.Tendsto
        (fun M =>
          powerShellLog M /
            powerShellScale M ^
              (1 - endpointDensityPower transport omega))
        Filter.atTop (nhds 0) := by
    simpa [powerShellLog, Function.comp_apply] using
      ((isLittleO_log_rpow_atTop hgap).tendsto_div_nhds_zero).comp
        powerShellScale_tendsto_atTop
  have hlogSqGap :
      Filter.Tendsto
        (fun M =>
          (powerShellLog M) ^ (2 : ℝ) /
            powerShellScale M ^
              (1 - endpointDensityPower transport omega))
        Filter.atTop (nhds 0) := by
    simpa [powerShellLog, Function.comp_apply] using
      ((isLittleO_log_rpow_rpow_atTop
        (2 : ℝ) hgap).tendsto_div_nhds_zero).comp
          powerShellScale_tendsto_atTop
  have hpowGap :
      Filter.Tendsto
        (fun M =>
          1 /
            powerShellScale M ^
              (1 - endpointDensityPower transport omega))
        Filter.atTop (nhds 0) := by
    have h :=
      (tendsto_rpow_neg_atTop hgap).comp
        powerShellScale_tendsto_atTop
    convert h using 1
    funext M
    simp only [Function.comp_apply]
    rw [Real.rpow_neg (powerShellScale_pos M).le]
    simp [one_div]
  have h1 :=
    hlogSqGap.const_mul
      (6 * omega * endpointDensityPower transport omega)
  have h2 :=
    hlogGap.const_mul
      (omega * centralRenyiEndpointCostConstant
          theta eta transport D0 +
        6 * endpointDensityPower transport omega)
  have h3 :=
    hpowGap.const_mul
      (centralRenyiEndpointCostConstant theta eta transport D0 +
        |Real.log 3|)
  have hsum := (h1.add h2).add h3
  have hsum0 :
      Filter.Tendsto
        (fun M =>
          (6 * omega * endpointDensityPower transport omega) *
              ((powerShellLog M) ^ (2 : ℝ) /
                powerShellScale M ^
                  (1 - endpointDensityPower transport omega)) +
            (omega * centralRenyiEndpointCostConstant
                  theta eta transport D0 +
                6 * endpointDensityPower transport omega) *
              (powerShellLog M /
                powerShellScale M ^
                  (1 - endpointDensityPower transport omega)) +
            (centralRenyiEndpointCostConstant theta eta transport D0 +
                |Real.log 3|) *
              (1 /
                powerShellScale M ^
                  (1 - endpointDensityPower transport omega)))
        Filter.atTop (nhds 0) := by
    simpa only [mul_zero, add_zero] using hsum
  convert hsum0 using 1
  funext M
  rw [centralRenyiEndpointLogCostEnvelope_eq]
  ring

/-- The central endpoint chains are eventually dominated by the same
stretched-exponential shell model as the abstract endpoint bootstrap. -/
theorem centralRenyiEndpointChainExceptionalRatio_eventually_le_model
    {theta eta transport t D0 Dcut omega : ℝ}
    (htheta0 : 0 < theta) (htheta1 : theta < 1)
    (heta0 : 0 < eta)
    (heta1 : eta < FixedTotal.centralRenyiAlpha theta - 1 / 2)
    (htransport0 : 0 < transport)
    (htransport : transport < FixedTotal.centralRenyiAsymptoticRate theta)
    (htransport1 : transport < 1)
    (hstep : EndpointDensityStep t transport
      (FixedTotal.centralRenyiStageConstant theta eta transport)
      Terras.quadraticWindowFixedGlobalConstant Dcut 6)
    (hD00 : 0 < D0) (hD01 : D0 ≤ 1) (hD0cut : D0 ≤ Dcut)
    (homega : 0 < omega)
    (hw : endpointDensityPower transport omega < 1) :
    ∀ᶠ M : ℕ in Filter.atTop,
      shellExceptionalRatio
          (endpointChain t (endpointStageCount omega M)) M ≤
        endpointShellDecayModel transport D0 omega M := by
  let d := endpointDensityConstant transport D0
  let c := Real.log 2 * d / 4
  have hd0 : 0 < d := by
    dsimp [d]
    exact endpointDensityConstant_pos htransport0 hD00
  have hc0 : 0 < c := by
    dsimp [c]
    positivity
  have hcost :=
    centralRenyiEndpointLogCostEnvelope_ratio_tendsto_zero
      htransport0 htransport1 homega hw
      (theta := theta) (eta := eta) (D0 := D0)
  have hsmall :
      ∀ᶠ M : ℕ in Filter.atTop,
        centralRenyiEndpointLogCostEnvelope
              theta eta transport D0 omega M /
            powerShellScale M ^
              (1 - endpointDensityPower transport omega) < c := by
    have hevent := (Metric.tendsto_atTop.1 hcost) c hc0
    filter_upwards [Filter.eventually_atTop.2 hevent] with M hM
    rw [Real.dist_eq] at hM
    exact lt_of_le_of_lt (le_abs_self _) (by simpa [sub_zero] using hM)
  have hM4 :
      ∀ᶠ M : ℕ in Filter.atTop, 4 ≤ M :=
    Filter.eventually_atTop.2 ⟨4, fun _ h => h⟩
  filter_upwards [hsmall, hM4] with M hsmallM hM4M
  have hcert :=
    centralRenyiEndpointScheduledChain_dense
      (omega := omega) hstep hD00 hD01 hD0cut M
  have hlogC :=
    centralRenyiEndpointScheduledLogC_le
      htheta0 htheta1 heta0 heta1 htransport0 htransport
      htransport1 hD00 hD01 homega M
  have hXgap0 :
      0 < powerShellScale M ^
          (1 - endpointDensityPower transport omega) :=
    Real.rpow_pos_of_pos (powerShellScale_pos M) _
  have hcostRaw :
      centralRenyiEndpointLogCostEnvelope
          theta eta transport D0 omega M <
        c * powerShellScale M ^
          (1 - endpointDensityPower transport omega) :=
    (div_lt_iff₀ hXgap0).mp hsmallM
  have hK0 :
      0 < FixedTotal.centralRenyiStageConstant theta eta transport :=
    FixedTotal.centralRenyiStageConstant_pos
      htheta0 htheta1 heta0 heta1 htransport0 htransport
  have hW0 :
      0 < Terras.quadraticWindowFixedGlobalConstant :=
    linearWindowConstant_pos
  have hC0 :
      0 < centralRenyiEndpointScheduledC
          theta eta transport D0 omega M := by
    unfold centralRenyiEndpointScheduledC
    exact endpointAbstractC_pos
      hK0 hW0 htransport0 hD00 (B := 6) _
  have hCtwo0 :
      0 < centralRenyiEndpointScheduledC
          theta eta transport D0 omega M + 2 := by
    linarith
  have hCexp :
      centralRenyiEndpointScheduledC theta eta transport D0 omega M ≤
        Real.exp
          (c * powerShellScale M ^
            (1 - endpointDensityPower transport omega)) := by
    have hlogBound :
        Real.log
            (centralRenyiEndpointScheduledC
              theta eta transport D0 omega M + 2) ≤
          c * powerShellScale M ^
            (1 - endpointDensityPower transport omega) :=
      hlogC.trans hcostRaw.le
    have hexp :
        centralRenyiEndpointScheduledC
              theta eta transport D0 omega M + 2 ≤
          Real.exp
            (c * powerShellScale M ^
              (1 - endpointDensityPower transport omega)) := by
      rw [← Real.exp_log hCtwo0]
      exact Real.exp_le_exp.2 hlogBound
    linarith
  have hDM :=
    endpointScheduledD_mul_shell_lower
      htransport0 htransport1 hD00 homega hM4M
  have hdecay :
      2 * c * powerShellScale M ^
            (1 - endpointDensityPower transport omega) ≤
        Real.log 2 * endpointScheduledD transport D0 omega M * (M : ℝ) := by
    have hmul :=
      mul_le_mul_of_nonneg_left hDM
        (Real.log_pos (show (1 : ℝ) < 2 by norm_num)).le
    dsimp [c, d]
    nlinarith
  have hexpDecay :
      Real.exp
          (-(Real.log 2 *
            endpointScheduledD transport D0 omega M * (M : ℝ))) ≤
        Real.exp
          (-(2 * c * powerShellScale M ^
            (1 - endpointDensityPower transport omega))) :=
    Real.exp_le_exp.2 (by linarith)
  calc
    shellExceptionalRatio
        (endpointChain t (endpointStageCount omega M)) M
        ≤
      2 * centralRenyiEndpointScheduledC
            theta eta transport D0 omega M *
        Real.exp
          (-(Real.log 2 *
            endpointScheduledD transport D0 omega M * M)) :=
      shellExceptionalRatio_le_of_isCDDense hcert M
    _ ≤
      2 * Real.exp
          (c * powerShellScale M ^
            (1 - endpointDensityPower transport omega)) *
        Real.exp
          (-(2 * c * powerShellScale M ^
            (1 - endpointDensityPower transport omega))) := by
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left hCexp (by norm_num))
        hexpDecay
        (Real.exp_nonneg _)
        (mul_nonneg (by norm_num) (Real.exp_nonneg _))
    _ = endpointShellDecayModel transport D0 omega M := by
      unfold endpointShellDecayModel
      dsimp [c, d]
      calc
        2 *
              Real.exp
                (Real.log 2 * endpointDensityConstant transport D0 / 4 *
                  powerShellScale M ^
                    (1 - endpointDensityPower transport omega)) *
              Real.exp
                (-(2 *
                  (Real.log 2 * endpointDensityConstant transport D0 / 4) *
                  powerShellScale M ^
                    (1 - endpointDensityPower transport omega)))
            =
          2 *
            (Real.exp
                (Real.log 2 * endpointDensityConstant transport D0 / 4 *
                  powerShellScale M ^
                    (1 - endpointDensityPower transport omega)) *
              Real.exp
                (-(2 *
                  (Real.log 2 * endpointDensityConstant transport D0 / 4) *
                  powerShellScale M ^
                    (1 - endpointDensityPower transport omega)))) := by ring
        _ =
          2 * Real.exp
            (Real.log 2 * endpointDensityConstant transport D0 / 4 *
                powerShellScale M ^
                  (1 - endpointDensityPower transport omega) +
              -(2 *
                (Real.log 2 * endpointDensityConstant transport D0 / 4) *
                powerShellScale M ^
                  (1 - endpointDensityPower transport omega))) := by
            rw [Real.exp_add]
        _ = _ := by
          congr 2
          ring

/-- The central higher-Renyi endpoint chains have vanishing exceptional
shell proportion. -/
theorem centralRenyiEndpointChainExceptionalRatio_tendsto_zero
    {theta eta transport t D0 Dcut omega : ℝ}
    (htheta0 : 0 < theta) (htheta1 : theta < 1)
    (heta0 : 0 < eta)
    (heta1 : eta < FixedTotal.centralRenyiAlpha theta - 1 / 2)
    (htransport0 : 0 < transport)
    (htransport : transport < FixedTotal.centralRenyiAsymptoticRate theta)
    (htransport1 : transport < 1)
    (hstep : EndpointDensityStep t transport
      (FixedTotal.centralRenyiStageConstant theta eta transport)
      Terras.quadraticWindowFixedGlobalConstant Dcut 6)
    (hD00 : 0 < D0) (hD01 : D0 ≤ 1) (hD0cut : D0 ≤ Dcut)
    (homega : 0 < omega)
    (hw : endpointDensityPower transport omega < 1) :
    Filter.Tendsto
      (fun M =>
        shellExceptionalRatio
          (endpointChain t (endpointStageCount omega M)) M)
      Filter.atTop (nhds 0) := by
  have hbound :=
    centralRenyiEndpointChainExceptionalRatio_eventually_le_model
      htheta0 htheta1 heta0 heta1 htransport0 htransport htransport1
      hstep hD00 hD01 hD0cut homega hw
  have hmodel :=
    endpointShellDecayModel_tendsto_zero htransport0 hD00 hw
  exact squeeze_zero'
    (Filter.Eventually.of_forall fun M =>
      shellExceptionalRatio_nonneg
        (endpointChain t (endpointStageCount omega M)) M)
    hbound hmodel

def centralRenyiEndpointExceptionalCountExponent
    (transport omega : ℝ) : ℝ :=
  1 - endpointDensityPower transport omega

def centralRenyiEndpointExceptionalCountRate
    (transport D0 : ℝ) : ℝ :=
  stretchedDyadicRate
      (Real.log 2 * endpointDensityConstant transport D0 / 4) / 2

/-- Shell-to-prefix exceptional-count theorem for a fixed central endpoint
schedule.  At the full headline range the count exponent is positive, but
need not exceed the orbit exponent. -/
theorem centralRenyiEndpointDescentSet_badPrefix_eventually_le_stretched_log
    {theta eta r transport D0 Dcut omega delta : ℝ}
    (htheta0 : 0 < theta) (htheta1 : theta < 1)
    (heta0 : 0 < eta)
    (heta1 : eta < FixedTotal.centralRenyiAlpha theta - 1 / 2)
    (hra : a0 < r) (hr1 : r < 1)
    (htransport0 : 0 < transport)
    (htransport : transport < FixedTotal.centralRenyiAsymptoticRate theta)
    (htransport1 : transport < 1)
    (hstep : EndpointDensityStep (r - a0) transport
      (FixedTotal.centralRenyiStageConstant theta eta transport)
      Terras.quadraticWindowFixedGlobalConstant Dcut 6)
    (hD00 : 0 < D0) (hD01 : D0 ≤ 1) (hD0cut : D0 ≤ Dcut)
    (homega : 0 < omega)
    (hdeltaU : delta < endpointOrbitPower r omega)
    (hdelta1 : delta < 1)
    (hw : endpointDensityPower transport omega < 1) :
    ∀ᶠ N : ℕ in Filter.atTop,
      ((badPrefix (endpointDescentSet r omega delta) N).card : ℝ) ≤
        5 * N *
          Real.exp
            (-(centralRenyiEndpointExceptionalCountRate transport D0) *
              (Real.log N) ^
                (centralRenyiEndpointExceptionalCountExponent
                  transport omega)) := by
  have halpha0 :
      0 < centralRenyiEndpointExceptionalCountExponent transport omega := by
    unfold centralRenyiEndpointExceptionalCountExponent
    linarith
  have halpha1 :
      centralRenyiEndpointExceptionalCountExponent transport omega ≤ 1 := by
    unfold centralRenyiEndpointExceptionalCountExponent
    have hw0 := endpointDensityPower_pos htransport0 htransport1 homega
    linarith
  have hbudget :=
    endpointOrbitBudget_eventually
      (a0_pos.trans hra) hr1 homega hdeltaU hdelta1
  have heq := endpointDescentShell_ratio_eventually_eq hbudget
  have hmodel :=
    centralRenyiEndpointChainExceptionalRatio_eventually_le_model
      htheta0 htheta1 heta0 heta1 htransport0 htransport htransport1
      hstep hD00 hD01 hD0cut homega hw
  have hshellEvent :
      ∀ᶠ M : ℕ in Filter.atTop,
        shellExceptionalRatio (endpointDescentShell r omega delta M) M ≤
          2 * Real.exp
            (-(Real.log 2 * endpointDensityConstant transport D0 / 4) *
              stretchedShellScale M ^
                (centralRenyiEndpointExceptionalCountExponent
                  transport omega)) := by
    filter_upwards [heq, hmodel] with M heqM hmodelM
    rw [heqM]
    simpa [endpointShellDecayModel, powerShellScale,
      stretchedShellScale, centralRenyiEndpointExceptionalCountExponent]
      using hmodelM
  obtain ⟨M₀, hM₀⟩ := Filter.eventually_atTop.1 hshellEvent
  let N₀ := 2 ^ (2 * M₀ + 2)
  filter_upwards [Filter.eventually_ge_atTop N₀] with N hN₀
  have hN0 : 0 < N := by
    have hpow0 : 0 < N₀ := by dsimp [N₀]; positivity
    omega
  have hlogLower : 2 * M₀ + 2 ≤ Nat.log 2 N := by
    apply Nat.le_log_of_pow_le (by norm_num)
    exact hN₀
  have hlogTwo : 2 ≤ Nat.log 2 N := by omega
  have hMhalf : M₀ ≤ Nat.log 2 N / 2 := by
    apply (Nat.le_div_iff_mul_le (by norm_num : 0 < 2)).2
    omega
  have hc :
      0 < Real.log 2 * endpointDensityConstant transport D0 / 4 := by
    exact div_pos
      (mul_pos (Real.log_pos (by norm_num))
        (endpointDensityConstant_pos htransport0 hD00))
      (by norm_num)
  have hcount :=
    card_badPrefix_assembleDyadic_le_stretched_log
      (endpointDescentShell r omega delta) M₀ N 2
      (Real.log 2 * endpointDensityConstant transport D0 / 4)
      (centralRenyiEndpointExceptionalCountExponent transport omega)
      (by norm_num) hc halpha0 halpha1
      (fun M hM => hM₀ M hM) hN0 hlogTwo hMhalf
  change
    ((badPrefix (assembleDyadic
      (endpointDescentShell r omega delta)) N).card : ℝ) ≤ _
  simpa only [centralRenyiEndpointExceptionalCountRate] using
    (show
      ((badPrefix (assembleDyadic
        (endpointDescentShell r omega delta)) N).card : ℝ) ≤
        5 * N *
          Real.exp
            (-(stretchedDyadicRate
                (Real.log 2 * endpointDensityConstant transport D0 / 4) / 2) *
              (Real.log N) ^
                (centralRenyiEndpointExceptionalCountExponent
                  transport omega)) by
      convert hcount using 1 <;> norm_num)

/-- Shell-to-prefix exceptional-count theorem with the total endpoint-chain
witness time retained. -/
theorem centralRenyiEndpointTimedDescentSet_badPrefix_eventually_le_stretched_log
    {theta eta r transport D0 Dcut omega delta timeConstant : ℝ}
    (htheta0 : 0 < theta) (htheta1 : theta < 1)
    (heta0 : 0 < eta)
    (heta1 : eta < FixedTotal.centralRenyiAlpha theta - 1 / 2)
    (hra : a0 < r) (hr1 : r < 1)
    (htransport0 : 0 < transport)
    (htransport : transport < FixedTotal.centralRenyiAsymptoticRate theta)
    (htransport1 : transport < 1)
    (hstep : EndpointDensityStep (r - a0) transport
      (FixedTotal.centralRenyiStageConstant theta eta transport)
      Terras.quadraticWindowFixedGlobalConstant Dcut 6)
    (hD00 : 0 < D0) (hD01 : D0 ≤ 1) (hD0cut : D0 ≤ Dcut)
    (homega : 0 < omega)
    (hdeltaU : delta < endpointOrbitPower r omega)
    (hdelta1 : delta < 1)
    (hw : endpointDensityPower transport omega < 1)
    (htime : (1 - r)⁻¹ / Real.log 2 < timeConstant) :
    ∀ᶠ N : ℕ in Filter.atTop,
      ((badPrefix
        (endpointTimedDescentSet r omega delta timeConstant) N).card : ℝ) ≤
        5 * N *
          Real.exp
            (-(centralRenyiEndpointExceptionalCountRate transport D0) *
              (Real.log N) ^
                (centralRenyiEndpointExceptionalCountExponent
                  transport omega)) := by
  have halpha0 :
      0 < centralRenyiEndpointExceptionalCountExponent transport omega := by
    unfold centralRenyiEndpointExceptionalCountExponent
    linarith
  have halpha1 :
      centralRenyiEndpointExceptionalCountExponent transport omega ≤ 1 := by
    unfold centralRenyiEndpointExceptionalCountExponent
    have hw0 := endpointDensityPower_pos htransport0 htransport1 homega
    linarith
  have hbudget :=
    endpointOrbitBudget_eventually
      (a0_pos.trans hra) hr1 homega hdeltaU hdelta1
  have htimeBudget :
      ∀ᶠ M : ℕ in Filter.atTop,
        endpointTimeShellBudget r omega timeConstant M := by
    simpa [endpointTimeShellBudget] using
      endpointTime_schedule_eventually_lt hra hr1 homega htime
  have heq := endpointTimedDescentShell_ratio_eventually_eq
    hbudget htimeBudget
  have hmodel :=
    centralRenyiEndpointChainExceptionalRatio_eventually_le_model
      htheta0 htheta1 heta0 heta1 htransport0 htransport htransport1
      hstep hD00 hD01 hD0cut homega hw
  have hshellEvent :
      ∀ᶠ M : ℕ in Filter.atTop,
        shellExceptionalRatio
            (endpointTimedDescentShell r omega delta timeConstant M) M ≤
          2 * Real.exp
            (-(Real.log 2 * endpointDensityConstant transport D0 / 4) *
              stretchedShellScale M ^
                (centralRenyiEndpointExceptionalCountExponent
                  transport omega)) := by
    filter_upwards [heq, hmodel] with M heqM hmodelM
    rw [heqM]
    simpa [endpointShellDecayModel, powerShellScale,
      stretchedShellScale, centralRenyiEndpointExceptionalCountExponent]
      using hmodelM
  obtain ⟨M₀, hM₀⟩ := Filter.eventually_atTop.1 hshellEvent
  let N₀ := 2 ^ (2 * M₀ + 2)
  filter_upwards [Filter.eventually_ge_atTop N₀] with N hN₀
  have hN0 : 0 < N := by
    have hpow0 : 0 < N₀ := by dsimp [N₀]; positivity
    omega
  have hlogLower : 2 * M₀ + 2 ≤ Nat.log 2 N := by
    apply Nat.le_log_of_pow_le (by norm_num)
    exact hN₀
  have hlogTwo : 2 ≤ Nat.log 2 N := by omega
  have hMhalf : M₀ ≤ Nat.log 2 N / 2 := by
    apply (Nat.le_div_iff_mul_le (by norm_num : 0 < 2)).2
    omega
  have hc :
      0 < Real.log 2 * endpointDensityConstant transport D0 / 4 := by
    exact div_pos
      (mul_pos (Real.log_pos (by norm_num))
        (endpointDensityConstant_pos htransport0 hD00))
      (by norm_num)
  have hcount :=
    card_badPrefix_assembleDyadic_le_stretched_log
      (endpointTimedDescentShell r omega delta timeConstant) M₀ N 2
      (Real.log 2 * endpointDensityConstant transport D0 / 4)
      (centralRenyiEndpointExceptionalCountExponent transport omega)
      (by norm_num) hc halpha0 halpha1
      (fun M hM => hM₀ M hM) hN0 hlogTwo hMhalf
  change
    ((badPrefix (assembleDyadic
      (endpointTimedDescentShell r omega delta timeConstant)) N).card : ℝ) ≤ _
  simpa only [centralRenyiEndpointExceptionalCountRate] using
    (show
      ((badPrefix (assembleDyadic
        (endpointTimedDescentShell r omega delta timeConstant)) N).card : ℝ) ≤
        5 * N *
          Real.exp
            (-(stretchedDyadicRate
                (Real.log 2 * endpointDensityConstant transport D0 / 4) / 2) *
              (Real.log N) ^
                (centralRenyiEndpointExceptionalCountExponent
                  transport omega)) by
      convert hcount using 1 <;> norm_num)

/-- Density-one assembly for the central higher-Renyi endpoint chain. -/
theorem centralRenyiEndpointDescentSet_hasNaturalDensityOne
    {theta eta r transport D0 Dcut omega delta : ℝ}
    (htheta0 : 0 < theta) (htheta1 : theta < 1)
    (heta0 : 0 < eta)
    (heta1 : eta < FixedTotal.centralRenyiAlpha theta - 1 / 2)
    (hra : a0 < r) (hr1 : r < 1)
    (htransport0 : 0 < transport)
    (htransport : transport < FixedTotal.centralRenyiAsymptoticRate theta)
    (htransport1 : transport < 1)
    (hstep : EndpointDensityStep (r - a0) transport
      (FixedTotal.centralRenyiStageConstant theta eta transport)
      Terras.quadraticWindowFixedGlobalConstant Dcut 6)
    (hD00 : 0 < D0) (hD01 : D0 ≤ 1) (hD0cut : D0 ≤ Dcut)
    (homega : 0 < omega)
    (hdeltaU : delta < endpointOrbitPower r omega)
    (hdelta1 : delta < 1)
    (hw : endpointDensityPower transport omega < 1) :
    HasNaturalDensityOne (endpointDescentSet r omega delta) := by
  have hbudget :=
    endpointOrbitBudget_eventually
      (a0_pos.trans hra) hr1 homega hdeltaU hdelta1
  have hratio :=
    centralRenyiEndpointChainExceptionalRatio_tendsto_zero
      htheta0 htheta1 heta0 heta1 htransport0 htransport htransport1
      hstep hD00 hD01 hD0cut homega hw
  have hratio' :=
    hratio.congr'
      (endpointDescentShell_ratio_eventually_eq hbudget).symm
  exact hasNaturalDensityOne_assembleDyadic _ hratio'

/-- Density-one assembly with the total endpoint-chain witness time retained. -/
theorem centralRenyiEndpointTimedDescentSet_hasNaturalDensityOne
    {theta eta r transport D0 Dcut omega delta timeConstant : ℝ}
    (htheta0 : 0 < theta) (htheta1 : theta < 1)
    (heta0 : 0 < eta)
    (heta1 : eta < FixedTotal.centralRenyiAlpha theta - 1 / 2)
    (hra : a0 < r) (hr1 : r < 1)
    (htransport0 : 0 < transport)
    (htransport : transport < FixedTotal.centralRenyiAsymptoticRate theta)
    (htransport1 : transport < 1)
    (hstep : EndpointDensityStep (r - a0) transport
      (FixedTotal.centralRenyiStageConstant theta eta transport)
      Terras.quadraticWindowFixedGlobalConstant Dcut 6)
    (hD00 : 0 < D0) (hD01 : D0 ≤ 1) (hD0cut : D0 ≤ Dcut)
    (homega : 0 < omega)
    (hdeltaU : delta < endpointOrbitPower r omega)
    (hdelta1 : delta < 1)
    (hw : endpointDensityPower transport omega < 1)
    (htime : (1 - r)⁻¹ / Real.log 2 < timeConstant) :
    HasNaturalDensityOne
      (endpointTimedDescentSet r omega delta timeConstant) := by
  have hbudget :=
    endpointOrbitBudget_eventually
      (a0_pos.trans hra) hr1 homega hdeltaU hdelta1
  have htimeBudget :
      ∀ᶠ M : ℕ in Filter.atTop,
        endpointTimeShellBudget r omega timeConstant M := by
    simpa [endpointTimeShellBudget] using
      endpointTime_schedule_eventually_lt hra hr1 homega htime
  have hratio :=
    centralRenyiEndpointChainExceptionalRatio_tendsto_zero
      htheta0 htheta1 heta0 heta1 htransport0 htransport htransport1
      hstep hD00 hD01 hD0cut homega hw
  have hratio' :=
    hratio.congr'
      (endpointTimedDescentShell_ratio_eventually_eq
        hbudget htimeBudget).symm
  exact hasNaturalDensityOne_assembleDyadic _ hratio'

/-- Fixed-parameter endpoint-only theorem driven by the central
higher-Renyi pullback. -/
theorem centralRenyiEndpointOnlyTheorem_parameterized
    {theta eta r transport D0 Dcut omega delta : ℝ}
    (htheta0 : 0 < theta) (htheta1 : theta < 1)
    (heta0 : 0 < eta)
    (heta1 : eta < FixedTotal.centralRenyiAlpha theta - 1 / 2)
    (hra : a0 < r) (hr1 : r < 1)
    (htransport0 : 0 < transport)
    (htransport : transport < FixedTotal.centralRenyiAsymptoticRate theta)
    (htransport1 : transport < 1)
    (hstep : EndpointDensityStep (r - a0) transport
      (FixedTotal.centralRenyiStageConstant theta eta transport)
      Terras.quadraticWindowFixedGlobalConstant Dcut 6)
    (hD00 : 0 < D0) (hD01 : D0 ≤ 1) (hD0cut : D0 ≤ Dcut)
    (homega : 0 < omega)
    (hdelta0 : 0 < delta)
    (hdeltaU : delta < endpointOrbitPower r omega)
    (htransportR : transport < r)
    (hw : endpointDensityPower transport omega < 1) :
    HasNaturalDensityOne
      (quantitativeLinearDescentSet delta 1) := by
  have hdelta1 : delta < 1 := by
    have hu0 :=
      endpointOrbitPower_pos (a0_pos.trans hra) hr1 homega
    have hw0 :=
      endpointDensityPower_pos htransport0 htransport1 homega
    have hlog :
        Real.log (1 / r) < Real.log (1 / transport) := by
      exact Real.strictMonoOn_log
        (Set.mem_Ioi.mpr (one_div_pos.mpr (a0_pos.trans hra)))
        (Set.mem_Ioi.mpr (one_div_pos.mpr htransport0))
        (one_div_lt_one_div_of_lt htransport0 htransportR)
    have huLt :
        endpointOrbitPower r omega <
          endpointDensityPower transport omega := by
      unfold endpointOrbitPower endpointDensityPower powerU
      exact mul_lt_mul_of_pos_left hlog homega
    linarith
  apply linearHasNaturalDensityOne_mono
    (endpointDescentSet_subset_quantitativeLinearDescentSet
      hra hr1 homega hdelta1)
  exact centralRenyiEndpointDescentSet_hasNaturalDensityOne
    htheta0 htheta1 heta0 heta1 hra hr1 htransport0 htransport
    htransport1 hstep hD00 hD01 hD0cut homega hdeltaU hdelta1 hw

theorem centralRenyiAsymptoticRate_eq_a0_mul
    (theta : ℝ) :
    FixedTotal.centralRenyiAsymptoticRate theta =
      theta / (1 + theta) * a0 := by
  unfold FixedTotal.centralRenyiAsymptoticRate a0 lg3 Real.logb
  ring

theorem centralRenyiAsymptoticRate_lt_a0
    {theta : ℝ} (htheta0 : 0 < theta) (htheta1 : theta < 1) :
    FixedTotal.centralRenyiAsymptoticRate theta < a0 := by
  rw [centralRenyiAsymptoticRate_eq_a0_mul]
  have hden : 0 < 1 + theta := by linarith
  have hratio : theta / (1 + theta) < 1 :=
    (div_lt_one hden).2 (by linarith)
  nlinarith [mul_pos a0_pos (sub_pos.mpr hratio)]

/-- The fixed central moment and one-block window hypotheses admit one
common positive density cutoff.  This packages the mechanical cutoff
construction shared by the density, timed, and exceptional-count exports. -/
theorem exists_centralRenyiEndpointStep
    {theta r transport : ℝ}
    (htheta0 : 0 < theta) (htheta1 : theta < 1)
    (hra : a0 < r) (hr1 : r < 1)
    (htransport0 : 0 < transport)
    (htransport : transport < FixedTotal.centralRenyiAsymptoticRate theta) :
    ∃ eta Dcut : ℝ,
      0 < eta ∧
      eta < FixedTotal.centralRenyiAlpha theta - 1 / 2 ∧
      0 < Dcut ∧ Dcut ≤ 1 ∧
      EndpointDensityStep (r - a0) transport
        (FixedTotal.centralRenyiStageConstant theta eta transport)
        Terras.quadraticWindowFixedGlobalConstant Dcut 6 := by
  let eta :=
    (FixedTotal.centralRenyiAlpha theta - 1 / 2) / 2
  have hgap :
      0 < FixedTotal.centralRenyiAlpha theta - 1 / 2 := by
    linarith [FixedTotal.one_half_lt_centralRenyiAlpha
      htheta0 htheta1]
  have heta0 : 0 < eta := by dsimp [eta]; linarith
  have heta1 :
      eta < FixedTotal.centralRenyiAlpha theta - 1 / 2 := by
    dsimp [eta]
    linarith
  obtain ⟨Dlinear, hDlinear0, hDlinear1, hlinear⟩ :=
    FixedTotal.exists_centralRenyi_full_cutoff
      htheta0 heta0 htransport0 htransport
  let t := r - a0
  let W := Terras.quadraticWindowDensityRate t
  let Dcut := min Dlinear (W / transport)
  have ht0 : 0 < t := by dsimp [t]; linarith
  have ht1 : t ≤ 1 := by dsimp [t]; linarith [a0_pos]
  have hW0 : 0 < W := by
    unfold W Terras.quadraticWindowDensityRate
    exact div_pos
      (mul_pos Terras.maximalBarrierC0_pos (sq_pos_of_pos ht0))
      (Real.log_pos (by norm_num))
  have hDcut0 : 0 < Dcut := by
    dsimp [Dcut]
    exact lt_min hDlinear0 (div_pos hW0 htransport0)
  have hDcut1 : Dcut ≤ 1 :=
    (min_le_left _ _).trans hDlinear1
  have hcut :
      ∀ D : ℝ, 0 < D → D ≤ Dcut →
        transport * D ≤
            FixedTotal.centralRenyiShellRate theta transport D /
              Real.log 2 ∧
        FixedTotal.centralRenyiShellRate theta transport D ≤
            eta * Real.log 2 / 16 ∧
        FixedTotal.centralRenyiShellRate theta transport D ≤ eta ^ 2 / 8 := by
    intro D hD hDcut
    exact hlinear D hD (hDcut.trans (min_le_left _ _))
  have hwindow : transport * Dcut ≤ W := by
    have h :=
      (le_div_iff₀ htransport0).mp
        (min_le_right Dlinear (W / transport))
    simpa [Dcut, mul_comm] using h
  have htransport1 : transport < 1 :=
    htransport.trans
      (centralRenyiAsymptoticRate_lt_a0 htheta0 htheta1) |>.trans a0_lt_one
  have hstep : EndpointDensityStep t transport
      (FixedTotal.centralRenyiStageConstant theta eta transport)
      Terras.quadraticWindowFixedGlobalConstant Dcut 6 :=
    centralRenyiEndpointDensityStep
      htheta0 htheta1 heta0 heta1 htransport0 htransport
      htransport1.le ht0 ht1 hDcut0 hcut
      (by simpa [W] using hwindow)
  exact ⟨eta, Dcut, heta0, heta1, hDcut0, hDcut1, by simpa [t] using hstep⟩

/-- Concrete cutoffs for the central endpoint theorem exist for every
transport rate below the central higher-Renyi limiting slope. -/
theorem centralRenyiEndpointOnlyTheorem_of_transport
    {theta r transport omega delta : ℝ}
    (htheta0 : 0 < theta) (htheta1 : theta < 1)
    (hra : a0 < r) (hr1 : r < 1)
    (htransport0 : 0 < transport)
    (htransport : transport < FixedTotal.centralRenyiAsymptoticRate theta)
    (homega : 0 < omega)
    (hdelta0 : 0 < delta)
    (hdeltaU : delta < endpointOrbitPower r omega)
    (hw : endpointDensityPower transport omega < 1) :
    HasNaturalDensityOne
      (quantitativeLinearDescentSet delta 1) := by
  obtain ⟨eta, Dcut, heta0, heta1, hDcut0, hDcut1, hstep⟩ :=
    exists_centralRenyiEndpointStep
      htheta0 htheta1 hra hr1 htransport0 htransport
  have htransport1 : transport < 1 :=
    htransport.trans
      (centralRenyiAsymptoticRate_lt_a0 htheta0 htheta1) |>.trans a0_lt_one
  exact centralRenyiEndpointOnlyTheorem_parameterized
    htheta0 htheta1 heta0 heta1 hra hr1 htransport0 htransport
    htransport1 hstep hDcut0 hDcut1 le_rfl homega hdelta0 hdeltaU
    (htransport.trans
      (centralRenyiAsymptoticRate_lt_a0 htheta0 htheta1) |>.trans hra)
    hw

theorem centralRenyiEndpointTimedTheorem_of_transport
    {theta r transport omega delta timeConstant : ℝ}
    (htheta0 : 0 < theta) (htheta1 : theta < 1)
    (hra : a0 < r) (hr1 : r < 1)
    (htransport0 : 0 < transport)
    (htransport : transport < FixedTotal.centralRenyiAsymptoticRate theta)
    (homega : 0 < omega)
    (hdelta0 : 0 < delta)
    (hdeltaU : delta < endpointOrbitPower r omega)
    (hw : endpointDensityPower transport omega < 1)
    (htime : (1 - r)⁻¹ / Real.log 2 < timeConstant) :
    HasNaturalDensityOne
      (quantitativeEndpointTimedDescentSet timeConstant delta 1) := by
  obtain ⟨eta, Dcut, heta0, heta1, hDcut0, hDcut1, hstep⟩ :=
    exists_centralRenyiEndpointStep
      htheta0 htheta1 hra hr1 htransport0 htransport
  have htransport1 : transport < 1 :=
    htransport.trans
      (centralRenyiAsymptoticRate_lt_a0 htheta0 htheta1) |>.trans a0_lt_one
  have htransportR : transport < r :=
    htransport.trans
      (centralRenyiAsymptoticRate_lt_a0 htheta0 htheta1) |>.trans hra
  have hdelta1 : delta < 1 := by
    have hu0 :=
      endpointOrbitPower_pos (a0_pos.trans hra) hr1 homega
    have hw0 :=
      endpointDensityPower_pos htransport0 htransport1 homega
    have hlog :
        Real.log (1 / r) < Real.log (1 / transport) := by
      exact Real.strictMonoOn_log
        (Set.mem_Ioi.mpr (one_div_pos.mpr (a0_pos.trans hra)))
        (Set.mem_Ioi.mpr (one_div_pos.mpr htransport0))
        (one_div_lt_one_div_of_lt htransport0 htransportR)
    have huLt :
        endpointOrbitPower r omega <
          endpointDensityPower transport omega := by
      unfold endpointOrbitPower endpointDensityPower powerU
      exact mul_lt_mul_of_pos_left hlog homega
    linarith
  apply linearHasNaturalDensityOne_mono
    (endpointTimedDescentSet_subset_quantitativeEndpointTimedDescentSet
      hra hr1 homega hdelta1)
  exact centralRenyiEndpointTimedDescentSet_hasNaturalDensityOne
    htheta0 htheta1 heta0 heta1 hra hr1 htransport0 htransport
    htransport1 hstep hDcut0 hDcut1 le_rfl homega hdeltaU hdelta1 hw htime

theorem centralRenyiEndpointExceptionalCount_of_transport
    {theta r transport omega delta : ℝ}
    (htheta0 : 0 < theta) (htheta1 : theta < 1)
    (hra : a0 < r) (hr1 : r < 1)
    (htransport0 : 0 < transport)
    (htransport : transport < FixedTotal.centralRenyiAsymptoticRate theta)
    (homega : 0 < omega)
    (hdelta0 : 0 < delta)
    (hdeltaU : delta < endpointOrbitPower r omega)
    (hw : endpointDensityPower transport omega < 1) :
    ∃ sigma c : ℝ,
      0 < sigma ∧ sigma ≤ 1 ∧ 0 < c ∧
      ∀ᶠ N : ℕ in Filter.atTop,
        ((badPrefix (endpointDescentSet r omega delta) N).card : ℝ) ≤
          5 * N * Real.exp (-c * (Real.log N) ^ sigma) := by
  obtain ⟨eta, Dcut, heta0, heta1, hDcut0, hDcut1, hstep⟩ :=
    exists_centralRenyiEndpointStep
      htheta0 htheta1 hra hr1 htransport0 htransport
  have htransport1 : transport < 1 :=
    htransport.trans
      (centralRenyiAsymptoticRate_lt_a0 htheta0 htheta1) |>.trans a0_lt_one
  have htransportR : transport < r :=
    htransport.trans
      (centralRenyiAsymptoticRate_lt_a0 htheta0 htheta1) |>.trans hra
  have hdelta1 : delta < 1 := by
    have hlog :
        Real.log (1 / r) < Real.log (1 / transport) := by
      exact Real.strictMonoOn_log
        (Set.mem_Ioi.mpr (one_div_pos.mpr (a0_pos.trans hra)))
        (Set.mem_Ioi.mpr (one_div_pos.mpr htransport0))
        (one_div_lt_one_div_of_lt htransport0 htransportR)
    have huLt :
        endpointOrbitPower r omega <
          endpointDensityPower transport omega := by
      unfold endpointOrbitPower endpointDensityPower powerU
      exact mul_lt_mul_of_pos_left hlog homega
    linarith
  let sigma := centralRenyiEndpointExceptionalCountExponent transport omega
  let c := centralRenyiEndpointExceptionalCountRate transport Dcut
  have hsigma0 : 0 < sigma := by
    dsimp [sigma, centralRenyiEndpointExceptionalCountExponent]
    linarith
  have hsigma1 : sigma ≤ 1 := by
    dsimp [sigma, centralRenyiEndpointExceptionalCountExponent]
    have hw0 := endpointDensityPower_pos htransport0 htransport1 homega
    linarith
  have hc0 : 0 < c := by
    dsimp [c, centralRenyiEndpointExceptionalCountRate]
    apply div_pos
    apply stretchedDyadicRate_pos
    exact div_pos
      (mul_pos (Real.log_pos (by norm_num))
        (endpointDensityConstant_pos htransport0 hDcut0))
      (by norm_num)
    norm_num
  refine ⟨sigma, c, hsigma0, hsigma1, hc0, ?_⟩
  simpa [sigma, c] using
    centralRenyiEndpointDescentSet_badPrefix_eventually_le_stretched_log
      htheta0 htheta1 heta0 heta1 hra hr1 htransport0 htransport
      htransport1 hstep hDcut0 hDcut1 le_rfl homega hdeltaU hdelta1 hw

/-- Quantitative timed exceptional count for fixed endpoint-only parameters. -/
theorem centralRenyiEndpointTimedExceptionalCount_of_transport
    {theta r transport omega delta timeConstant : ℝ}
    (htheta0 : 0 < theta) (htheta1 : theta < 1)
    (hra : a0 < r) (hr1 : r < 1)
    (htransport0 : 0 < transport)
    (htransport : transport < FixedTotal.centralRenyiAsymptoticRate theta)
    (homega : 0 < omega)
    (hdelta0 : 0 < delta)
    (hdeltaU : delta < endpointOrbitPower r omega)
    (hw : endpointDensityPower transport omega < 1)
    (htime : (1 - r)⁻¹ / Real.log 2 < timeConstant) :
    ∃ sigma c : ℝ,
      0 < sigma ∧ sigma ≤ 1 ∧ 0 < c ∧
      ∀ᶠ N : ℕ in Filter.atTop,
        ((badPrefix
          (endpointTimedDescentSet r omega delta timeConstant) N).card : ℝ) ≤
          5 * N * Real.exp (-c * (Real.log N) ^ sigma) := by
  obtain ⟨eta, Dcut, heta0, heta1, hDcut0, hDcut1, hstep⟩ :=
    exists_centralRenyiEndpointStep
      htheta0 htheta1 hra hr1 htransport0 htransport
  have htransport1 : transport < 1 :=
    htransport.trans
      (centralRenyiAsymptoticRate_lt_a0 htheta0 htheta1) |>.trans a0_lt_one
  have htransportR : transport < r :=
    htransport.trans
      (centralRenyiAsymptoticRate_lt_a0 htheta0 htheta1) |>.trans hra
  have hdelta1 : delta < 1 := by
    have hlog :
        Real.log (1 / r) < Real.log (1 / transport) := by
      exact Real.strictMonoOn_log
        (Set.mem_Ioi.mpr (one_div_pos.mpr (a0_pos.trans hra)))
        (Set.mem_Ioi.mpr (one_div_pos.mpr htransport0))
        (one_div_lt_one_div_of_lt htransport0 htransportR)
    have huLt :
        endpointOrbitPower r omega <
          endpointDensityPower transport omega := by
      unfold endpointOrbitPower endpointDensityPower powerU
      exact mul_lt_mul_of_pos_left hlog homega
    linarith
  let sigma := centralRenyiEndpointExceptionalCountExponent transport omega
  let c := centralRenyiEndpointExceptionalCountRate transport Dcut
  have hsigma0 : 0 < sigma := by
    dsimp [sigma, centralRenyiEndpointExceptionalCountExponent]
    linarith
  have hsigma1 : sigma ≤ 1 := by
    dsimp [sigma, centralRenyiEndpointExceptionalCountExponent]
    have hw0 := endpointDensityPower_pos htransport0 htransport1 homega
    linarith
  have hc0 : 0 < c := by
    dsimp [c, centralRenyiEndpointExceptionalCountRate]
    apply div_pos
    apply stretchedDyadicRate_pos
    exact div_pos
      (mul_pos (Real.log_pos (by norm_num))
        (endpointDensityConstant_pos htransport0 hDcut0))
      (by norm_num)
    norm_num
  refine ⟨sigma, c, hsigma0, hsigma1, hc0, ?_⟩
  simpa [sigma, c] using
    centralRenyiEndpointTimedDescentSet_badPrefix_eventually_le_stretched_log
      htheta0 htheta1 heta0 heta1 hra hr1 htransport0 htransport
      htransport1 hstep hDcut0 hDcut1 le_rfl homega hdeltaU hdelta1 hw htime

/-- Limiting transport slope as the central Renyi parameter tends to one
from below. -/
def centralRenyiEndpointTransportLimit : ℝ := a0 / 2

/-- Exact endpoint exponent supported by the full central range
`1/2 < theta < 1`. -/
def centralRenyiEndpointHeadlineExponent : ℝ :=
  endpointParameterDelta a0 centralRenyiEndpointTransportLimit

theorem centralRenyiEndpointHeadlineExponent_eq :
    centralRenyiEndpointHeadlineExponent =
      Real.log (1 / a0) / Real.log (2 / a0) := by
  unfold centralRenyiEndpointHeadlineExponent endpointParameterDelta
    centralRenyiEndpointTransportLimit
  congr 1
  field_simp [a0_pos.ne']

theorem centralRenyiEndpointTransportLimit_pos :
    0 < centralRenyiEndpointTransportLimit := by
  unfold centralRenyiEndpointTransportLimit
  linarith [a0_pos]

theorem centralRenyiEndpointTransportLimit_lt_one :
    centralRenyiEndpointTransportLimit < 1 := by
  unfold centralRenyiEndpointTransportLimit
  linarith [a0_lt_one]

theorem centralRenyiEndpointHeadlineExponent_pos :
    0 < centralRenyiEndpointHeadlineExponent := by
  unfold centralRenyiEndpointHeadlineExponent endpointParameterDelta
  exact div_pos
    (log_one_div_pos a0_pos a0_lt_one)
    (log_one_div_pos centralRenyiEndpointTransportLimit_pos
      centralRenyiEndpointTransportLimit_lt_one)

theorem centralRenyiEndpointHeadlineExponent_lt_one :
    centralRenyiEndpointHeadlineExponent < 1 := by
  unfold centralRenyiEndpointHeadlineExponent endpointParameterDelta
  have htransportA0 : centralRenyiEndpointTransportLimit < a0 := by
    unfold centralRenyiEndpointTransportLimit
    linarith [a0_pos]
  have hinv :
      1 / a0 < 1 / centralRenyiEndpointTransportLimit :=
    one_div_lt_one_div_of_lt centralRenyiEndpointTransportLimit_pos htransportA0
  have hlog :
      Real.log (1 / a0) <
        Real.log (1 / centralRenyiEndpointTransportLimit) :=
    Real.log_lt_log (one_div_pos.mpr a0_pos) hinv
  exact (div_lt_one
    (log_one_div_pos centralRenyiEndpointTransportLimit_pos
      centralRenyiEndpointTransportLimit_lt_one)).2 hlog

def centralRenyiChoiceTheta (n : ℕ) : ℝ :=
  1 - linearChoiceEps n / 2

def centralRenyiChoiceTransport (n : ℕ) : ℝ :=
  centralRenyiChoiceTheta n *
    FixedTotal.centralRenyiAsymptoticRate (centralRenyiChoiceTheta n)

theorem centralRenyiChoiceTheta_properties (n : ℕ) :
    1 / 2 < centralRenyiChoiceTheta n ∧
      centralRenyiChoiceTheta n < 1 := by
  have he0 := linearChoiceEps_pos n
  have heHalf := linearChoiceEps_le_half n
  unfold centralRenyiChoiceTheta
  constructor <;> linarith

theorem centralRenyiChoiceTransport_properties (n : ℕ) :
    0 < centralRenyiChoiceTransport n ∧
      centralRenyiChoiceTransport n <
        FixedTotal.centralRenyiAsymptoticRate
          (centralRenyiChoiceTheta n) := by
  have htheta := centralRenyiChoiceTheta_properties n
  have hrate :=
    FixedTotal.centralRenyiAsymptoticRate_pos (by linarith [htheta.1])
  unfold centralRenyiChoiceTransport
  constructor
  · exact mul_pos (by linarith [htheta.1]) hrate
  · nlinarith [mul_pos hrate (sub_pos.mpr htheta.2)]

theorem centralRenyiChoiceTheta_tendsto :
    Filter.Tendsto centralRenyiChoiceTheta Filter.atTop (nhds 1) := by
  have h :=
    (linearChoiceEps_tendsto_zero.const_mul (1 / 2 : ℝ)).neg.const_add 1
  convert h using 1
  · funext n
    unfold centralRenyiChoiceTheta
    ring
  · norm_num

theorem centralRenyiChoiceAsymptoticRate_tendsto :
    Filter.Tendsto
      (fun n => FixedTotal.centralRenyiAsymptoticRate
        (centralRenyiChoiceTheta n))
      Filter.atTop (nhds centralRenyiEndpointTransportLimit) := by
  have ht := centralRenyiChoiceTheta_tendsto
  have hden := ht.const_add 1
  have hratio := ht.div hden (by norm_num : (1 + 1 : ℝ) ≠ 0)
  have hmul := hratio.mul_const a0
  convert hmul using 1
  · funext n
    rw [centralRenyiAsymptoticRate_eq_a0_mul]
    rfl
  · unfold centralRenyiEndpointTransportLimit
    ring

theorem centralRenyiChoiceTransport_tendsto :
    Filter.Tendsto centralRenyiChoiceTransport Filter.atTop
      (nhds centralRenyiEndpointTransportLimit) := by
  have h := centralRenyiChoiceTheta_tendsto.mul
    centralRenyiChoiceAsymptoticRate_tendsto
  simpa [centralRenyiChoiceTransport] using h

theorem centralRenyiEndpointParameterDelta_choice_tendsto :
    Filter.Tendsto
      (fun n => endpointParameterDelta
        (linearChoiceQ n) (centralRenyiChoiceTransport n))
      Filter.atTop (nhds centralRenyiEndpointHeadlineExponent) := by
  have hr := linearChoiceQ_tendsto
  have ht := centralRenyiChoiceTransport_tendsto
  have hnum :
      Filter.Tendsto
        (fun n => Real.log (1 / linearChoiceQ n))
        Filter.atTop (nhds (Real.log (1 / a0))) := by
    have hinv := hr.inv₀ a0_pos.ne'
    simpa [one_div] using hinv.log (inv_ne_zero a0_pos.ne')
  have hden :
      Filter.Tendsto
        (fun n => Real.log (1 / centralRenyiChoiceTransport n))
        Filter.atTop
          (nhds (Real.log (1 / centralRenyiEndpointTransportLimit))) := by
    have hinv := ht.inv₀ centralRenyiEndpointTransportLimit_pos.ne'
    simpa [one_div] using hinv.log
      (inv_ne_zero centralRenyiEndpointTransportLimit_pos.ne')
  have hden0 :
      Real.log (1 / centralRenyiEndpointTransportLimit) ≠ 0 :=
    ne_of_gt (log_one_div_pos centralRenyiEndpointTransportLimit_pos
      centralRenyiEndpointTransportLimit_lt_one)
  have hratio := hnum.div hden hden0
  change Filter.Tendsto
    (fun n =>
      Real.log (1 / linearChoiceQ n) /
        Real.log (1 / centralRenyiChoiceTransport n))
    Filter.atTop
    (nhds
      (Real.log (1 / a0) /
        Real.log (1 / centralRenyiEndpointTransportLimit)))
  exact hratio

/-- Every exponent below the central endpoint boundary admits fixed
interior Renyi, contraction, transport, and schedule parameters. -/
theorem exists_centralRenyi_endpoint_only_parameters
    {delta : ℝ}
    (hdelta0 : 0 < delta)
    (hdelta : delta < centralRenyiEndpointHeadlineExponent) :
    ∃ theta r transport omega : ℝ,
      1 / 2 < theta ∧ theta < 1 ∧
      a0 < r ∧ r < 1 ∧
      0 < transport ∧
      transport < FixedTotal.centralRenyiAsymptoticRate theta ∧
      0 < omega ∧
      delta < endpointOrbitPower r omega ∧
      endpointDensityPower transport omega < 1 := by
  have hevent :
      ∀ᶠ n : ℕ in Filter.atTop,
        delta < endpointParameterDelta
          (linearChoiceQ n) (centralRenyiChoiceTransport n) :=
    centralRenyiEndpointParameterDelta_choice_tendsto.eventually
      (Ioi_mem_nhds hdelta)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hevent
  let theta := centralRenyiChoiceTheta N
  let r := linearChoiceQ N
  let transport := centralRenyiChoiceTransport N
  have htheta := centralRenyiChoiceTheta_properties N
  have hr := linearChoiceQ_properties N
  have ht := centralRenyiChoiceTransport_properties N
  have htransport1 : transport < 1 := by
    exact ht.2.trans
      (centralRenyiAsymptoticRate_lt_a0 (by linarith [htheta.1]) htheta.2) |>.trans
        a0_lt_one
  have hparam : delta < endpointParameterDelta r transport :=
    hN N le_rfl
  obtain ⟨omega, homega0, hdeltaU, hw⟩ :=
    exists_endpoint_omega_of_delta_lt_parameter
      hdelta0 hr.1 hr.2.2 ht.1 htransport1 hparam
  exact ⟨theta, r, transport, omega,
    htheta.1, htheta.2, hr.2.1, hr.2.2,
    ht.1, ht.2, homega0, hdeltaU, hw⟩

/-- Every exceptional-count power below the scalar endpoint budget admits
fixed central-Renyi and endpoint-schedule parameters realizing that power
exactly. -/
theorem exists_centralRenyi_endpoint_exceptional_parameters
    {delta sigma : ℝ}
    (hdelta0 : 0 < delta)
    (hdelta : delta < centralRenyiEndpointHeadlineExponent)
    (hsigma0 : 0 < sigma)
    (hsigma : sigma < 1 - delta / centralRenyiEndpointHeadlineExponent) :
    ∃ theta r transport omega : ℝ,
      1 / 2 < theta ∧ theta < 1 ∧
      a0 < r ∧ r < 1 ∧
      0 < transport ∧
      transport < FixedTotal.centralRenyiAsymptoticRate theta ∧
      0 < omega ∧
      delta < endpointOrbitPower r omega ∧
      endpointDensityPower transport omega < 1 ∧
      centralRenyiEndpointExceptionalCountExponent transport omega = sigma := by
  have hheadline0 : 0 < centralRenyiEndpointHeadlineExponent :=
    centralRenyiEndpointHeadlineExponent_pos
  have hratio0 : 0 < delta / centralRenyiEndpointHeadlineExponent :=
    div_pos hdelta0 hheadline0
  have hOneSigma : 0 < 1 - sigma := by
    linarith
  have hscaled0 : 0 < delta / (1 - sigma) :=
    div_pos hdelta0 hOneSigma
  have hratio :
      delta / centralRenyiEndpointHeadlineExponent < 1 - sigma := by
    linarith
  have hdeltaMul :
      delta < (1 - sigma) * centralRenyiEndpointHeadlineExponent := by
    exact (div_lt_iff₀ hheadline0).mp hratio
  have hscaled :
      delta / (1 - sigma) < centralRenyiEndpointHeadlineExponent := by
    exact (div_lt_iff₀ hOneSigma).2 (by nlinarith)
  have hevent :
      ∀ᶠ n : ℕ in Filter.atTop,
        delta / (1 - sigma) < endpointParameterDelta
          (linearChoiceQ n) (centralRenyiChoiceTransport n) :=
    centralRenyiEndpointParameterDelta_choice_tendsto.eventually
      (Ioi_mem_nhds hscaled)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hevent
  let theta := centralRenyiChoiceTheta N
  let r := linearChoiceQ N
  let transport := centralRenyiChoiceTransport N
  have htheta := centralRenyiChoiceTheta_properties N
  have hr := linearChoiceQ_properties N
  have ht := centralRenyiChoiceTransport_properties N
  have htransport1 : transport < 1 := by
    exact ht.2.trans
      (centralRenyiAsymptoticRate_lt_a0 (by linarith [htheta.1]) htheta.2) |>.trans
        a0_lt_one
  have hparam :
      delta / (1 - sigma) < endpointParameterDelta r transport :=
    hN N le_rfl
  let Lr := Real.log (1 / r)
  let Lt := Real.log (1 / transport)
  have hLr : 0 < Lr := by
    dsimp [Lr]
    exact log_one_div_pos (a0_pos.trans hr.2.1) hr.2.2
  have hLt : 0 < Lt := by
    dsimp [Lt]
    exact log_one_div_pos ht.1 htransport1
  have hcross : delta * Lt < (1 - sigma) * Lr := by
    unfold endpointParameterDelta at hparam
    dsimp [Lr, Lt]
    rw [div_lt_div_iff₀ hOneSigma hLt] at hparam
    nlinarith
  let omega := (1 - sigma) / Lt
  have homega : 0 < omega := by
    dsimp [omega]
    exact div_pos hOneSigma hLt
  have hdeltaU : delta < endpointOrbitPower r omega := by
    unfold endpointOrbitPower powerU
    change delta < (1 - sigma) / Lt * Lr
    have hquot : delta < ((1 - sigma) * Lr) / Lt :=
      (lt_div_iff₀ hLt).2 (by nlinarith)
    calc
      delta < ((1 - sigma) * Lr) / Lt := hquot
      _ = (1 - sigma) / Lt * Lr := by ring
  have hdensityEq : endpointDensityPower transport omega = 1 - sigma := by
    unfold endpointDensityPower powerU
    dsimp [omega, Lt]
    field_simp [hLt.ne']
  have hw : endpointDensityPower transport omega < 1 := by
    rw [hdensityEq]
    linarith
  have hexponent :
      centralRenyiEndpointExceptionalCountExponent transport omega = sigma := by
    unfold centralRenyiEndpointExceptionalCountExponent
    rw [hdensityEq]
    ring
  exact ⟨theta, r, transport, omega,
    htheta.1, htheta.2, hr.2.1, hr.2.2,
    ht.1, ht.2, homega, hdeltaU, hw, hexponent⟩

/-- Parameter selection with enough room to absorb the logarithmic number
of endpoint blocks into the explicit `6.953 * log n` witness time. -/
theorem exists_centralRenyi_endpoint_only_timed_parameters
    {delta : ℝ}
    (hdelta0 : 0 < delta)
    (hdelta : delta < centralRenyiEndpointHeadlineExponent) :
    ∃ theta r transport omega : ℝ,
      1 / 2 < theta ∧ theta < 1 ∧
      a0 < r ∧ r < 1 ∧
      0 < transport ∧
      transport < FixedTotal.centralRenyiAsymptoticRate theta ∧
      0 < omega ∧
      delta < endpointOrbitPower r omega ∧
      endpointDensityPower transport omega < 1 ∧
      (1 - r)⁻¹ / Real.log 2 < (6953 / 1000 : ℝ) := by
  have hdeltaEvent :
      ∀ᶠ n : ℕ in Filter.atTop,
        delta < endpointParameterDelta
          (linearChoiceQ n) (centralRenyiChoiceTransport n) :=
    centralRenyiEndpointParameterDelta_choice_tendsto.eventually
      (Ioi_mem_nhds hdelta)
  have hrLimit :
      Filter.Tendsto
        (fun n => 1 - linearChoiceQ n)
        Filter.atTop (nhds bConst) := by
    simpa [bConst] using tendsto_const_nhds.sub linearChoiceQ_tendsto
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have htimeLimit :
      bConst⁻¹ / Real.log 2 < (6953 / 1000 : ℝ) := by
    rw [show bConst⁻¹ / Real.log 2 =
        1 / (bConst * Real.log 2) by
      field_simp [bConst_pos.ne', hlog2.ne']]
    exact inv_bConst_mul_log_two_lt_6953
  have htimeTendsto :
      Filter.Tendsto
        (fun n => (1 - linearChoiceQ n)⁻¹ / Real.log 2)
        Filter.atTop (nhds (bConst⁻¹ / Real.log 2)) := by
    exact (hrLimit.inv₀ bConst_pos.ne').div_const (Real.log 2)
  have htimeEvent :
      ∀ᶠ n : ℕ in Filter.atTop,
        (1 - linearChoiceQ n)⁻¹ / Real.log 2 <
          (6953 / 1000 : ℝ) :=
    htimeTendsto.eventually (Iio_mem_nhds htimeLimit)
  obtain ⟨N, hN⟩ :=
    Filter.eventually_atTop.1 (hdeltaEvent.and htimeEvent)
  have hparam := (hN N le_rfl).1
  have htime := (hN N le_rfl).2
  let theta := centralRenyiChoiceTheta N
  let r := linearChoiceQ N
  let transport := centralRenyiChoiceTransport N
  have htheta := centralRenyiChoiceTheta_properties N
  have hr := linearChoiceQ_properties N
  have ht := centralRenyiChoiceTransport_properties N
  have htransport1 : transport < 1 := by
    exact ht.2.trans
      (centralRenyiAsymptoticRate_lt_a0 (by linarith [htheta.1]) htheta.2) |>.trans
        a0_lt_one
  obtain ⟨omega, homega0, hdeltaU, hw⟩ :=
    exists_endpoint_omega_of_delta_lt_parameter
      hdelta0 hr.1 hr.2.2 ht.1 htransport1 hparam
  exact ⟨theta, r, transport, omega,
    htheta.1, htheta.2, hr.2.1, hr.2.2,
    ht.1, ht.2, homega0, hdeltaU, hw, htime⟩

/-- **Central higher-Renyi endpoint-only theorem.**  Every positive
exponent below `log(1/a0) / log(2/a0)` gives stretched-logarithmic Collatz
descent on a natural-density-one set. -/
theorem centralRenyiEndpointOnlyTheorem_one
    {delta : ℝ}
    (hdelta0 : 0 < delta)
    (hdelta : delta < centralRenyiEndpointHeadlineExponent) :
    HasNaturalDensityOne
      (quantitativeLinearDescentSet delta 1) := by
  obtain ⟨theta, r, transport, omega,
      hthetaHalf, htheta1, hra, hr1, ht0, ht1,
      homega, hdu, hw⟩ :=
    exists_centralRenyi_endpoint_only_parameters hdelta0 hdelta
  exact centralRenyiEndpointOnlyTheorem_of_transport
    (by linarith [hthetaHalf]) htheta1 hra hr1 ht0 ht1
    homega hdelta0 hdu hw

/-- Full central-range endpoint theorem with an actual iterate witness before
`6.953 * log n`. -/
theorem centralRenyiEndpointOnlyTheorem_timed
    {delta : ℝ}
    (hdelta0 : 0 < delta)
    (hdelta : delta < centralRenyiEndpointHeadlineExponent) :
    HasNaturalDensityOne
      (quantitativeEndpointTimedDescentSet (6953 / 1000) delta 1) := by
  obtain ⟨theta, r, transport, omega,
      hthetaHalf, htheta1, hra, hr1, ht0, ht1,
      homega, hdu, hw, htime⟩ :=
    exists_centralRenyi_endpoint_only_timed_parameters hdelta0 hdelta
  exact centralRenyiEndpointTimedTheorem_of_transport
    (by linarith [hthetaHalf]) htheta1 hra hr1 ht0 ht1
    homega hdelta0 hdu hw htime

/-- Full central-range quantitative exceptional-count theorem.  The shell
power `sigma` is positive throughout the headline range; unlike the
full-envelope companion, it is not asserted to exceed `delta`. -/
theorem centralRenyiEndpointOnlyTheorem_exceptional_count
    {delta : ℝ}
    (hdelta0 : 0 < delta)
    (hdelta : delta < centralRenyiEndpointHeadlineExponent) :
    ∃ sigma c : ℝ,
      0 < sigma ∧ sigma ≤ 1 ∧ 0 < c ∧
      ∀ᶠ N : ℕ in Filter.atTop,
        ((badPrefix (quantitativeLinearDescentSet delta 1) N).card : ℝ) ≤
          5 * N * Real.exp (-c * (Real.log N) ^ sigma) := by
  obtain ⟨theta, r, transport, omega,
      hthetaHalf, htheta1, hra, hr1, ht0, ht1,
      homega, hdu, hw⟩ :=
    exists_centralRenyi_endpoint_only_parameters hdelta0 hdelta
  have htheta0 : 0 < theta := by linarith [hthetaHalf]
  obtain ⟨sigma, c, hsigma0, hsigma1, hc0, hcount⟩ :=
    centralRenyiEndpointExceptionalCount_of_transport
      htheta0 htheta1 hra hr1 ht0 ht1 homega hdelta0 hdu hw
  have htransport1 : transport < 1 :=
    ht1.trans
      (centralRenyiAsymptoticRate_lt_a0 htheta0 htheta1) |>.trans a0_lt_one
  have htransportR : transport < r :=
    ht1.trans
      (centralRenyiAsymptoticRate_lt_a0 htheta0 htheta1) |>.trans hra
  have hdelta1 : delta < 1 := by
    have hlog :
        Real.log (1 / r) < Real.log (1 / transport) := by
      exact Real.strictMonoOn_log
        (Set.mem_Ioi.mpr (one_div_pos.mpr (a0_pos.trans hra)))
        (Set.mem_Ioi.mpr (one_div_pos.mpr ht0))
        (one_div_lt_one_div_of_lt ht0 htransportR)
    have huLt :
        endpointOrbitPower r omega <
          endpointDensityPower transport omega := by
      unfold endpointOrbitPower endpointDensityPower powerU
      exact mul_lt_mul_of_pos_left hlog homega
    linarith
  refine ⟨sigma, c, hsigma0, hsigma1, hc0, ?_⟩
  filter_upwards [hcount] with N hN
  have hsub :
      badPrefix (quantitativeLinearDescentSet delta 1) N ⊆
        badPrefix (endpointDescentSet r omega delta) N := by
    intro n hn
    simp only [badPrefix, Finset.mem_filter] at hn ⊢
    exact ⟨hn.1, fun hgood =>
      hn.2 (endpointDescentSet_subset_quantitativeLinearDescentSet
        hra hr1 homega hdelta1 hgood)⟩
  have hcard :
      ((badPrefix (quantitativeLinearDescentSet delta 1) N).card : ℝ) ≤
        ((badPrefix (endpointDescentSet r omega delta) N).card : ℝ) := by
    exact_mod_cast Finset.card_le_card hsub
  exact hcard.trans hN

/-- Optimized exceptional-count theorem. Every power strictly below
`1 - delta / centralRenyiEndpointHeadlineExponent` is available. -/
theorem centralRenyiEndpointOnlyTheorem_exceptional_count_at_exponent
    {delta sigma : ℝ}
    (hdelta0 : 0 < delta)
    (hdelta : delta < centralRenyiEndpointHeadlineExponent)
    (hsigma0 : 0 < sigma)
    (hsigma : sigma < 1 - delta / centralRenyiEndpointHeadlineExponent) :
    ∃ c : ℝ,
      0 < c ∧
      ∀ᶠ N : ℕ in Filter.atTop,
        ((badPrefix (quantitativeLinearDescentSet delta 1) N).card : ℝ) ≤
          5 * N * Real.exp (-c * (Real.log N) ^ sigma) := by
  obtain ⟨theta, r, transport, omega,
      hthetaHalf, htheta1, hra, hr1, ht0, ht1,
      homega, hdu, hw, hexponent⟩ :=
    exists_centralRenyi_endpoint_exceptional_parameters
      hdelta0 hdelta hsigma0 hsigma
  have htheta0 : 0 < theta := by linarith [hthetaHalf]
  obtain ⟨eta, Dcut, heta0, heta1, hDcut0, hDcut1, hstep⟩ :=
    exists_centralRenyiEndpointStep
      htheta0 htheta1 hra hr1 ht0 ht1
  have htransport1 : transport < 1 :=
    ht1.trans
      (centralRenyiAsymptoticRate_lt_a0 htheta0 htheta1) |>.trans a0_lt_one
  have htransportR : transport < r :=
    ht1.trans
      (centralRenyiAsymptoticRate_lt_a0 htheta0 htheta1) |>.trans hra
  have hdelta1 : delta < 1 := by
    have hlog :
        Real.log (1 / r) < Real.log (1 / transport) := by
      exact Real.strictMonoOn_log
        (Set.mem_Ioi.mpr (one_div_pos.mpr (a0_pos.trans hra)))
        (Set.mem_Ioi.mpr (one_div_pos.mpr ht0))
        (one_div_lt_one_div_of_lt ht0 htransportR)
    have huLt :
        endpointOrbitPower r omega <
          endpointDensityPower transport omega := by
      unfold endpointOrbitPower endpointDensityPower powerU
      exact mul_lt_mul_of_pos_left hlog homega
    linarith
  let c := centralRenyiEndpointExceptionalCountRate transport Dcut
  have hc0 : 0 < c := by
    dsimp [c, centralRenyiEndpointExceptionalCountRate]
    apply div_pos
    apply stretchedDyadicRate_pos
    exact div_pos
      (mul_pos (Real.log_pos (by norm_num))
        (endpointDensityConstant_pos ht0 hDcut0))
      (by norm_num)
    norm_num
  have hcount :=
    centralRenyiEndpointDescentSet_badPrefix_eventually_le_stretched_log
      htheta0 htheta1 heta0 heta1 hra hr1 ht0 ht1
      htransport1 hstep hDcut0 hDcut1 le_rfl homega hdu hdelta1 hw
  rw [hexponent] at hcount
  refine ⟨c, hc0, ?_⟩
  filter_upwards [hcount] with N hN
  have hsub :
      badPrefix (quantitativeLinearDescentSet delta 1) N ⊆
        badPrefix (endpointDescentSet r omega delta) N := by
    intro n hn
    simp only [badPrefix, Finset.mem_filter] at hn ⊢
    exact ⟨hn.1, fun hgood =>
      hn.2 (endpointDescentSet_subset_quantitativeLinearDescentSet
        hra hr1 homega hdelta1 hgood)⟩
  have hcard :
      ((badPrefix (quantitativeLinearDescentSet delta 1) N).card : ℝ) ≤
        ((badPrefix (endpointDescentSet r omega delta) N).card : ℝ) := by
    exact_mod_cast Finset.card_le_card hsub
  simpa [c] using hcard.trans hN

/-- Full central-range quantitative exceptional count with the iterate-time
witness retained. -/
theorem centralRenyiEndpointOnlyTheorem_timed_exceptional_count
    {delta : ℝ}
    (hdelta0 : 0 < delta)
    (hdelta : delta < centralRenyiEndpointHeadlineExponent) :
    ∃ sigma c : ℝ,
      0 < sigma ∧ sigma ≤ 1 ∧ 0 < c ∧
      ∀ᶠ N : ℕ in Filter.atTop,
        ((badPrefix
          (quantitativeEndpointTimedDescentSet
            (6953 / 1000) delta 1) N).card : ℝ) ≤
          5 * N * Real.exp (-c * (Real.log N) ^ sigma) := by
  obtain ⟨theta, r, transport, omega,
      hthetaHalf, htheta1, hra, hr1, ht0, ht1,
      homega, hdu, hw, htime⟩ :=
    exists_centralRenyi_endpoint_only_timed_parameters hdelta0 hdelta
  have htheta0 : 0 < theta := by linarith [hthetaHalf]
  obtain ⟨sigma, c, hsigma0, hsigma1, hc0, hcount⟩ :=
    centralRenyiEndpointTimedExceptionalCount_of_transport
      htheta0 htheta1 hra hr1 ht0 ht1 homega hdelta0 hdu hw htime
  have htransport1 : transport < 1 :=
    ht1.trans
      (centralRenyiAsymptoticRate_lt_a0 htheta0 htheta1) |>.trans a0_lt_one
  have htransportR : transport < r :=
    ht1.trans
      (centralRenyiAsymptoticRate_lt_a0 htheta0 htheta1) |>.trans hra
  have hdelta1 : delta < 1 := by
    have hlog :
        Real.log (1 / r) < Real.log (1 / transport) := by
      exact Real.strictMonoOn_log
        (Set.mem_Ioi.mpr (one_div_pos.mpr (a0_pos.trans hra)))
        (Set.mem_Ioi.mpr (one_div_pos.mpr ht0))
        (one_div_lt_one_div_of_lt ht0 htransportR)
    have huLt :
        endpointOrbitPower r omega <
          endpointDensityPower transport omega := by
      unfold endpointOrbitPower endpointDensityPower powerU
      exact mul_lt_mul_of_pos_left hlog homega
    linarith
  refine ⟨sigma, c, hsigma0, hsigma1, hc0, ?_⟩
  filter_upwards [hcount] with N hN
  have hsub :
      badPrefix
          (quantitativeEndpointTimedDescentSet
            (6953 / 1000) delta 1) N ⊆
        badPrefix
          (endpointTimedDescentSet
            r omega delta (6953 / 1000)) N := by
    intro n hn
    simp only [badPrefix, Finset.mem_filter] at hn ⊢
    exact ⟨hn.1, fun hgood =>
      hn.2 (endpointTimedDescentSet_subset_quantitativeEndpointTimedDescentSet
        hra hr1 homega hdelta1 hgood)⟩
  have hcard :
      ((badPrefix
        (quantitativeEndpointTimedDescentSet
          (6953 / 1000) delta 1) N).card : ℝ) ≤
      ((badPrefix
        (endpointTimedDescentSet
          r omega delta (6953 / 1000)) N).card : ℝ) := by
    exact_mod_cast Finset.card_le_card hsub
  exact hcard.trans hN

/-! ### Certified decimal endpoint -/

private def centralLogApprox (x : ℝ) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range n, x ^ (i + 1) / (i + 1)

private def centralLogError (x : ℝ) (n : ℕ) : ℝ :=
  |x| ^ (n + 1) / (1 - |x|)

private theorem neg_log_one_sub_mem
    {x : ℝ} (hx : |x| < 1) (n : ℕ) :
    centralLogApprox x n - centralLogError x n ≤ -Real.log (1 - x) ∧
      -Real.log (1 - x) ≤ centralLogApprox x n + centralLogError x n := by
  have h := Real.abs_log_sub_add_sum_range_le hx n
  rw [abs_le] at h
  unfold centralLogApprox centralLogError
  constructor <;> linarith

private theorem certified_log_two_bounds :
    (69314718055994 / 10^14 : ℝ) < Real.log 2 ∧
      Real.log 2 < (69314718055995 / 10^14 : ℝ) := by
  have h := neg_log_one_sub_mem (x := (1 / 2 : ℝ))
    (by norm_num [abs_of_nonneg]) 48
  have heq : -Real.log (1 - (1 / 2 : ℝ)) = Real.log 2 := by
    rw [show 1 - (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num,
      Real.log_inv]
    ring
  rw [heq] at h
  constructor
  · exact lt_of_lt_of_le
      (by norm_num [centralLogApprox, centralLogError, abs_of_nonneg]) h.1
  · exact lt_of_le_of_lt h.2
      (by norm_num [centralLogApprox, centralLogError, abs_of_nonneg])

private theorem certified_log_three_halves_upper :
    Real.log (3 / 2 : ℝ) < (40546510810817 / 10^14 : ℝ) := by
  have h := neg_log_one_sub_mem (x := (1 / 3 : ℝ))
    (by norm_num [abs_of_nonneg]) 32
  have heq : -Real.log (1 - (1 / 3 : ℝ)) = Real.log (3 / 2 : ℝ) := by
    rw [show 1 - (1 / 3 : ℝ) = (3 / 2 : ℝ)⁻¹ by norm_num,
      Real.log_inv]
    ring
  rw [heq] at h
  exact lt_of_le_of_lt h.2
    (by norm_num [centralLogApprox, centralLogError, abs_of_nonneg])

private def centralRenyiDecimalUpperA : ℝ :=
  792481250361 / 10^12

private theorem a0_lt_centralRenyiDecimalUpperA :
    a0 < centralRenyiDecimalUpperA := by
  have hL := certified_log_two_bounds.1
  have hH := certified_log_three_halves_upper
  have hlog3 : Real.log 3 = Real.log (3 / 2 : ℝ) + Real.log 2 := by
    rw [← Real.log_mul (by norm_num : (3 / 2 : ℝ) ≠ 0)
      (by norm_num : (2 : ℝ) ≠ 0)]
    norm_num
  unfold a0 lg3 Real.logb centralRenyiDecimalUpperA
  rw [hlog3]
  have hlog2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  rw [div_div, div_lt_iff₀ (mul_pos hlog2 (by norm_num : (0 : ℝ) < 2))]
  nlinarith

private theorem neg_log_centralRenyiDecimalUpperA_lower :
    (23258643236104 / 10^14 : ℝ) <
      -Real.log centralRenyiDecimalUpperA := by
  let x : ℝ := 1 - centralRenyiDecimalUpperA
  have hx : |x| < 1 := by
    dsimp [x, centralRenyiDecimalUpperA]
    norm_num [abs_of_nonneg]
  have h := (neg_log_one_sub_mem hx 22).1
  have heq : 1 - x = centralRenyiDecimalUpperA := by
    dsimp [x]
    ring
  rw [heq] at h
  exact lt_of_lt_of_le
    (by norm_num [centralLogApprox, centralLogError, x,
      centralRenyiDecimalUpperA, abs_of_nonneg]) h

private theorem certified_decimal_lt_ratio_upperA :
    (251245530155 / 10^12 : ℝ) <
      Real.log (1 / centralRenyiDecimalUpperA) /
        Real.log (2 / centralRenyiDecimalUpperA) := by
  have hL := certified_log_two_bounds.2
  have hH := neg_log_centralRenyiDecimalUpperA_lower
  have hA0 : 0 < centralRenyiDecimalUpperA := by
    norm_num [centralRenyiDecimalUpperA]
  have hA1 : centralRenyiDecimalUpperA < 1 := by
    norm_num [centralRenyiDecimalUpperA]
  have hlogA :
      Real.log (1 / centralRenyiDecimalUpperA) =
        -Real.log centralRenyiDecimalUpperA := by
    rw [one_div, Real.log_inv]
  have hlog2A :
      Real.log (2 / centralRenyiDecimalUpperA) =
        Real.log 2 - Real.log centralRenyiDecimalUpperA := by
    rw [Real.log_div (by norm_num : (2 : ℝ) ≠ 0) hA0.ne']
  have hden : 0 < Real.log (2 / centralRenyiDecimalUpperA) :=
    Real.log_pos (by rw [one_lt_div hA0]; linarith)
  apply (lt_div_iff₀ hden).2
  rw [hlogA, hlog2A]
  nlinarith

/-- Certified twelve-decimal lower bound for the exact central endpoint.
This is proved from finite Taylor remainders for the logarithm. -/
theorem centralRenyiEndpointDecimal_lt_headline :
    (251245530155 / 10^12 : ℝ) <
      centralRenyiEndpointHeadlineExponent := by
  rw [centralRenyiEndpointHeadlineExponent_eq]
  have ha := a0_lt_centralRenyiDecimalUpperA
  have ha0 := a0_pos
  have hA0 : 0 < centralRenyiDecimalUpperA := by
    norm_num [centralRenyiDecimalUpperA]
  have hA1 : centralRenyiDecimalUpperA < 1 := by
    norm_num [centralRenyiDecimalUpperA]
  have hlog : Real.log a0 < Real.log centralRenyiDecimalUpperA :=
    Real.log_lt_log ha0 ha
  have hH : -Real.log centralRenyiDecimalUpperA < -Real.log a0 := by
    linarith
  have hLA :
      Real.log (1 / centralRenyiDecimalUpperA) =
        -Real.log centralRenyiDecimalUpperA := by
    rw [one_div, Real.log_inv]
  have hLa : Real.log (1 / a0) = -Real.log a0 := by
    rw [one_div, Real.log_inv]
  have hDA :
      Real.log (2 / centralRenyiDecimalUpperA) =
        Real.log 2 - Real.log centralRenyiDecimalUpperA := by
    rw [Real.log_div (by norm_num : (2 : ℝ) ≠ 0) hA0.ne']
  have hDa : Real.log (2 / a0) = Real.log 2 - Real.log a0 := by
    rw [Real.log_div (by norm_num : (2 : ℝ) ≠ 0) ha0.ne']
  have hdenA0 :
      0 < Real.log 2 - Real.log centralRenyiDecimalUpperA := by
    rw [← hDA]
    exact Real.log_pos (by rw [one_lt_div hA0]; linarith)
  have hdena0 : 0 < Real.log 2 - Real.log a0 := by
    rw [← hDa]
    exact Real.log_pos (by rw [one_lt_div ha0]; linarith [a0_lt_one])
  have hratio :
      Real.log (1 / centralRenyiDecimalUpperA) /
          Real.log (2 / centralRenyiDecimalUpperA) <
        Real.log (1 / a0) / Real.log (2 / a0) := by
    rw [hLA, hLa, hDA, hDa]
    apply (div_lt_div_iff₀ hdenA0 hdena0).2
    nlinarith [mul_pos (Real.log_pos (by norm_num : (1 : ℝ) < 2))
      (sub_pos.mpr hH)]
  exact certified_decimal_lt_ratio_upperA.trans hratio

end

end OptimizedLinearPullback

end CollatzEndpointTransport
