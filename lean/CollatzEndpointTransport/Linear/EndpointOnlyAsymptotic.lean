/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik
-/
import CollatzEndpointTransport.Linear.EndpointOnlyCost
import CollatzEndpointTransport.Linear.OptimizedLinearPowerShellVanishing

/-!
# Endpoint Only Asymptotic

Shell vanishing for the endpoint-only logarithmic schedule.

The terminal prefactor has logarithm `O((log X)^2)`, while the density
exponent times the shell size is bounded below by a fixed multiple of
`X^(1-w)`.  Hence every `w < 1` gives a stretched-exponentially vanishing
shell exceptional proportion.
-/

namespace CollatzEndpointTransport

namespace OptimizedLinearPullback

open scoped Real Topology

noncomputable section

open QuantitativeDensity

theorem endpointLogCostEnvelope_eq
    (transport eta D0 omega : ℝ) (M : ℕ) :
    endpointLogCostEnvelope transport eta D0 omega M =
      (2 * omega * endpointDensityPower transport omega) *
          (powerShellLog M) ^ (2 : ℝ) +
        (omega * endpointCostConstant transport eta D0 +
            2 * endpointDensityPower transport omega) *
          powerShellLog M +
        (endpointCostConstant transport eta D0 + |Real.log 3|) := by
  unfold endpointLogCostEnvelope
  rw [Real.rpow_two]
  ring

/-- The endpoint-only prefactor cost is negligible against the retained
density power. -/
theorem endpointLogCostEnvelope_ratio_tendsto_zero
    {transport eta D0 omega : ℝ}
    (htransport0 : 0 < transport)
    (htransport1 : transport < 1)
    (homega : 0 < omega)
    (hw : endpointDensityPower transport omega < 1) :
    Filter.Tendsto
      (fun M =>
        endpointLogCostEnvelope transport eta D0 omega M /
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
      (2 * omega * endpointDensityPower transport omega)
  have h2 :=
    hlogGap.const_mul
      (omega * endpointCostConstant transport eta D0 +
        2 * endpointDensityPower transport omega)
  have h3 :=
    hpowGap.const_mul
      (endpointCostConstant transport eta D0 + |Real.log 3|)
  have hsum := (h1.add h2).add h3
  have hsum0 :
      Filter.Tendsto
        (fun M =>
          (2 * omega * endpointDensityPower transport omega) *
              ((powerShellLog M) ^ (2 : ℝ) /
                powerShellScale M ^
                  (1 - endpointDensityPower transport omega)) +
            (omega * endpointCostConstant transport eta D0 +
                2 * endpointDensityPower transport omega) *
              (powerShellLog M /
                powerShellScale M ^
                  (1 - endpointDensityPower transport omega)) +
            (endpointCostConstant transport eta D0 + |Real.log 3|) *
              (1 /
                powerShellScale M ^
                  (1 - endpointDensityPower transport omega)))
        Filter.atTop (nhds 0) := by
    simpa only [mul_zero, add_zero] using hsum
  convert hsum0 using 1
  funext M
  rw [endpointLogCostEnvelope_eq]
  ring

def endpointShellDecayModel
    (transport D0 omega : ℝ) (M : ℕ) : ℝ :=
  2 * Real.exp
    (-(Real.log 2 * endpointDensityConstant transport D0 / 4) *
      powerShellScale M ^
        (1 - endpointDensityPower transport omega))

theorem endpointShellDecayModel_tendsto_zero
    {transport D0 omega : ℝ}
    (htransport0 : 0 < transport)
    (hD00 : 0 < D0)
    (hw : endpointDensityPower transport omega < 1) :
    Filter.Tendsto
      (endpointShellDecayModel transport D0 omega)
      Filter.atTop (nhds 0) := by
  have hgap :
      0 < 1 - endpointDensityPower transport omega := by
    linarith
  have hcoef :
      0 < Real.log 2 * endpointDensityConstant transport D0 / 4 := by
    exact div_pos
      (mul_pos (Real.log_pos (by norm_num))
        (endpointDensityConstant_pos htransport0 hD00))
      (by norm_num)
  have hpow :
      Filter.Tendsto
        (fun M =>
          powerShellScale M ^
            (1 - endpointDensityPower transport omega))
        Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop hgap).comp powerShellScale_tendsto_atTop
  have hscaled :
      Filter.Tendsto
        (fun M =>
          (Real.log 2 * endpointDensityConstant transport D0 / 4) *
            powerShellScale M ^
              (1 - endpointDensityPower transport omega))
        Filter.atTop Filter.atTop :=
    hpow.const_mul_atTop hcoef
  have hexp :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp hscaled
  convert hexp.const_mul 2 using 1
  · funext M
    unfold endpointShellDecayModel
    congr 2
    ring
  · norm_num

theorem endpointScheduledD_mul_shell_lower
    {transport D0 omega : ℝ}
    (htransport0 : 0 < transport)
    (htransport1 : transport < 1)
    (hD00 : 0 < D0)
    (homega : 0 < omega)
    {M : ℕ} (hM4 : 4 ≤ M) :
    endpointDensityConstant transport D0 / 2 *
        powerShellScale M ^
          (1 - endpointDensityPower transport omega) ≤
      endpointScheduledD transport D0 omega M * (M : ℝ) := by
  have hD :=
    endpointScheduledD_lower
      htransport0 htransport1 hD00 homega M
  have hd0 :=
    endpointDensityConstant_pos htransport0 hD00
  have hX0 := powerShellScale_pos M
  have hM0 : 0 ≤ (M : ℝ) := Nat.cast_nonneg M
  have hMhalf :
      powerShellScale M / 2 ≤ (M : ℝ) := by
    unfold powerShellScale
    have hM4R : (4 : ℝ) ≤ M := by exact_mod_cast hM4
    linarith
  have hbase0 :
      0 ≤
        endpointDensityConstant transport D0 *
          powerShellScale M ^
            (-endpointDensityPower transport omega) := by
    positivity
  have hright :
      endpointDensityConstant transport D0 *
            powerShellScale M ^
              (-endpointDensityPower transport omega) *
            (M : ℝ) ≤
        endpointScheduledD transport D0 omega M * (M : ℝ) :=
    mul_le_mul_of_nonneg_right hD hM0
  have hleft :
      endpointDensityConstant transport D0 *
            powerShellScale M ^
              (-endpointDensityPower transport omega) *
            (powerShellScale M / 2) ≤
        endpointDensityConstant transport D0 *
            powerShellScale M ^
              (-endpointDensityPower transport omega) *
            (M : ℝ) :=
    mul_le_mul_of_nonneg_left hMhalf hbase0
  calc
    endpointDensityConstant transport D0 / 2 *
          powerShellScale M ^
            (1 - endpointDensityPower transport omega)
        =
      endpointDensityConstant transport D0 *
          powerShellScale M ^
            (-endpointDensityPower transport omega) *
          (powerShellScale M / 2) := by
      rw [show
          powerShellScale M ^
              (1 - endpointDensityPower transport omega) =
            powerShellScale M ^
                (-endpointDensityPower transport omega) *
              powerShellScale M by
        calc
          powerShellScale M ^
                (1 - endpointDensityPower transport omega)
              =
            powerShellScale M ^
                (-endpointDensityPower transport omega + 1) := by
              congr 1
              ring
          _ =
            powerShellScale M ^
                (-endpointDensityPower transport omega) *
              powerShellScale M ^ (1 : ℝ) :=
            Real.rpow_add hX0 _ _
          _ = _ := by rw [Real.rpow_one]]
      ring
    _ ≤
      endpointDensityConstant transport D0 *
          powerShellScale M ^
            (-endpointDensityPower transport omega) *
          (M : ℝ) := hleft
    _ ≤ endpointScheduledD transport D0 omega M * (M : ℝ) := hright

/-- The scheduled endpoint chains are eventually dominated by the explicit
stretched-exponential shell model. -/
theorem endpointChainExceptionalRatio_eventually_le_model
    {transport eta t D0 Dcut omega : ℝ}
    (htransport0 : 0 < transport)
    (htransport1 : transport < 1)
    (heta0 : 0 < eta) (heta1 : eta < 1)
    (ht0 : 0 < t) (ht1 : t ≤ 1)
    (hD00 : 0 < D0) (hD01 : D0 ≤ 1)
    (hDcut0 : 0 < Dcut) (hD0cut : D0 ≤ Dcut)
    (hcut :
      ∀ D : ℝ, 0 < D → D ≤ Dcut →
        transport * D ≤ shellRate eta D / Real.log 2)
    (hwindow0 :
      transport * D0 ≤ Terras.quadraticWindowDensityRate t)
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
    endpointLogCostEnvelope_ratio_tendsto_zero
      htransport0 htransport1 homega hw
      (eta := eta) (D0 := D0)
  have hsmall :
      ∀ᶠ M : ℕ in Filter.atTop,
        endpointLogCostEnvelope transport eta D0 omega M /
            powerShellScale M ^
              (1 - endpointDensityPower transport omega) < c := by
    have hevent :=
      (Metric.tendsto_atTop.1 hcost) c hc0
    filter_upwards [Filter.eventually_atTop.2 hevent] with M hM
    rw [Real.dist_eq] at hM
    exact lt_of_le_of_lt (le_abs_self _) (by simpa [sub_zero] using hM)
  have hM4 :
      ∀ᶠ M : ℕ in Filter.atTop, 4 ≤ M :=
    Filter.eventually_atTop.2 ⟨4, fun _ h => h⟩
  filter_upwards [hsmall, hM4] with M hsmallM hM4M
  have hcert :=
    endpointScheduledChain_dense (omega := omega)
      htransport0 htransport1.le
      heta0 heta1 ht0 ht1 hD00 hD01 hDcut0 hD0cut
      hcut hwindow0 M
  have hlogC :=
    endpointScheduledLogC_le htransport0 htransport1
      heta0 heta1 ht0 ht1 hD00 hD01 homega M
  have hXgap0 :
      0 <
        powerShellScale M ^
          (1 - endpointDensityPower transport omega) :=
    Real.rpow_pos_of_pos (powerShellScale_pos M) _
  have hcostRaw :
      endpointLogCostEnvelope transport eta D0 omega M <
        c * powerShellScale M ^
          (1 - endpointDensityPower transport omega) :=
    (div_lt_iff₀ hXgap0).mp hsmallM
  have hC0 :
      0 < endpointScheduledC transport eta t D0 omega M := by
    exact endpointC_pos (D0 := D0)
      htransport0 heta0 heta1 ht0 ht1 _
  have hCtwo0 :
      0 < endpointScheduledC transport eta t D0 omega M + 2 := by
    linarith
  have hCexp :
      endpointScheduledC transport eta t D0 omega M ≤
        Real.exp
          (c * powerShellScale M ^
            (1 - endpointDensityPower transport omega)) := by
    have hlogBound :
        Real.log
            (endpointScheduledC transport eta t D0 omega M + 2) ≤
          c * powerShellScale M ^
            (1 - endpointDensityPower transport omega) :=
      hlogC.trans hcostRaw.le
    have hexp :
        endpointScheduledC transport eta t D0 omega M + 2 ≤
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
      2 * c *
          powerShellScale M ^
            (1 - endpointDensityPower transport omega) ≤
        Real.log 2 *
          endpointScheduledD transport D0 omega M * (M : ℝ) := by
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
          (-(2 * c *
            powerShellScale M ^
              (1 - endpointDensityPower transport omega))) :=
    Real.exp_le_exp.2 (by linarith)
  calc
    shellExceptionalRatio
        (endpointChain t (endpointStageCount omega M)) M
        ≤
      2 * endpointScheduledC transport eta t D0 omega M *
        Real.exp
          (-(Real.log 2 *
            endpointScheduledD transport D0 omega M * M)) :=
      shellExceptionalRatio_le_of_isCDDense hcert M
    _ ≤
      2 *
        Real.exp
          (c * powerShellScale M ^
            (1 - endpointDensityPower transport omega)) *
        Real.exp
          (-(2 * c *
            powerShellScale M ^
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

/-- The scheduled endpoint chains have vanishing exceptional shell
proportion. -/
theorem endpointChainExceptionalRatio_tendsto_zero
    {transport eta t D0 Dcut omega : ℝ}
    (htransport0 : 0 < transport)
    (htransport1 : transport < 1)
    (heta0 : 0 < eta) (heta1 : eta < 1)
    (ht0 : 0 < t) (ht1 : t ≤ 1)
    (hD00 : 0 < D0) (hD01 : D0 ≤ 1)
    (hDcut0 : 0 < Dcut) (hD0cut : D0 ≤ Dcut)
    (hcut :
      ∀ D : ℝ, 0 < D → D ≤ Dcut →
        transport * D ≤ shellRate eta D / Real.log 2)
    (hwindow0 :
      transport * D0 ≤ Terras.quadraticWindowDensityRate t)
    (homega : 0 < omega)
    (hw : endpointDensityPower transport omega < 1) :
    Filter.Tendsto
      (fun M =>
        shellExceptionalRatio
          (endpointChain t (endpointStageCount omega M)) M)
      Filter.atTop (nhds 0) := by
  have hbound :=
    endpointChainExceptionalRatio_eventually_le_model
      htransport0 htransport1 heta0 heta1 ht0 ht1
      hD00 hD01 hDcut0 hD0cut hcut hwindow0 homega hw
  have hmodel :=
    endpointShellDecayModel_tendsto_zero
      htransport0 hD00 hw
  exact squeeze_zero'
    (Filter.Eventually.of_forall fun M =>
      shellExceptionalRatio_nonneg
        (endpointChain t (endpointStageCount omega M)) M)
    hbound hmodel

end

end OptimizedLinearPullback

end CollatzEndpointTransport
