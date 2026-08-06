/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik
-/
import CollatzEndpointTransport.Linear.OptimizedLinearPowerCost

/-!
# Optimized Linear Power Asymptotic

Asymptotic comparison for the optimized linear power schedule.

If

  u = s log(1/q),   w = s log(1/(transport*kappa^2*q^2)),

and `u + w < 1`, then the terminal prefactor cost is negligible compared
with the terminal density exponent times the shell size:

  log(C_M + 2) = o((M+4)^(1-w)).
-/

namespace CollatzEndpointTransport

namespace OptimizedLinearPullback

open scoped Real Topology

noncomputable section

open QuantitativeDensity

theorem powerW_pos
    {q transport kappa s : ℝ}
    (hq0 : 0 < q) (hq1 : q < 1)
    (htransport0 : 0 < transport) (htransport1 : transport < 1)
    (hk : KappaAdmissible kappa) (hs : 0 < s) :
    0 < powerW q transport kappa s := by
  unfold powerW
  have hr0 :=
    power_combined_base_pos hq0 htransport0 hk
  have hr1 :=
    power_combined_base_lt_one hq0 hq1
      htransport0 htransport1 hk
  exact mul_pos hs (log_one_div_pos hr0 hr1)

theorem powerLogCostEnvelope_div_eq
    (q transport kappa s : ℝ) (M : ℕ) :
    powerLogCostEnvelope q transport kappa s M /
        powerShellScale M ^
          (1 - powerW q transport kappa s) =
      (s * powerCostConstant q transport kappa) *
          (powerShellLog M /
            powerShellScale M ^
              (1 - powerW q transport kappa s)) +
        powerCostConstant q transport kappa /
          powerShellScale M ^
            (1 - powerW q transport kappa s) +
        (2 * s * powerW q transport kappa s) *
          ((powerShellLog M) ^ (2 : ℝ) /
            powerShellScale M ^
              (1 - powerW q transport kappa s)) +
        (2 * powerW q transport kappa s) *
          (powerShellLog M /
            powerShellScale M ^
              (1 - powerW q transport kappa s)) +
        (s * (linearStartupB q / (a0 * q))) *
          (powerShellLog M * powerShellScale M ^ (powerU q s) /
            powerShellScale M ^
              (1 - powerW q transport kappa s)) +
        (linearStartupB q / (a0 * q)) *
          (powerShellScale M ^ (powerU q s) /
            powerShellScale M ^
              (1 - powerW q transport kappa s)) +
        |Real.log
            (Terras.quadraticWindowFixedGlobalConstant + 2)| /
          powerShellScale M ^
            (1 - powerW q transport kappa s) := by
  unfold powerLogCostEnvelope
  simp only [div_eq_mul_inv]
  rw [Real.rpow_two]
  ring_nf

/-- The terminal prefactor cost is negligible relative to the power
`X^(1-w)` left by the density exponent. -/
theorem powerLogCostEnvelope_ratio_tendsto_zero
    {q transport kappa s : ℝ}
    (hq0 : 0 < q) (hq1 : q < 1)
    (htransport0 : 0 < transport) (htransport1 : transport < 1)
    (hk : KappaAdmissible kappa) (hs : 0 < s)
    (huw : powerU q s + powerW q transport kappa s < 1) :
    Filter.Tendsto
      (fun M =>
        powerLogCostEnvelope q transport kappa s M /
          powerShellScale M ^
            (1 - powerW q transport kappa s))
      Filter.atTop (nhds 0) := by
  have hu := powerU_pos hq0 hq1 hs
  have hw :=
    powerW_pos hq0 hq1 htransport0 htransport1 hk hs
  have hgap : 0 < 1 - powerW q transport kappa s := by
    linarith
  have hgapU :
      0 <
        (1 - powerW q transport kappa s) - powerU q s := by
    linarith
  have hlogGap :
      Filter.Tendsto
        (fun M =>
          powerShellLog M /
            powerShellScale M ^
              (1 - powerW q transport kappa s))
        Filter.atTop (nhds 0) := by
    simpa [powerShellLog, Function.comp_apply] using
      ((isLittleO_log_rpow_atTop hgap).tendsto_div_nhds_zero).comp
        powerShellScale_tendsto_atTop
  have hlogSqGap :
      Filter.Tendsto
        (fun M =>
          (powerShellLog M) ^ (2 : ℝ) /
            powerShellScale M ^
              (1 - powerW q transport kappa s))
        Filter.atTop (nhds 0) := by
    simpa [powerShellLog, Function.comp_apply] using
      ((isLittleO_log_rpow_rpow_atTop
        (2 : ℝ) hgap).tendsto_div_nhds_zero).comp
          powerShellScale_tendsto_atTop
  have hpowGap :
      Filter.Tendsto
        (fun M =>
          powerShellScale M ^
            (-(1 - powerW q transport kappa s)))
        Filter.atTop (nhds 0) :=
    (tendsto_rpow_neg_atTop hgap).comp
      powerShellScale_tendsto_atTop
  have hpowGapRaw :
      Filter.Tendsto
        (fun M =>
          1 /
            powerShellScale M ^
              (1 - powerW q transport kappa s))
        Filter.atTop (nhds 0) := by
    convert hpowGap using 1
    funext M
    rw [Real.rpow_neg (powerShellScale_pos M).le]
    simp [one_div]
  have hlogGapU :
      Filter.Tendsto
        (fun M =>
          powerShellLog M /
            powerShellScale M ^
              ((1 - powerW q transport kappa s) - powerU q s))
        Filter.atTop (nhds 0) := by
    simpa [powerShellLog, Function.comp_apply] using
      ((isLittleO_log_rpow_atTop hgapU).tendsto_div_nhds_zero).comp
        powerShellScale_tendsto_atTop
  have hpowGapU :
      Filter.Tendsto
        (fun M =>
          powerShellScale M ^
            (-((1 - powerW q transport kappa s) - powerU q s)))
        Filter.atTop (nhds 0) :=
    (tendsto_rpow_neg_atTop hgapU).comp
      powerShellScale_tendsto_atTop
  have hshift :
      ∀ M : ℕ,
        powerShellScale M ^ (powerU q s) /
            powerShellScale M ^
              (1 - powerW q transport kappa s) =
          powerShellScale M ^
            (-((1 - powerW q transport kappa s) - powerU q s)) := by
    intro M
    have hX := powerShellScale_pos M
    calc
      powerShellScale M ^ (powerU q s) /
            powerShellScale M ^
              (1 - powerW q transport kappa s)
          = powerShellScale M ^
              (powerU q s -
                (1 - powerW q transport kappa s)) :=
            (Real.rpow_sub hX _ _).symm
      _ = powerShellScale M ^
            (-((1 - powerW q transport kappa s) - powerU q s)) := by
          congr 1
          ring
  have hpowGapURaw :
      Filter.Tendsto
        (fun M =>
          powerShellScale M ^ (powerU q s) /
            powerShellScale M ^
              (1 - powerW q transport kappa s))
        Filter.atTop (nhds 0) := by
    convert hpowGapU using 1
    funext M
    exact hshift M
  have hlogGapURaw :
      Filter.Tendsto
        (fun M =>
          powerShellLog M * powerShellScale M ^ (powerU q s) /
            powerShellScale M ^
              (1 - powerW q transport kappa s))
        Filter.atTop (nhds 0) := by
    convert hlogGapU using 1
    funext M
    have hX := powerShellScale_pos M
    calc
      powerShellLog M * powerShellScale M ^ (powerU q s) /
            powerShellScale M ^
              (1 - powerW q transport kappa s)
          = powerShellLog M *
              (powerShellScale M ^ (powerU q s) /
                powerShellScale M ^
                  (1 - powerW q transport kappa s)) := by ring
      _ = powerShellLog M *
            powerShellScale M ^
              (-((1 - powerW q transport kappa s) - powerU q s)) := by
          rw [hshift M]
      _ = powerShellLog M /
            powerShellScale M ^
              ((1 - powerW q transport kappa s) - powerU q s) := by
          rw [Real.rpow_neg hX.le]
          ring
  have h1 :=
    hlogGap.const_mul
      (s * powerCostConstant q transport kappa)
  have h2 :=
    hpowGapRaw.const_mul
      (powerCostConstant q transport kappa)
  have h3 :=
    hlogSqGap.const_mul
      (2 * s * powerW q transport kappa s)
  have h4 :=
    hlogGap.const_mul
      (2 * powerW q transport kappa s)
  have h5 :=
    hlogGapURaw.const_mul
      (s * (linearStartupB q / (a0 * q)))
  have h6 :=
    hpowGapURaw.const_mul
      (linearStartupB q / (a0 * q))
  have h7 :=
    hpowGapRaw.const_mul
      |Real.log
        (Terras.quadraticWindowFixedGlobalConstant + 2)|
  have hsum :=
    (((((h1.add h2).add h3).add h4).add h5).add h6).add h7
  have hsum0 :
      Filter.Tendsto
        (fun M =>
          (s * powerCostConstant q transport kappa) *
              (powerShellLog M /
                powerShellScale M ^
                  (1 - powerW q transport kappa s)) +
            powerCostConstant q transport kappa *
              (1 /
                powerShellScale M ^
                  (1 - powerW q transport kappa s)) +
            (2 * s * powerW q transport kappa s) *
              ((powerShellLog M) ^ (2 : ℝ) /
                powerShellScale M ^
                  (1 - powerW q transport kappa s)) +
            (2 * powerW q transport kappa s) *
              (powerShellLog M /
                powerShellScale M ^
                  (1 - powerW q transport kappa s)) +
            (s * (linearStartupB q / (a0 * q))) *
              (powerShellLog M *
                  powerShellScale M ^ (powerU q s) /
                powerShellScale M ^
                  (1 - powerW q transport kappa s)) +
            (linearStartupB q / (a0 * q)) *
              (powerShellScale M ^ (powerU q s) /
                powerShellScale M ^
                  (1 - powerW q transport kappa s)) +
            |Real.log
                (Terras.quadraticWindowFixedGlobalConstant + 2)| *
              (1 /
                powerShellScale M ^
                  (1 - powerW q transport kappa s)))
        Filter.atTop (nhds 0) := by
    simpa only [mul_zero, add_zero] using hsum
  convert hsum0 using 1
  funext M
  simpa [div_eq_mul_inv] using
    powerLogCostEnvelope_div_eq q transport kappa s M

end

end OptimizedLinearPullback

end CollatzEndpointTransport
