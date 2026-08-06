/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik
-/
import CollatzEndpointTransport.Linear.OptimizedLinearPowerAsymptotic

/-!
# Optimized Linear Power Shell Vanishing

Vanishing shell mass for the optimized linear power schedule.

For

  w = s log (1 / (transport * kappa^2 * q^2)),

the terminal density exponent is bounded below by a fixed multiple of
`(M+4)^(-w)`.  If `u+w<1`, the terminal prefactor has logarithm
`o((M+4)^(1-w))`.  The resulting exceptional shell proportion therefore
tends to zero.
-/

namespace CollatzEndpointTransport

namespace OptimizedLinearPullback

open scoped Real Topology

noncomputable section

open QuantitativeDensity

theorem powerEnvelopeC_pos
    {q transport kappa s : ℝ}
    (htransport0 : 0 < transport)
    (htransportLimit : transport < asymptoticRateLimit)
    (M : ℕ) :
    0 < powerEnvelopeC q transport kappa s M := by
  exact linearC_pos htransport0
    (asymptoticEta_pos htransport0)
    (asymptoticEta_lt_one htransportLimit)
    (powerR s M)

theorem powerEnvelopeD_pos
    {q transport kappa s : ℝ}
    (htransport0 : 0 < transport)
    (hk : KappaAdmissible kappa)
    (hq0 : 0 < q) (hqa : a0 < q)
    (M : ℕ) :
    0 < powerEnvelopeD q transport kappa s M := by
  exact linearD_pos_all
    (R := powerR s M) htransport0 hk
    (powerTerminalTolerance_pos hk hq0 hqa _) (powerR s M)

theorem powerEnvelopeD_le_one_of_D0_le
    {q transport kappa s Dcut : ℝ}
    (htransport0 : 0 < transport)
    (htransport1 : transport ≤ 1)
    (hk : KappaAdmissible kappa)
    (hq0 : 0 < q) (hqa : a0 < q)
    (hDcut1 : Dcut ≤ 1)
    {M : ℕ}
    (hDzero :
      powerEnvelopeD0 q transport kappa s M ≤ Dcut) :
    powerEnvelopeD q transport kappa s M ≤ 1 := by
  have hterminal :
      powerEnvelopeD q transport kappa s M ≤
        powerEnvelopeD0 q transport kappa s M := by
    exact linearD_terminal_le
      htransport0 htransport1 hk
      (powerTerminalTolerance_pos hk hq0 hqa _)
      (show 0 ≤ powerR s M by omega)
  exact hterminal.trans (hDzero.trans hDcut1)

/-- The fixed stretched-exponential model used to dominate the shell
exceptional proportion. -/
def powerShellDecayModel
    (q transport kappa s : ℝ) (M : ℕ) : ℝ :=
  2 * Real.exp
    (-(Real.log 2 * powerDensityConstant q transport kappa / 4) *
      powerShellScale M ^ (1 - powerW q transport kappa s))

theorem powerShellDecayModel_tendsto_zero
    {q transport kappa s : ℝ}
    (hq0 : 0 < q) (hqa : a0 < q) (hq1 : q < 1)
    (htransport0 : 0 < transport)
    (hk : KappaAdmissible kappa)
    (hs : 0 < s)
    (huw : powerU q s + powerW q transport kappa s < 1) :
    Filter.Tendsto
      (powerShellDecayModel q transport kappa s)
      Filter.atTop (nhds 0) := by
  have hgap : 0 < 1 - powerW q transport kappa s := by
    have hu := powerU_pos hq0 hq1 hs
    linarith
  have hd0 :
      0 < powerDensityConstant q transport kappa :=
    powerDensityConstant_pos hk hq0 hqa htransport0
  have hcoef :
      0 <
        Real.log 2 * powerDensityConstant q transport kappa / 4 :=
    div_pos (mul_pos (Real.log_pos (by norm_num)) hd0) (by norm_num)
  have hpow :
      Filter.Tendsto
        (fun M =>
          powerShellScale M ^
            (1 - powerW q transport kappa s))
        Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop hgap).comp powerShellScale_tendsto_atTop
  have hscaled :
      Filter.Tendsto
        (fun M =>
          (Real.log 2 * powerDensityConstant q transport kappa / 4) *
            powerShellScale M ^
              (1 - powerW q transport kappa s))
        Filter.atTop Filter.atTop :=
    hpow.const_mul_atTop hcoef
  have hexp :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp hscaled
  convert hexp.const_mul 2 using 1
  · funext M
    unfold powerShellDecayModel
    congr 2
    ring
  · norm_num

theorem powerEnvelopeD_mul_shell_lower
    {q transport kappa s : ℝ}
    (hq0 : 0 < q) (hqa : a0 < q) (hq1 : q < 1)
    (htransport0 : 0 < transport) (htransport1 : transport < 1)
    (hk : KappaAdmissible kappa)
    (hs : 0 < s)
    {M : ℕ} (hM4 : 4 ≤ M) :
    powerDensityConstant q transport kappa / 2 *
        powerShellScale M ^
          (1 - powerW q transport kappa s) ≤
      powerEnvelopeD q transport kappa s M * (M : ℝ) := by
  have hD :=
    linearD_power_lower hq0 hqa hq1
      htransport0 htransport1 hk hs M
  have hd0 :
      0 < powerDensityConstant q transport kappa :=
    powerDensityConstant_pos hk hq0 hqa htransport0
  have hX0 := powerShellScale_pos M
  have hM0 : 0 ≤ (M : ℝ) := Nat.cast_nonneg M
  have hMhalf :
      powerShellScale M / 2 ≤ (M : ℝ) := by
    unfold powerShellScale
    have hM4R : (4 : ℝ) ≤ M := by exact_mod_cast hM4
    linarith
  have hbase0 :
      0 ≤
        powerDensityConstant q transport kappa *
          powerShellScale M ^
            (-powerW q transport kappa s) := by
    positivity
  have hright :
      powerDensityConstant q transport kappa *
            powerShellScale M ^
              (-powerW q transport kappa s) *
            (M : ℝ) ≤
        powerEnvelopeD q transport kappa s M * (M : ℝ) :=
    mul_le_mul_of_nonneg_right hD hM0
  have hleft :
      powerDensityConstant q transport kappa *
            powerShellScale M ^
              (-powerW q transport kappa s) *
            (powerShellScale M / 2) ≤
        powerDensityConstant q transport kappa *
            powerShellScale M ^
              (-powerW q transport kappa s) *
            (M : ℝ) :=
    mul_le_mul_of_nonneg_left hMhalf hbase0
  calc
    powerDensityConstant q transport kappa / 2 *
          powerShellScale M ^
            (1 - powerW q transport kappa s)
        =
      powerDensityConstant q transport kappa *
          powerShellScale M ^
            (-powerW q transport kappa s) *
          (powerShellScale M / 2) := by
      rw [show
          powerShellScale M ^
              (1 - powerW q transport kappa s) =
            powerShellScale M ^
                (-powerW q transport kappa s) *
              powerShellScale M by
        calc
          powerShellScale M ^
                (1 - powerW q transport kappa s)
              =
            powerShellScale M ^
                (-powerW q transport kappa s + 1) := by
              congr 1
              ring
          _ = powerShellScale M ^
                  (-powerW q transport kappa s) *
                powerShellScale M ^ (1 : ℝ) :=
              Real.rpow_add hX0 _ _
          _ = _ := by rw [Real.rpow_one]]
      ring
    _ ≤
      powerDensityConstant q transport kappa *
          powerShellScale M ^
            (-powerW q transport kappa s) *
          (M : ℝ) := hleft
    _ ≤ powerEnvelopeD q transport kappa s M * (M : ℝ) := hright

/-- The concrete terminal-envelope exceptional ratio is eventually bounded
by the explicit stretched-exponential shell model. -/
theorem powerEnvelopeExceptionalRatio_eventually_le_model
    {q transport kappa s : ℝ}
    (hq0 : 0 < q) (hqa : a0 < q) (hq1 : q < 1)
    (htransport0 : 0 < transport)
    (htransportLimit : transport < asymptoticRateLimit)
    (hk : KappaAdmissible kappa)
    (hs : 0 < s)
    (huw : powerU q s + powerW q transport kappa s < 1) :
    ∀ᶠ M : ℕ in Filter.atTop,
      shellExceptionalRatio (powerEnvelope q kappa s M) M ≤
        powerShellDecayModel q transport kappa s M := by
  have htransport1 : transport < 1 :=
    htransportLimit.trans asymptoticRateLimit_lt_one
  obtain ⟨Dcut, hDcut0, hDcut1, hcut⟩ :=
    exists_linear_cutoff htransport0 htransportLimit
  have hDzero :
      ∀ᶠ M : ℕ in Filter.atTop,
        powerEnvelopeD0 q transport kappa s M ≤ Dcut :=
    powerEnvelopeD0_eventually_le htransport0 hk
      hq0 hqa hq1 hs hDcut0
  have hM4 :
      ∀ᶠ M : ℕ in Filter.atTop, 4 ≤ M :=
    Filter.eventually_atTop.2 ⟨4, fun _ h => h⟩
  let d := powerDensityConstant q transport kappa
  let c := Real.log 2 * d / 4
  have hd0 : 0 < d := by
    dsimp [d]
    exact powerDensityConstant_pos hk hq0 hqa htransport0
  have hc0 : 0 < c := by
    dsimp [c]
    positivity
  have hcost :=
    powerLogCostEnvelope_ratio_tendsto_zero
      hq0 hq1 htransport0 htransport1 hk hs huw
  have hsmall :
      ∀ᶠ M : ℕ in Filter.atTop,
        powerLogCostEnvelope q transport kappa s M /
            powerShellScale M ^
              (1 - powerW q transport kappa s) < c := by
    have hevent :=
      (Metric.tendsto_atTop.1 hcost) c hc0
    filter_upwards [Filter.eventually_atTop.2 hevent] with M hM
    rw [Real.dist_eq] at hM
    have habs :
        |powerLogCostEnvelope q transport kappa s M /
            powerShellScale M ^
              (1 - powerW q transport kappa s)| < c := by
      simpa [sub_zero] using hM
    exact lt_of_le_of_lt (le_abs_self _) habs
  have hbound :
      ∀ᶠ M : ℕ in Filter.atTop,
        shellExceptionalRatio (powerEnvelope q kappa s M) M ≤
          powerShellDecayModel q transport kappa s M := by
    filter_upwards [hDzero, hM4, hsmall] with M hD0M hM4M hsmallM
    have hcert :=
      powerEnvelope_dense htransport0 htransportLimit hk
        hq0 hqa hq1 hDcut0 hDcut1 hcut hD0M
    have hDterminal1 :
        powerEnvelopeD q transport kappa s M ≤ 1 :=
      powerEnvelopeD_le_one_of_D0_le htransport0
        htransport1.le hk hq0 hqa hDcut1 hD0M
    have hlogC :=
      powerEnvelopeLogC_le htransport0 htransportLimit
        hk hq0 hqa hq1 hs hDterminal1
    have hXgap0 :
        0 <
          powerShellScale M ^
            (1 - powerW q transport kappa s) :=
      Real.rpow_pos_of_pos (powerShellScale_pos M) _
    have hcostRaw :
        powerLogCostEnvelope q transport kappa s M <
          c * powerShellScale M ^
            (1 - powerW q transport kappa s) := by
      exact (div_lt_iff₀ hXgap0).mp hsmallM
    have hC0 :=
      powerEnvelopeC_pos htransport0 htransportLimit
        (q := q) (kappa := kappa) (s := s) M
    have hCtwo0 :
        0 < powerEnvelopeC q transport kappa s M + 2 := by
      linarith
    have hCexp :
        powerEnvelopeC q transport kappa s M ≤
          Real.exp
            (c * powerShellScale M ^
              (1 - powerW q transport kappa s)) := by
      have hlogBound :
          Real.log (powerEnvelopeC q transport kappa s M + 2) ≤
            c * powerShellScale M ^
              (1 - powerW q transport kappa s) :=
        hlogC.trans hcostRaw.le
      have hexp :
          powerEnvelopeC q transport kappa s M + 2 ≤
            Real.exp
              (c * powerShellScale M ^
                (1 - powerW q transport kappa s)) := by
        rw [← Real.exp_log hCtwo0]
        exact Real.exp_le_exp.2 hlogBound
      linarith
    have hDM :=
      powerEnvelopeD_mul_shell_lower hq0 hqa hq1
        htransport0 htransport1 hk hs hM4M
    have hdecay :
        2 * c *
            powerShellScale M ^
              (1 - powerW q transport kappa s) ≤
          Real.log 2 *
            powerEnvelopeD q transport kappa s M * (M : ℝ) := by
      have hmul :=
        mul_le_mul_of_nonneg_left hDM
          (Real.log_pos (show (1 : ℝ) < 2 by norm_num)).le
      dsimp [c, d]
      nlinarith
    have hexpDecay :
        Real.exp
            (-(Real.log 2 *
              powerEnvelopeD q transport kappa s M * (M : ℝ))) ≤
          Real.exp
            (-(2 * c *
              powerShellScale M ^
                (1 - powerW q transport kappa s))) := by
      exact Real.exp_le_exp.2 (by linarith)
    calc
      shellExceptionalRatio (powerEnvelope q kappa s M) M
          ≤ 2 * powerEnvelopeC q transport kappa s M *
              Real.exp
                (-(Real.log 2 *
                  powerEnvelopeD q transport kappa s M * M)) :=
        shellExceptionalRatio_le_of_isCDDense hcert M
      _ ≤ 2 *
            Real.exp
              (c * powerShellScale M ^
                (1 - powerW q transport kappa s)) *
            Real.exp
              (-(2 * c *
                powerShellScale M ^
                  (1 - powerW q transport kappa s))) := by
        exact mul_le_mul
          (mul_le_mul_of_nonneg_left hCexp (by norm_num))
          hexpDecay
          (Real.exp_nonneg _)
          (mul_nonneg (by norm_num) (Real.exp_nonneg _))
      _ = powerShellDecayModel q transport kappa s M := by
        unfold powerShellDecayModel
        dsimp [c, d]
        calc
          2 *
                Real.exp
                  (Real.log 2 *
                    powerDensityConstant q transport kappa / 4 *
                    powerShellScale M ^
                      (1 - powerW q transport kappa s)) *
                Real.exp
                  (-(2 *
                    (Real.log 2 *
                      powerDensityConstant q transport kappa / 4) *
                    powerShellScale M ^
                      (1 - powerW q transport kappa s)))
              =
            2 * (Real.exp
                  (Real.log 2 *
                    powerDensityConstant q transport kappa / 4 *
                    powerShellScale M ^
                      (1 - powerW q transport kappa s)) *
                Real.exp
                  (-(2 *
                    (Real.log 2 *
                      powerDensityConstant q transport kappa / 4) *
                    powerShellScale M ^
                      (1 - powerW q transport kappa s)))) := by ring
          _ = 2 * Real.exp
                (Real.log 2 *
                    powerDensityConstant q transport kappa / 4 *
                    powerShellScale M ^
                      (1 - powerW q transport kappa s) +
                  -(2 *
                    (Real.log 2 *
                      powerDensityConstant q transport kappa / 4) *
                    powerShellScale M ^
                      (1 - powerW q transport kappa s))) := by
                rw [Real.exp_add]
          _ = _ := by
                congr 2
                ring
  exact hbound

/-- The concrete terminal envelopes have vanishing exceptional proportion
on their own dyadic shells. -/
theorem powerEnvelopeExceptionalRatio_tendsto_zero
    {q transport kappa s : ℝ}
    (hq0 : 0 < q) (hqa : a0 < q) (hq1 : q < 1)
    (htransport0 : 0 < transport)
    (htransportLimit : transport < asymptoticRateLimit)
    (hk : KappaAdmissible kappa)
    (hs : 0 < s)
    (huw : powerU q s + powerW q transport kappa s < 1) :
    Filter.Tendsto
      (fun M =>
        shellExceptionalRatio (powerEnvelope q kappa s M) M)
      Filter.atTop (nhds 0) := by
  have hbound :=
    powerEnvelopeExceptionalRatio_eventually_le_model
      hq0 hqa hq1 htransport0 htransportLimit hk hs huw
  have hmodel :=
    powerShellDecayModel_tendsto_zero hq0 hqa hq1
      htransport0 hk hs huw
  exact squeeze_zero'
    (Filter.Eventually.of_forall fun M =>
      shellExceptionalRatio_nonneg (powerEnvelope q kappa s M) M)
    hbound hmodel

end

end OptimizedLinearPullback

end CollatzEndpointTransport
