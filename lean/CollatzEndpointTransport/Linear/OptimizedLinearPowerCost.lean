/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik
-/
import CollatzEndpointTransport.Linear.OptimizedLinearPowerEnvelope

/-!
# Optimized Linear Power Cost

Explicit terminal-cost bounds for the optimized linear power schedule.

The terminal density satisfies `D_M >= d X^(-w)`, while the startup
parameter satisfies `lambda_M >= a0*q*X^(-u)`.  Taking logarithms in the
exact recurrence majorant therefore bounds `log (C_M + 2)` by

  O((log X)^2 + X^u log X).

No asymptotic conclusion is asserted here; the next module compares this
cost with `D_M M`.
-/

namespace CollatzEndpointTransport

namespace OptimizedLinearPullback

open scoped Real Topology

noncomputable section

open QuantitativeDensity

def powerCostConstant
    (q transport kappa : ℝ) : ℝ :=
  |Real.log
      (linearStageK transport (asymptoticEta transport))| +
    2 * |Real.log (1 / powerDensityConstant q transport kappa)| + 1

def powerLogCostEnvelope
    (q transport kappa s : ℝ) (M : ℕ) : ℝ :=
  (s * powerShellLog M + 1) *
    (powerCostConstant q transport kappa +
      2 * powerW q transport kappa s * powerShellLog M +
      (linearStartupB q / (a0 * q)) *
        powerShellScale M ^ (powerU q s)) +
    |Real.log (Terras.quadraticWindowFixedGlobalConstant + 2)|

theorem powerLambda_lower
    {q s : ℝ}
    (hq0 : 0 < q) (hq1 : q < 1) (hs : 0 < s)
    (M : ℕ) :
    a0 * q * powerShellScale M ^ (-powerU q s) ≤
      linearLambda q (powerR s M) := by
  unfold linearLambda powerR
  simpa [mul_assoc] using
    mul_le_mul_of_nonneg_left
      (power_q_pow_lower hq0 hq1 hs M) a0_pos.le

theorem powerLambda_inv_le
    {q s : ℝ}
    (hq0 : 0 < q) (hq1 : q < 1) (hs : 0 < s)
    (M : ℕ) :
    (linearLambda q (powerR s M))⁻¹ ≤
      (a0 * q)⁻¹ * powerShellScale M ^ (powerU q s) := by
  have hlower := powerLambda_lower hq0 hq1 hs M
  have hleft0 :
      0 < a0 * q * powerShellScale M ^ (-powerU q s) :=
    mul_pos (mul_pos a0_pos hq0)
      (Real.rpow_pos_of_pos (powerShellScale_pos M) _)
  have hright0 := linearLambda_pos hq0 (powerR s M)
  have hinv :
      (linearLambda q (powerR s M))⁻¹ ≤
        (a0 * q * powerShellScale M ^ (-powerU q s))⁻¹ := by
    simpa [one_div] using
      one_div_le_one_div_of_le hleft0 hlower
  calc
    (linearLambda q (powerR s M))⁻¹
        ≤ (a0 * q *
            powerShellScale M ^ (-powerU q s))⁻¹ := hinv
    _ = (a0 * q)⁻¹ *
          powerShellScale M ^ (powerU q s) := by
      rw [mul_inv_rev, Real.rpow_neg (powerShellScale_pos M).le,
        inv_inv]
      ring

theorem powerEnvelopeD_inv_le
    {q transport kappa s : ℝ}
    (hq0 : 0 < q) (hqa : a0 < q) (hq1 : q < 1)
    (htransport0 : 0 < transport) (htransport1 : transport < 1)
    (hk : KappaAdmissible kappa)
    (hs : 0 < s) (M : ℕ) :
    (powerEnvelopeD q transport kappa s M)⁻¹ ≤
      (powerDensityConstant q transport kappa)⁻¹ *
        powerShellScale M ^ (powerW q transport kappa s) := by
  have hlower :=
    linearD_power_lower hq0 hqa hq1 htransport0 htransport1 hk hs M
  have hleft0 :
      0 <
        powerDensityConstant q transport kappa *
          powerShellScale M ^ (-powerW q transport kappa s) :=
    mul_pos
      (powerDensityConstant_pos hk hq0 hqa htransport0)
      (Real.rpow_pos_of_pos (powerShellScale_pos M) _)
  have hright0 :
      0 < powerEnvelopeD q transport kappa s M := by
    exact linearD_pos_all
      (R := powerR s M) htransport0 hk
      (powerTerminalTolerance_pos hk hq0 hqa _) (powerR s M)
  have hinv :
      (powerEnvelopeD q transport kappa s M)⁻¹ ≤
        (powerDensityConstant q transport kappa *
          powerShellScale M ^
            (-powerW q transport kappa s))⁻¹ := by
    simpa [one_div] using
      one_div_le_one_div_of_le hleft0 hlower
  calc
    (powerEnvelopeD q transport kappa s M)⁻¹
        ≤ (powerDensityConstant q transport kappa *
            powerShellScale M ^
              (-powerW q transport kappa s))⁻¹ := hinv
    _ = (powerDensityConstant q transport kappa)⁻¹ *
          powerShellScale M ^ (powerW q transport kappa s) := by
      rw [mul_inv_rev, Real.rpow_neg (powerShellScale_pos M).le,
        inv_inv]
      ring

theorem powerEnvelopeLogC_le_raw
    {q transport kappa s : ℝ}
    (htransport0 : 0 < transport)
    (htransportLimit : transport < asymptoticRateLimit)
    (hk : KappaAdmissible kappa)
    (hq0 : 0 < q) (hqa : a0 < q) (hq1 : q < 1)
    {M : ℕ}
    (hDterminal1 :
      powerEnvelopeD q transport kappa s M ≤ 1) :
    Real.log (powerEnvelopeC q transport kappa s M + 2) ≤
      (powerR s M : ℝ) *
        (Real.log
            (linearStageK transport (asymptoticEta transport)) +
          2 * Real.log
            ((powerEnvelopeD q transport kappa s M)⁻¹) +
          linearStartupB q /
            linearLambda q (powerR s M)) +
        Real.log
          (Terras.quadraticWindowFixedGlobalConstant + 2) := by
  let F :=
    linearStageK transport (asymptoticEta transport) *
      ((powerEnvelopeD q transport kappa s M)⁻¹) ^ 2 *
      Real.exp
        (linearStartupB q / linearLambda q (powerR s M))
  let W := Terras.quadraticWindowFixedGlobalConstant + 2
  have hbound :=
    powerEnvelopeC_terminal_bound
      htransport0 htransportLimit hk hq0 hqa hq1 hDterminal1
  have hC0 :
      0 < powerEnvelopeC q transport kappa s M + 2 := by
    have hC :=
      linearC_pos
        (q := q) (transport := transport)
        (eta := asymptoticEta transport)
        (kappa := kappa) (R := powerR s M)
        (tR := powerTR kappa q s M)
        htransport0
        (asymptoticEta_pos htransport0)
        (asymptoticEta_lt_one htransportLimit)
        (powerR s M)
    have hC' :
        0 < powerEnvelopeC q transport kappa s M := by
      simpa [powerEnvelopeC, powerTR, powerR] using hC
    linarith
  have hD0 :
      0 < powerEnvelopeD q transport kappa s M := by
    exact linearD_pos_all
      (R := powerR s M) htransport0 hk
      (powerTerminalTolerance_pos hk hq0 hqa _) (powerR s M)
  have hK0 :
      0 <
        linearStageK transport (asymptoticEta transport) :=
    linearStageK_pos htransport0
      (asymptoticEta_pos htransport0)
      (asymptoticEta_lt_one htransportLimit)
  have hF0 : 0 < F := by
    dsimp [F]
    positivity
  have hW0 : 0 < W := by
    dsimp [W]
    linarith [linearWindowConstant_pos]
  have hright0 : 0 < F ^ powerR s M * W :=
    mul_pos (pow_pos hF0 _) hW0
  have hlogMono :
      Real.log (powerEnvelopeC q transport kappa s M + 2) ≤
        Real.log (F ^ powerR s M * W) :=
    Real.strictMonoOn_log.monotoneOn
      (Set.mem_Ioi.mpr hC0) (Set.mem_Ioi.mpr hright0)
      (by simpa [F, W] using hbound)
  calc
    Real.log (powerEnvelopeC q transport kappa s M + 2)
        ≤ Real.log (F ^ powerR s M * W) := hlogMono
    _ = (powerR s M : ℝ) * Real.log F + Real.log W := by
      rw [Real.log_mul (pow_ne_zero _ hF0.ne') hW0.ne',
        Real.log_pow]
    _ = (powerR s M : ℝ) *
          (Real.log
              (linearStageK transport (asymptoticEta transport)) +
            2 * Real.log
              ((powerEnvelopeD q transport kappa s M)⁻¹) +
            linearStartupB q /
              linearLambda q (powerR s M)) +
          Real.log
            (Terras.quadraticWindowFixedGlobalConstant + 2) := by
      dsimp [F, W]
      rw [Real.log_mul
          (mul_ne_zero hK0.ne'
            (pow_ne_zero 2 (inv_ne_zero hD0.ne')))
          (Real.exp_ne_zero _),
        Real.log_mul hK0.ne' (pow_ne_zero 2 (inv_ne_zero hD0.ne')),
        Real.log_pow, Real.log_exp]
      ring

theorem powerEnvelopeLogDInv_le
    {q transport kappa s : ℝ}
    (hq0 : 0 < q) (hqa : a0 < q) (hq1 : q < 1)
    (htransport0 : 0 < transport) (htransport1 : transport < 1)
    (hk : KappaAdmissible kappa)
    (hs : 0 < s) (M : ℕ) :
    Real.log ((powerEnvelopeD q transport kappa s M)⁻¹) ≤
      |Real.log
          ((powerDensityConstant q transport kappa)⁻¹)| +
        powerW q transport kappa s * powerShellLog M := by
  have hinv :=
    powerEnvelopeD_inv_le hq0 hqa hq1
      htransport0 htransport1 hk hs M
  have hleft0 :
      0 < (powerEnvelopeD q transport kappa s M)⁻¹ :=
    inv_pos.mpr (linearD_pos_all
      (R := powerR s M) htransport0 hk
      (powerTerminalTolerance_pos hk hq0 hqa _) (powerR s M))
  have hright0 :
      0 <
        (powerDensityConstant q transport kappa)⁻¹ *
          powerShellScale M ^ (powerW q transport kappa s) :=
    mul_pos
      (inv_pos.mpr
        (powerDensityConstant_pos hk hq0 hqa htransport0))
      (Real.rpow_pos_of_pos (powerShellScale_pos M) _)
  have hlog :=
    Real.strictMonoOn_log.monotoneOn
      (Set.mem_Ioi.mpr hleft0) (Set.mem_Ioi.mpr hright0) hinv
  calc
    Real.log ((powerEnvelopeD q transport kappa s M)⁻¹)
        ≤ Real.log
          ((powerDensityConstant q transport kappa)⁻¹ *
            powerShellScale M ^ (powerW q transport kappa s)) := hlog
    _ = Real.log
          ((powerDensityConstant q transport kappa)⁻¹) +
        powerW q transport kappa s * powerShellLog M := by
      rw [Real.log_mul
        (inv_ne_zero
          (powerDensityConstant_pos hk hq0 hqa htransport0).ne')
        (Real.rpow_pos_of_pos (powerShellScale_pos M) _).ne',
        Real.log_rpow (powerShellScale_pos M)]
      rfl
    _ ≤ |Real.log
          ((powerDensityConstant q transport kappa)⁻¹)| +
        powerW q transport kappa s * powerShellLog M :=
      add_le_add_right (le_abs_self _) _

theorem powerStartupTerm_le
    {q s : ℝ}
    (hq0 : 0 < q) (hqa : a0 < q) (hq1 : q < 1)
    (hs : 0 < s) (M : ℕ) :
    linearStartupB q / linearLambda q (powerR s M) ≤
      (linearStartupB q / (a0 * q)) *
        powerShellScale M ^ (powerU q s) := by
  have hinv := powerLambda_inv_le hq0 hq1 hs M
  have hB0 := (linearStartupB_pos hqa).le
  rw [div_eq_mul_inv, div_eq_mul_inv]
  simpa [mul_assoc] using
    mul_le_mul_of_nonneg_left hinv hB0

/-- Explicit pointwise upper bound for the terminal density prefactor. -/
theorem powerEnvelopeLogC_le
    {q transport kappa s : ℝ}
    (htransport0 : 0 < transport)
    (htransportLimit : transport < asymptoticRateLimit)
    (hk : KappaAdmissible kappa)
    (hq0 : 0 < q) (hqa : a0 < q) (hq1 : q < 1)
    (hs : 0 < s)
    {M : ℕ}
    (hDterminal1 :
      powerEnvelopeD q transport kappa s M ≤ 1) :
    Real.log (powerEnvelopeC q transport kappa s M + 2) ≤
      powerLogCostEnvelope q transport kappa s M := by
  have hraw :=
    powerEnvelopeLogC_le_raw htransport0 htransportLimit
      hk hq0 hqa hq1 hDterminal1
  have hR := (powerStageCount_bounds hs M).2.le
  have hlogD :=
    powerEnvelopeLogDInv_le hq0 hqa hq1
      htransport0
      (htransportLimit.trans asymptoticRateLimit_lt_one)
      hk hs M
  have hlogD' :
      Real.log ((powerEnvelopeD q transport kappa s M)⁻¹) ≤
        |Real.log
          (1 / powerDensityConstant q transport kappa)| +
          powerW q transport kappa s * powerShellLog M := by
    simpa [one_div] using hlogD
  have hstartup := powerStartupTerm_le hq0 hqa hq1 hs M
  have hR0 : 0 ≤ (powerR s M : ℝ) := Nat.cast_nonneg _
  have hinner :
      Real.log
            (linearStageK transport (asymptoticEta transport)) +
          2 * Real.log
            ((powerEnvelopeD q transport kappa s M)⁻¹) +
          linearStartupB q /
            linearLambda q (powerR s M)
        ≤
      powerCostConstant q transport kappa +
        2 * powerW q transport kappa s * powerShellLog M +
        (linearStartupB q / (a0 * q)) *
          powerShellScale M ^ (powerU q s) := by
    unfold powerCostConstant
    have hlogK :=
      le_abs_self
        (Real.log
          (linearStageK transport (asymptoticEta transport)))
    linarith [hlogD']
  have hinner0 :
      0 ≤
        powerCostConstant q transport kappa +
          2 * powerW q transport kappa s * powerShellLog M +
          (linearStartupB q / (a0 * q)) *
            powerShellScale M ^ (powerU q s) := by
    unfold powerCostConstant
    have hB :
        0 ≤ linearStartupB q / (a0 * q) :=
      div_nonneg (linearStartupB_pos hqa).le
        (mul_nonneg a0_pos.le hq0.le)
    have hw0 :
        0 ≤ powerW q transport kappa s := by
      unfold powerW
      have hbase :=
        power_combined_base_lt_one hq0 hq1 htransport0
          (htransportLimit.trans asymptoticRateLimit_lt_one) hk
      exact mul_nonneg hs.le
        (Real.log_nonneg
          ((one_le_div₀ (power_combined_base_pos
              hq0 htransport0 hk)).2 hbase.le))
    have hcost0 :
        0 ≤
          |Real.log
              (linearStageK transport (asymptoticEta transport))| +
            2 * |Real.log
              (1 / powerDensityConstant q transport kappa)| + 1 := by
      positivity
    have hlog0 := (powerShellLog_pos M).le
    have hpow0 :
        0 ≤ powerShellScale M ^ (powerU q s) :=
      Real.rpow_nonneg (powerShellScale_pos M).le _
    nlinarith [mul_nonneg hw0 hlog0, mul_nonneg hB hpow0]
  calc
    Real.log (powerEnvelopeC q transport kappa s M + 2)
        ≤ (powerR s M : ℝ) *
            (Real.log
                (linearStageK transport (asymptoticEta transport)) +
              2 * Real.log
                ((powerEnvelopeD q transport kappa s M)⁻¹) +
              linearStartupB q /
                linearLambda q (powerR s M)) +
            Real.log
              (Terras.quadraticWindowFixedGlobalConstant + 2) := hraw
    _ ≤ (s * powerShellLog M + 1) *
          (powerCostConstant q transport kappa +
            2 * powerW q transport kappa s * powerShellLog M +
            (linearStartupB q / (a0 * q)) *
              powerShellScale M ^ (powerU q s)) +
          |Real.log
            (Terras.quadraticWindowFixedGlobalConstant + 2)| := by
      apply add_le_add _ (le_abs_self _)
      calc
        (powerR s M : ℝ) *
              (Real.log
                  (linearStageK transport (asymptoticEta transport)) +
                2 * Real.log
                  ((powerEnvelopeD q transport kappa s M)⁻¹) +
                linearStartupB q /
                  linearLambda q (powerR s M))
            ≤ (powerR s M : ℝ) *
                (powerCostConstant q transport kappa +
                  2 * powerW q transport kappa s * powerShellLog M +
                  (linearStartupB q / (a0 * q)) *
                    powerShellScale M ^ (powerU q s)) :=
          mul_le_mul_of_nonneg_left hinner hR0
        _ ≤ (s * powerShellLog M + 1) *
              (powerCostConstant q transport kappa +
                2 * powerW q transport kappa s * powerShellLog M +
                (linearStartupB q / (a0 * q)) *
                  powerShellScale M ^ (powerU q s)) :=
          mul_le_mul_of_nonneg_right hR hinner0
    _ = powerLogCostEnvelope q transport kappa s M := rfl

end

end OptimizedLinearPullback

end CollatzEndpointTransport
