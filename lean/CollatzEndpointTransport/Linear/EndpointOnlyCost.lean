/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik
-/
import CollatzEndpointTransport.Linear.EndpointOnlySchedule

/-!
# Endpoint Only Cost

Explicit logarithmic cost for the endpoint-only schedule.

The terminal density has the lower bound

  D_M >= D0 * transport * X^(-w),

and the endpoint-only prefactor recurrence has no horizon-startup term.
Consequently

  log (C_M + 2) = O((log X)^2).
-/

namespace CollatzEndpointTransport

namespace OptimizedLinearPullback

open scoped Real Topology

noncomputable section

open QuantitativeDensity

def endpointDensityConstant (transport D0 : ℝ) : ℝ :=
  D0 * transport

def endpointCostConstant
    (transport eta D0 : ℝ) : ℝ :=
  |Real.log (endpointStageK transport eta)| +
    2 * |Real.log ((endpointDensityConstant transport D0)⁻¹)| + 1

def endpointLogCostEnvelope
    (transport eta D0 omega : ℝ) (M : ℕ) : ℝ :=
  (omega * powerShellLog M + 1) *
      (endpointCostConstant transport eta D0 +
        2 * endpointDensityPower transport omega * powerShellLog M) +
    |Real.log 3|

theorem endpointDensityConstant_pos
    {transport D0 : ℝ}
    (htransport0 : 0 < transport) (hD00 : 0 < D0) :
    0 < endpointDensityConstant transport D0 :=
  mul_pos hD00 htransport0

theorem endpointScheduledD_inv_le
    {transport D0 omega : ℝ}
    (htransport0 : 0 < transport)
    (htransport1 : transport < 1)
    (hD00 : 0 < D0)
    (homega : 0 < omega)
    (M : ℕ) :
    (endpointScheduledD transport D0 omega M)⁻¹ ≤
      (endpointDensityConstant transport D0)⁻¹ *
        powerShellScale M ^ (endpointDensityPower transport omega) := by
  have hlower :=
    endpointScheduledD_lower htransport0 htransport1 hD00 homega M
  have hleft0 :
      0 <
        endpointDensityConstant transport D0 *
          powerShellScale M ^ (-endpointDensityPower transport omega) :=
    mul_pos (endpointDensityConstant_pos htransport0 hD00)
      (Real.rpow_pos_of_pos (powerShellScale_pos M) _)
  have hright0 :
      0 < endpointScheduledD transport D0 omega M :=
    endpointScheduledD_pos htransport0 hD00 M
  have hinv :
      (endpointScheduledD transport D0 omega M)⁻¹ ≤
        (endpointDensityConstant transport D0 *
          powerShellScale M ^
            (-endpointDensityPower transport omega))⁻¹ := by
    simpa [one_div] using
      one_div_le_one_div_of_le hleft0 hlower
  calc
    (endpointScheduledD transport D0 omega M)⁻¹
        ≤
      (endpointDensityConstant transport D0 *
        powerShellScale M ^
          (-endpointDensityPower transport omega))⁻¹ := hinv
    _ =
      (endpointDensityConstant transport D0)⁻¹ *
        powerShellScale M ^ (endpointDensityPower transport omega) := by
      rw [mul_inv_rev,
        Real.rpow_neg (powerShellScale_pos M).le, inv_inv]
      ring

theorem endpointScheduledLogDInv_le
    {transport D0 omega : ℝ}
    (htransport0 : 0 < transport)
    (htransport1 : transport < 1)
    (hD00 : 0 < D0)
    (homega : 0 < omega)
    (M : ℕ) :
    Real.log ((endpointScheduledD transport D0 omega M)⁻¹) ≤
      |Real.log ((endpointDensityConstant transport D0)⁻¹)| +
        endpointDensityPower transport omega * powerShellLog M := by
  have hinv :=
    endpointScheduledD_inv_le
      htransport0 htransport1 hD00 homega M
  have hleft0 :
      0 < (endpointScheduledD transport D0 omega M)⁻¹ :=
    inv_pos.mpr (endpointScheduledD_pos htransport0 hD00 M)
  have hright0 :
      0 <
        (endpointDensityConstant transport D0)⁻¹ *
          powerShellScale M ^ (endpointDensityPower transport omega) :=
    mul_pos
      (inv_pos.mpr (endpointDensityConstant_pos htransport0 hD00))
      (Real.rpow_pos_of_pos (powerShellScale_pos M) _)
  have hlog :=
    Real.strictMonoOn_log.monotoneOn
      (Set.mem_Ioi.mpr hleft0) (Set.mem_Ioi.mpr hright0) hinv
  calc
    Real.log ((endpointScheduledD transport D0 omega M)⁻¹)
        ≤
      Real.log
        ((endpointDensityConstant transport D0)⁻¹ *
          powerShellScale M ^
            (endpointDensityPower transport omega)) := hlog
    _ =
      Real.log ((endpointDensityConstant transport D0)⁻¹) +
        endpointDensityPower transport omega * powerShellLog M := by
      rw [Real.log_mul
          (inv_ne_zero
            (endpointDensityConstant_pos htransport0 hD00).ne')
          (Real.rpow_pos_of_pos (powerShellScale_pos M) _).ne',
        Real.log_rpow (powerShellScale_pos M)]
      rfl
    _ ≤
      |Real.log ((endpointDensityConstant transport D0)⁻¹)| +
        endpointDensityPower transport omega * powerShellLog M :=
      add_le_add_right (le_abs_self _) _

/-- Raw logarithm of the exact terminal-prefactor majorant. -/
theorem endpointScheduledLogC_le_raw
    {transport eta t D0 omega : ℝ}
    (htransport0 : 0 < transport)
    (htransport1 : transport ≤ 1)
    (heta0 : 0 < eta) (heta1 : eta < 1)
    (ht0 : 0 < t) (ht1 : t ≤ 1)
    (hD00 : 0 < D0) (hD01 : D0 ≤ 1)
    (M : ℕ) :
    Real.log (endpointScheduledC transport eta t D0 omega M + 2) ≤
      (endpointStageCount omega M : ℝ) *
        (Real.log (endpointStageK transport eta) +
          2 * Real.log
            ((endpointScheduledD transport D0 omega M)⁻¹)) +
        Real.log 3 := by
  let F :=
    endpointStageK transport eta *
      ((endpointScheduledD transport D0 omega M)⁻¹) ^ 2
  have hbound :=
    endpointScheduledC_bound (omega := omega)
      htransport0 htransport1
      heta0 heta1 ht0 ht1 hD00 hD01 M
  have hC0 :
      0 < endpointScheduledC transport eta t D0 omega M + 2 := by
    have hC :=
      endpointC_pos (D0 := D0)
        htransport0 heta0 heta1 ht0 ht1
        (endpointStageCount omega M)
    change 0 < endpointC transport eta t D0
      (endpointStageCount omega M) + 2
    linarith
  have hD0 :
      0 < endpointScheduledD transport D0 omega M :=
    endpointScheduledD_pos htransport0 hD00 M
  have hK0 :
      0 < endpointStageK transport eta :=
    endpointStageK_pos htransport0 heta0 heta1
  have hF0 : 0 < F := by
    dsimp [F]
    positivity
  have hright0 :
      0 < 3 * F ^ endpointStageCount omega M :=
    mul_pos (by norm_num) (pow_pos hF0 _)
  have hlogMono :
      Real.log (endpointScheduledC transport eta t D0 omega M + 2) ≤
        Real.log (3 * F ^ endpointStageCount omega M) :=
    Real.strictMonoOn_log.monotoneOn
      (Set.mem_Ioi.mpr hC0) (Set.mem_Ioi.mpr hright0)
      (by simpa [F] using hbound)
  calc
    Real.log (endpointScheduledC transport eta t D0 omega M + 2)
        ≤ Real.log (3 * F ^ endpointStageCount omega M) := hlogMono
    _ =
      (endpointStageCount omega M : ℝ) * Real.log F +
        Real.log 3 := by
      rw [Real.log_mul (by norm_num : (3 : ℝ) ≠ 0)
          (pow_ne_zero _ hF0.ne'),
        Real.log_pow]
      ring
    _ =
      (endpointStageCount omega M : ℝ) *
        (Real.log (endpointStageK transport eta) +
          2 * Real.log
            ((endpointScheduledD transport D0 omega M)⁻¹)) +
        Real.log 3 := by
      dsimp [F]
      rw [Real.log_mul hK0.ne'
          (pow_ne_zero 2 (inv_ne_zero hD0.ne')),
        Real.log_pow]
      norm_num

/-- Explicit quadratic-in-`log X` upper bound for the terminal prefactor. -/
theorem endpointScheduledLogC_le
    {transport eta t D0 omega : ℝ}
    (htransport0 : 0 < transport)
    (htransport1 : transport < 1)
    (heta0 : 0 < eta) (heta1 : eta < 1)
    (ht0 : 0 < t) (ht1 : t ≤ 1)
    (hD00 : 0 < D0) (hD01 : D0 ≤ 1)
    (homega : 0 < omega)
    (M : ℕ) :
    Real.log (endpointScheduledC transport eta t D0 omega M + 2) ≤
      endpointLogCostEnvelope transport eta D0 omega M := by
  have hraw :=
    endpointScheduledLogC_le_raw (omega := omega)
      htransport0 htransport1.le
      heta0 heta1 ht0 ht1 hD00 hD01 M
  have hR := (endpointStageCount_bounds homega M).2.le
  have hlogD :=
    endpointScheduledLogDInv_le
      htransport0 htransport1 hD00 homega M
  have hKabs :
      Real.log (endpointStageK transport eta) ≤
        |Real.log (endpointStageK transport eta)| :=
    le_abs_self _
  have hinner :
      Real.log (endpointStageK transport eta) +
            2 * Real.log
              ((endpointScheduledD transport D0 omega M)⁻¹)
          ≤
        endpointCostConstant transport eta D0 +
          2 * endpointDensityPower transport omega * powerShellLog M := by
    unfold endpointCostConstant
    nlinarith
  have hinner0 :
      0 ≤
        endpointCostConstant transport eta D0 +
          2 * endpointDensityPower transport omega * powerShellLog M := by
    unfold endpointCostConstant
    have hw0 :
        0 ≤ endpointDensityPower transport omega :=
      (endpointDensityPower_pos htransport0 htransport1 homega).le
    have hlogX0 := (powerShellLog_pos M).le
    positivity
  have hrawInner0 :
      0 ≤
        Real.log (endpointStageK transport eta) +
          2 * Real.log
            ((endpointScheduledD transport D0 omega M)⁻¹) := by
    have hlogK0 :
        0 ≤ Real.log (endpointStageK transport eta) :=
      Real.log_nonneg
        (endpointStageK_ge_one htransport0 heta0 heta1)
    have hDM0 :=
      endpointScheduledD_pos (omega := omega)
        htransport0 hD00 M
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
          (Real.log (endpointStageK transport eta) +
            2 * Real.log
              ((endpointScheduledD transport D0 omega M)⁻¹))
        ≤
      (omega * powerShellLog M + 1) *
        (endpointCostConstant transport eta D0 +
          2 * endpointDensityPower transport omega * powerShellLog M) := by
    exact mul_le_mul hR hinner hrawInner0 hRright0
  unfold endpointLogCostEnvelope
  exact hraw.trans (add_le_add hmul (le_abs_self _))

end

end OptimizedLinearPullback

end CollatzEndpointTransport
