/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik
-/
import CollatzEndpointTransport.Linear.EndpointOnlyRecurrenceBound
import CollatzEndpointTransport.Linear.OptimizedLinearPowerSchedule

/-!
# Endpoint Only Schedule

Logarithmic shell schedule for the endpoint-only bootstrap.

For `X = M + 4` and

  R_M = ceil (omega * log X),

the orbit contraction contributes the power

  u = omega * log (1 / r),

while the terminal density exponent contributes

  w = omega * log (1 / transport).

No tolerance ratio occurs in either exponent.
-/

namespace CollatzEndpointTransport

namespace OptimizedLinearPullback

open scoped Real Topology

noncomputable section

open QuantitativeDensity

def endpointStageCount (omega : ℝ) (M : ℕ) : ℕ :=
  powerStageCount omega M

def endpointOrbitPower (r omega : ℝ) : ℝ :=
  powerU r omega

def endpointDensityPower (transport omega : ℝ) : ℝ :=
  powerU transport omega

def endpointScheduledD
    (transport D0 omega : ℝ) (M : ℕ) : ℝ :=
  endpointD transport D0 (endpointStageCount omega M)

def endpointScheduledC
    (transport eta t D0 omega : ℝ) (M : ℕ) : ℝ :=
  endpointC transport eta t D0 (endpointStageCount omega M)

theorem endpointStageCount_bounds
    {omega : ℝ} (homega : 0 < omega) (M : ℕ) :
    omega * powerShellLog M ≤ endpointStageCount omega M ∧
      (endpointStageCount omega M : ℝ) <
        omega * powerShellLog M + 1 := by
  simpa [endpointStageCount] using
    powerStageCount_bounds homega M

/-- The logarithmic number of endpoint blocks is negligible compared with
the source-shell index. -/
theorem endpointStageCount_div_scale_tendsto_zero
    {omega : ℝ} (homega : 0 < omega) :
    Filter.Tendsto
      (fun M =>
        (endpointStageCount omega M : ℝ) / powerShellScale M)
      Filter.atTop (nhds 0) := by
  have hlog :
      Filter.Tendsto
        (fun M => powerShellLog M / powerShellScale M)
        Filter.atTop (nhds 0) := by
    simpa [powerShellLog, Function.comp_apply] using
      Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp
        powerShellScale_tendsto_atTop
  have hinv :
      Filter.Tendsto
        (fun M => 1 / powerShellScale M)
        Filter.atTop (nhds 0) := by
    simpa [one_div] using
      tendsto_inv_atTop_zero.comp powerShellScale_tendsto_atTop
  have hupper :
      Filter.Tendsto
        (fun M =>
          omega * (powerShellLog M / powerShellScale M) +
            1 / powerShellScale M)
        Filter.atTop (nhds 0) := by
    simpa using (hlog.const_mul omega).add hinv
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall fun M =>
      div_nonneg (Nat.cast_nonneg _) (powerShellScale_pos M).le
  · exact Filter.Eventually.of_forall fun M => by
      have hR := (endpointStageCount_bounds homega M).2.le
      have hX0 := (powerShellScale_pos M).le
      calc
        (endpointStageCount omega M : ℝ) / powerShellScale M
            ≤ (omega * powerShellLog M + 1) / powerShellScale M :=
          div_le_div_of_nonneg_right hR hX0
        _ = omega * (powerShellLog M / powerShellScale M) +
              1 / powerShellScale M := by ring
  · exact hupper

/-- Once the geometric main coefficient lies below `timeConstant`, the
scheduled endpoint chain is eventually witnessed before
`timeConstant * log n`. -/
theorem endpointTime_schedule_eventually_lt
    {r omega timeConstant : ℝ}
    (hra : a0 < r) (hr1 : r < 1)
    (homega : 0 < omega)
    (htime : (1 - r)⁻¹ / Real.log 2 < timeConstant) :
    ∀ᶠ M : ℕ in Filter.atTop,
      ∀ n : ℕ,
        Nat.log 2 n = M →
        0 < n →
        n ∈ endpointChain (r - a0) (endpointStageCount omega M) →
        (endpointTime (endpointStageCount omega M) n : ℝ) <
          timeConstant * Real.log n := by
  let gap := timeConstant - (1 - r)⁻¹ / Real.log 2
  have hgap : 0 < gap := by dsimp [gap]; linarith
  have hstage := endpointStageCount_div_scale_tendsto_zero homega
  have hscaled := hstage.const_mul
    (bConst * (1 - r)⁻¹)
  have hscaled0 :
      Filter.Tendsto
        (fun M =>
          bConst * (1 - r)⁻¹ *
            ((endpointStageCount omega M : ℝ) / powerShellScale M))
        Filter.atTop (nhds 0) := by
    simpa using hscaled
  have hevent :
      ∀ᶠ M : ℕ in Filter.atTop,
        bConst * (1 - r)⁻¹ *
              ((endpointStageCount omega M : ℝ) / powerShellScale M) <
            gap * Real.log 2 / 2 := by
    have htarget : 0 < gap * Real.log 2 / 2 := by
      positivity
    exact hscaled0.eventually (Iio_mem_nhds htarget)
  have hM4 : ∀ᶠ M : ℕ in Filter.atTop, 4 ≤ M :=
    Filter.eventually_atTop.2 ⟨4, fun _ h => h⟩
  filter_upwards [hevent, hM4] with M hsmall hM4M
  intro n hMn hn hchain
  have hraw := endpointTime_le hn hra hr1 hchain
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hpowNat : 2 ^ M ≤ n := by
    rw [← hMn]
    exact Nat.pow_log_le_self 2 hn.ne'
  have hpow : (2 : ℝ) ^ M ≤ (n : ℝ) := by
    exact_mod_cast hpowNat
  have hnR0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hlogLower : (M : ℝ) * Real.log 2 ≤ Real.log n := by
    have h :=
      Real.strictMonoOn_log.monotoneOn
        (Set.mem_Ioi.mpr (by positivity : 0 < (2 : ℝ) ^ M))
        (Set.mem_Ioi.mpr hnR0) hpow
    rw [Real.log_pow] at h
    simpa [mul_comm] using h
  have hscaleM : powerShellScale M ≤ 2 * (M : ℝ) := by
    unfold powerShellScale
    have hMR : (4 : ℝ) ≤ M := by exact_mod_cast hM4M
    linarith
  have herror :
      (endpointStageCount omega M : ℝ) * bConst * (1 - r)⁻¹ <
        gap * Real.log n := by
    have hX0 : 0 < powerShellScale M := powerShellScale_pos M
    have hden : 0 < 1 - r := sub_pos.mpr hr1
    have hrewrite :
        (endpointStageCount omega M : ℝ) * bConst * (1 - r)⁻¹ =
          (bConst * (1 - r)⁻¹ *
              ((endpointStageCount omega M : ℝ) / powerShellScale M)) *
            powerShellScale M := by
      field_simp [hX0.ne', hden.ne']
      ring
    rw [hrewrite]
    calc
      (bConst * (1 - r)⁻¹ *
            ((endpointStageCount omega M : ℝ) / powerShellScale M)) *
          powerShellScale M
          < (gap * Real.log 2 / 2) * powerShellScale M :=
        mul_lt_mul_of_pos_right hsmall hX0
      _ ≤ gap * ((M : ℝ) * Real.log 2) := by
        calc
          (gap * Real.log 2 / 2) * powerShellScale M
              ≤ (gap * Real.log 2 / 2) * (2 * (M : ℝ)) :=
            mul_le_mul_of_nonneg_left hscaleM (by positivity)
          _ = gap * ((M : ℝ) * Real.log 2) := by ring
      _ ≤ gap * Real.log n :=
        mul_le_mul_of_nonneg_left hlogLower hgap.le
  calc
    (endpointTime (endpointStageCount omega M) n : ℝ)
        ≤ (1 - r)⁻¹ / Real.log 2 * Real.log n +
            (endpointStageCount omega M : ℝ) * bConst * (1 - r)⁻¹ := hraw
    _ < (1 - r)⁻¹ / Real.log 2 * Real.log n +
          gap * Real.log n := add_lt_add_left herror _
    _ = timeConstant * Real.log n := by
      dsimp [gap]
      ring

theorem endpointOrbitPower_pos
    {r omega : ℝ}
    (hr0 : 0 < r) (hr1 : r < 1) (homega : 0 < omega) :
    0 < endpointOrbitPower r omega := by
  exact powerU_pos hr0 hr1 homega

theorem endpointDensityPower_pos
    {transport omega : ℝ}
    (htransport0 : 0 < transport)
    (htransport1 : transport < 1)
    (homega : 0 < omega) :
    0 < endpointDensityPower transport omega := by
  exact powerU_pos htransport0 htransport1 homega

/-- Scheduled orbit contraction. -/
theorem endpoint_r_pow_upper
    {r omega : ℝ}
    (hr0 : 0 < r) (hr1 : r < 1)
    (homega : 0 < omega) (M : ℕ) :
    r ^ endpointStageCount omega M ≤
      powerShellScale M ^ (-endpointOrbitPower r omega) := by
  simpa [endpointStageCount, endpointOrbitPower] using
    power_q_pow_upper hr0 hr1 homega M

/-- Scheduled terminal density lower bound. -/
theorem endpointScheduledD_lower
    {transport D0 omega : ℝ}
    (htransport0 : 0 < transport)
    (htransport1 : transport < 1)
    (hD00 : 0 < D0)
    (homega : 0 < omega)
    (M : ℕ) :
    D0 * transport *
        powerShellScale M ^ (-endpointDensityPower transport omega) ≤
      endpointScheduledD transport D0 omega M := by
  have hp :=
    power_q_pow_lower htransport0 htransport1 homega M
  unfold endpointScheduledD endpointD endpointStageCount
  calc
    D0 * transport *
          powerShellScale M ^ (-endpointDensityPower transport omega)
        =
      D0 *
        (transport *
          powerShellScale M ^ (-powerU transport omega)) := by
            simp only [endpointDensityPower]
            ring
    _ ≤ D0 * transport ^ powerStageCount omega M :=
      mul_le_mul_of_nonneg_left hp hD00.le
    _ = transport ^ powerStageCount omega M * D0 := by ring

theorem endpointScheduledD_pos
    {transport D0 omega : ℝ}
    (htransport0 : 0 < transport)
    (hD00 : 0 < D0) (M : ℕ) :
    0 < endpointScheduledD transport D0 omega M := by
  exact endpointD_pos htransport0 hD00 _

theorem endpointScheduledD_le_D0
    {transport D0 omega : ℝ}
    (htransport0 : 0 < transport)
    (htransport1 : transport ≤ 1)
    (hD00 : 0 < D0) (M : ℕ) :
    endpointScheduledD transport D0 omega M ≤ D0 := by
  exact endpointD_le_D0 htransport0.le htransport1 hD00.le _

/-- The exact fixed-stage density theorem specialized to the shell schedule. -/
theorem endpointScheduledChain_dense
    {transport eta t D0 Dcut omega : ℝ}
    (htransport0 : 0 < transport) (htransport1 : transport ≤ 1)
    (heta0 : 0 < eta) (heta1 : eta < 1)
    (ht0 : 0 < t) (ht1 : t ≤ 1)
    (hD00 : 0 < D0) (hD01 : D0 ≤ 1)
    (hDcut0 : 0 < Dcut) (hD0cut : D0 ≤ Dcut)
    (hcut :
      ∀ D : ℝ, 0 < D → D ≤ Dcut →
        transport * D ≤ shellRate eta D / Real.log 2)
    (hwindow0 :
      transport * D0 ≤ Terras.quadraticWindowDensityRate t)
    (M : ℕ) :
    IsCDDense
      (endpointChain t (endpointStageCount omega M))
      (endpointScheduledC transport eta t D0 omega M)
      (endpointScheduledD transport D0 omega M) := by
  simpa [endpointScheduledC, endpointScheduledD] using
    endpointChain_dense htransport0 htransport1
      heta0 heta1 ht0 ht1 hD00 hD01 hDcut0 hD0cut
      hcut hwindow0 (endpointStageCount omega M)

/-- Terminal prefactor majorant on the logarithmic schedule. -/
theorem endpointScheduledC_bound
    {transport eta t D0 omega : ℝ}
    (htransport0 : 0 < transport)
    (htransport1 : transport ≤ 1)
    (heta0 : 0 < eta) (heta1 : eta < 1)
    (ht0 : 0 < t) (ht1 : t ≤ 1)
    (hD00 : 0 < D0) (hD01 : D0 ≤ 1)
    (M : ℕ) :
    endpointScheduledC transport eta t D0 omega M + 2 ≤
      3 *
        (endpointStageK transport eta *
          ((endpointScheduledD transport D0 omega M)⁻¹) ^ 2) ^
            endpointStageCount omega M := by
  exact endpointC_terminal_bound htransport0 htransport1
    heta0 heta1 ht0 ht1 hD00
    (endpointScheduledD_le_D0 htransport0 htransport1 hD00 M |>.trans hD01)

/-- Scheduled endpoint contraction in logarithmic form. -/
theorem log_endpointIter_schedule_le
    {n M : ℕ} {r t omega : ℝ}
    (hn : 0 < n)
    (hM : M = Nat.log 2 n)
    (hra : a0 < r) (hr1 : r < 1)
    (ht : t = r - a0)
    (homega : 0 < omega)
    (hchain : n ∈ endpointChain t (endpointStageCount omega M)) :
    Real.log
        (endpointIter (endpointStageCount omega M) n) ≤
      powerShellScale M ^ (-endpointOrbitPower r omega) *
          Real.log n +
        Real.log endpointK * endpointGeom r (endpointStageCount omega M) := by
  subst t
  have hraw :=
    log_endpointIter_le hn hra hr1 hchain
  have hpow :=
    endpoint_r_pow_upper
      (a0_pos.trans hra) hr1 homega M
  have hlog0 : 0 ≤ Real.log n := by
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    exact Real.log_nonneg (by exact_mod_cast hn)
  exact hraw.trans
    (add_le_add_right
      (mul_le_mul_of_nonneg_right hpow hlog0) _)

end

end OptimizedLinearPullback

end CollatzEndpointTransport
