/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik
-/
import CollatzEndpointTransport.Linear.OptimizedLinearRecurrenceBound
import CollatzEndpointTransport.Common.VaryingShellDensity

/-!
# Optimized Linear Power Schedule

The explicit power schedule for the optimized linear bootstrap.

For `X = M + 4` and a fixed slope `s`, set

  R_M = ceil (s * log X).

Then `q ^ R_M` is comparable with `X ^ (-u)`, where
`u = s * log (1 / q)`, and the terminal density exponent is bounded below
by a fixed multiple of `X ^ (-w)`, where

  w = s * log (1 / (transport * kappa^2 * q^2)).

These are the pointwise scalar estimates used by the varying-shell proof.
-/

namespace CollatzEndpointTransport

namespace OptimizedLinearPullback

open scoped Real Topology

noncomputable section

open QuantitativeDensity

def powerShellScale (M : ℕ) : ℝ :=
  (M : ℝ) + 4

def powerShellLog (M : ℕ) : ℝ :=
  Real.log (powerShellScale M)

def powerStageCount (s : ℝ) (M : ℕ) : ℕ :=
  ⌈s * powerShellLog M⌉₊

def powerU (q s : ℝ) : ℝ :=
  s * Real.log (1 / q)

def powerW (q transport kappa s : ℝ) : ℝ :=
  s * Real.log (1 / (transport * kappa ^ 2 * q ^ 2))

def powerTerminalTolerance
    (kappa q : ℝ) (R : ℕ) : ℝ :=
  let x := cq kappa q * linearLambda q R
  x / (2 * (1 + x))

def powerToleranceBaseConstant (kappa q : ℝ) : ℝ :=
  cq kappa q / (2 * (1 + cq kappa q)) * a0

def powerToleranceConstant (kappa q : ℝ) : ℝ :=
  powerToleranceBaseConstant kappa q * q

def powerDensityConstant
    (q transport kappa : ℝ) : ℝ :=
  Terras.maximalBarrierC0 / Real.log 2 *
    (powerToleranceBaseConstant kappa q) ^ 2 *
    (transport * kappa ^ 2 * q ^ 2)

theorem powerShellScale_pos (M : ℕ) :
    0 < powerShellScale M := by
  unfold powerShellScale
  positivity

theorem powerShellScale_gt_one (M : ℕ) :
    1 < powerShellScale M := by
  unfold powerShellScale
  have hM : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  linarith

theorem powerShellLog_pos (M : ℕ) :
    0 < powerShellLog M := by
  unfold powerShellLog
  exact Real.log_pos (powerShellScale_gt_one M)

theorem powerShellScale_tendsto_atTop :
    Filter.Tendsto powerShellScale Filter.atTop Filter.atTop :=
  tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds

theorem powerShellLog_tendsto_atTop :
    Filter.Tendsto powerShellLog Filter.atTop Filter.atTop :=
  Real.tendsto_log_atTop.comp powerShellScale_tendsto_atTop

theorem powerStageCount_bounds
    {s : ℝ} (hs : 0 < s) (M : ℕ) :
    s * powerShellLog M ≤ powerStageCount s M ∧
      (powerStageCount s M : ℝ) <
        s * powerShellLog M + 1 := by
  have hx0 : 0 ≤ s * powerShellLog M :=
    mul_nonneg hs.le (powerShellLog_pos M).le
  exact ⟨Nat.le_ceil _, Nat.ceil_lt_add_one hx0⟩

theorem power_base_identity
    {r s : ℝ} (hr : 0 < r) (M : ℕ) :
    r ^ (s * powerShellLog M) =
      powerShellScale M ^ (s * Real.log r) := by
  rw [Real.rpow_def_of_pos hr,
    Real.rpow_def_of_pos (powerShellScale_pos M)]
  unfold powerShellLog
  congr 1
  ring

theorem power_q_identity
    {q s : ℝ} (hq : 0 < q) (M : ℕ) :
    q ^ (s * powerShellLog M) =
      powerShellScale M ^ (-powerU q s) := by
  rw [power_base_identity hq]
  unfold powerU
  rw [show Real.log (1 / q) = -Real.log q by
    rw [one_div, Real.log_inv]]
  congr 1
  ring

theorem power_q_pow_upper
    {q s : ℝ}
    (hq0 : 0 < q) (hq1 : q < 1) (hs : 0 < s) (M : ℕ) :
    q ^ powerStageCount s M ≤
      powerShellScale M ^ (-powerU q s) := by
  have hR := (powerStageCount_bounds hs M).1
  rw [← Real.rpow_natCast, ← power_q_identity hq0 M]
  exact Real.rpow_le_rpow_of_exponent_ge hq0 hq1.le hR

theorem power_q_pow_lower
    {q s : ℝ}
    (hq0 : 0 < q) (hq1 : q < 1) (hs : 0 < s) (M : ℕ) :
    q * powerShellScale M ^ (-powerU q s) ≤
      q ^ powerStageCount s M := by
  have hR := (powerStageCount_bounds hs M).2.le
  rw [← Real.rpow_natCast, ← power_q_identity hq0 M]
  have hpow :
      q ^ (s * powerShellLog M + 1) ≤
        q ^ (powerStageCount s M : ℝ) :=
    Real.rpow_le_rpow_of_exponent_ge hq0 hq1.le hR
  rw [Real.rpow_add hq0, Real.rpow_one] at hpow
  simpa [mul_comm] using hpow

theorem powerU_pos
    {q s : ℝ}
    (hq0 : 0 < q) (hq1 : q < 1) (hs : 0 < s) :
    0 < powerU q s := by
  unfold powerU
  exact mul_pos hs (log_one_div_pos hq0 hq1)

theorem powerTerminalTolerance_pos
    {kappa q : ℝ}
    (hk : KappaAdmissible kappa)
    (hq0 : 0 < q) (hqa : a0 < q) (R : ℕ) :
    0 < powerTerminalTolerance kappa q R := by
  unfold powerTerminalTolerance
  have hcq :
      0 < cq kappa q := by
    unfold cq
    exact div_pos (sub_pos.mpr hqa)
      (mul_pos (mul_pos (by norm_num) hk.1) hq0)
  have hx :
      0 < cq kappa q * linearLambda q R :=
    mul_pos hcq (linearLambda_pos hq0 R)
  positivity

theorem powerTerminalTolerance_le_one
    {kappa q : ℝ}
    (hk : KappaAdmissible kappa)
    (hq0 : 0 < q) (hqa : a0 < q) (R : ℕ) :
    powerTerminalTolerance kappa q R ≤ 1 := by
  unfold powerTerminalTolerance
  have hcq :
      0 < cq kappa q := by
    unfold cq
    exact div_pos (sub_pos.mpr hqa)
      (mul_pos (mul_pos (by norm_num) hk.1) hq0)
  have hx :
      0 < cq kappa q * linearLambda q R :=
    mul_pos hcq (linearLambda_pos hq0 R)
  have hden : 0 < 2 * (1 + cq kappa q * linearLambda q R) := by
    positivity
  rw [div_le_iff₀ hden]
  nlinarith

theorem powerTerminalTolerance_le_cap
    {kappa q : ℝ}
    (hk : KappaAdmissible kappa)
    (hq0 : 0 < q) (hqa : a0 < q) (R : ℕ) :
    powerTerminalTolerance kappa q R ≤
      cq kappa q * linearLambda q R := by
  unfold powerTerminalTolerance
  have hcq :
      0 < cq kappa q := by
    unfold cq
    exact div_pos (sub_pos.mpr hqa)
      (mul_pos (mul_pos (by norm_num) hk.1) hq0)
  have hx :
      0 < cq kappa q * linearLambda q R :=
    mul_pos hcq (linearLambda_pos hq0 R)
  have hden : 0 < 2 * (1 + cq kappa q * linearLambda q R) := by
    positivity
  rw [div_le_iff₀ hden]
  nlinarith [sq_nonneg (cq kappa q * linearLambda q R)]

theorem powerToleranceBaseConstant_pos
    {kappa q : ℝ}
    (hk : KappaAdmissible kappa)
    (hq0 : 0 < q) (hqa : a0 < q) :
    0 < powerToleranceBaseConstant kappa q := by
  unfold powerToleranceBaseConstant
  have hcq :
      0 < cq kappa q := by
    unfold cq
    exact div_pos (sub_pos.mpr hqa)
      (mul_pos (mul_pos (by norm_num) hk.1) hq0)
  have hden : 0 < 2 * (1 + cq kappa q) := by positivity
  exact mul_pos (div_pos hcq hden) a0_pos

theorem powerToleranceConstant_pos
    {kappa q : ℝ}
    (hk : KappaAdmissible kappa)
    (hq0 : 0 < q) (hqa : a0 < q) :
    0 < powerToleranceConstant kappa q := by
  unfold powerToleranceConstant
  exact mul_pos (powerToleranceBaseConstant_pos hk hq0 hqa) hq0

theorem powerTerminalTolerance_lower
    {kappa q : ℝ}
    (hk : KappaAdmissible kappa)
    (hq0 : 0 < q) (hqa : a0 < q) (hq1 : q < 1)
    (R : ℕ) :
    powerToleranceBaseConstant kappa q * q ^ R ≤
      powerTerminalTolerance kappa q R := by
  have hcq :
      0 < cq kappa q := by
    unfold cq
    exact div_pos (sub_pos.mpr hqa)
      (mul_pos (mul_pos (by norm_num) hk.1) hq0)
  have hlam0 := linearLambda_pos hq0 R
  have hlam1 := (linearLambda_lt_one hq0 hq1 R).le
  unfold powerTerminalTolerance powerToleranceBaseConstant linearLambda
  dsimp only
  have hden0 : 0 < 2 * (1 + cq kappa q) := by positivity
  have hdenR0 :
      0 < 2 * (1 + cq kappa q * (a0 * q ^ R)) := by
    positivity
  have hmul :
      cq kappa q * (a0 * q ^ R) ≤ cq kappa q :=
    (mul_le_mul_of_nonneg_left hlam1 hcq.le).trans_eq (mul_one _)
  calc
    cq kappa q / (2 * (1 + cq kappa q)) * a0 * q ^ R =
        cq kappa q * (a0 * q ^ R) /
          (2 * (1 + cq kappa q)) := by ring
    _ ≤ cq kappa q * (a0 * q ^ R) /
          (2 * (1 + cq kappa q * (a0 * q ^ R))) := by
      rw [div_le_div_iff₀ hden0 hdenR0]
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg hcq.le hlam0.le)
      nlinarith [hmul]

theorem powerTerminalTolerance_schedule_lower
    {kappa q s : ℝ}
    (hk : KappaAdmissible kappa)
    (hq0 : 0 < q) (hqa : a0 < q) (hq1 : q < 1)
    (hs : 0 < s) (M : ℕ) :
    powerToleranceConstant kappa q *
        powerShellScale M ^ (-powerU q s) ≤
      powerTerminalTolerance kappa q (powerStageCount s M) := by
  have ht :=
    powerTerminalTolerance_lower hk hq0 hqa hq1
      (powerStageCount s M)
  have hqpow := power_q_pow_lower hq0 hq1 hs M
  have hK0 := (powerToleranceConstant_pos hk hq0 hqa).le
  unfold powerToleranceConstant
  calc
    powerToleranceBaseConstant kappa q * q *
          powerShellScale M ^ (-powerU q s)
        = powerToleranceBaseConstant kappa q *
            (q * powerShellScale M ^ (-powerU q s)) := by ring
    _ ≤ powerToleranceBaseConstant kappa q *
          q ^ powerStageCount s M :=
      mul_le_mul_of_nonneg_left hqpow
        (powerToleranceBaseConstant_pos hk hq0 hqa).le
    _ ≤ powerTerminalTolerance kappa q (powerStageCount s M) := ht

theorem powerTerminalTolerance_schedule_upper
    {kappa q s : ℝ}
    (hk : KappaAdmissible kappa)
    (hq0 : 0 < q) (hqa : a0 < q) (hq1 : q < 1)
    (hs : 0 < s) (M : ℕ) :
    powerTerminalTolerance kappa q (powerStageCount s M) ≤
      cq kappa q * a0 *
        powerShellScale M ^ (-powerU q s) := by
  have ht :=
    powerTerminalTolerance_le_cap hk hq0 hqa
      (powerStageCount s M)
  have hqpow := power_q_pow_upper hq0 hq1 hs M
  have hcq0 :
      0 ≤ cq kappa q := by
    unfold cq
    exact div_nonneg (sub_nonneg.mpr hqa.le)
      (mul_nonneg (mul_nonneg (by norm_num) hk.1.le) hq0.le)
  unfold linearLambda at ht
  calc
    powerTerminalTolerance kappa q (powerStageCount s M)
        ≤ cq kappa q * (a0 * q ^ powerStageCount s M) := ht
    _ ≤ cq kappa q *
          (a0 * powerShellScale M ^ (-powerU q s)) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hqpow a0_pos.le) hcq0
    _ = cq kappa q * a0 *
          powerShellScale M ^ (-powerU q s) := by ring

theorem powerTerminalTolerance_tendsto_zero
    {kappa q s : ℝ}
    (hk : KappaAdmissible kappa)
    (hq0 : 0 < q) (hqa : a0 < q) (hq1 : q < 1)
    (hs : 0 < s) :
    Filter.Tendsto
      (fun M =>
        powerTerminalTolerance kappa q (powerStageCount s M))
      Filter.atTop (nhds 0) := by
  have hu := powerU_pos hq0 hq1 hs
  have hmodel :
      Filter.Tendsto
        (fun M =>
          cq kappa q * a0 *
            powerShellScale M ^ (-powerU q s))
        Filter.atTop (nhds 0) := by
      simpa [Function.comp_apply] using
        ((tendsto_rpow_neg_atTop hu).comp
          powerShellScale_tendsto_atTop).const_mul (cq kappa q * a0)
  exact squeeze_zero
    (fun M => (powerTerminalTolerance_pos hk hq0 hqa _).le)
    (fun M => powerTerminalTolerance_schedule_upper
      hk hq0 hqa hq1 hs M)
    hmodel

theorem powerDensityConstant_pos
    {q transport kappa : ℝ}
    (hk : KappaAdmissible kappa)
    (hq0 : 0 < q) (hqa : a0 < q)
    (htransport : 0 < transport) :
    0 < powerDensityConstant q transport kappa := by
  unfold powerDensityConstant
  exact mul_pos
      (mul_pos
      (div_pos Terras.maximalBarrierC0_pos
        (Real.log_pos (by norm_num)))
      (sq_pos_of_pos (powerToleranceBaseConstant_pos hk hq0 hqa)))
    (mul_pos
      (mul_pos htransport (sq_pos_of_pos hk.1))
      (sq_pos_of_pos hq0))

theorem power_combined_base_pos
    {q transport kappa : ℝ}
    (hq0 : 0 < q) (htransport : 0 < transport)
    (hk : KappaAdmissible kappa) :
    0 < transport * kappa ^ 2 * q ^ 2 := by
  exact mul_pos
    (mul_pos htransport (sq_pos_of_pos hk.1))
    (sq_pos_of_pos hq0)

theorem power_combined_base_lt_one
    {q transport kappa : ℝ}
    (hq0 : 0 < q) (hq1 : q < 1)
    (htransport0 : 0 < transport) (htransport1 : transport < 1)
    (hk : KappaAdmissible kappa) :
    transport * kappa ^ 2 * q ^ 2 < 1 := by
  have hk1 := kappa_lt_one hk
  have hk2 : kappa ^ 2 < 1 := by
    nlinarith [mul_pos hk.1 (sub_pos.mpr hk1)]
  have hq2 : q ^ 2 < 1 := by
    nlinarith [mul_pos hq0 (sub_pos.mpr hq1)]
  have htk :
      transport * kappa ^ 2 < 1 := by
    calc
      transport * kappa ^ 2 < 1 * kappa ^ 2 :=
        mul_lt_mul_of_pos_right htransport1 (sq_pos_of_pos hk.1)
      _ < 1 := by simpa using hk2
  calc
    transport * kappa ^ 2 * q ^ 2 < 1 * q ^ 2 :=
      mul_lt_mul_of_pos_right htk (sq_pos_of_pos hq0)
    _ < 1 := by simpa using hq2

theorem power_combined_pow_lower
    {q transport kappa s : ℝ}
    (hq0 : 0 < q) (hq1 : q < 1)
    (htransport0 : 0 < transport) (htransport1 : transport < 1)
    (hk : KappaAdmissible kappa)
    (hs : 0 < s) (M : ℕ) :
    (transport * kappa ^ 2 * q ^ 2) *
        powerShellScale M ^ (-powerW q transport kappa s) ≤
      (transport * kappa ^ 2 * q ^ 2) ^
        powerStageCount s M := by
  let r := transport * kappa ^ 2 * q ^ 2
  have hr0 : 0 < r :=
    power_combined_base_pos hq0 htransport0 hk
  have hr1 : r < 1 :=
    power_combined_base_lt_one hq0 hq1
      htransport0 htransport1 hk
  have hR := (powerStageCount_bounds hs M).2.le
  have hid :
      r ^ (s * powerShellLog M) =
        powerShellScale M ^
          (-powerW q transport kappa s) := by
    rw [power_base_identity hr0]
    unfold r powerW
    rw [show Real.log
        (1 / (transport * kappa ^ 2 * q ^ 2)) =
          -Real.log (transport * kappa ^ 2 * q ^ 2) by
      rw [one_div, Real.log_inv]]
    congr 1
    ring
  rw [← Real.rpow_natCast, ← hid]
  have hpow :
      r ^ (s * powerShellLog M + 1) ≤
        r ^ (powerStageCount s M : ℝ) :=
    Real.rpow_le_rpow_of_exponent_ge hr0 hr1.le hR
  rw [Real.rpow_add hr0, Real.rpow_one] at hpow
  simpa [r, mul_comm] using hpow

/-- The terminal density exponent has a fixed power-law lower bound. -/
theorem linearD_power_lower
    {q transport kappa s : ℝ}
    (hq0 : 0 < q) (hqa : a0 < q) (hq1 : q < 1)
    (htransport0 : 0 < transport) (htransport1 : transport < 1)
    (hk : KappaAdmissible kappa)
    (hs : 0 < s) (M : ℕ) :
    powerDensityConstant q transport kappa *
        powerShellScale M ^ (-powerW q transport kappa s) ≤
      linearD transport kappa (powerStageCount s M)
        (powerTerminalTolerance kappa q (powerStageCount s M))
        (powerStageCount s M) := by
  let R := powerStageCount s M
  let tR := powerTerminalTolerance kappa q R
  have htLower :=
    powerTerminalTolerance_lower hk hq0 hqa hq1 R
  have ht0 := powerTerminalTolerance_pos hk hq0 hqa R
  have hcombined :=
    power_combined_pow_lower hq0 hq1
      htransport0 htransport1 hk hs M
  have hwindow :
      linearD transport kappa R tR R =
        Terras.maximalBarrierC0 / Real.log 2 *
          tR ^ 2 *
          (transport * kappa ^ 2) ^ R := by
    rw [linearD_exact]
    simp only [linearD_zero, linearTolerance, Nat.sub_zero]
    unfold Terras.quadraticWindowDensityRate
    ring
  have htSq :
      (powerToleranceBaseConstant kappa q * q ^ R) ^ 2 ≤ tR ^ 2 := by
    simpa [pow_two] using
      mul_self_le_mul_self
        (mul_nonneg
          (powerToleranceBaseConstant_pos hk hq0 hqa).le
          (pow_nonneg hq0.le R))
        htLower
  rw [hwindow]
  have hcoef0 :
      0 ≤ Terras.maximalBarrierC0 / Real.log 2 :=
    (div_pos Terras.maximalBarrierC0_pos
      (Real.log_pos (by norm_num))).le
  have htk0 : 0 ≤ (transport * kappa ^ 2) ^ R := by positivity
  calc
    powerDensityConstant q transport kappa *
          powerShellScale M ^ (-powerW q transport kappa s)
        =
      (Terras.maximalBarrierC0 / Real.log 2) *
        (powerToleranceBaseConstant kappa q) ^ 2 *
        ((transport * kappa ^ 2 * q ^ 2) *
          powerShellScale M ^ (-powerW q transport kappa s)) := by
            unfold powerDensityConstant
            ring
    _ ≤
      (Terras.maximalBarrierC0 / Real.log 2) *
        (powerToleranceBaseConstant kappa q) ^ 2 *
        (transport * kappa ^ 2 * q ^ 2) ^ R := by
          gcongr
    _ =
      (Terras.maximalBarrierC0 / Real.log 2) *
        (powerToleranceBaseConstant kappa q * q ^ R) ^ 2 *
        (transport * kappa ^ 2) ^ R := by ring
    _ ≤
      (Terras.maximalBarrierC0 / Real.log 2) *
        tR ^ 2 * (transport * kappa ^ 2) ^ R := by
          gcongr

end

end OptimizedLinearPullback

end CollatzEndpointTransport
