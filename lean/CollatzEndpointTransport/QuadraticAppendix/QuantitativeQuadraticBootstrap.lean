/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik
-/
import CollatzEndpointTransport.QuadraticAppendix.QuantitativeQuadraticPullbackGlobal
import CollatzEndpointTransport.Common.TerrasMaximalInitialWindowDensity

/-!
# Quantitative Quadratic Bootstrap

Scalar arithmetic for the strengthened quadratic bootstrap.

MB3 and MB4 replace the old cubic density update by

  D_(j+1) = c * D_j^2.

This file formalizes the resulting recurrence, its majorant, and the exact
open endpoint

  log(1/a0) / log 2.
-/

namespace CollatzEndpointTransport

namespace QuantitativeDensity

open scoped Real Topology

noncomputable section

def quadraticUniformExponentConstant (cPull cWindow : ℝ) : ℝ :=
  min 1 (min cPull cWindow)

theorem quadraticUniformExponentConstant_pos
    {cPull cWindow : ℝ}
    (hPull : 0 < cPull) (hWindow : 0 < cWindow) :
    0 < quadraticUniformExponentConstant cPull cWindow := by
  simp [quadraticUniformExponentConstant, hPull, hWindow]

theorem quadraticUniformExponentConstant_le_one (cPull cWindow : ℝ) :
    quadraticUniformExponentConstant cPull cWindow ≤ 1 :=
  min_le_left _ _

theorem quadraticUniformExponentStep
    {D t cPull cWindow : ℝ}
    (hD : 0 ≤ D) (hDt : D ≤ t)
    (hWindow : 0 < cWindow) :
    let c := quadraticUniformExponentConstant cPull cWindow
    c * D ^ 2 ≤ cPull * D ^ 2 ∧
      c * D ^ 2 ≤ cWindow * t ^ 2 := by
  intro c
  have hD2 : 0 ≤ D ^ 2 := sq_nonneg D
  have hDt2 : D ^ 2 ≤ t ^ 2 :=
    pow_le_pow_left₀ hD hDt 2
  have hcPull : c ≤ cPull :=
    le_trans (min_le_right _ _) (min_le_left _ _)
  have hcWindow : c ≤ cWindow :=
    le_trans (min_le_right _ _) (min_le_right _ _)
  constructor
  · exact mul_le_mul_of_nonneg_right hcPull hD2
  · calc
      c * D ^ 2 ≤ cWindow * D ^ 2 :=
        mul_le_mul_of_nonneg_right hcWindow hD2
      _ ≤ cWindow * t ^ 2 :=
        mul_le_mul_of_nonneg_left hDt2 hWindow.le

/-- The quadratic update preserves `0 <= D_next <= D <= t_next`. -/
theorem quadraticExponentInvariantStep
    {D t tNext c : ℝ}
    (hD : 0 ≤ D) (hD1 : D ≤ 1)
    (hDt : D ≤ t) (httNext : t ≤ tNext)
    (hc : 0 ≤ c) (hc1 : c ≤ 1) :
    0 ≤ c * D ^ 2 ∧
      c * D ^ 2 ≤ D ∧
      c * D ^ 2 ≤ tNext ∧
      c * D ^ 2 ≤ 1 := by
  have hD2 : 0 ≤ D ^ 2 := sq_nonneg D
  have hD2D : D ^ 2 ≤ D := by
    nlinarith [mul_nonneg hD (sub_nonneg.mpr hD1)]
  have hcD2 : c * D ^ 2 ≤ D ^ 2 := by simpa using mul_le_mul_of_nonneg_right hc1 hD2
  have hnextD := hcD2.trans hD2D
  exact ⟨mul_nonneg hc hD2, hnextD,
    hnextD.trans (hDt.trans httNext), hnextD.trans hD1⟩

/-- Exponent accumulated by `x_(n+1)=c*x_n^2`. -/
def quadraticWeight : ℕ → ℕ
  | 0 => 0
  | n + 1 => 2 * quadraticWeight n + 1

@[simp] theorem quadraticWeight_zero : quadraticWeight 0 = 0 := rfl

@[simp] theorem quadraticWeight_succ (n : ℕ) :
    quadraticWeight (n + 1) = 2 * quadraticWeight n + 1 := rfl

theorem quadraticWeight_add_one (n : ℕ) :
    quadraticWeight n + 1 = 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [quadraticWeight_succ, pow_succ]
      omega

/-- Exact solution of the quadratic exponent recurrence. -/
theorem quadraticRecurrence_exact
    (c D0 : ℝ) (D : ℕ → ℝ)
    (hD0 : D 0 = D0)
    (hstep : ∀ n, D (n + 1) = c * (D n) ^ 2) :
    ∀ n, D n = c ^ quadraticWeight n * D0 ^ (2 ^ n) := by
  intro n
  induction n with
  | zero => simp [hD0]
  | succ n ih =>
      rw [hstep, ih, quadraticWeight_succ, mul_pow]
      have hcPow :
          c * (c ^ quadraticWeight n) ^ 2 =
            c ^ (2 * quadraticWeight n + 1) := by
        rw [← pow_mul,
          show quadraticWeight n * 2 = 2 * quadraticWeight n by omega,
          pow_succ]
        ring
      have hDpow :
          (D0 ^ (2 ^ n)) ^ 2 = D0 ^ (2 ^ (n + 1)) := by
        rw [← pow_mul, pow_succ]
      calc
        c * ((c ^ quadraticWeight n) ^ 2 *
            (D0 ^ (2 ^ n)) ^ 2)
            = (c * (c ^ quadraticWeight n) ^ 2) *
                (D0 ^ (2 ^ n)) ^ 2 := by ring
        _ = c ^ (2 * quadraticWeight n + 1) *
              D0 ^ (2 ^ (n + 1)) := by rw [hcPow, hDpow]

/-- Quadratic majorant iteration. -/
theorem quadraticMajorant_iterate
    (A : ℝ) (Y : ℕ → ℝ)
    (hA : 0 ≤ A) (hY : ∀ n, 0 ≤ Y n)
    (hstep : ∀ n, Y (n + 1) ≤ A * (Y n) ^ 2) :
    ∀ n, Y n ≤
      A ^ quadraticWeight n * (Y 0) ^ (2 ^ n) := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      have hpow :
          (Y n) ^ 2 ≤
            (A ^ quadraticWeight n * (Y 0) ^ (2 ^ n)) ^ 2 :=
        pow_le_pow_left₀ (hY n) ih 2
      have hAPow :
          A * (A ^ quadraticWeight n) ^ 2 =
            A ^ (2 * quadraticWeight n + 1) := by
        rw [← pow_mul,
          show quadraticWeight n * 2 = 2 * quadraticWeight n by omega,
          pow_succ]
        ring
      have hYPow :
          ((Y 0) ^ (2 ^ n)) ^ 2 =
            (Y 0) ^ (2 ^ (n + 1)) := by
        rw [← pow_mul, pow_succ]
      calc
        Y (n + 1) ≤ A * (Y n) ^ 2 := hstep n
        _ ≤ A * (A ^ quadraticWeight n *
            (Y 0) ^ (2 ^ n)) ^ 2 :=
          mul_le_mul_of_nonneg_left hpow hA
        _ = (A * (A ^ quadraticWeight n) ^ 2) *
            ((Y 0) ^ (2 ^ n)) ^ 2 := by rw [mul_pow]; ring
        _ = A ^ quadraticWeight (n + 1) *
            (Y 0) ^ (2 ^ (n + 1)) := by
          rw [quadraticWeight_succ, hAPow, hYPow]

def quadraticAdmissibleExponent (q : ℝ) : ℝ :=
  Real.log (1 / q) / Real.log 2

def quadraticGammaExponent (q : ℝ) : ℝ :=
  Real.log 2 / Real.log (1 / q)

def quadraticHeadlineExponent : ℝ :=
  quadraticAdmissibleExponent a0

theorem log_two_pos : 0 < Real.log 2 :=
  Real.log_pos (by norm_num)

theorem quadraticAdmissibleExponent_pos
    {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    0 < quadraticAdmissibleExponent q :=
  div_pos (log_one_div_pos hq0 hq1) log_two_pos

theorem quadraticGammaExponent_pos
    {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    0 < quadraticGammaExponent q :=
  div_pos log_two_pos (log_one_div_pos hq0 hq1)

theorem quadraticAdmissibleExponent_strictAnti
    {q₁ q₂ : ℝ}
    (hq₁0 : 0 < q₁) (hq₁q₂ : q₁ < q₂) (_hq₂1 : q₂ < 1) :
    quadraticAdmissibleExponent q₂ <
      quadraticAdmissibleExponent q₁ := by
  have hq₂0 : 0 < q₂ := hq₁0.trans hq₁q₂
  have hinv : 1 / q₂ < 1 / q₁ :=
    one_div_lt_one_div_of_lt hq₁0 hq₁q₂
  have hlog : Real.log (1 / q₂) < Real.log (1 / q₁) :=
    Real.strictMonoOn_log
      (Set.mem_Ioi.mpr (one_div_pos.mpr hq₂0))
      (Set.mem_Ioi.mpr (one_div_pos.mpr hq₁0))
      hinv
  unfold quadraticAdmissibleExponent
  exact (div_lt_div_iff_of_pos_right log_two_pos).2 hlog

theorem quadraticAdmissibleExponent_lt_headline
    {q : ℝ} (hqa : a0 < q) (hq1 : q < 1) :
    quadraticAdmissibleExponent q < quadraticHeadlineExponent := by
  unfold quadraticHeadlineExponent
  exact quadraticAdmissibleExponent_strictAnti a0_pos hqa hq1

theorem quadraticHeadlineExponent_eq :
    quadraticHeadlineExponent =
      Real.log (2 / lg3) / Real.log 2 := by
  have harg : 1 / a0 = 2 / lg3 := by
    unfold a0
    field_simp [ne_of_gt lg3_pos]
  simp only [quadraticHeadlineExponent,
    quadraticAdmissibleExponent, harg]

theorem quadraticAdmissibleExponent_tendsto_headline :
    Filter.Tendsto quadraticAdmissibleExponent
      (nhdsWithin a0 (Set.Ioi a0))
      (nhds quadraticHeadlineExponent) := by
  have ha0ne : a0 ≠ 0 := ne_of_gt a0_pos
  have hlog2ne : Real.log 2 ≠ 0 := ne_of_gt log_two_pos
  have hinv : ContinuousAt (fun q : ℝ => 1 / q) a0 :=
    continuousAt_const.div continuousAt_id ha0ne
  have hlog : ContinuousAt (fun q : ℝ => Real.log (1 / q)) a0 :=
    hinv.log (one_div_ne_zero ha0ne)
  have hcont : ContinuousAt quadraticAdmissibleExponent a0 := by
    simpa only [quadraticAdmissibleExponent] using
      hlog.div continuousAt_const hlog2ne
  exact hcont.tendsto.mono_left inf_le_left

theorem quadraticAdmissibleExponent_mul_gamma
    {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    quadraticAdmissibleExponent q *
      quadraticGammaExponent q = 1 := by
  have hlogne : Real.log (1 / q) ≠ 0 :=
    ne_of_gt (log_one_div_pos hq0 hq1)
  have hlog2ne : Real.log 2 ≠ 0 := ne_of_gt log_two_pos
  unfold quadraticAdmissibleExponent quadraticGammaExponent
  field_simp

theorem quadraticExponentCondition_iff
    {a q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    a < quadraticAdmissibleExponent q ↔
      a * quadraticGammaExponent q < 1 := by
  have hgamma := quadraticGammaExponent_pos hq0 hq1
  have hid := quadraticAdmissibleExponent_mul_gamma hq0 hq1
  constructor
  · intro ha
    calc
      a * quadraticGammaExponent q <
          quadraticAdmissibleExponent q *
            quadraticGammaExponent q :=
        mul_lt_mul_of_pos_right ha hgamma
      _ = 1 := hid
  · intro ha
    by_contra hnot
    have hle : quadraticAdmissibleExponent q ≤ a :=
      le_of_not_gt hnot
    have hmul :
        quadraticAdmissibleExponent q *
            quadraticGammaExponent q ≤
          a * quadraticGammaExponent q :=
      mul_le_mul_of_nonneg_right hle hgamma.le
    rw [hid] at hmul
    linarith

end

end QuantitativeDensity

end CollatzEndpointTransport
