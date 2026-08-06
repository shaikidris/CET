/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik
-/
import CollatzEndpointTransport.Linear.FixedTotalNonlinearShell
import CollatzEndpointTransport.Common.ShellToGlobalDensity

/-!
# Optimized Linear Pullback Absorption

Absorption of the conservative polynomial endpoint-information loss.

The exact nonlinear shell estimate has rate `psi(D)/3` and a factor
`M^(3/2)`.  For any fixed `0 < eta < 1`, this file absorbs that polynomial
into the unused fraction `1-eta` of the exponential rate.  Retaining `eta`
as a parameter preserves the optimized small-density slope.
-/

namespace CollatzEndpointTransport

namespace OptimizedLinearPullback

open scoped Real

noncomputable section

/-- A quadratic polynomial is absorbed by any positive fraction of an
exponential rate. -/
theorem sq_mul_exp_neg_le
    {r eta x : ℝ}
    (hr : 0 < r) (heta0 : 0 < eta) (heta1 : eta < 1)
    (hx : 0 ≤ x) :
    x ^ 2 * Real.exp (-r * x) ≤
      2 * (((1 - eta) * r)⁻¹) ^ 2 *
        Real.exp (-(eta * r) * x) := by
  let a := (1 - eta) * r
  have ha : 0 < a := by
    unfold a
    exact mul_pos (sub_pos.mpr heta1) hr
  have hquad :
      (a * x) ^ 2 ≤ 2 * Real.exp (a * x) := by
    have h :=
      Real.quadratic_le_exp_of_nonneg
        (mul_nonneg ha.le hx)
    nlinarith
  calc
    x ^ 2 * Real.exp (-r * x) =
        2 * (a⁻¹) ^ 2 *
            ((a * x) ^ 2 / 2) *
          Real.exp (-r * x) := by
      field_simp [ne_of_gt ha]
      ring
    _ ≤
        2 * (a⁻¹) ^ 2 *
            Real.exp (a * x) *
          Real.exp (-r * x) := by
      gcongr
      nlinarith
    _ =
        2 * (((1 - eta) * r)⁻¹) ^ 2 *
          Real.exp (-(eta * r) * x) := by
      unfold a
      rw [show
        2 * (((1 - eta) * r)⁻¹) ^ 2 *
              Real.exp ((1 - eta) * r * x) *
              Real.exp (-r * x) =
          2 * (((1 - eta) * r)⁻¹) ^ 2 *
            (Real.exp ((1 - eta) * r * x) *
              Real.exp (-r * x)) by ring]
      rw [← Real.exp_add]
      congr 2
      ring

theorem psi_lt_log_two (D : ℝ) :
    psi D < Real.log 2 := by
  have hhalf : (0 : ℝ) < 1 / 2 := by norm_num
  have hinner := psi_inner_pos D
  have hlt :
      (1 / 2 : ℝ) <
        (1 + Real.exp (-D * Real.log 3)) / 2 := by
    have := Real.exp_pos (-D * Real.log 3)
    linarith
  have hlog :=
    Real.strictMonoOn_log hhalf hinner hlt
  have hlogHalf :
      Real.log (1 / 2 : ℝ) = -Real.log 2 := by
    rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num,
      Real.log_inv]
  unfold psi
  rw [hlogHalf] at hlog
  linarith

/-- Exponential shell rate retained after polynomial absorption. -/
def shellRate (eta D : ℝ) : ℝ :=
  eta * (psi D / 3)

/-- Explicit shell prefactor.  The added `1` handles the zero shell. -/
def shellConstant (C eta D : ℝ) : ℝ :=
  1 + C +
    36 * ((((1 - eta) * (psi D / 3))⁻¹) ^ 2)

theorem shellRate_pos
    {eta D : ℝ} (heta : 0 < eta) (hD : 0 < D) :
    0 < shellRate eta D := by
  unfold shellRate
  exact mul_pos heta (div_pos (psi_pos hD) (by norm_num))

theorem shellRate_lt_log_two
    {eta D : ℝ}
    (heta0 : 0 < eta) (heta1 : eta < 1) (hD : 0 < D) :
    shellRate eta D < Real.log 2 := by
  have hpsi := psi_pos hD
  have hpsiLt := psi_lt_log_two D
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  unfold shellRate
  have hr : 0 < psi D / 3 := div_pos hpsi (by norm_num)
  have hetaRate : eta * (psi D / 3) < psi D / 3 :=
    mul_lt_of_lt_one_left hr heta1
  nlinarith

theorem shellConstant_pos
    {C eta D : ℝ}
    (hC : 0 < C) :
    0 < shellConstant C eta D := by
  unfold shellConstant
  nlinarith [sq_nonneg ((((1 - eta) * (psi D / 3))⁻¹))]

/-- Uniform absorbed shell proportion. -/
theorem sourceEndpointBad_div_pow_le_absorbed
    {S : Set ℕ} {C D eta : ℝ}
    (hS : QuantitativeDensity.IsCDDense S C D)
    (heta0 : 0 < eta) (heta1 : eta < 1)
    (M : ℕ) :
    ((FixedTotal.sourceEndpointBad S M).card : ℝ) /
        (2 ^ M : ℝ) ≤
      shellConstant C eta D *
        Real.exp (-shellRate eta D * M) := by
  by_cases hM0 : M = 0
  · subst M
    have hcard :
        ((FixedTotal.sourceEndpointBad S 0).card : ℝ) ≤ 1 := by
      have hnat :
          (FixedTotal.sourceEndpointBad S 0).card ≤
            Fintype.card (FixedTotal.SourceCode 0) := by
        exact Finset.card_le_univ _
      simpa [FixedTotal.SourceCode] using hnat
    simp only [pow_zero, Nat.cast_one, div_one, Nat.cast_zero,
      mul_zero, neg_zero, Real.exp_zero, mul_one]
    exact hcard.trans (by
      unfold shellConstant
      nlinarith [hS.C_pos,
        sq_nonneg ((((1 - eta) * (psi D / 3))⁻¹))])
  · have hM : 1 ≤ M := Nat.one_le_iff_ne_zero.mpr hM0
    have hpsi : 0 < psi D := psi_pos hS.D_pos
    let r := psi D / 3
    have hr : 0 < r := by unfold r; positivity
    have hsqrtM : Real.sqrt M ≤ (M : ℝ) := by
      rw [Real.sqrt_le_iff]
      constructor
      · positivity
      · have hMr : (1 : ℝ) ≤ M := by exact_mod_cast hM
        nlinarith
    have hsqrt3 : Real.sqrt 3 ≤ 2 := by
      rw [Real.sqrt_le_iff]
      norm_num
    have hpoly :
        9 * Real.sqrt 3 * (M : ℝ) * Real.sqrt M ≤
          18 * (M : ℝ) ^ 2 := by
      nlinarith [mul_le_mul hsqrt3 hsqrtM (by positivity) (by positivity)]
    have habsorb :=
      sq_mul_exp_neg_le hr heta0 heta1
        (show 0 ≤ (M : ℝ) by positivity)
    have hq :
        Real.exp (-D * Real.log 3) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
      nlinarith [hS.D_pos]
    have hbase :=
      FixedTotal.sourceEndpointBad_div_pow_le_nonlinear hS M hM
    calc
      ((FixedTotal.sourceEndpointBad S M).card : ℝ) /
          (2 ^ M : ℝ) ≤
        (C * Real.exp (-D * Real.log 3) +
            9 * Real.sqrt 3 * (M : ℝ) * Real.sqrt M) *
          Real.exp (-r * M) := by
        simpa [r] using hbase
      _ ≤
        (C + 18 * (M : ℝ) ^ 2) *
          Real.exp (-r * M) := by
        gcongr
        · exact mul_le_of_le_one_right hS.C_pos.le hq
      _ =
        C * Real.exp (-r * M) +
          18 * ((M : ℝ) ^ 2 * Real.exp (-r * M)) := by
        ring
      _ ≤
        C * Real.exp (-(eta * r) * M) +
          36 * ((((1 - eta) * r)⁻¹) ^ 2) *
            Real.exp (-(eta * r) * M) := by
        apply add_le_add
        · have hetaRate : eta * r ≤ r := by
            exact mul_le_of_le_one_left hr.le heta1.le
          have hexp :
              Real.exp (-r * (M : ℝ)) ≤
                Real.exp (-(eta * r) * M) := by
            apply Real.exp_le_exp.mpr
            have hMr : 0 ≤ (M : ℝ) := by positivity
            nlinarith
          exact mul_le_mul_of_nonneg_left hexp hS.C_pos.le
        · calc
            18 * ((M : ℝ) ^ 2 * Real.exp (-r * M)) ≤
                18 *
                  (2 * (((1 - eta) * r)⁻¹) ^ 2 *
                    Real.exp (-(eta * r) * M)) :=
              mul_le_mul_of_nonneg_left habsorb (by norm_num)
            _ =
                36 * (((1 - eta) * r)⁻¹) ^ 2 *
                  Real.exp (-(eta * r) * M) := by ring
      _ ≤
        shellConstant C eta D *
          Real.exp (-shellRate eta D * M) := by
        unfold shellConstant shellRate
        unfold r
        have hexp : 0 < Real.exp
            (-(eta * (psi D / 3)) * (M : ℝ)) :=
          Real.exp_pos _
        nlinarith

end

end OptimizedLinearPullback

end CollatzEndpointTransport
