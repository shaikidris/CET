/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik
-/
import CollatzEndpointTransport.Common.QuantitativeDensityConstants
import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# Optimized Linear Pullback Constants

Scalar constants for the optimized fixed-total linear pullback.

This file formalizes the stable analytic layer of
`collatz_fixed_total_renyi_linear_pullback.md`:

* the exact nonlinear rate `psi`;
* its derivative and small-density slope;
* the parameterized envelope-loss condition;
* the exact linear density recurrence;
* the beta/delta bookkeeping used by the power schedule.

It does not assert the fixed-total endpoint moment theorem.  That finite
combinatorial dependency remains a separate formalization target.
-/

namespace CollatzEndpointTransport

namespace OptimizedLinearPullback

open scoped Real Topology

noncomputable section

/-- Exact parity-level rate
`-log ((1 + 3^(-D))/2)`, written using `exp` for differentiation. -/
def psi (D : ℝ) : ℝ :=
  -Real.log ((1 + Real.exp (-D * Real.log 3)) / 2)

@[simp] theorem psi_zero : psi 0 = 0 := by
  simp [psi]

theorem psi_inner_pos (D : ℝ) :
    0 < (1 + Real.exp (-D * Real.log 3)) / 2 := by
  positivity

theorem psi_pos {D : ℝ} (hD : 0 < D) :
    0 < psi D := by
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hexp :
      Real.exp (-D * Real.log 3) < 1 := by
    rw [Real.exp_lt_one_iff]
    nlinarith
  have hinner :
      (1 + Real.exp (-D * Real.log 3)) / 2 < 1 := by
    linarith
  unfold psi
  exact neg_pos.mpr (Real.log_neg (psi_inner_pos D) hinner)

/-- Exact first derivative of the nonlinear rate. -/
theorem hasDerivAt_psi (D : ℝ) :
    HasDerivAt psi
      (Real.log 3 * Real.exp (-D * Real.log 3) /
        (1 + Real.exp (-D * Real.log 3))) D := by
  have hlin :
      HasDerivAt (fun x : ℝ => -x * Real.log 3) (-Real.log 3) D := by
    convert (hasDerivAt_id D).neg.mul_const (Real.log 3) using 1
    ring
  have hexp :
      HasDerivAt (fun x : ℝ => Real.exp (-x * Real.log 3))
        ((-Real.log 3) * Real.exp (-D * Real.log 3)) D := by
    simpa [mul_comm] using hlin.exp
  have hinner :
      HasDerivAt
        (fun x : ℝ => (1 + Real.exp (-x * Real.log 3)) / 2)
        (((-Real.log 3) * Real.exp (-D * Real.log 3)) / 2) D := by
    convert (hasDerivAt_const D 1).add hexp |>.div_const 2 using 1
    ring
  have hlog :=
    hinner.log (ne_of_gt (psi_inner_pos D))
  change HasDerivAt
    (fun x : ℝ => -Real.log ((1 + Real.exp (-x * Real.log 3)) / 2))
    (Real.log 3 * Real.exp (-D * Real.log 3) /
      (1 + Real.exp (-D * Real.log 3))) D
  convert hlog.neg using 1
  field_simp [ne_of_gt (psi_inner_pos D)]
  ring

theorem deriv_psi_zero :
    deriv psi 0 = Real.log 3 / 2 := by
  rw [(hasDerivAt_psi 0).deriv]
  simp
  ring

/-- The critical small-density slope:
`psi(D)/D -> log(3)/2` from the right. -/
theorem tendsto_psi_div_zero_right :
    Filter.Tendsto (fun D : ℝ => psi D / D)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (Real.log 3 / 2)) := by
  have h :=
    (hasDerivAt_psi 0).tendsto_slope_zero_right
  convert h using 1 <;>
    norm_num [psi_zero, div_eq_mul_inv, mul_comm]

def uniformRateLimit : ℝ :=
  Real.log (3 / 2) / (3 * Real.log 2)

def asymptoticRateLimit : ℝ :=
  Real.log 3 / (6 * Real.log 2)

/-- The nonlinear pullback rate divided by `D` tends to the optimized
small-density transport constant. -/
theorem tendsto_normalizedRate_zero_right :
    Filter.Tendsto
      (fun D : ℝ => psi D / (3 * Real.log 2 * D))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds asymptoticRateLimit) := by
  have h :=
    tendsto_psi_div_zero_right.div_const (3 * Real.log 2)
  have hfun :
      (fun D : ℝ => psi D / (3 * Real.log 2 * D)) =
        (fun D : ℝ => (psi D / D) / (3 * Real.log 2)) := by
    funext D
    simp only [div_eq_mul_inv, mul_inv]
    ring
  have hlim :
      Real.log 3 / 2 / (3 * Real.log 2) = asymptoticRateLimit := by
    unfold asymptoticRateLimit
    ring_nf
  rw [hfun]
  rw [← hlim]
  exact h

theorem asymptoticRateLimit_pos :
    0 < asymptoticRateLimit := by
  unfold asymptoticRateLimit
  positivity

theorem asymptoticRateLimit_lt_one :
    asymptoticRateLimit < 1 := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog3lt : Real.log 3 < Real.log 4 :=
    Real.log_lt_log (by norm_num) (by norm_num)
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]
    norm_num
  unfold asymptoticRateLimit
  rw [div_lt_one (by positivity)]
  linarith

/-- The exact admissibility condition for the geometric tolerance ratio. -/
def KappaAdmissible (kappa : ℝ) : Prop :=
  0 < kappa ∧ 2 * kappa + kappa ^ 2 < 1

/-- A parameterized version of the one-step tolerance budget. -/
theorem tolerance_budget
    {kappa t : ℝ}
    (hk : KappaAdmissible kappa)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    2 * (kappa * t) + (kappa * t) ^ 2 ≤ t := by
  have ht2 : t ^ 2 ≤ t := by nlinarith [mul_nonneg ht0 (sub_nonneg.mpr ht1)]
  have hk20 : 0 ≤ kappa ^ 2 := sq_nonneg kappa
  have hquad : kappa ^ 2 * t ^ 2 ≤ kappa ^ 2 * t :=
    mul_le_mul_of_nonneg_left ht2 hk20
  have hcoef : (2 * kappa + kappa ^ 2) * t ≤ t :=
    mul_le_of_le_one_left ht0 hk.2.le
  nlinarith

/-- Exact endpoint-margin identity for arbitrary admissible `kappa`. -/
def cq (kappa q : ℝ) : ℝ :=
  (q - QuantitativeDensity.a0) / (4 * kappa * q)

theorem kappa_mul_cq_mul
    {kappa q : ℝ} (hk : 0 < kappa) (hq : 0 < q) :
    kappa * cq kappa q * q =
      (q - QuantitativeDensity.a0) / 4 := by
  unfold cq
  field_simp [ne_of_gt hk, ne_of_gt hq]
  ring

/-- Exact solution of `D_(j+1) = c D_j`. -/
theorem linearRecurrence_exact
    (c D0 : ℝ) (D : ℕ → ℝ)
    (hD0 : D 0 = D0)
    (hstep : ∀ j, D (j + 1) = c * D j) :
    ∀ j, D j = c ^ j * D0 := by
  intro j
  induction j with
  | zero => simpa using hD0
  | succ j ih =>
      rw [hstep, ih, pow_succ]
      ring

/-- Exponent paid by the geometric schedule. -/
def beta
    (q kappa transport : ℝ) : ℝ :=
  2 +
    Real.log (1 / (transport * kappa ^ 2)) /
      Real.log (1 / q)

/-- Admissible stretched-log exponent at fixed parameters. -/
def delta
    (q kappa transport : ℝ) : ℝ :=
  1 / (beta q kappa transport + 1)

theorem delta_condition_iff
    {q kappa transport d : ℝ}
    (hbeta : 0 < beta q kappa transport + 1) :
    d < delta q kappa transport ↔
      d * (beta q kappa transport + 1) < 1 := by
  unfold delta
  exact lt_div_iff₀ hbeta

end

end OptimizedLinearPullback

end CollatzEndpointTransport
