/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik
-/
import Mathlib

/-!
# Quantitative Transport Constants

Constants of the quantitative endpoint-transport bootstrap.

This file promotes those three audit gates from 40-digit numerical checks to
theorems. Everything here is pure real arithmetic: no density, no measure
theory, no borrowed analytic input.

The constants are

  a_0   = (log_2 3)/2        the one-block drift exponent,
  b     = 1 - a_0            the per-step drift of the (sqrt 3)/2 approximation,
  kappa = 1/(8(2 + log_2 3)) the bootstrap tolerance scale,
  L_0   = 1/(4(1 + 1/b))     the terminal-window scale.

The design identities `kappa * (1 + a_0) = 1/16` and `L_0 * (1 + 1/b) = 1/4`
are exact, not approximate; they are what make the one-step loss inequalities
close.
-/

namespace CollatzEndpointTransport

namespace QuantitativeDensity

/-- `log_2 3`, written once so the algebra below stays readable. -/
noncomputable def lg3 : ℝ := Real.logb 2 3

theorem lg3_pos : 0 < lg3 := Real.logb_pos (by norm_num) (by norm_num)

theorem lg3_lt_two : lg3 < 2 := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h34 : Real.log 3 < Real.log 4 :=
    Real.log_lt_log (by norm_num) (by norm_num)
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]
    push_cast
    ring
  unfold lg3 Real.logb
  rw [div_lt_iff₀ hlog2]
  linarith

/-- `a_0 = (log_2 3)/2`. -/
noncomputable def a0 : ℝ := lg3 / 2

/-- `b = 1 - a_0`, the per-step drift. -/
noncomputable def bConst : ℝ := 1 - a0

/-- `kappa = 1/(8(2 + log_2 3))`. -/
noncomputable def kappa : ℝ := 1 / (8 * (2 + lg3))

/-- `L_0 = 1/(4(1 + 1/b))`. -/
noncomputable def L0 : ℝ := 1 / (4 * (1 + 1 / bConst))

theorem two_add_lg3_pos : 0 < 2 + lg3 := by have := lg3_pos; linarith

theorem a0_pos : 0 < a0 := by have := lg3_pos; unfold a0; linarith

theorem a0_lt_one : a0 < 1 := by have := lg3_lt_two; unfold a0; linarith

theorem bConst_pos : 0 < bConst := by have := a0_lt_one; unfold bConst; linarith

theorem bConst_lt_one : bConst < 1 := by have := a0_pos; unfold bConst; linarith

theorem kappa_pos : 0 < kappa := by
  have h := two_add_lg3_pos
  unfold kappa
  exact div_pos one_pos (by linarith)

/-! ### Gate A: the design identities -/

/-- **Design identity 1.** `kappa` is chosen exactly so that
`kappa * (1 + a_0) = 1/16`. This is what makes the orbit-loss inequality
close, and it identifies `1/(8(2 + log_2 3))` as the real definition: the
`min` with `1/16` in the source note is never active. -/
theorem kappa_mul_one_add_a0 : kappa * (1 + a0) = 1 / 16 := by
  have h : (2 : ℝ) + lg3 ≠ 0 := ne_of_gt two_add_lg3_pos
  unfold kappa a0
  field_simp
  ring

/-- **Design identity 2.** `L_0 * (1 + 1/b) = 1/4`, which makes the exponent
paid by the shortcut steps come out as exactly `eps/4`. -/
theorem L0_mul_one_add_inv_bConst : L0 * (1 + 1 / bConst) = 1 / 4 := by
  have hb : (0 : ℝ) < bConst := bConst_pos
  have hbne : bConst ≠ 0 := ne_of_gt hb
  have hinv : (0 : ℝ) < 1 / bConst := div_pos one_pos hb
  have h1 : bConst + 1 ≠ 0 := by linarith
  unfold L0
  field_simp
  ring

/-- **Design identity 3.** `b` is exactly the per-step drift of the
`(sqrt 3)/2` approximation: `b = -log_2 ((sqrt 3)/2)`. This is why the window
length is `K = floor (M / b)`, matching the drift-optimal logarithmic horizon. -/
theorem bConst_eq_neg_logb_sqrt :
    bConst = -Real.logb 2 (Real.sqrt 3 / 2) := by
  have hs : Real.sqrt 3 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  have hlog : Real.log (Real.sqrt 3) = Real.log 3 / 2 :=
    Real.log_sqrt (by norm_num)
  have hl2 : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  unfold bConst a0 lg3
  simp only [Real.logb]
  rw [Real.log_div hs (by norm_num), hlog]
  field_simp
  ring

/-! ### Gate B: the two one-step loss inequalities -/

theorem kappa_lt_sixteenth : kappa < 1 / 16 := by
  have h := lg3_pos
  have hp := two_add_lg3_pos
  unfold kappa
  rw [div_lt_div_iff₀ (by linarith) (by norm_num)]
  linarith

/-- **Orbit loss.** With `delta = zeta = kappa * t`, the orbit exponent loses
`delta + a_0 * zeta + delta * zeta`, and this is below `t/2`.

This is `(1 + delta)(1 + zeta) - b * zeta`, expanded using `1 - b = a_0`. -/
theorem orbit_loss_lt_half {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) :
    kappa * t + a0 * (kappa * t) + kappa * t * (kappa * t) < t / 2 := by
  have hk := kappa_pos
  have hklt := kappa_lt_sixteenth
  have hkt : 0 < kappa * t := mul_pos hk ht0
  have hlin : kappa * t + a0 * (kappa * t) = t / 16 := by
    linear_combination t * kappa_mul_one_add_a0
  have hkt16 : kappa * t < t / 16 := by nlinarith
  have hsq : kappa * t * (kappa * t) < t / 4 := by nlinarith
  linarith

/-- **Correction loss.** The correction exponent loses at most
`max delta ((1 + delta) * zeta + delta * log_2 3)`; the second argument
dominates, and it too is below `t/2`.

The two terms are `m^delta` and
`3^delta * m^((1 + delta) zeta + delta log_2 3)`. -/
theorem correction_loss_lt_half {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) :
    (1 + kappa * t) * (kappa * t) + kappa * t * lg3 < t / 2 := by
  have hk := kappa_pos
  have hklt := kappa_lt_sixteenth
  have hl0 := lg3_pos
  have hp := two_add_lg3_pos
  have hkt : 0 < kappa * t := mul_pos hk ht0
  have hkt16 : kappa * t < t / 16 := by nlinarith
  -- kappa * (1 + lg3) < 1/8 because (1 + lg3)/(2 + lg3) < 1
  have hcoef : kappa * (1 + lg3) < 1 / 8 := by
    unfold kappa
    rw [div_mul_eq_mul_div, one_mul, div_lt_div_iff₀ (by linarith) (by norm_num)]
    linarith
  have hmain : kappa * t * (1 + lg3) < t / 8 := by nlinarith
  have hsq : kappa * t * (kappa * t) < t / 8 := by nlinarith
  nlinarith

/-! ### Gate C: the `c_q` algebra -/

/-- `c_q = (q - a_0) / (4 * kappa * q)`. -/
noncomputable def cq (q : ℝ) : ℝ := (q - a0) / (4 * kappa * q)

/-- **The `c_q` identity.** At the cap `t = c_q * lambda_(j+1)` with
`lambda_(j+1) = q * lambda_j`, the tolerance `delta = kappa * t` equals
exactly `lambda_j * (q - a_0) / 4`. -/
theorem kappa_mul_cq_mul (q : ℝ) (hq : 0 < q) :
    kappa * cq q * q = (q - a0) / 4 := by
  have hk : kappa ≠ 0 := ne_of_gt kappa_pos
  have hq' : q ≠ 0 := ne_of_gt hq
  unfold cq
  field_simp
  ring

/-- `c_q > 0` exactly when `q > a_0`, the standing contraction constraint. -/
theorem cq_pos {q : ℝ} (hq : 0 < q) (hqa : a0 < q) : 0 < cq q := by
  have hk := kappa_pos
  unfold cq
  exact div_pos (by linarith) (by nlinarith)

/-- **The cap clears the requirement.** The bootstrap needs
`delta <= lambda (q - a_0) / (2 (1 - lambda))`; the cap supplies
`lambda (q - a_0) / 4`. Since `0 < lambda < 1`, the cap is strictly smaller,
so it clears the requirement by a factor of at least two, uniformly in `j`. -/
theorem cap_clears_requirement
    {lam q : ℝ} (hlam0 : 0 < lam) (hlam1 : lam < 1) (hqa : a0 < q) :
    lam * (q - a0) / 4 < lam * (q - a0) / (2 * (1 - lam)) := by
  have hnum : 0 < lam * (q - a0) := mul_pos hlam0 (by linarith)
  have hden : 0 < 2 * (1 - lam) := by linarith
  rw [div_lt_div_iff₀ (by norm_num) hden]
  nlinarith

/-! ### Gates D and F: the endpoint exponent -/

/-- The admissible exponent at a fixed bootstrap ratio `q`. -/
noncomputable def admissibleExponent (q : ℝ) : ℝ :=
  Real.log (1 / q) / Real.log 3

/-- The headline endpoint approached as `q -> a_0` from above. -/
noncomputable def headlineExponent : ℝ :=
  admissibleExponent a0

/-- `gamma(q)`, the cubic-bootstrap loss exponent. -/
noncomputable def gammaExponent (q : ℝ) : ℝ :=
  Real.log 3 / Real.log (1 / q)

theorem log_three_pos : 0 < Real.log 3 :=
  Real.log_pos (by norm_num)

theorem log_one_div_pos {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    0 < Real.log (1 / q) := by
  apply Real.log_pos
  rw [one_div]
  exact (one_lt_inv₀ hq0).2 hq1

theorem admissibleExponent_pos {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    0 < admissibleExponent q := by
  exact div_pos (log_one_div_pos hq0 hq1) log_three_pos

theorem gammaExponent_pos {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    0 < gammaExponent q := by
  exact div_pos log_three_pos (log_one_div_pos hq0 hq1)

/-- `a_max(q)` is strictly decreasing on `(0,1)`. -/
theorem admissibleExponent_strictAnti
    {q₁ q₂ : ℝ} (hq₁0 : 0 < q₁) (hq₁q₂ : q₁ < q₂) (_hq₂1 : q₂ < 1) :
    admissibleExponent q₂ < admissibleExponent q₁ := by
  have hq₂0 : 0 < q₂ := lt_trans hq₁0 hq₁q₂
  have hinv : 1 / q₂ < 1 / q₁ :=
    one_div_lt_one_div_of_lt hq₁0 hq₁q₂
  have hlog : Real.log (1 / q₂) < Real.log (1 / q₁) :=
    Real.strictMonoOn_log
      (by exact Set.mem_Ioi.mpr (one_div_pos.mpr hq₂0))
      (by exact Set.mem_Ioi.mpr (one_div_pos.mpr hq₁0))
      hinv
  unfold admissibleExponent
  exact (div_lt_div_iff_of_pos_right log_three_pos).2 hlog

/-- Every admissible `q > a_0` gives a strict exponent below the headline
constant. -/
theorem admissibleExponent_lt_headline
    {q : ℝ} (hqa : a0 < q) (hq1 : q < 1) :
    admissibleExponent q < headlineExponent := by
  unfold headlineExponent
  exact admissibleExponent_strictAnti a0_pos hqa hq1

/-- Independent algebraic form of the headline constant:
`log(1/a_0)/log 3 = log(2/log_2 3)/log 3`. -/
theorem headlineExponent_eq :
    headlineExponent = Real.log (2 / lg3) / Real.log 3 := by
  have hlg3 : lg3 ≠ 0 := ne_of_gt lg3_pos
  have harg : 1 / a0 = 2 / lg3 := by
    unfold a0
    field_simp
  simp only [headlineExponent, admissibleExponent, harg]

/-- Gate D in endpoint form: the admissible exponents converge to the
headline constant as `q -> a_0` from above. Together with
`admissibleExponent_lt_headline`, this is the exact open-interval supremum
statement. -/
theorem admissibleExponent_tendsto_headline :
    Filter.Tendsto admissibleExponent
      (nhdsWithin a0 (Set.Ioi a0)) (nhds headlineExponent) := by
  have ha0ne : a0 ≠ 0 := ne_of_gt a0_pos
  have hlog3ne : Real.log 3 ≠ 0 := ne_of_gt log_three_pos
  have hinv : ContinuousAt (fun q : ℝ => 1 / q) a0 := by
    exact continuousAt_const.div continuousAt_id ha0ne
  have hlog : ContinuousAt (fun q : ℝ => Real.log (1 / q)) a0 :=
    hinv.log (one_div_ne_zero ha0ne)
  have hcont : ContinuousAt admissibleExponent a0 := by
    simpa only [admissibleExponent] using hlog.div continuousAt_const hlog3ne
  exact hcont.tendsto.mono_left inf_le_left

/-- Gate F's exact reciprocal identity. -/
theorem admissibleExponent_mul_gamma
    {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    admissibleExponent q * gammaExponent q = 1 := by
  have hlogne : Real.log (1 / q) ≠ 0 :=
    ne_of_gt (log_one_div_pos hq0 hq1)
  have hlog3ne : Real.log 3 ≠ 0 := ne_of_gt log_three_pos
  unfold admissibleExponent gammaExponent
  field_simp

/-- **Gate F.** The document's condition
`a < log(1/q)/log 3` is exactly `a * gamma(q) < 1`. -/
theorem exponentCondition_iff
    {a q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    a < admissibleExponent q ↔ a * gammaExponent q < 1 := by
  have hgamma : 0 < gammaExponent q := gammaExponent_pos hq0 hq1
  have hid := admissibleExponent_mul_gamma hq0 hq1
  constructor
  · intro ha
    calc
      a * gammaExponent q <
          admissibleExponent q * gammaExponent q :=
        mul_lt_mul_of_pos_right ha hgamma
      _ = 1 := hid
  · intro ha
    by_contra hnot
    have hle : admissibleExponent q ≤ a := le_of_not_gt hnot
    have hmul :
        admissibleExponent q * gammaExponent q ≤ a * gammaExponent q :=
      mul_le_mul_of_nonneg_right hle (le_of_lt hgamma)
    rw [hid] at hmul
    linarith

end QuantitativeDensity

namespace Terras

/-- Elementary lower bound used by the maximal-barrier startup arithmetic. -/
theorem lg3_one_lt : 1 < QuantitativeDensity.lg3 := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog : Real.log 2 < Real.log 3 :=
    Real.log_lt_log (by norm_num) (by norm_num)
  unfold QuantitativeDensity.lg3 Real.logb
  exact (lt_div_iff₀ hlog2).2 (by simpa [one_mul] using hlog)

end Terras

end CollatzEndpointTransport
