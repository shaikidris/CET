/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik
-/
import CollatzEndpointTransport.Linear.OptimizedLinearPullbackDensity

/-!
# Optimized Linear Pullback Asymptotic

Small-density linearization of the optimized nonlinear Collatz pullback.

For every fixed transport constant below the limiting slope

  log 3 / (6 log 2),

this file chooses one fixed absorption parameter and one positive density
cutoff.  Below that cutoff the exact nonlinear pullback has exponent at
least `transport * D`.  Its density prefactor is bounded by a fixed
multiple of `(C + 1) * D⁻²`.

The power two in the prefactor comes from the conservative absorption of
the proved `M^(3/2)` endpoint-information bound.  It affects only the
logarithmic prefactor ledger, not the linear exponent recurrence.
-/

namespace CollatzEndpointTransport

namespace OptimizedLinearPullback

open scoped Real Topology

noncomputable section

/-- The normalized exponent returned by the absorbed nonlinear pullback. -/
def normalizedShellRate (eta D : ℝ) : ℝ :=
  shellRate eta D / (Real.log 2 * D)

theorem normalizedShellRate_eq
    {eta D : ℝ} :
    normalizedShellRate eta D =
      eta * (psi D / (3 * Real.log 2 * D)) := by
  unfold normalizedShellRate shellRate
  ring

theorem tendsto_normalizedShellRate_zero_right (eta : ℝ) :
    Filter.Tendsto (normalizedShellRate eta)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (eta * asymptoticRateLimit)) := by
  have h :=
    tendsto_normalizedRate_zero_right.const_mul eta
  exact h.congr' (Filter.Eventually.of_forall fun D =>
    normalizedShellRate_eq.symm)

/-- A fixed absorption parameter strictly between `transport / limit` and
one. -/
def asymptoticEta (transport : ℝ) : ℝ :=
  (transport + asymptoticRateLimit) /
    (2 * asymptoticRateLimit)

theorem asymptoticEta_pos
    {transport : ℝ} (htransport : 0 < transport) :
    0 < asymptoticEta transport := by
  unfold asymptoticEta
  exact div_pos (add_pos htransport asymptoticRateLimit_pos)
    (mul_pos (by norm_num) asymptoticRateLimit_pos)

theorem asymptoticEta_lt_one
    {transport : ℝ} (htransport : transport < asymptoticRateLimit) :
    asymptoticEta transport < 1 := by
  unfold asymptoticEta
  have hlimit := asymptoticRateLimit_pos
  rw [div_lt_one (by positivity)]
  linarith

theorem transport_lt_eta_mul_limit
    {transport : ℝ} (htransport : transport < asymptoticRateLimit) :
    transport <
      asymptoticEta transport * asymptoticRateLimit := by
  unfold asymptoticEta
  have hlimit := asymptoticRateLimit_pos
  have heq :
      (transport + asymptoticRateLimit) /
          (2 * asymptoticRateLimit) *
          asymptoticRateLimit =
        (transport + asymptoticRateLimit) / 2 := by
    field_simp [ne_of_gt hlimit]
    ring
  rw [heq]
  linarith

/-- The limiting slope gives a uniform linear lower bound on a punctured
right neighborhood of zero. -/
theorem eventually_transport_lt_normalizedShellRate
    {transport : ℝ}
    (htransport0 : 0 < transport)
    (htransport : transport < asymptoticRateLimit) :
    ∀ᶠ D in nhdsWithin 0 (Set.Ioi 0),
      transport < normalizedShellRate (asymptoticEta transport) D := by
  have htend :=
    tendsto_normalizedShellRate_zero_right
      (asymptoticEta transport)
  have hopen :
      Set.Ioi transport ∈
        nhds (asymptoticEta transport * asymptoticRateLimit) :=
    Ioi_mem_nhds (transport_lt_eta_mul_limit htransport)
  exact htend.eventually hopen

/-- Concrete small-density cutoff for the optimized linear recurrence. -/
theorem exists_linear_cutoff
    {transport : ℝ}
    (htransport0 : 0 < transport)
    (htransport : transport < asymptoticRateLimit) :
    ∃ Dcut : ℝ,
      0 < Dcut ∧ Dcut ≤ 1 ∧
      ∀ D : ℝ, 0 < D → D ≤ Dcut →
        transport * D ≤
          shellRate (asymptoticEta transport) D / Real.log 2 := by
  have hevent :=
    eventually_transport_lt_normalizedShellRate
      htransport0 htransport
  rw [eventually_nhdsWithin_iff] at hevent
  rcases Metric.eventually_nhds_iff.mp hevent with
    ⟨eps, heps, hball⟩
  let Dcut : ℝ := min (eps / 2) 1
  refine ⟨Dcut, ?_, min_le_right _ _, ?_⟩
  · dsimp [Dcut]
    positivity
  · intro D hD hDcut
    have hDeps : D < eps := by
      have hle : D ≤ eps / 2 := hDcut.trans (min_le_left _ _)
      linarith
    have hdist : dist D 0 < eps := by
      rw [Real.dist_eq]
      simpa [abs_of_pos hD] using hDeps
    have hnorm :
        transport <
          normalizedShellRate (asymptoticEta transport) D :=
      hball hdist hD
    have hscaled :=
      mul_le_mul_of_nonneg_right hnorm.le hD.le
    calc
      transport * D ≤
          normalizedShellRate (asymptoticEta transport) D * D :=
        hscaled
      _ = shellRate (asymptoticEta transport) D / Real.log 2 := by
        unfold normalizedShellRate
        field_simp [ne_of_gt hD,
          ne_of_gt (Real.log_pos (by norm_num : (1 : ℝ) < 2))]
        ring

/-- Fixed coefficient used in the polynomial prefactor bound. -/
def prefactorSlope (transport eta : ℝ) : ℝ :=
  (1 - eta) * transport * Real.log 2 / eta

/-- Fixed prefactor coefficient for a chosen transport and absorption
parameter. -/
def linearPrefactorConstant (transport eta : ℝ) : ℝ :=
  6 * (1 + 36 * ((prefactorSlope transport eta)⁻¹) ^ 2)

theorem prefactorSlope_pos
    {transport eta : ℝ}
    (htransport : 0 < transport)
    (heta0 : 0 < eta) (heta1 : eta < 1) :
    0 < prefactorSlope transport eta := by
  unfold prefactorSlope
  exact div_pos
    (mul_pos
      (mul_pos (sub_pos.mpr heta1) htransport)
      (Real.log_pos (by norm_num)))
    heta0

theorem linearPrefactorConstant_pos
    {transport eta : ℝ}
    (htransport : 0 < transport)
    (heta0 : 0 < eta) (heta1 : eta < 1) :
    0 < linearPrefactorConstant transport eta := by
  unfold linearPrefactorConstant
  nlinarith [sq_nonneg ((prefactorSlope transport eta)⁻¹)]

theorem pullback_denominator_ge_third
    {eta D : ℝ}
    (heta0 : 0 < eta) (heta1 : eta < 1) (hD : 0 < D) :
    (1 : ℝ) / 3 ≤
      2 * Real.exp (-shellRate eta D) - 1 := by
  have hrate0 := shellRate_pos heta0 hD
  have hrateLt := shellRate_lt_log_two heta0 heta1 hD
  have hlogTwoLt : Real.log 2 < 1 :=
    Real.log_two_lt_d9.trans (by norm_num)
  have hrateThird : shellRate eta D ≤ (1 : ℝ) / 3 := by
    unfold shellRate
    have hr : 0 < psi D / 3 := div_pos (psi_pos hD) (by norm_num)
    have hetaRate :
        eta * (psi D / 3) < psi D / 3 :=
      mul_lt_of_lt_one_left hr heta1
    nlinarith [psi_lt_log_two D]
  have hexp :=
    Real.add_one_le_exp (-shellRate eta D)
  nlinarith

theorem pullbackConstant_le_six_mul_shellConstant
    {C eta D : ℝ}
    (hC : 0 < C)
    (heta0 : 0 < eta) (heta1 : eta < 1) (hD : 0 < D) :
    pullbackConstant C eta D ≤
      6 * shellConstant C eta D := by
  have hden :=
    pullback_denominator_ge_third heta0 heta1 hD
  have hden0 :
      0 < 2 * Real.exp (-shellRate eta D) - 1 := by
    linarith
  have hshell0 := shellConstant_pos (C := C) (eta := eta) (D := D) hC
  unfold pullbackConstant
  rw [div_le_iff₀ hden0]
  nlinarith

theorem absorption_inverse_sq_le
    {transport eta D : ℝ}
    (htransport : 0 < transport)
    (heta0 : 0 < eta) (heta1 : eta < 1)
    (hD : 0 < D)
    (hlinear :
      transport * D ≤ shellRate eta D / Real.log 2) :
    ((((1 - eta) * (psi D / 3))⁻¹) ^ 2) ≤
      ((prefactorSlope transport eta)⁻¹) ^ 2 * (D⁻¹) ^ 2 := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hpsi := psi_pos hD
  have ha0 :
      0 < (1 - eta) * (psi D / 3) :=
    mul_pos (sub_pos.mpr heta1) (div_pos hpsi (by norm_num))
  have hslope0 := prefactorSlope_pos htransport heta0 heta1
  have hbase0 : 0 < prefactorSlope transport eta * D :=
    mul_pos hslope0 hD
  have hrate :
      prefactorSlope transport eta * D ≤
        (1 - eta) * (psi D / 3) := by
    have hfactor0 :
        0 ≤ (1 - eta) * Real.log 2 / eta :=
      div_nonneg
        (mul_nonneg (sub_nonneg.mpr heta1.le)
          (Real.log_pos (by norm_num)).le)
        heta0.le
    have hscaled :=
      mul_le_mul_of_nonneg_left hlinear
        hfactor0
    unfold shellRate at hscaled
    unfold prefactorSlope
    convert hscaled using 1 <;>
      field_simp [ne_of_gt heta0, ne_of_gt hlog2] <;> ring
  have hinv :
      ((1 - eta) * (psi D / 3))⁻¹ ≤
        (prefactorSlope transport eta * D)⁻¹ :=
    (inv_le_inv₀ ha0 hbase0).2 hrate
  have hsq :=
    mul_self_le_mul_self
      (inv_nonneg.mpr ha0.le) hinv
  convert hsq using 1 <;> simp only [mul_inv_rev, pow_two] <;> ring

/-- Polynomial majorant for the exact nonlinear pullback prefactor. -/
theorem pullbackConstant_le_linearPrefactor
    {C D transport eta : ℝ}
    (hC : 0 < C)
    (hD0 : 0 < D) (hD1 : D ≤ 1)
    (htransport : 0 < transport)
    (heta0 : 0 < eta) (heta1 : eta < 1)
    (hlinear :
      transport * D ≤ shellRate eta D / Real.log 2) :
    pullbackConstant C eta D ≤
      linearPrefactorConstant transport eta *
        (C + 1) * (D⁻¹) ^ 2 := by
  have hC1 : 1 ≤ C + 1 := by linarith
  have hDinv : 1 ≤ D⁻¹ := (one_le_inv₀ hD0).2 hD1
  have hDinvSq : 1 ≤ (D⁻¹) ^ 2 := by
    simpa [pow_two] using
      mul_self_le_mul_self (by norm_num : (0 : ℝ) ≤ 1) hDinv
  have habs :=
    absorption_inverse_sq_le htransport heta0 heta1 hD0 hlinear
  have hshell :
      shellConstant C eta D ≤
        (1 + 36 * ((prefactorSlope transport eta)⁻¹) ^ 2) *
          (C + 1) * (D⁻¹) ^ 2 := by
    unfold shellConstant
    have hslopeSq : 0 ≤ ((prefactorSlope transport eta)⁻¹) ^ 2 :=
      sq_nonneg _
    have hmain :
        36 * ((((1 - eta) * (psi D / 3))⁻¹) ^ 2) ≤
          36 * ((prefactorSlope transport eta)⁻¹) ^ 2 *
            (D⁻¹) ^ 2 := by
      nlinarith
    have hbase :
        1 + C ≤ (C + 1) * (D⁻¹) ^ 2 := by
      have hC1nonneg : 0 ≤ C + 1 := by linarith
      have hmul :=
        mul_le_mul_of_nonneg_left hDinvSq hC1nonneg
      nlinarith
    have hextra :
        36 * ((prefactorSlope transport eta)⁻¹) ^ 2 *
            (D⁻¹) ^ 2 ≤
          36 * ((prefactorSlope transport eta)⁻¹) ^ 2 *
            (C + 1) * (D⁻¹) ^ 2 := by
      have hnonneg :
          0 ≤ 36 * ((prefactorSlope transport eta)⁻¹) ^ 2 *
            (D⁻¹) ^ 2 := by
        positivity
      nlinarith [mul_le_mul_of_nonneg_right hC1
        (mul_nonneg (by positivity : 0 ≤ 36 *
          ((prefactorSlope transport eta)⁻¹) ^ 2)
          (by positivity : 0 ≤ (D⁻¹) ^ 2))]
    nlinarith
  have hpull :=
    pullbackConstant_le_six_mul_shellConstant hC heta0 heta1 hD0
  unfold linearPrefactorConstant
  nlinarith [mul_nonneg
    (by positivity : 0 ≤
      (1 + 36 * ((prefactorSlope transport eta)⁻¹) ^ 2) * (C + 1))
    (by positivity : 0 ≤ (D⁻¹) ^ 2)]

end

end OptimizedLinearPullback

end CollatzEndpointTransport
