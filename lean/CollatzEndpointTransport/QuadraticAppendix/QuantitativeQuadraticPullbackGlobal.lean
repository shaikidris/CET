/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik
-/
import CollatzEndpointTransport.QuadraticAppendix.QuantitativeQuadraticPullbackDensity

/-!
# Quantitative Quadratic Pullback Global

Global density wrapper for the quadratic pullback shell theorem.

This is separate from `QuantitativeQuadraticPullbackDensity` so Lean consumes
the large shell proof through an opaque compiled interface.
-/

namespace CollatzEndpointTransport

namespace QuantitativeDensity

open scoped Real

noncomputable section

set_option maxHeartbeats 1000000 in
/-- Exact shell-to-global output before replacing the denominator by a fixed
absolute one. -/
theorem collatzPullback_dense_quadratic_raw
    {S : Set ℕ} {C D : ℝ}
    (hS : IsCDDense S C D) :
    IsCDDense (collatzPullback S)
      (2 * (quadraticPullbackStartupConstant * (C + 1)) /
        (2 * Real.exp (-(quadraticPullbackShellRate D)) - 1))
      (quadraticPullbackShellRate D / Real.log 2) := by
  apply isCDDense_of_shell_bound
    (S := collatzPullback S)
    (K := quadraticPullbackStartupConstant * (C + 1))
    (c := quadraticPullbackShellRate D)
    (mul_pos quadraticPullbackStartupConstant_pos
      (by linarith [hS.C_pos] : 0 < C + 1))
    (quadraticPullbackShellRate_pos hS.D_pos)
    (quadraticPullbackShellRate_lt_log_two hS.D_pos.le hS.D_le_one)
  intro M
  simpa only [neg_mul] using
    (card_shellBad_collatzPullback_le_quadratic (M := M) hS)

/-- **MB4.** A `(C,D)`-dense set has a one-block Collatz pullback with a
quadratic retained exponent and a prefactor linear in `C+1`. -/
theorem collatzPullback_dense_quadratic
    {S : Set ℕ} {C D : ℝ}
    (hS : IsCDDense S C D) :
    IsCDDense (collatzPullback S)
      (quadraticPullbackGlobalConstant * (C + 1))
      (quadraticPullbackShellRate D / Real.log 2) := by
  have hraw := collatzPullback_dense_quadratic_raw hS
  apply hraw.mono_constant
  have hrateLe :
      quadraticPullbackShellRate D ≤ 1 / 288 := by
    unfold quadraticPullbackShellRate
    have hDsq : D ^ 2 ≤ 1 := by
      nlinarith [sq_nonneg D, hS.D_le_one, hS.D_pos]
    gcongr
  have hden :
      2 * Real.exp (-(1 / 288 : ℝ)) - 1 ≤
        2 * Real.exp (-(quadraticPullbackShellRate D)) - 1 := by
    gcongr
  have hnum :
      0 ≤ 2 * (quadraticPullbackStartupConstant * (C + 1)) := by
    exact mul_nonneg (by norm_num)
      (mul_nonneg quadraticPullbackStartupConstant_pos.le
        (by linarith [hS.C_pos]))
  have hdiv :
      2 * (quadraticPullbackStartupConstant * (C + 1)) /
          (2 * Real.exp (-(quadraticPullbackShellRate D)) - 1) ≤
        2 * (quadraticPullbackStartupConstant * (C + 1)) /
          (2 * Real.exp (-(1 / 288 : ℝ)) - 1) := by
    exact div_le_div_of_nonneg_left hnum
      quadraticPullbackFixedDenominator_pos hden
  calc
    2 * (quadraticPullbackStartupConstant * (C + 1)) /
          (2 * Real.exp (-(quadraticPullbackShellRate D)) - 1)
        ≤ 2 * (quadraticPullbackStartupConstant * (C + 1)) /
          (2 * Real.exp (-(1 / 288 : ℝ)) - 1) := hdiv
    _ = quadraticPullbackGlobalConstant * (C + 1) := by
      unfold quadraticPullbackGlobalConstant
      field_simp
      ring

end

end QuantitativeDensity

end CollatzEndpointTransport
