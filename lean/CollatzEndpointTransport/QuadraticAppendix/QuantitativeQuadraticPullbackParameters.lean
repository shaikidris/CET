/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik
-/
import CollatzEndpointTransport.QuadraticAppendix.Shared.QuantitativePullbackParameters

/-!
# Quantitative Quadratic Pullback Parameters

Optimized scalar parameters for the quadratic Collatz pullback.

The historical pullback package uses `eta = D/64` and `etaPrime = D/4`.
The quadratic proof has a sharper terminal excess bound

  ell < (3/2) * eta * M + 1,

so it can use the larger barrier and cone parameters

  eta       = D / 12,
  etaPrime  = 2 * D / 5,
  alpha     = 1/2 - eta.

The resulting maximal-barrier shell rate is `D^2/288`, and every
deterministic startup condition closes once `36 <= D*M`.
-/

namespace CollatzEndpointTransport

namespace QuantitativeDensity

open scoped Real

noncomputable section

def quadraticPullEta (D : ℝ) : ℝ := D / 12

def quadraticPullEtaPrime (D : ℝ) : ℝ := 2 * D / 5

def quadraticPullAlpha (D : ℝ) : ℝ :=
  1 / 2 - quadraticPullEta D

def quadraticPullConeExponent (D : ℝ) : ℝ :=
  D - 2 * quadraticPullEtaPrime D

theorem quadraticPullEta_pos {D : ℝ} (hD : 0 < D) :
    0 < quadraticPullEta D := by
  unfold quadraticPullEta
  positivity

theorem quadraticPullEtaPrime_pos {D : ℝ} (hD : 0 < D) :
    0 < quadraticPullEtaPrime D := by
  unfold quadraticPullEtaPrime
  positivity

theorem quadraticPullEta_le_one_twelfth {D : ℝ} (hD : D ≤ 1) :
    quadraticPullEta D ≤ 1 / 12 := by
  unfold quadraticPullEta
  linarith

theorem quadraticPullAlpha_le_half {D : ℝ} (hD : 0 ≤ D) :
    quadraticPullAlpha D ≤ 1 / 2 := by
  unfold quadraticPullAlpha quadraticPullEta
  linarith

theorem quadraticPullAlpha_ge_five_twelfths
    {D : ℝ} (hD : D ≤ 1) :
    5 / 12 ≤ quadraticPullAlpha D := by
  unfold quadraticPullAlpha quadraticPullEta
  linarith

theorem quadraticPullAlpha_pos
    {D : ℝ} (_hD0 : 0 < D) (hD1 : D ≤ 1) :
    0 < quadraticPullAlpha D := by
  have h := quadraticPullAlpha_ge_five_twelfths hD1
  norm_num at h ⊢
  linarith

/-- The optimized cone parameter remains inside the cone-density range. -/
theorem quadraticPullEtaPrime_lt_cone_limit
    {D : ℝ} (hD0 : 0 < D) (hD1 : D ≤ 1) :
    quadraticPullEtaPrime D < D / (2 - D) := by
  have hden : 0 < 2 - D := by linarith
  unfold quadraticPullEtaPrime
  rw [div_lt_div_iff₀ (by norm_num : (0 : ℝ) < 5) hden]
  nlinarith

theorem quadraticPullConeExponent_eq (D : ℝ) :
    quadraticPullConeExponent D = D / 5 := by
  unfold quadraticPullConeExponent quadraticPullEtaPrime
  ring

theorem quadraticPullConeExponent_pos {D : ℝ} (hD : 0 < D) :
    0 < quadraticPullConeExponent D := by
  rw [quadraticPullConeExponent_eq]
  positivity

/-- The optimized cone and base scales retain at least
`(D/12) * log 3` in the shell exponent. -/
theorem quadratic_pull_base_density_exponent_lower
    {D : ℝ} (hD0 : 0 ≤ D) (hD1 : D ≤ 1) :
    (1 / 12) * D * lg3 ≤
      quadraticPullConeExponent D * quadraticPullAlpha D * lg3 := by
  have hAlpha := quadraticPullAlpha_ge_five_twelfths hD1
  have hlg := lg3_pos
  rw [quadraticPullConeExponent_eq]
  calc
    (1 / 12) * D * lg3 =
        (D / 5) * (5 / 12) * lg3 := by ring
    _ ≤ (D / 5) * quadraticPullAlpha D * lg3 := by
      gcongr

/-- Floor-sensitive cone-depth inequality using the sharp
`(3/2) * eta * M` terminal excess.  At the worst corner
`D=1`, `D*M=36`, the remaining slack is exactly `59/640`. -/
theorem quadratic_pull_cone_depth_startup
    {D M : ℝ} (_hD0 : 0 < D) (hD1 : D ≤ 1)
    (_hM0 : 0 ≤ M) (hstart : 36 ≤ D * M) :
    3 * quadraticPullEta D * M / 2 + 1 + 1 / 128 ≤
      quadraticPullEtaPrime D * (quadraticPullAlpha D * M - 1) := by
  have hDnonneg : 0 ≤ D := le_of_lt _hD0
  have hcoef : 0 ≤ 3 / 40 - D / 30 := by
    nlinarith
  have hx :
      36 * (3 / 40 - D / 30) ≤
        (D * M) * (3 / 40 - D / 30) :=
    mul_le_mul_of_nonneg_right hstart hcoef
  unfold quadraticPullAlpha quadraticPullEtaPrime quadraticPullEta
  nlinarith

end

end QuantitativeDensity

end CollatzEndpointTransport
