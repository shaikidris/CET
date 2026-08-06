/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik
-/
import CollatzEndpointTransport.Linear.OptimizedLinearPullbackAbsorption

/-!
# Optimized Linear Pullback Density

The concrete fixed-total nonlinear pullback in `(C,D)`-density form.

This file connects the finite endpoint theorem to the literal Collatz
pullback and then applies the exact dyadic shell-to-prefix summation.
-/

namespace CollatzEndpointTransport

namespace OptimizedLinearPullback

noncomputable section

/-- The prefix-density constant returned by dyadic shell summation. -/
def pullbackConstant (C eta D : ℝ) : ℝ :=
  2 * shellConstant C eta D /
    (2 * Real.exp (-shellRate eta D) - 1)

theorem shellBad_collatzPullback_le
    {S : Set ℕ} {C D eta : ℝ}
    (hS : QuantitativeDensity.IsCDDense S C D)
    (heta0 : 0 < eta) (heta1 : eta < 1)
    (M : ℕ) :
    ((QuantitativeDensity.shellBad
        (QuantitativeDensity.collatzPullback S) M).card : ℝ) ≤
      shellConstant C eta D *
        Real.exp (-shellRate eta D * M) *
        (2 ^ M : ℝ) := by
  rw [FixedTotal.card_shellBad_collatzPullback_eq_sourceEndpointBad]
  have hfrac :=
    sourceEndpointBad_div_pow_le_absorbed hS heta0 heta1 M
  exact (div_le_iff₀ (by positivity : (0 : ℝ) < 2 ^ M)).mp hfrac

/-- **Concrete nonlinear Collatz pullback.**

The target exponent `D` is transported to
`eta * psi(D) / (3 log 2)`.  Since `psi(D)/D -> log(3)/2`, this is
asymptotically linear in `D`. -/
theorem collatzPullback_dense
    {S : Set ℕ} {C D eta : ℝ}
    (hS : QuantitativeDensity.IsCDDense S C D)
    (heta0 : 0 < eta) (heta1 : eta < 1) :
    QuantitativeDensity.IsCDDense
      (QuantitativeDensity.collatzPullback S)
      (pullbackConstant C eta D)
      (shellRate eta D / Real.log 2) := by
  unfold pullbackConstant
  exact QuantitativeDensity.isCDDense_of_shell_bound
    (shellConstant_pos hS.C_pos)
    (shellRate_pos heta0 hS.D_pos)
    (shellRate_lt_log_two heta0 heta1 hS.D_pos)
    (shellBad_collatzPullback_le hS heta0 heta1)

end

end OptimizedLinearPullback

end CollatzEndpointTransport
