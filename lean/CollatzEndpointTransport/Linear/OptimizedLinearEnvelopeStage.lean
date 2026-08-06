/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik
-/
import CollatzEndpointTransport.Linear.OptimizedLinearPullbackAsymptotic
import CollatzEndpointTransport.Common.QuantitativeEnvelope

/-!
# Optimized Linear Envelope Stage

One concrete optimized-linear envelope stage.

This is the linear analogue of the quadratic one-stage theorem, but it
depends only on the shared envelope concatenation lemma.  The previous
envelope is pulled back with the fixed-total nonlinear theorem, intersected
with the new maximal-barrier initial window, and restricted past the finite
startup index.
-/

namespace CollatzEndpointTransport

namespace OptimizedLinearPullback

open scoped Real

noncomputable section

open QuantitativeDensity

/-- The integers whose dyadic logarithm has passed a fixed startup index. -/
def LinearLogStartup (M₀ : ℕ) : Set ℕ :=
  {n | M₀ ≤ Nat.log 2 n}

theorem LinearLogStartup_subset_EnvelopeStartup
    {M₀ : ℕ} {mu : ℝ}
    (hM₀ : (1 + bConst) / mu ≤ (M₀ : ℝ)) :
    LinearLogStartup M₀ ⊆ EnvelopeStartup mu := by
  intro n hn
  change (1 + bConst) / mu ≤ (Nat.log 2 n : ℝ)
  exact hM₀.trans (by exact_mod_cast hn)

theorem LinearLogStartup_dense
    {M₀ : ℕ} {D : ℝ} (hD0 : 0 < D) (hD1 : D ≤ 1) :
    IsCDDense (LinearLogStartup M₀) ((2 : ℝ) ^ M₀) D := by
  refine ⟨by positivity, hD0, hD1, ?_⟩
  intro N hN
  have hsub :
      badPrefix (LinearLogStartup M₀) N ⊆
        Finset.Ico 1 (2 ^ M₀) := by
    intro n hn
    simp only [badPrefix, Finset.mem_filter, positivePrefix,
      Finset.mem_Icc, Finset.mem_Ico, LinearLogStartup,
      Set.mem_setOf_eq] at hn ⊢
    refine ⟨hn.1.1, ?_⟩
    exact Nat.lt_pow_of_log_lt (by norm_num) (Nat.lt_of_not_ge hn.2)
  have hcard :
      (badPrefix (LinearLogStartup M₀) N).card ≤ 2 ^ M₀ := by
    calc
      (badPrefix (LinearLogStartup M₀) N).card
          ≤ (Finset.Ico 1 (2 ^ M₀)).card := Finset.card_le_card hsub
      _ ≤ 2 ^ M₀ := by simp [Nat.card_Ico]
  have hcardR :
      ((badPrefix (LinearLogStartup M₀) N).card : ℝ) ≤
        (2 : ℝ) ^ M₀ := by
    exact_mod_cast hcard
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hpow : 1 ≤ (N : ℝ) ^ (1 - D) :=
    Real.one_le_rpow hN1 (by linarith)
  calc
    ((badPrefix (LinearLogStartup M₀) N).card : ℝ)
        ≤ (2 : ℝ) ^ M₀ := hcardR
    _ ≤ (2 : ℝ) ^ M₀ * (N : ℝ) ^ (1 - D) := by
      nlinarith [show 0 ≤ (2 : ℝ) ^ M₀ by positivity]

/-- **One optimized-linear envelope stage.**

The hypotheses `hlinear` and `hwindow` expose the two exponent comparisons
used by the recurrence.  The returned prefactor already uses the polynomial
majorant for the exact nonlinear pullback constant. -/
theorem envelopeGood_dense_one_linear_stage
    {lambda q delta zeta t mu C D eta transport : ℝ} {M₀ : ℕ}
    (hG : IsCDDense (EnvelopeGood lambda delta) C D)
    (hlambda0 : 0 < lambda) (hlambda1 : lambda < 1)
    (hdelta0 : 0 ≤ delta) (hdelta1 : delta ≤ 1)
    (hzeta0 : 0 < zeta) (hzeta1 : zeta ≤ 1)
    (ht : delta + zeta + delta * zeta ≤ t)
    (hmu :
      mu = lambda * (q - a0) - zeta * (1 - lambda))
    (hmu0 : 0 < mu)
    (hM₀ : (1 + bConst) / mu ≤ (M₀ : ℝ))
    (heta0 : 0 < eta) (heta1 : eta < 1)
    (htransport0 : 0 < transport)
    (hlinear :
      transport * D ≤ shellRate eta D / Real.log 2)
    (hwindow :
      transport * D ≤ Terras.quadraticWindowDensityRate zeta)
    (hnext1 : transport * D ≤ 1) :
    IsCDDense (EnvelopeGood (q * lambda) t)
      (linearPrefactorConstant transport eta *
          (C + 1) * (D⁻¹) ^ 2 +
        Terras.quadraticWindowFixedGlobalConstant +
        (2 : ℝ) ^ M₀)
      (transport * D) := by
  have hnext0 : 0 < transport * D :=
    mul_pos htransport0 hG.D_pos
  have hPullRaw :=
    collatzPullback_dense hG heta0 heta1
  have hPullExp :=
    hPullRaw.degrade_exponent hnext0 hlinear
  have hPull :=
    hPullExp.mono_constant
      (pullbackConstant_le_linearPrefactor
        hG.C_pos hG.D_pos hG.D_le_one htransport0
        heta0 heta1 hlinear)
  have hWindowRaw :=
    Terras.initialWindowGood_dense_quadratic_fixed hzeta0 hzeta1
  have hWindow :=
    hWindowRaw.degrade_exponent hnext0 hwindow
  have hStartupBase :=
    LinearLogStartup_dense (M₀ := M₀) hnext0 hnext1
  have hStartup :
      IsCDDense (EnvelopeStartup mu) ((2 : ℝ) ^ M₀)
        (transport * D) :=
    hStartupBase.mono_set
      (LinearLogStartup_subset_EnvelopeStartup hM₀)
  have hInter := (hPull.inter hWindow).inter hStartup
  apply hInter.mono_set
  exact one_step_envelope_concatenation hlambda0 hlambda1
    hdelta0 hdelta1 hzeta0.le hzeta1 ht hmu hmu0

end

end OptimizedLinearPullback

end CollatzEndpointTransport
