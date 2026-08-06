/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik
-/
import CollatzEndpointTransport.QuadraticAppendix.QuantitativeQuadraticBootstrap
import CollatzEndpointTransport.Common.QuantitativeEnvelope

/-!
# Quantitative Quadratic Stage

The concrete one-stage density theorem, equations (7.9)--(7.12).

Unlike the earlier scalar majorant, this file combines the actual sets:

* the quadratic Collatz pullback of `EnvelopeGood lambda delta`;
* the quadratic initial window `initialWindowGood zeta`;
* the finite logarithmic startup range required by envelope concatenation.

Their intersection is included in `EnvelopeGood (q*lambda) t`, so the
resulting density theorem implements one real bootstrap stage.
-/

namespace CollatzEndpointTransport

namespace QuantitativeDensity

open scoped Real

noncomputable section

def quadraticPullbackDensityConstant : ℝ :=
  1 / (288 * Real.log 2)

def quadraticWindowDensityConstant : ℝ :=
  Terras.maximalBarrierC0 / Real.log 2

def quadraticStageExponentConstant : ℝ :=
  quadraticUniformExponentConstant
    quadraticPullbackDensityConstant quadraticWindowDensityConstant

def quadraticStageExponent (D : ℝ) : ℝ :=
  quadraticStageExponentConstant * D ^ 2

theorem quadraticPullbackDensityConstant_pos :
    0 < quadraticPullbackDensityConstant := by
  unfold quadraticPullbackDensityConstant
  positivity

theorem quadraticWindowDensityConstant_pos :
    0 < quadraticWindowDensityConstant := by
  unfold quadraticWindowDensityConstant
  exact div_pos Terras.maximalBarrierC0_pos (Real.log_pos (by norm_num))

theorem quadraticStageExponentConstant_pos :
    0 < quadraticStageExponentConstant :=
  quadraticUniformExponentConstant_pos
    quadraticPullbackDensityConstant_pos
    quadraticWindowDensityConstant_pos

theorem quadraticStageExponentConstant_le_one :
    quadraticStageExponentConstant ≤ 1 :=
  quadraticUniformExponentConstant_le_one _ _

theorem quadraticStageExponent_pos {D : ℝ} (hD : 0 < D) :
    0 < quadraticStageExponent D := by
  unfold quadraticStageExponent
  exact mul_pos quadraticStageExponentConstant_pos (sq_pos_of_pos hD)

theorem quadraticStageExponent_le_one {D : ℝ}
    (hD0 : 0 ≤ D) (hD1 : D ≤ 1) :
    quadraticStageExponent D ≤ 1 := by
  unfold quadraticStageExponent
  have hDsq : D ^ 2 ≤ 1 := by nlinarith [sq_nonneg D]
  nlinarith [quadraticStageExponentConstant_pos,
    quadraticStageExponentConstant_le_one]

theorem quadraticStageExponent_le_pullback {D : ℝ} :
    quadraticStageExponent D ≤
      quadraticPullbackShellRate D / Real.log 2 := by
  unfold quadraticStageExponent quadraticStageExponentConstant
    quadraticPullbackDensityConstant quadraticPullbackShellRate
    quadraticUniformExponentConstant
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hc :
      min 1 (min (1 / (288 * Real.log 2))
        quadraticWindowDensityConstant) ≤
        1 / (288 * Real.log 2) := by simp
  have hDsq : 0 ≤ D ^ 2 := sq_nonneg D
  calc
    min 1 (min (1 / (288 * Real.log 2))
        quadraticWindowDensityConstant) * D ^ 2
        ≤ (1 / (288 * Real.log 2)) * D ^ 2 :=
      mul_le_mul_of_nonneg_right hc hDsq
    _ = (D ^ 2 / 288) / Real.log 2 := by
      field_simp [ne_of_gt hlog]

theorem quadraticStageExponent_le_window
    {D t : ℝ} (hD0 : 0 ≤ D) (hDt : D ≤ t) :
    quadraticStageExponent D ≤ Terras.quadraticWindowDensityRate t := by
  unfold quadraticStageExponent quadraticStageExponentConstant
    quadraticWindowDensityConstant quadraticUniformExponentConstant
    Terras.quadraticWindowDensityRate
  have hcoef :
      min 1
          (min quadraticPullbackDensityConstant
            (Terras.maximalBarrierC0 / Real.log 2)) ≤
        Terras.maximalBarrierC0 / Real.log 2 := by simp
  have hDsq : D ^ 2 ≤ t ^ 2 := by nlinarith
  have hcpos :
      0 ≤ Terras.maximalBarrierC0 / Real.log 2 :=
    (div_pos Terras.maximalBarrierC0_pos
      (Real.log_pos (by norm_num))).le
  calc
    min 1
          (min quadraticPullbackDensityConstant
            (Terras.maximalBarrierC0 / Real.log 2)) * D ^ 2
        ≤ (Terras.maximalBarrierC0 / Real.log 2) * D ^ 2 :=
      mul_le_mul_of_nonneg_right hcoef (sq_nonneg D)
    _ ≤ (Terras.maximalBarrierC0 / Real.log 2) * t ^ 2 :=
      mul_le_mul_of_nonneg_left hDsq hcpos
    _ = Terras.maximalBarrierC0 * t ^ 2 / Real.log 2 := by ring

/-- The integers whose dyadic logarithm has passed a fixed startup index. -/
def LogStartup (M₀ : ℕ) : Set ℕ :=
  {n | M₀ ≤ Nat.log 2 n}

theorem LogStartup_subset_EnvelopeStartup
    {M₀ : ℕ} {mu : ℝ}
    (hM₀ : (1 + bConst) / mu ≤ (M₀ : ℝ)) :
    LogStartup M₀ ⊆ EnvelopeStartup mu := by
  intro n hn
  change (1 + bConst) / mu ≤ (Nat.log 2 n : ℝ)
  exact hM₀.trans (by exact_mod_cast hn)

/-- Removing all integers below a fixed dyadic-logarithmic startup costs
at most `2^M₀` in the density prefactor, at any retained exponent. -/
theorem LogStartup_dense
    {M₀ : ℕ} {D : ℝ} (hD0 : 0 < D) (hD1 : D ≤ 1) :
    IsCDDense (LogStartup M₀) ((2 : ℝ) ^ M₀) D := by
  refine ⟨by positivity, hD0, hD1, ?_⟩
  intro N hN
  have hsub :
      badPrefix (LogStartup M₀) N ⊆ Finset.Ico 1 (2 ^ M₀) := by
    intro n hn
    simp only [badPrefix, Finset.mem_filter, positivePrefix,
      Finset.mem_Icc, Finset.mem_Ico, LogStartup, Set.mem_setOf_eq] at hn ⊢
    refine ⟨hn.1.1, ?_⟩
    exact Nat.lt_pow_of_log_lt (by norm_num) (Nat.lt_of_not_ge hn.2)
  have hcard :
      (badPrefix (LogStartup M₀) N).card ≤ 2 ^ M₀ := by
    calc
      (badPrefix (LogStartup M₀) N).card
          ≤ (Finset.Ico 1 (2 ^ M₀)).card := Finset.card_le_card hsub
      _ ≤ 2 ^ M₀ := by simp [Nat.card_Ico]
  have hcardR :
      ((badPrefix (LogStartup M₀) N).card : ℝ) ≤ (2 : ℝ) ^ M₀ := by
    exact_mod_cast hcard
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hpow : 1 ≤ (N : ℝ) ^ (1 - D) :=
    Real.one_le_rpow hN1 (by linarith)
  calc
    ((badPrefix (LogStartup M₀) N).card : ℝ) ≤ (2 : ℝ) ^ M₀ := hcardR
    _ ≤ (2 : ℝ) ^ M₀ * (N : ℝ) ^ (1 - D) := by
      nlinarith [show 0 ≤ (2 : ℝ) ^ M₀ by positivity]

/-- **Concrete one-stage density theorem (7.9)--(7.12).** -/
theorem envelopeGood_dense_one_stage
    {lambda q delta zeta t mu C D : ℝ} {M₀ : ℕ}
    (hG : IsCDDense (EnvelopeGood lambda delta) C D)
    (hDle : D ≤ zeta)
    (hlambda0 : 0 < lambda) (hlambda1 : lambda < 1)
    (hdelta0 : 0 ≤ delta) (hdelta1 : delta ≤ 1)
    (hzeta0 : 0 < zeta) (hzeta1 : zeta ≤ 1)
    (ht : delta + zeta + delta * zeta ≤ t)
    (hmu :
      mu = lambda * (q - a0) - zeta * (1 - lambda))
    (hmu0 : 0 < mu)
    (hM₀ : (1 + bConst) / mu ≤ (M₀ : ℝ)) :
    IsCDDense (EnvelopeGood (q * lambda) t)
      (quadraticPullbackGlobalConstant * (C + 1) +
        Terras.quadraticWindowFixedGlobalConstant + (2 : ℝ) ^ M₀)
      (quadraticStageExponent D) := by
  have hDnext0 := quadraticStageExponent_pos hG.D_pos
  have hDnext1 :=
    quadraticStageExponent_le_one hG.D_pos.le hG.D_le_one
  have hPull :=
    (collatzPullback_dense_quadratic hG).degrade_exponent hDnext0
      quadraticStageExponent_le_pullback
  have hWindowRaw :=
    Terras.initialWindowGood_dense_quadratic_fixed hzeta0 hzeta1
  have hWindow :=
    hWindowRaw.degrade_exponent hDnext0
      (quadraticStageExponent_le_window hG.D_pos.le hDle)
  have hStartupBase :=
    LogStartup_dense (M₀ := M₀) hDnext0 hDnext1
  have hStartup :
      IsCDDense (EnvelopeStartup mu) ((2 : ℝ) ^ M₀)
        (quadraticStageExponent D) :=
    hStartupBase.mono_set (LogStartup_subset_EnvelopeStartup hM₀)
  have hInter := (hPull.inter hWindow).inter hStartup
  apply hInter.mono_set
  exact one_step_envelope_concatenation hlambda0 hlambda1
    hdelta0 hdelta1 hzeta0.le hzeta1 ht hmu hmu0

end

end QuantitativeDensity

end CollatzEndpointTransport
