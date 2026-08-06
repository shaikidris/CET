/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik
-/
import CollatzEndpointTransport.Linear.OptimizedLinearPullbackAsymptotic
import CollatzEndpointTransport.Common.TerrasMaximalInitialWindowDensity

/-!
# Endpoint Only Core

The endpoint-only logarithmic-block recursion.

Unlike the envelope bootstrap, this recursion retains only membership of
successive logarithmic-block endpoints in one fixed initial-window set.
There is no lambda schedule, tolerance schedule, or concatenation startup.
-/

namespace CollatzEndpointTransport

namespace OptimizedLinearPullback

open scoped Real

noncomputable section

open QuantitativeDensity

/-- One logarithmic Collatz block. -/
def endpointBlock (n : ℕ) : ℕ :=
  (Terras.T^[Nat.log 2 n]) n

/-- The set supporting `R` consecutive good logarithmic blocks. -/
def endpointChain (t : ℝ) : ℕ → Set ℕ
  | 0 => Set.univ
  | R + 1 =>
      Terras.initialWindowGood t ∩
        collatzPullback (endpointChain t R)

@[simp]
theorem endpointChain_zero (t : ℝ) :
    endpointChain t 0 = Set.univ :=
  rfl

@[simp]
theorem endpointChain_succ (t : ℝ) (R : ℕ) :
    endpointChain t (R + 1) =
      Terras.initialWindowGood t ∩
        collatzPullback (endpointChain t R) :=
  rfl

theorem mem_endpointChain_succ
    {t : ℝ} {R n : ℕ} :
    n ∈ endpointChain t (R + 1) ↔
      n ∈ Terras.initialWindowGood t ∧
        endpointBlock n ∈ endpointChain t R := by
  rfl

/-- Exact density exponent after `R` endpoint pulls. -/
def endpointD (transport D0 : ℝ) (R : ℕ) : ℝ :=
  transport ^ R * D0

@[simp]
theorem endpointD_zero (transport D0 : ℝ) :
    endpointD transport D0 0 = D0 := by
  simp [endpointD]

theorem endpointD_succ (transport D0 : ℝ) (R : ℕ) :
    endpointD transport D0 (R + 1) =
      transport * endpointD transport D0 R := by
  simp [endpointD, pow_succ]
  ring

theorem endpointD_pos
    {transport D0 : ℝ}
    (htransport : 0 < transport) (hD0 : 0 < D0) :
    ∀ R, 0 < endpointD transport D0 R := by
  intro R
  exact mul_pos (pow_pos htransport R) hD0

theorem endpointD_le_D0
    {transport D0 : ℝ}
    (htransport0 : 0 ≤ transport) (htransport1 : transport ≤ 1)
    (hD0 : 0 ≤ D0) :
    ∀ R, endpointD transport D0 R ≤ D0 := by
  intro R
  unfold endpointD
  have hp : transport ^ R ≤ 1 :=
    pow_le_one₀ htransport0 htransport1
  nlinarith [pow_nonneg htransport0 R]

/-- Exact prefactor recurrence for the endpoint-only chain. -/
def endpointC
    (transport eta t D0 : ℝ) : ℕ → ℝ
  | 0 => 1
  | R + 1 =>
      linearPrefactorConstant transport eta *
          (endpointC transport eta t D0 R + 1) *
          ((endpointD transport D0 R)⁻¹) ^ 2 +
        Terras.quadraticWindowFixedGlobalConstant

@[simp]
theorem endpointC_zero
    (transport eta t D0 : ℝ) :
    endpointC transport eta t D0 0 = 1 :=
  rfl

theorem endpointC_succ
    (transport eta t D0 : ℝ) (R : ℕ) :
    endpointC transport eta t D0 (R + 1) =
      linearPrefactorConstant transport eta *
          (endpointC transport eta t D0 R + 1) *
          ((endpointD transport D0 R)⁻¹) ^ 2 +
        Terras.quadraticWindowFixedGlobalConstant :=
  rfl

theorem endpointC_pos
    {transport eta t D0 : ℝ}
    (htransport : 0 < transport)
    (heta0 : 0 < eta) (heta1 : eta < 1)
    (ht0 : 0 < t) (ht1 : t ≤ 1) :
    ∀ R, 0 < endpointC transport eta t D0 R := by
  intro R
  induction R with
  | zero => simp
  | succ R ih =>
      rw [endpointC_succ]
      have hp :=
        linearPrefactorConstant_pos htransport heta0 heta1
      have hw :=
        (Terras.initialWindowGood_dense_quadratic_fixed ht0 ht1).C_pos
      have hsquare :
          0 ≤ ((endpointD transport D0 R)⁻¹) ^ 2 :=
        sq_nonneg _
      nlinarith [mul_nonneg
        (mul_nonneg hp.le (by linarith : 0 ≤
          endpointC transport eta t D0 R + 1)) hsquare]

/-- One endpoint-only density stage. -/
theorem endpointChain_dense_one_stage
    {S : Set ℕ} {C D t eta transport : ℝ}
    (hS : IsCDDense S C D)
    (ht0 : 0 < t) (ht1 : t ≤ 1)
    (heta0 : 0 < eta) (heta1 : eta < 1)
    (htransport0 : 0 < transport)
    (hlinear :
      transport * D ≤ shellRate eta D / Real.log 2)
    (hwindow :
      transport * D ≤ Terras.quadraticWindowDensityRate t)
    (hnext1 : transport * D ≤ 1) :
    IsCDDense
      (Terras.initialWindowGood t ∩ collatzPullback S)
      (linearPrefactorConstant transport eta *
          (C + 1) * (D⁻¹) ^ 2 +
        Terras.quadraticWindowFixedGlobalConstant)
      (transport * D) := by
  have hnext0 : 0 < transport * D :=
    mul_pos htransport0 hS.D_pos
  have hPullRaw :=
    collatzPullback_dense hS heta0 heta1
  have hPullExp :=
    hPullRaw.degrade_exponent hnext0 hlinear
  have hPull :=
    hPullExp.mono_constant
      (pullbackConstant_le_linearPrefactor
        hS.C_pos hS.D_pos hS.D_le_one htransport0
        heta0 heta1 hlinear)
  have hWindowRaw :=
    Terras.initialWindowGood_dense_quadratic_fixed ht0 ht1
  have hWindow :=
    hWindowRaw.degrade_exponent hnext0 hwindow
  simpa [add_comm] using hWindow.inter hPull

/-- The full concrete density recurrence for `endpointChain`. -/
theorem endpointChain_dense
    {transport eta t D0 Dcut : ℝ}
    (htransport0 : 0 < transport) (htransport1 : transport ≤ 1)
    (heta0 : 0 < eta) (heta1 : eta < 1)
    (ht0 : 0 < t) (ht1 : t ≤ 1)
    (hD00 : 0 < D0) (hD01 : D0 ≤ 1)
    (hDcut0 : 0 < Dcut) (hD0cut : D0 ≤ Dcut)
    (hcut :
      ∀ D : ℝ, 0 < D → D ≤ Dcut →
        transport * D ≤ shellRate eta D / Real.log 2)
    (hwindow0 :
      transport * D0 ≤ Terras.quadraticWindowDensityRate t) :
    ∀ R,
      IsCDDense (endpointChain t R)
        (endpointC transport eta t D0 R)
        (endpointD transport D0 R) := by
  intro R
  induction R with
  | zero =>
      refine ⟨by simp [endpointC], ?_, ?_, ?_⟩
      · simpa [endpointD] using hD00
      · simpa [endpointD] using hD01
      intro N hN
      have hnonneg :
          0 ≤ (N : ℝ) ^ (1 - D0) :=
        Real.rpow_nonneg (Nat.cast_nonneg N) _
      simpa [badPrefix, endpointC, endpointD] using hnonneg
  | succ R ih =>
      rw [endpointChain_succ, endpointC_succ, endpointD_succ]
      have hDR0 :=
        endpointD_pos htransport0 hD00 R
      have hDRle :=
        endpointD_le_D0 htransport0.le htransport1 hD00.le R
      have hDRcut : endpointD transport D0 R ≤ Dcut :=
        hDRle.trans hD0cut
      have hlinear := hcut _ hDR0 hDRcut
      have hwindow :
          transport * endpointD transport D0 R ≤
            Terras.quadraticWindowDensityRate t := by
        exact (mul_le_mul_of_nonneg_left hDRle htransport0.le).trans hwindow0
      have hnext1 :
          transport * endpointD transport D0 R ≤ 1 := by
        have htransportD :
            transport * endpointD transport D0 R ≤
              endpointD transport D0 R :=
          mul_le_of_le_one_left hDR0.le htransport1
        exact htransportD.trans (hDRle.trans hD01)
      exact endpointChain_dense_one_stage ih ht0 ht1
        heta0 heta1 htransport0 hlinear hwindow hnext1

end

end OptimizedLinearPullback

end CollatzEndpointTransport
