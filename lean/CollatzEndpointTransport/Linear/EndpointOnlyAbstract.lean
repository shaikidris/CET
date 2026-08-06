/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik
-/
import CollatzEndpointTransport.Linear.EndpointOnlyCore

/-!
# Endpoint Only Abstract

Transport-agnostic density recurrence for the endpoint-only bootstrap.

The concrete fixed-total theorem currently supplies a stage bound with
inverse-density power `B = 2`.  A higher Renyi theorem may supply a
different power and transport constant.  This file isolates the part of
the endpoint argument that depends only on the abstract one-stage shape

  (C,D) |-> (K * (C+1) * D^(-B) + W, transport * D).

No higher-moment estimate is assumed or asserted here.
-/

namespace CollatzEndpointTransport

namespace OptimizedLinearPullback

open scoped Real

noncomputable section

open QuantitativeDensity

/-- Exact prefactor recurrence for an abstract endpoint pullback with
inverse-density power `B`. -/
def endpointAbstractC
    (K W transport D0 : ℝ) (B : ℕ) : ℕ → ℝ
  | 0 => 1
  | R + 1 =>
      K * (endpointAbstractC K W transport D0 B R + 1) *
          ((endpointD transport D0 R)⁻¹) ^ B +
        W

@[simp]
theorem endpointAbstractC_zero
    (K W transport D0 : ℝ) (B : ℕ) :
    endpointAbstractC K W transport D0 B 0 = 1 :=
  rfl

theorem endpointAbstractC_succ
    (K W transport D0 : ℝ) (B R : ℕ) :
    endpointAbstractC K W transport D0 B (R + 1) =
      K * (endpointAbstractC K W transport D0 B R + 1) *
          ((endpointD transport D0 R)⁻¹) ^ B +
        W :=
  rfl

theorem endpointAbstractC_pos
    {K W transport D0 : ℝ} {B : ℕ}
    (hK : 0 < K) (hW : 0 < W)
    (htransport : 0 < transport) (hD0 : 0 < D0) :
    ∀ R, 0 < endpointAbstractC K W transport D0 B R := by
  intro R
  induction R with
  | zero => simp
  | succ R ih =>
      rw [endpointAbstractC_succ]
      have hD :=
        endpointD_pos htransport hD0 R
      have hpow :
          0 ≤ ((endpointD transport D0 R)⁻¹) ^ B :=
        pow_nonneg (inv_nonneg.mpr hD.le) _
      nlinarith [mul_nonneg
        (mul_nonneg hK.le
          (by linarith :
            0 ≤ endpointAbstractC K W transport D0 B R + 1))
        hpow]

/-- Abstract one-stage socket for a future endpoint pullback theorem.

An inhabitant certifies the actual Collatz set operation used by
`endpointChain`; the structure itself contributes no analytic assumption.
-/
structure EndpointDensityStep
    (t transport K W Dcut : ℝ) (B : ℕ) : Prop where
  transport_pos : 0 < transport
  transport_le_one : transport ≤ 1
  K_pos : 0 < K
  W_pos : 0 < W
  Dcut_pos : 0 < Dcut
  step :
    ∀ {S : Set ℕ} {C D : ℝ},
      IsCDDense S C D →
      D ≤ Dcut →
      IsCDDense
        (Terras.initialWindowGood t ∩ collatzPullback S)
        (K * (C + 1) * (D⁻¹) ^ B + W)
        (transport * D)

/-- Iteration of an abstract linear endpoint-density step. -/
theorem endpointChain_dense_of_abstract_step
    {t transport K W D0 Dcut : ℝ} {B : ℕ}
    (hstep : EndpointDensityStep t transport K W Dcut B)
    (hD00 : 0 < D0) (hD01 : D0 ≤ 1)
    (hD0cut : D0 ≤ Dcut) :
    ∀ R,
      IsCDDense (endpointChain t R)
        (endpointAbstractC K W transport D0 B R)
        (endpointD transport D0 R) := by
  intro R
  induction R with
  | zero =>
      refine ⟨by simp, ?_, ?_, ?_⟩
      · simpa [endpointD] using hD00
      · simpa [endpointD] using hD01
      intro N hN
      have hnonneg :
          0 ≤ (N : ℝ) ^ (1 - D0) :=
        Real.rpow_nonneg (Nat.cast_nonneg N) _
      simpa [badPrefix, endpointD] using hnonneg
  | succ R ih =>
      rw [endpointChain_succ, endpointAbstractC_succ, endpointD_succ]
      apply hstep.step ih
      have hDRle :=
        endpointD_le_D0 hstep.transport_pos.le
          hstep.transport_le_one hD00.le R
      exact hDRle.trans hD0cut

/-- Coarse fixed majorant for one abstract endpoint-density stage. -/
def endpointAbstractStageK (K W : ℝ) : ℝ :=
  K + W + 3

theorem endpointAbstractStageK_ge_one
    {K W : ℝ} (hK : 0 < K) (hW : 0 < W) :
    1 ≤ endpointAbstractStageK K W := by
  unfold endpointAbstractStageK
  linarith

/-- Earlier linear density exponents dominate the terminal exponent. -/
theorem endpointD_terminal_le_abstract
    {transport D0 : ℝ} {R j : ℕ}
    (htransport0 : 0 < transport)
    (htransport1 : transport ≤ 1)
    (hD00 : 0 < D0)
    (hj : j ≤ R) :
    endpointD transport D0 R ≤ endpointD transport D0 j := by
  have hp :
      transport ^ R ≤ transport ^ j :=
    pow_le_pow_of_le_one htransport0.le htransport1 hj
  unfold endpointD
  exact mul_le_mul_of_nonneg_right hp hD00.le

/-- The abstract prefactor has the same terminal majorant for every fixed
finite inverse-density power `B`. -/
theorem endpointAbstractC_terminal_bound
    {K W transport D0 : ℝ} {B R : ℕ}
    (hK : 0 < K) (hW : 0 < W)
    (htransport0 : 0 < transport)
    (htransport1 : transport ≤ 1)
    (hD00 : 0 < D0)
    (hDterminal1 : endpointD transport D0 R ≤ 1) :
    endpointAbstractC K W transport D0 B R + 2 ≤
      3 *
        (endpointAbstractStageK K W *
          ((endpointD transport D0 R)⁻¹) ^ B) ^ R := by
  let F :=
    endpointAbstractStageK K W *
      ((endpointD transport D0 R)⁻¹) ^ B
  have hDR0 :=
    endpointD_pos htransport0 hD00 R
  have hDRinv :
      1 ≤ (endpointD transport D0 R)⁻¹ :=
    (one_le_inv₀ hDR0).2 hDterminal1
  have hDRinvPow :
      1 ≤ ((endpointD transport D0 R)⁻¹) ^ B :=
    one_le_pow₀ hDRinv
  have hF1 : 1 ≤ F := by
    dsimp [F]
    exact one_le_mul_of_one_le_of_one_le
      (endpointAbstractStageK_ge_one hK hW)
      hDRinvPow
  have hF0 : 0 < F :=
    zero_lt_one.trans_le hF1
  have hind :
      ∀ j : ℕ, j ≤ R →
        endpointAbstractC K W transport D0 B j + 2 ≤
          3 * F ^ j := by
    intro j hj
    induction j with
    | zero =>
        norm_num [endpointAbstractC_zero]
    | succ j ih =>
        have hprev := ih (by omega)
        have hDj0 :=
          endpointD_pos htransport0 hD00 j
        have hDterm :=
          endpointD_terminal_le_abstract htransport0 htransport1 hD00
            (by omega : j ≤ R)
        have hinv :
            (endpointD transport D0 j)⁻¹ ≤
              (endpointD transport D0 R)⁻¹ :=
          (inv_le_inv₀ hDj0 hDR0).2 hDterm
        have hinvPow :
            ((endpointD transport D0 j)⁻¹) ^ B ≤
              ((endpointD transport D0 R)⁻¹) ^ B :=
          pow_le_pow_left₀ (inv_nonneg.mpr hDj0.le) hinv B
        have hCpos :=
          endpointAbstractC_pos (B := B) hK hW htransport0 hD00 j
        have hC12 :
            endpointAbstractC K W transport D0 B j + 1 ≤
              endpointAbstractC K W transport D0 B j + 2 := by
          linarith
        have hcommon :
            1 ≤
              ((endpointD transport D0 R)⁻¹) ^ B *
                (endpointAbstractC K W transport D0 B j + 2) :=
          one_le_mul_of_one_le_of_one_le hDRinvPow (by linarith)
        rw [endpointAbstractC_succ]
        have hstage :
            K * (endpointAbstractC K W transport D0 B j + 1) *
                  ((endpointD transport D0 j)⁻¹) ^ B +
                W + 2
              ≤
            endpointAbstractStageK K W *
              (((endpointD transport D0 R)⁻¹) ^ B *
                (endpointAbstractC K W transport D0 B j + 2)) := by
          have hfirst :
              K * (endpointAbstractC K W transport D0 B j + 1) *
                    ((endpointD transport D0 j)⁻¹) ^ B
                ≤
              K *
                (((endpointD transport D0 R)⁻¹) ^ B *
                  (endpointAbstractC K W transport D0 B j + 2)) := by
            have hprod :
                (endpointAbstractC K W transport D0 B j + 1) *
                      ((endpointD transport D0 j)⁻¹) ^ B
                    ≤
                  (endpointAbstractC K W transport D0 B j + 2) *
                      ((endpointD transport D0 R)⁻¹) ^ B :=
              mul_le_mul hC12 hinvPow
                (pow_nonneg (inv_nonneg.mpr hDj0.le) _)
                (by linarith)
            calc
              K * (endpointAbstractC K W transport D0 B j + 1) *
                    ((endpointD transport D0 j)⁻¹) ^ B
                  =
                K *
                  ((endpointAbstractC K W transport D0 B j + 1) *
                    ((endpointD transport D0 j)⁻¹) ^ B) := by ring
              _ ≤
                K *
                  ((endpointAbstractC K W transport D0 B j + 2) *
                    ((endpointD transport D0 R)⁻¹) ^ B) :=
                mul_le_mul_of_nonneg_left hprod hK.le
              _ = _ := by ring
          have htail :
              W + 2 ≤
                (W + 2) *
                  (((endpointD transport D0 R)⁻¹) ^ B *
                    (endpointAbstractC K W transport D0 B j + 2)) := by
            have hW2 : 0 ≤ W + 2 := by linarith
            simpa only [mul_one] using
              mul_le_mul_of_nonneg_left hcommon hW2
          have hcommon0 :
              0 ≤
                ((endpointD transport D0 R)⁻¹) ^ B *
                  (endpointAbstractC K W transport D0 B j + 2) :=
            mul_nonneg
              (pow_nonneg (inv_nonneg.mpr hDR0.le) _)
              (by linarith)
          unfold endpointAbstractStageK
          nlinarith
        calc
          K * (endpointAbstractC K W transport D0 B j + 1) *
                  ((endpointD transport D0 j)⁻¹) ^ B +
                W + 2
              ≤
            endpointAbstractStageK K W *
              (((endpointD transport D0 R)⁻¹) ^ B *
                (endpointAbstractC K W transport D0 B j + 2)) :=
              hstage
          _ = F * (endpointAbstractC K W transport D0 B j + 2) := by
            dsimp [F]
            ring
          _ ≤ F * (3 * F ^ j) :=
            mul_le_mul_of_nonneg_left hprev hF0.le
          _ = 3 * F ^ (j + 1) := by
            rw [pow_succ]
            ring
  simpa [F] using hind R le_rfl

end

end OptimizedLinearPullback

end CollatzEndpointTransport
