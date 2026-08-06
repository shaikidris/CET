/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik
-/
import CollatzEndpointTransport.Linear.EndpointOnlyOrbit
import CollatzEndpointTransport.Linear.OptimizedLinearRecurrenceBound

/-!
# Endpoint Only Recurrence Bound

Terminal prefactor control for the endpoint-only recursion.

The endpoint-only chain has no horizon-startup term.  At a fixed terminal
stage `R`, every earlier inverse density is bounded by `D_R⁻¹`, giving

  C_R + 2 <= 3 * (K * D_R⁻²)^R.

Consequently its logarithm has quadratic, rather than exponential, cost in
the number of logarithmic blocks.
-/

namespace CollatzEndpointTransport

namespace OptimizedLinearPullback

open scoped Real

noncomputable section

open QuantitativeDensity

/-- One fixed majorant for the pullback and window constants in an
endpoint-only stage. -/
def endpointStageK (transport eta : ℝ) : ℝ :=
  linearPrefactorConstant transport eta +
    Terras.quadraticWindowFixedGlobalConstant + 3

theorem endpointStageK_pos
    {transport eta : ℝ}
    (htransport : 0 < transport)
    (heta0 : 0 < eta) (heta1 : eta < 1) :
    0 < endpointStageK transport eta := by
  unfold endpointStageK
  have hp :=
    linearPrefactorConstant_pos htransport heta0 heta1
  have hw :=
    linearWindowConstant_pos
  linarith

theorem endpointStageK_ge_one
    {transport eta : ℝ}
    (htransport : 0 < transport)
    (heta0 : 0 < eta) (heta1 : eta < 1) :
    1 ≤ endpointStageK transport eta := by
  unfold endpointStageK
  have hp :=
    linearPrefactorConstant_pos htransport heta0 heta1
  have hw :=
    linearWindowConstant_pos
  linarith

/-- Earlier density exponents dominate the terminal exponent. -/
theorem endpointD_terminal_le
    {transport D0 : ℝ} {R j : ℕ}
    (htransport0 : 0 < transport)
    (htransport1 : transport ≤ 1)
    (hD00 : 0 < D0)
    (hj : j ≤ R) :
    endpointD transport D0 R ≤ endpointD transport D0 j := by
  have hp :
      transport ^ R ≤ transport ^ j :=
    pow_le_pow_of_le_one htransport0.le htransport1 hj
  have hD0nonneg : 0 ≤ D0 := hD00.le
  unfold endpointD
  exact mul_le_mul_of_nonneg_right hp hD0nonneg

/-- Deliberately coarse terminal majorant for the exact endpoint prefactor
recurrence. -/
theorem endpointC_terminal_bound
    {transport eta t D0 : ℝ} {R : ℕ}
    (htransport0 : 0 < transport)
    (htransport1 : transport ≤ 1)
    (heta0 : 0 < eta) (heta1 : eta < 1)
    (ht0 : 0 < t) (ht1 : t ≤ 1)
    (hD00 : 0 < D0)
    (hDterminal1 : endpointD transport D0 R ≤ 1) :
    endpointC transport eta t D0 R + 2 ≤
      3 *
        (endpointStageK transport eta *
          ((endpointD transport D0 R)⁻¹) ^ 2) ^ R := by
  let F :=
    endpointStageK transport eta *
      ((endpointD transport D0 R)⁻¹) ^ 2
  have hDR0 :=
    endpointD_pos htransport0 hD00 R
  have hDRinv :
      1 ≤ (endpointD transport D0 R)⁻¹ :=
    (one_le_inv₀ hDR0).2 hDterminal1
  have hDRinvSq :
      1 ≤ ((endpointD transport D0 R)⁻¹) ^ 2 := by
    simpa [pow_two] using
      mul_self_le_mul_self (by norm_num : (0 : ℝ) ≤ 1) hDRinv
  have hF1 : 1 ≤ F := by
    dsimp [F]
    exact one_le_mul_of_one_le_of_one_le
      (endpointStageK_ge_one htransport0 heta0 heta1)
      hDRinvSq
  have hF0 : 0 < F :=
    zero_lt_one.trans_le hF1
  have hind :
      ∀ j : ℕ, j ≤ R →
        endpointC transport eta t D0 j + 2 ≤ 3 * F ^ j := by
    intro j hj
    induction j with
    | zero =>
        norm_num [endpointC_zero]
    | succ j ih =>
        have hjR : j < R := by omega
        have hprev := ih (by omega)
        have hDj0 :=
          endpointD_pos htransport0 hD00 j
        have hDterm :=
          endpointD_terminal_le htransport0 htransport1 hD00
            (by omega : j ≤ R)
        have hinv :
            (endpointD transport D0 j)⁻¹ ≤
              (endpointD transport D0 R)⁻¹ :=
          (inv_le_inv₀ hDj0 hDR0).2 hDterm
        have hinvSq :
            ((endpointD transport D0 j)⁻¹) ^ 2 ≤
              ((endpointD transport D0 R)⁻¹) ^ 2 := by
          simpa [pow_two] using
            mul_self_le_mul_self
              (inv_nonneg.mpr hDj0.le) hinv
        have hCpos :=
          endpointC_pos (D0 := D0)
            htransport0 heta0 heta1 ht0 ht1 j
        have hC12 :
            endpointC transport eta t D0 j + 1 ≤
              endpointC transport eta t D0 j + 2 := by
          linarith
        have hcommon :
            1 ≤
              ((endpointD transport D0 R)⁻¹) ^ 2 *
                (endpointC transport eta t D0 j + 2) := by
          exact one_le_mul_of_one_le_of_one_le hDRinvSq
            (by linarith)
        rw [endpointC_succ]
        have hstage :
            linearPrefactorConstant transport eta *
                  (endpointC transport eta t D0 j + 1) *
                  ((endpointD transport D0 j)⁻¹) ^ 2 +
                Terras.quadraticWindowFixedGlobalConstant + 2
              ≤
            endpointStageK transport eta *
              (((endpointD transport D0 R)⁻¹) ^ 2 *
                (endpointC transport eta t D0 j + 2)) := by
          have hp0 :
              0 ≤ linearPrefactorConstant transport eta :=
            (linearPrefactorConstant_pos htransport0 heta0 heta1).le
          have hfirst :
              linearPrefactorConstant transport eta *
                    (endpointC transport eta t D0 j + 1) *
                    ((endpointD transport D0 j)⁻¹) ^ 2
                ≤
              linearPrefactorConstant transport eta *
                    (((endpointD transport D0 R)⁻¹) ^ 2 *
                      (endpointC transport eta t D0 j + 2)) := by
            have hprod :
                (endpointC transport eta t D0 j + 1) *
                      ((endpointD transport D0 j)⁻¹) ^ 2
                    ≤
                  (endpointC transport eta t D0 j + 2) *
                      ((endpointD transport D0 R)⁻¹) ^ 2 :=
              mul_le_mul hC12 hinvSq (sq_nonneg _) (by linarith)
            calc
              linearPrefactorConstant transport eta *
                    (endpointC transport eta t D0 j + 1) *
                    ((endpointD transport D0 j)⁻¹) ^ 2
                  =
                linearPrefactorConstant transport eta *
                  ((endpointC transport eta t D0 j + 1) *
                    ((endpointD transport D0 j)⁻¹) ^ 2) := by ring
              _ ≤
                linearPrefactorConstant transport eta *
                  ((endpointC transport eta t D0 j + 2) *
                    ((endpointD transport D0 R)⁻¹) ^ 2) :=
                mul_le_mul_of_nonneg_left hprod hp0
              _ = _ := by ring
          have htail :
              Terras.quadraticWindowFixedGlobalConstant + 2 ≤
                (Terras.quadraticWindowFixedGlobalConstant + 2) *
                  (((endpointD transport D0 R)⁻¹) ^ 2 *
                    (endpointC transport eta t D0 j + 2)) := by
            have hw2 :
                0 ≤ Terras.quadraticWindowFixedGlobalConstant + 2 := by
              linarith [linearWindowConstant_pos]
            simpa only [mul_one] using
              mul_le_mul_of_nonneg_left hcommon hw2
          have hcommon0 :
              0 ≤
                ((endpointD transport D0 R)⁻¹) ^ 2 *
                  (endpointC transport eta t D0 j + 2) :=
            mul_nonneg (sq_nonneg _)
              (by linarith : 0 ≤ endpointC transport eta t D0 j + 2)
          unfold endpointStageK
          nlinarith
        calc
          linearPrefactorConstant transport eta *
                (endpointC transport eta t D0 j + 1) *
                ((endpointD transport D0 j)⁻¹) ^ 2 +
              Terras.quadraticWindowFixedGlobalConstant + 2
              ≤ endpointStageK transport eta *
                  (((endpointD transport D0 R)⁻¹) ^ 2 *
                    (endpointC transport eta t D0 j + 2)) := hstage
          _ = F * (endpointC transport eta t D0 j + 2) := by
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
