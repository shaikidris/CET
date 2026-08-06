/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik
-/
import CollatzEndpointTransport.Linear.OptimizedLinearSchedule

/-!
# Optimized Linear Recurrence Bound

Scalar bounds for the concrete optimized-linear stage recurrence.

For a fixed terminal stage `R`, all earlier startup costs, inverse density
factors, and lambda factors are bounded by their terminal values.  This
gives a deliberately conservative but explicit multiplicative majorant.
Its logarithm has the required size

  O(R * (log(1 / D_R) + 1 / lambda_R + 1)).
-/

namespace CollatzEndpointTransport

namespace OptimizedLinearPullback

open scoped Real

noncomputable section

open QuantitativeDensity

def linearStartupB (q : ℝ) : ℝ :=
  (linearStartupA q + 1) * Real.log 2

def linearStageK (transport eta : ℝ) : ℝ :=
  linearPrefactorConstant transport eta +
    Terras.quadraticWindowFixedGlobalConstant + 3

theorem linearStartupA_pos
    {q : ℝ} (hqa : a0 < q) :
    0 < linearStartupA q := by
  unfold linearStartupA
  exact div_pos
    (mul_pos (by norm_num) (by linarith [bConst_pos]))
    (mul_pos (by norm_num) (sub_pos.mpr hqa))

theorem linearStartupB_pos
    {q : ℝ} (hqa : a0 < q) :
    0 < linearStartupB q := by
  unfold linearStartupB
  exact mul_pos (by linarith [linearStartupA_pos hqa])
    (Real.log_pos (by norm_num))

theorem linearWindowConstant_pos :
    0 < Terras.quadraticWindowFixedGlobalConstant := by
  have hhalf :
      (1 : ℝ) / 2 <
        Real.exp (-Terras.maximalBarrierC0) := by
    have hExpLog :
        Real.exp (-Real.log 2) = (1 : ℝ) / 2 := by
      rw [Real.exp_neg, Real.exp_log (by norm_num)]
      norm_num
    rw [← hExpLog]
    exact Real.exp_lt_exp.2
      (by linarith [Terras.maximalBarrierC0_lt_log_two])
  unfold Terras.quadraticWindowFixedGlobalConstant
  exact div_pos
    (mul_pos (by norm_num)
      Terras.quadraticWindowShellConstant_pos)
    (by linarith)

theorem linearStageK_pos
    {transport eta : ℝ}
    (htransport : 0 < transport)
    (heta0 : 0 < eta) (heta1 : eta < 1) :
    0 < linearStageK transport eta := by
  unfold linearStageK
  have hp :=
    linearPrefactorConstant_pos htransport heta0 heta1
  linarith [linearWindowConstant_pos]

theorem linearStageK_ge_one
    {transport eta : ℝ}
    (htransport : 0 < transport)
    (heta0 : 0 < eta) (heta1 : eta < 1) :
    1 ≤ linearStageK transport eta := by
  unfold linearStageK
  have hp := linearPrefactorConstant_pos htransport heta0 heta1
  have hw := linearWindowConstant_pos
  linarith

theorem linear_startup_pow_le_exp
    {q lambda : ℝ}
    (hqa : a0 < q) (hlambda0 : 0 < lambda)
    (hlambda1 : lambda ≤ 1) :
    (2 : ℝ) ^ linearStartupIndex q lambda ≤
      Real.exp (linearStartupB q / lambda) := by
  have hA0 := linearStartupA_pos hqa
  have hx0 : 0 ≤ linearStartupA q / lambda :=
    (div_pos hA0 hlambda0).le
  have hceil :
      (linearStartupIndex q lambda : ℝ) <
        linearStartupA q / lambda + 1 :=
    Nat.ceil_lt_add_one hx0
  have hexpArg :
      Real.log 2 * (linearStartupIndex q lambda : ℝ) ≤
        linearStartupB q / lambda := by
    unfold linearStartupB
    have hlog := Real.log_pos (by norm_num : (1 : ℝ) < 2)
    have hinv : 1 ≤ lambda⁻¹ :=
      (one_le_inv₀ hlambda0).2 hlambda1
    have hone :
        linearStartupA q / lambda + 1 ≤
          (linearStartupA q + 1) / lambda := by
      rw [div_eq_mul_inv, div_eq_mul_inv]
      nlinarith [hA0, inv_pos.mpr hlambda0]
    calc
      Real.log 2 * (linearStartupIndex q lambda : ℝ)
          ≤ Real.log 2 *
              (linearStartupA q / lambda + 1) :=
        mul_le_mul_of_nonneg_left hceil.le hlog.le
      _ ≤ Real.log 2 *
              ((linearStartupA q + 1) / lambda) :=
        mul_le_mul_of_nonneg_left hone hlog.le
      _ = (linearStartupA q + 1) * Real.log 2 /
            lambda := by ring
  rw [← Real.rpow_natCast,
    Real.rpow_def_of_pos (by norm_num)]
  exact Real.exp_le_exp.2 hexpArg

theorem linearD_exact
    (transport kappa : ℝ) (R : ℕ) (tR : ℝ) (j : ℕ) :
    linearD transport kappa R tR j =
      transport ^ j * linearD transport kappa R tR 0 := by
  exact linearRecurrence_exact
    transport (linearD transport kappa R tR 0)
    (linearD transport kappa R tR) rfl
    (fun n => linearD_succ transport kappa R tR n) j

theorem linearD_pos_all
    {transport kappa tR : ℝ} {R : ℕ}
    (htransport : 0 < transport)
    (hk : KappaAdmissible kappa)
    (htR : 0 < tR) :
    ∀ j, 0 < linearD transport kappa R tR j := by
  intro j
  rw [linearD_exact]
  have ht0 :=
    linearTolerance_pos (R := R) (j := 0) hk htR
  have hbase :
      0 <
        Terras.quadraticWindowDensityRate
          (linearTolerance kappa R tR 0) := by
    unfold Terras.quadraticWindowDensityRate
    exact div_pos
      (mul_pos Terras.maximalBarrierC0_pos
        (sq_pos_of_pos ht0))
      (Real.log_pos (by norm_num))
  exact mul_pos (pow_pos htransport j) (by simpa using hbase)

theorem linearD_terminal_le
    {transport kappa tR : ℝ} {R j : ℕ}
    (htransport0 : 0 < transport)
    (htransport1 : transport ≤ 1)
    (hk : KappaAdmissible kappa)
    (htR : 0 < tR)
    (hj : j ≤ R) :
    linearD transport kappa R tR R ≤
      linearD transport kappa R tR j := by
  have hp :
      transport ^ R ≤ transport ^ j :=
    pow_le_pow_of_le_one htransport0.le htransport1 hj
  have hbase0 :
      0 ≤ linearD transport kappa R tR 0 :=
    (linearD_pos_all htransport0 hk htR 0).le
  calc
    linearD transport kappa R tR R =
        transport ^ R * linearD transport kappa R tR 0 :=
      linearD_exact transport kappa R tR R
    _ ≤ transport ^ j * linearD transport kappa R tR 0 :=
      mul_le_mul_of_nonneg_right hp hbase0
    _ = linearD transport kappa R tR j :=
      (linearD_exact transport kappa R tR j).symm

theorem linearC_pos
    {q transport eta kappa tR : ℝ} {R : ℕ}
    (htransport : 0 < transport)
    (heta0 : 0 < eta) (heta1 : eta < 1) :
    ∀ j, 0 < linearC q transport eta kappa R tR j := by
  intro j
  induction j with
  | zero =>
      rw [linearC_zero]
      exact linearWindowConstant_pos
  | succ j ih =>
      rw [linearC_succ]
      have hp :=
        linearPrefactorConstant_pos htransport heta0 heta1
      have hfirst :
          0 ≤ linearPrefactorConstant transport eta *
              (linearC q transport eta kappa R tR j + 1) *
              ((linearD transport kappa R tR j)⁻¹) ^ 2 := by
        positivity
      have htail :
          0 < Terras.quadraticWindowFixedGlobalConstant +
              (2 : ℝ) ^
                linearStartupIndex q (linearLambda q j) :=
        add_pos linearWindowConstant_pos
          (pow_pos (by norm_num) _)
      linarith

theorem linear_startup_exp_terminal
    {q : ℝ} {R j : ℕ}
    (hq0 : 0 < q) (hqa : a0 < q) (hq1 : q < 1)
    (hj : j ≤ R) :
    (2 : ℝ) ^
        linearStartupIndex q (linearLambda q j) ≤
      Real.exp
        (linearStartupB q / linearLambda q R) := by
  have hpow :=
    linear_startup_pow_le_exp hqa
      (linearLambda_pos hq0 j)
      (linearLambda_lt_one hq0 hq1 j).le
  have hlam :=
    linearLambda_terminal_le hq0 hq1 hj
  have hmono :
      linearStartupB q / linearLambda q j ≤
        linearStartupB q / linearLambda q R :=
    div_le_div_of_nonneg_left
      (linearStartupB_pos hqa).le
      (linearLambda_pos hq0 R) hlam
  exact hpow.trans (Real.exp_le_exp.2 hmono)

/-- A terminal majorant for the exact prefactor recurrence. -/
theorem linearC_terminal_bound
    {q transport eta kappa tR : ℝ} {R : ℕ}
    (htransport0 : 0 < transport)
    (htransport1 : transport ≤ 1)
    (heta0 : 0 < eta) (heta1 : eta < 1)
    (hk : KappaAdmissible kappa)
    (htR0 : 0 < tR)
    (hDterminal1 :
      linearD transport kappa R tR R ≤ 1)
    (hq0 : 0 < q) (hqa : a0 < q) (hq1 : q < 1) :
    linearC q transport eta kappa R tR R + 2 ≤
      (linearStageK transport eta *
          ((linearD transport kappa R tR R)⁻¹) ^ 2 *
          Real.exp
            (linearStartupB q / linearLambda q R)) ^ R *
        (Terras.quadraticWindowFixedGlobalConstant + 2) := by
  let F :=
    linearStageK transport eta *
      ((linearD transport kappa R tR R)⁻¹) ^ 2 *
      Real.exp (linearStartupB q / linearLambda q R)
  have hDR0 :=
    linearD_pos_all (R := R) htransport0 hk htR0 R
  have hDRinv :
      1 ≤ (linearD transport kappa R tR R)⁻¹ :=
    (one_le_inv₀ hDR0).2 hDterminal1
  have hF1 : 1 ≤ F := by
    dsimp [F]
    have hK1 :=
      linearStageK_ge_one htransport0 heta0 heta1
    have hsq1 :
        1 ≤ ((linearD transport kappa R tR R)⁻¹) ^ 2 := by
      nlinarith [sq_nonneg
        ((linearD transport kappa R tR R)⁻¹)]
    have hexp1 :
        1 ≤ Real.exp
          (linearStartupB q / linearLambda q R) :=
      Real.one_le_exp
        (div_nonneg (linearStartupB_pos hqa).le
          (linearLambda_pos hq0 R).le)
    nlinarith [mul_le_mul hK1 hsq1
      (by norm_num : (0 : ℝ) ≤ 1)
      (by positivity :
        0 ≤ linearStageK transport eta)]
  have hF0 : 0 < F := zero_lt_one.trans_le hF1
  have hW0 :
      0 ≤ Terras.quadraticWindowFixedGlobalConstant + 2 := by
    linarith [linearWindowConstant_pos]
  have hind :
      ∀ j : ℕ, j ≤ R →
        linearC q transport eta kappa R tR j + 2 ≤
          F ^ j *
            (Terras.quadraticWindowFixedGlobalConstant + 2) := by
    intro j hj
    induction j with
    | zero => simp [linearC_zero]
    | succ j ih =>
        have hjR : j < R := by omega
        have hprev := ih (by omega)
        have hDj0 :=
          linearD_pos_all (R := R) htransport0 hk htR0 j
        have hDterm :=
          linearD_terminal_le
            (R := R) (j := j)
            htransport0 htransport1 hk htR0
            (by omega : j ≤ R)
        have hinv :
            (linearD transport kappa R tR j)⁻¹ ≤
              (linearD transport kappa R tR R)⁻¹ :=
          (inv_le_inv₀ hDj0 hDR0).2 hDterm
        have hinvSq :
            ((linearD transport kappa R tR j)⁻¹) ^ 2 ≤
              ((linearD transport kappa R tR R)⁻¹) ^ 2 := by
            simpa [pow_two] using
              mul_self_le_mul_self
                (inv_nonneg.mpr hDj0.le) hinv
        have hstartup :=
          linear_startup_exp_terminal hq0 hqa hq1
            (by omega : j ≤ R)
        have hC1 :
            1 ≤ linearC q transport eta kappa R tR j + 2 := by
          linarith [linearC_pos
            (q := q) (transport := transport)
            (eta := eta) (kappa := kappa)
            (tR := tR) (R := R)
            htransport0 heta0 heta1 j]
        have hcommon :
            1 ≤
              ((linearD transport kappa R tR R)⁻¹) ^ 2 *
                Real.exp
                  (linearStartupB q / linearLambda q R) *
                (linearC q transport eta kappa R tR j + 2) := by
          have hexp1 :
              1 ≤ Real.exp
                (linearStartupB q / linearLambda q R) :=
            Real.one_le_exp
              (div_nonneg (linearStartupB_pos hqa).le
                (linearLambda_pos hq0 R).le)
          have hsquare1 :
              1 ≤
                ((linearD transport kappa R tR R)⁻¹) ^ 2 := by
            nlinarith [sq_nonneg
              ((linearD transport kappa R tR R)⁻¹)]
          nlinarith [mul_le_mul hsquare1 hexp1
            (by norm_num : (0 : ℝ) ≤ 1)
            (by positivity :
              0 ≤ ((linearD transport kappa R tR R)⁻¹) ^ 2)]
        rw [linearC_succ]
        have hfactor :
            linearPrefactorConstant transport eta *
                  (linearC q transport eta kappa R tR j + 1) *
                  ((linearD transport kappa R tR j)⁻¹) ^ 2 +
                Terras.quadraticWindowFixedGlobalConstant +
                (2 : ℝ) ^
                  linearStartupIndex q (linearLambda q j) + 2
              ≤ F *
                  (linearC q transport eta kappa R tR j + 2) := by
          dsimp [F]
          have hfirst :
              linearPrefactorConstant transport eta *
                    (linearC q transport eta kappa R tR j + 1) *
                    ((linearD transport kappa R tR j)⁻¹) ^ 2
                ≤
              linearPrefactorConstant transport eta *
                    (((linearD transport kappa R tR R)⁻¹) ^ 2 *
                      Real.exp
                        (linearStartupB q / linearLambda q R) *
                      (linearC q transport eta kappa R tR j + 2)) := by
            have hC12 :
                linearC q transport eta kappa R tR j + 1 ≤
                  linearC q transport eta kappa R tR j + 2 := by linarith
            have hexp0 :
                0 ≤ Real.exp
                  (linearStartupB q / linearLambda q R) :=
              (Real.exp_pos _).le
            have hprod :
                (linearC q transport eta kappa R tR j + 1) *
                    ((linearD transport kappa R tR j)⁻¹) ^ 2 ≤
                  ((linearD transport kappa R tR R)⁻¹) ^ 2 *
                    Real.exp
                      (linearStartupB q / linearLambda q R) *
                    (linearC q transport eta kappa R tR j + 2) := by
              have hnonnegC :
                  0 ≤ linearC q transport eta kappa R tR j + 1 := by
                linarith
              calc
                (linearC q transport eta kappa R tR j + 1) *
                      ((linearD transport kappa R tR j)⁻¹) ^ 2
                    ≤ (linearC q transport eta kappa R tR j + 2) *
                      ((linearD transport kappa R tR R)⁻¹) ^ 2 :=
                  mul_le_mul hC12 hinvSq
                    (sq_nonneg _) (by linarith)
                _ ≤
                    (linearC q transport eta kappa R tR j + 2) *
                      (((linearD transport kappa R tR R)⁻¹) ^ 2 *
                        Real.exp
                          (linearStartupB q / linearLambda q R)) := by
                  have hE1 :
                      1 ≤ Real.exp
                        (linearStartupB q / linearLambda q R) :=
                    Real.one_le_exp
                      (div_nonneg (linearStartupB_pos hqa).le
                        (linearLambda_pos hq0 R).le)
                  apply mul_le_mul_of_nonneg_left _ (by linarith)
                  calc
                    ((linearD transport kappa R tR R)⁻¹) ^ 2 =
                        ((linearD transport kappa R tR R)⁻¹) ^ 2 *
                          1 := by ring
                    _ ≤
                        ((linearD transport kappa R tR R)⁻¹) ^ 2 *
                          Real.exp
                            (linearStartupB q / linearLambda q R) :=
                      mul_le_mul_of_nonneg_left hE1 (sq_nonneg _)
                _ = _ := by ring
            simpa [mul_assoc] using
              mul_le_mul_of_nonneg_left hprod
                (linearPrefactorConstant_pos
                  htransport0 heta0 heta1).le
          have hwindow :
              Terras.quadraticWindowFixedGlobalConstant ≤
                Terras.quadraticWindowFixedGlobalConstant *
                  (((linearD transport kappa R tR R)⁻¹) ^ 2 *
                    Real.exp
                      (linearStartupB q / linearLambda q R) *
                    (linearC q transport eta kappa R tR j + 2)) := by
            have hw0 : 0 ≤
                Terras.quadraticWindowFixedGlobalConstant := by
              exact linearWindowConstant_pos.le
            calc
              Terras.quadraticWindowFixedGlobalConstant =
                  Terras.quadraticWindowFixedGlobalConstant * 1 := by ring
              _ ≤ _ := mul_le_mul_of_nonneg_left hcommon hw0
          have hstartupTerm :
              (2 : ℝ) ^
                    linearStartupIndex q (linearLambda q j) + 2 ≤
                3 *
                  (((linearD transport kappa R tR R)⁻¹) ^ 2 *
                    Real.exp
                      (linearStartupB q / linearLambda q R) *
                    (linearC q transport eta kappa R tR j + 2)) := by
            have hstartCommon :
                (2 : ℝ) ^
                    linearStartupIndex q (linearLambda q j) ≤
                  ((linearD transport kappa R tR R)⁻¹) ^ 2 *
                    Real.exp
                      (linearStartupB q / linearLambda q R) *
                    (linearC q transport eta kappa R tR j + 2) := by
              exact hstartup.trans (by
                have hmult :
                    1 ≤
                      ((linearD transport kappa R tR R)⁻¹) ^ 2 *
                        (linearC q transport eta kappa R tR j + 2) := by
                  exact one_le_mul_of_one_le_of_one_le
                    (by
                      nlinarith [sq_nonneg
                        ((linearD transport kappa R tR R)⁻¹)])
                    hC1
                have hE0 := (Real.exp_pos
                  (linearStartupB q / linearLambda q R)).le
                calc
                  Real.exp
                        (linearStartupB q / linearLambda q R) =
                      1 * Real.exp
                        (linearStartupB q / linearLambda q R) := by ring
                  _ ≤
                      (((linearD transport kappa R tR R)⁻¹) ^ 2 *
                        (linearC q transport eta kappa R tR j + 2)) *
                        Real.exp
                          (linearStartupB q / linearLambda q R) :=
                    mul_le_mul_of_nonneg_right hmult hE0
                  _ = _ := by ring)
            have htwo :
                (2 : ℝ) ≤
                  2 *
                    (((linearD transport kappa R tR R)⁻¹) ^ 2 *
                      Real.exp
                        (linearStartupB q / linearLambda q R) *
                      (linearC q transport eta kappa R tR j + 2)) := by
                simpa only [mul_one] using
                  mul_le_mul_of_nonneg_left hcommon
                    (by norm_num : (0 : ℝ) ≤ 2)
            linarith only [hstartCommon, htwo]
          unfold linearStageK
          linarith only [hfirst, hwindow, hstartupTerm]
        exact hfactor.trans (by
          calc
            F * (linearC q transport eta kappa R tR j + 2)
                ≤ F *
                    (F ^ j *
                      (Terras.quadraticWindowFixedGlobalConstant + 2)) :=
              mul_le_mul_of_nonneg_left hprev hF0.le
            _ = F ^ (j + 1) *
                  (Terras.quadraticWindowFixedGlobalConstant + 2) := by
              rw [pow_succ]
              ring)
  simpa [F] using hind R le_rfl

end

end OptimizedLinearPullback

end CollatzEndpointTransport
