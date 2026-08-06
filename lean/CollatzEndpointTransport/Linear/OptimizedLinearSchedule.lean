/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik
-/
import CollatzEndpointTransport.Linear.OptimizedLinearEnvelopeStage

/-!
# Optimized Linear Schedule

The actual optimized-linear envelope schedule.

The tolerance ratio is parameterized by any `kappa` satisfying
`2*kappa + kappa^2 < 1`.  The density exponent is initialized by the
maximal-barrier window theorem and then follows the exact linear recurrence

  D_(j+1) = transport * D_j.

The main theorem proves the concrete envelope set at every stage has the
recursively defined density parameters.
-/

namespace CollatzEndpointTransport

namespace OptimizedLinearPullback

open scoped Real

noncomputable section

open QuantitativeDensity

def linearLambda (q : ℝ) (j : ℕ) : ℝ :=
  a0 * q ^ j

def linearTolerance
    (kappa : ℝ) (R : ℕ) (tR : ℝ) (j : ℕ) : ℝ :=
  kappa ^ (R - j) * tR

def linearMu
    (q kappa : ℝ) (R : ℕ) (tR : ℝ) (j : ℕ) : ℝ :=
  linearLambda q j * (q - a0) -
    linearTolerance kappa R tR j *
      (1 - linearLambda q j)

def linearStartupA (q : ℝ) : ℝ :=
  4 * (1 + bConst) / (3 * (q - a0))

def linearStartupIndex (q lambda : ℝ) : ℕ :=
  ⌈linearStartupA q / lambda⌉₊

def linearD
    (transport kappa : ℝ) (R : ℕ) (tR : ℝ) : ℕ → ℝ
  | 0 =>
      Terras.quadraticWindowDensityRate
        (linearTolerance kappa R tR 0)
  | j + 1 => transport * linearD transport kappa R tR j

def linearC
    (q transport eta kappa : ℝ)
    (R : ℕ) (tR : ℝ) : ℕ → ℝ
  | 0 => Terras.quadraticWindowFixedGlobalConstant
  | j + 1 =>
      linearPrefactorConstant transport eta *
          (linearC q transport eta kappa R tR j + 1) *
          ((linearD transport kappa R tR j)⁻¹) ^ 2 +
        Terras.quadraticWindowFixedGlobalConstant +
        (2 : ℝ) ^
          linearStartupIndex q (linearLambda q j)

@[simp] theorem linearLambda_zero (q : ℝ) :
    linearLambda q 0 = a0 := by
  simp [linearLambda]

theorem linearLambda_succ (q : ℝ) (j : ℕ) :
    linearLambda q (j + 1) = q * linearLambda q j := by
  simp [linearLambda, pow_succ]
  ring

theorem linearTolerance_succ
    {kappa tR : ℝ} {R j : ℕ} (hj : j < R) :
    linearTolerance kappa R tR j =
      kappa * linearTolerance kappa R tR (j + 1) := by
  unfold linearTolerance
  have hsub : R - j = (R - (j + 1)) + 1 := by omega
  rw [hsub, pow_succ]
  ring

@[simp] theorem linearD_zero
    (transport kappa : ℝ) (R : ℕ) (tR : ℝ) :
    linearD transport kappa R tR 0 =
      Terras.quadraticWindowDensityRate
        (linearTolerance kappa R tR 0) := rfl

@[simp] theorem linearD_succ
    (transport kappa : ℝ) (R : ℕ) (tR : ℝ) (j : ℕ) :
    linearD transport kappa R tR (j + 1) =
      transport * linearD transport kappa R tR j := rfl

@[simp] theorem linearC_zero
    (q transport eta kappa : ℝ) (R : ℕ) (tR : ℝ) :
    linearC q transport eta kappa R tR 0 =
      Terras.quadraticWindowFixedGlobalConstant := rfl

@[simp] theorem linearC_succ
    (q transport eta kappa : ℝ)
    (R : ℕ) (tR : ℝ) (j : ℕ) :
    linearC q transport eta kappa R tR (j + 1) =
      linearPrefactorConstant transport eta *
          (linearC q transport eta kappa R tR j + 1) *
          ((linearD transport kappa R tR j)⁻¹) ^ 2 +
        Terras.quadraticWindowFixedGlobalConstant +
        (2 : ℝ) ^
          linearStartupIndex q (linearLambda q j) := rfl

theorem kappa_lt_one
    {kappa : ℝ} (hk : KappaAdmissible kappa) :
    kappa < 1 := by
  change 0 < kappa ∧ 2 * kappa + kappa ^ 2 < 1 at hk
  rcases hk with ⟨hk0, hkquad⟩
  nlinarith [sq_nonneg kappa]

theorem kappa_le_one
    {kappa : ℝ} (hk : KappaAdmissible kappa) :
    kappa ≤ 1 :=
  (kappa_lt_one hk).le

theorem linearLambda_pos
    {q : ℝ} (hq : 0 < q) (j : ℕ) :
    0 < linearLambda q j := by
  unfold linearLambda
  exact mul_pos a0_pos (pow_pos hq j)

theorem linearLambda_lt_one
    {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (j : ℕ) :
    linearLambda q j < 1 := by
  have hpow : q ^ j ≤ 1 := pow_le_one₀ hq0.le hq1.le
  unfold linearLambda
  nlinarith [a0_pos, a0_lt_one]

theorem linearTolerance_pos
    {kappa tR : ℝ} {R j : ℕ}
    (hk : KappaAdmissible kappa) (htR : 0 < tR) :
    0 < linearTolerance kappa R tR j := by
  unfold linearTolerance
  exact mul_pos (pow_pos hk.1 _) htR

theorem linearTolerance_le_terminal
    {kappa tR : ℝ} {R j : ℕ}
    (hk : KappaAdmissible kappa) (htR : 0 ≤ tR) :
    linearTolerance kappa R tR j ≤ tR := by
  unfold linearTolerance
  have hkpow : kappa ^ (R - j) ≤ 1 :=
    pow_le_one₀ hk.1.le (kappa_le_one hk)
  nlinarith [pow_nonneg hk.1.le (R - j)]

theorem linearTolerance_mono
    {kappa tR : ℝ} {R j : ℕ}
    (hk : KappaAdmissible kappa)
    (hj : j < R) (htR : 0 ≤ tR) :
    linearTolerance kappa R tR j ≤
      linearTolerance kappa R tR (j + 1) := by
  rw [linearTolerance_succ hj]
  have hnext :
      0 ≤ linearTolerance kappa R tR (j + 1) := by
    unfold linearTolerance
    exact mul_nonneg (pow_nonneg hk.1.le _) htR
  exact mul_le_of_le_one_left hnext (kappa_le_one hk)

theorem linearLambda_terminal_le
    {q : ℝ} {R j : ℕ}
    (hq0 : 0 < q) (hq1 : q < 1) (hj : j ≤ R) :
    linearLambda q R ≤ linearLambda q j := by
  unfold linearLambda
  have hp : q ^ R ≤ q ^ j :=
    pow_le_pow_of_le_one hq0.le hq1.le hj
  exact mul_le_mul_of_nonneg_left hp a0_pos.le

theorem linearStage_cap_of_terminal
    {q kappa tR : ℝ} {R j : ℕ}
    (hk : KappaAdmissible kappa)
    (hq0 : 0 < q) (hqa : a0 < q) (hq1 : q < 1)
    (htR0 : 0 ≤ tR)
    (hcapR :
      tR ≤ cq kappa q * linearLambda q R)
    (hj : j < R) :
    linearTolerance kappa R tR (j + 1) ≤
      cq kappa q * linearLambda q (j + 1) := by
  have ht :=
    linearTolerance_le_terminal (R := R) (j := j + 1) hk htR0
  have hlam :=
    linearLambda_terminal_le hq0 hq1
      (Nat.succ_le_iff.mpr hj)
  have hcq :
      0 ≤ cq kappa q := by
    unfold cq
    exact div_nonneg (sub_nonneg.mpr hqa.le)
      (mul_nonneg
        (mul_nonneg (by norm_num) hk.1.le) hq0.le)
  exact ht.trans
    (hcapR.trans (mul_le_mul_of_nonneg_left hlam hcq))

theorem linearStage_small_tolerance
    {q kappa tR : ℝ} {R j : ℕ}
    (hk : KappaAdmissible kappa)
    (hq0 : 0 < q) (hqa : a0 < q) (hq1 : q < 1)
    (htR0 : 0 < tR)
    (hcapR :
      tR ≤ cq kappa q * linearLambda q R)
    (hj : j < R) :
    linearTolerance kappa R tR j ≤
      linearLambda q j * (q - a0) / 4 := by
  have hcap :=
    linearStage_cap_of_terminal hk hq0 hqa hq1
      htR0.le hcapR hj
  rw [linearTolerance_succ hj]
  have hmul :=
    mul_le_mul_of_nonneg_left hcap hk.1.le
  calc
    kappa * linearTolerance kappa R tR (j + 1)
        ≤ kappa *
            (cq kappa q * linearLambda q (j + 1)) := hmul
    _ = linearLambda q j * (q - a0) / 4 := by
      rw [linearLambda_succ]
      have hid := kappa_mul_cq_mul hk.1 hq0
      calc
        kappa * (cq kappa q * (q * linearLambda q j))
            = (kappa * cq kappa q * q) *
                linearLambda q j := by ring
        _ = ((q - a0) / 4) * linearLambda q j := by
          rw [hid]
        _ = linearLambda q j * (q - a0) / 4 := by ring

theorem linearStageMu_lower
    {q kappa tR : ℝ} {R j : ℕ}
    (hk : KappaAdmissible kappa)
    (hq0 : 0 < q) (hqa : a0 < q) (hq1 : q < 1)
    (htR0 : 0 < tR)
    (hcapR :
      tR ≤ cq kappa q * linearLambda q R)
    (hj : j < R) :
    3 * (linearLambda q j * (q - a0)) / 4 ≤
      linearMu q kappa R tR j := by
  have hsmall :=
    linearStage_small_tolerance hk hq0 hqa hq1
      htR0 hcapR hj
  have hlam0 := linearLambda_pos hq0 j
  have hlam1 := linearLambda_lt_one hq0 hq1 j
  unfold linearMu
  have hfactor : 0 ≤ 1 - linearLambda q j := by linarith
  have hupper0 :
      0 ≤ linearLambda q j * (q - a0) / 4 :=
    div_nonneg
      (mul_nonneg hlam0.le (sub_nonneg.mpr hqa.le))
      (by norm_num)
  have hprod :
      linearTolerance kappa R tR j *
          (1 - linearLambda q j) ≤
        (linearLambda q j * (q - a0) / 4) * 1 :=
    mul_le_mul hsmall (by linarith) hfactor hupper0
  nlinarith

theorem linearStageMu_pos
    {q kappa tR : ℝ} {R j : ℕ}
    (hk : KappaAdmissible kappa)
    (hq0 : 0 < q) (hqa : a0 < q) (hq1 : q < 1)
    (htR0 : 0 < tR)
    (hcapR :
      tR ≤ cq kappa q * linearLambda q R)
    (hj : j < R) :
    0 < linearMu q kappa R tR j := by
  have hlo :=
    linearStageMu_lower hk hq0 hqa hq1 htR0 hcapR hj
  have hprod :
      0 < linearLambda q j * (q - a0) :=
    mul_pos (linearLambda_pos hq0 j) (sub_pos.mpr hqa)
  nlinarith

theorem linearStageStartupIndex_clears
    {q kappa tR : ℝ} {R j : ℕ}
    (hk : KappaAdmissible kappa)
    (hq0 : 0 < q) (hqa : a0 < q) (hq1 : q < 1)
    (htR0 : 0 < tR)
    (hcapR :
      tR ≤ cq kappa q * linearLambda q R)
    (hj : j < R) :
    (1 + bConst) / linearMu q kappa R tR j ≤
      (linearStartupIndex q (linearLambda q j) : ℝ) := by
  have hmu :=
    linearStageMu_lower hk hq0 hqa hq1 htR0 hcapR hj
  have hlam0 := linearLambda_pos hq0 j
  have hbase0 :
      0 < 3 * (linearLambda q j * (q - a0)) / 4 := by
    exact div_pos
      (mul_pos (by norm_num)
        (mul_pos (linearLambda_pos hq0 j) (sub_pos.mpr hqa)))
      (by norm_num)
  have hbound :
      (1 + bConst) / linearMu q kappa R tR j ≤
        linearStartupA q / linearLambda q j := by
    have hleft : 0 < 1 + bConst := by linarith [bConst_pos]
    calc
      (1 + bConst) / linearMu q kappa R tR j
          ≤ (1 + bConst) /
              (3 * (linearLambda q j * (q - a0)) / 4) :=
        div_le_div_of_nonneg_left hleft.le hbase0 hmu
      _ = linearStartupA q / linearLambda q j := by
        unfold linearStartupA
        field_simp [ne_of_gt (sub_pos.mpr hqa),
          ne_of_gt hlam0]
        ring
  exact hbound.trans (Nat.le_ceil _)

theorem linearTolerance_budget
    {kappa tR : ℝ} {R j : ℕ}
    (hk : KappaAdmissible kappa)
    (hj : j < R)
    (htNext : linearTolerance kappa R tR (j + 1) ≤ 1)
    (htR : 0 < tR) :
    linearTolerance kappa R tR j +
        linearTolerance kappa R tR j +
        linearTolerance kappa R tR j *
          linearTolerance kappa R tR j ≤
      linearTolerance kappa R tR (j + 1) := by
  rw [linearTolerance_succ hj]
  have hnext0 :=
    (linearTolerance_pos
      (R := R) (j := j + 1) hk htR).le
  simpa [two_mul, pow_two] using
    tolerance_budget hk hnext0 htNext

theorem linearD_invariants
    {transport kappa tR Dcut : ℝ} {R : ℕ}
    (htransport0 : 0 < transport) (htransport1 : transport ≤ 1)
    (hk : KappaAdmissible kappa)
    (htR0 : 0 < tR) (htR1 : tR ≤ 1)
    (hDcut :
      linearD transport kappa R tR 0 ≤ Dcut) :
    ∀ j : ℕ, j ≤ R →
      0 < linearD transport kappa R tR j ∧
      linearD transport kappa R tR j ≤
        Terras.quadraticWindowDensityRate
          (linearTolerance kappa R tR j) ∧
      linearD transport kappa R tR j ≤ 1 ∧
      linearD transport kappa R tR j ≤ Dcut := by
  intro j hj
  induction j with
  | zero =>
      have ht0 :=
        linearTolerance_pos (R := R) (j := 0) hk htR0
      have ht1 :=
        (linearTolerance_le_terminal
          (R := R) (j := 0) hk htR0.le).trans htR1
      have hwindow :=
        Terras.initialWindowGood_dense_quadratic_fixed ht0 ht1
      simp only [linearD_zero]
      exact ⟨hwindow.D_pos, le_rfl, hwindow.D_le_one, hDcut⟩
  | succ j ih =>
      have hjR : j < R := by omega
      have hprev := ih (by omega)
      have htmono :=
        linearTolerance_mono hk hjR htR0.le
      have hrateMono :
          Terras.quadraticWindowDensityRate
              (linearTolerance kappa R tR j) ≤
            Terras.quadraticWindowDensityRate
              (linearTolerance kappa R tR (j + 1)) := by
        unfold Terras.quadraticWindowDensityRate
        have hsq :
            (linearTolerance kappa R tR j) ^ 2 ≤
              (linearTolerance kappa R tR (j + 1)) ^ 2 := by
          nlinarith [linearTolerance_pos
            (R := R) (j := j) hk htR0,
            linearTolerance_pos
              (R := R) (j := j + 1) hk htR0]
        have hmul :=
          mul_le_mul_of_nonneg_left hsq
            (div_nonneg Terras.maximalBarrierC0_pos.le
              (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le)
        convert hmul using 1 <;> ring
      rw [linearD_succ]
      refine ⟨mul_pos htransport0 hprev.1, ?_, ?_, ?_⟩
      · exact
          (mul_le_of_le_one_left hprev.1.le htransport1).trans
            (hprev.2.1.trans hrateMono)
      · exact
          (mul_le_of_le_one_left hprev.1.le htransport1).trans
            hprev.2.2.1
      · exact
          (mul_le_of_le_one_left hprev.1.le htransport1).trans
            hprev.2.2.2

/-- **Concrete optimized-linear stage induction.** -/
theorem envelopeGood_dense_linear_stage
    {q transport kappa tR Dcut : ℝ} {R : ℕ}
    (htransport0 : 0 < transport)
    (htransportLimit : transport < asymptoticRateLimit)
    (hk : KappaAdmissible kappa)
    (hq0 : 0 < q) (hqa : a0 < q) (hq1 : q < 1)
    (htR0 : 0 < tR) (htR1 : tR ≤ 1)
    (hcapR :
      tR ≤ cq kappa q * linearLambda q R)
    (hDcut0 : 0 < Dcut) (hDcut1 : Dcut ≤ 1)
    (hcut :
      ∀ D : ℝ, 0 < D → D ≤ Dcut →
        transport * D ≤
          shellRate (asymptoticEta transport) D /
            Real.log 2)
    (hDzero :
      linearD transport kappa R tR 0 ≤ Dcut) :
    ∀ j : ℕ, j ≤ R →
      IsCDDense
        (EnvelopeGood
          (linearLambda q j)
          (linearTolerance kappa R tR j))
        (linearC q transport (asymptoticEta transport)
          kappa R tR j)
        (linearD transport kappa R tR j) := by
  have htransport1 :
      transport ≤ 1 :=
    (htransportLimit.trans asymptoticRateLimit_lt_one).le
  have heta0 := asymptoticEta_pos htransport0
  have heta1 := asymptoticEta_lt_one htransportLimit
  intro j hj
  induction j with
  | zero =>
      have ht0 :=
        linearTolerance_pos (R := R) (j := 0) hk htR0
      have ht1 :=
        (linearTolerance_le_terminal
          (R := R) (j := 0) hk htR0.le).trans htR1
      have hbase :=
        Terras.initialWindowGood_dense_quadratic_fixed ht0 ht1
      simpa [linearLambda_zero, EnvelopeGood_a0,
        linearC_zero, linearD_zero] using hbase
  | succ j ih =>
      have hjR : j < R := by omega
      have hprev := ih (by omega)
      have hinv :=
        linearD_invariants htransport0 htransport1 hk
          htR0 htR1 hDzero j (by omega)
      have htj0 :=
        linearTolerance_pos (R := R) (j := j) hk htR0
      have htj1 :=
        (linearTolerance_le_terminal
          (R := R) (j := j) hk htR0.le).trans htR1
      have htNext1 :=
        (linearTolerance_le_terminal
          (R := R) (j := j + 1) hk htR0.le).trans htR1
      have hl0 := linearLambda_pos hq0 j
      have hl1 := linearLambda_lt_one hq0 hq1 j
      have hbudget :=
        linearTolerance_budget hk hjR htNext1 htR0
      have hmu0 :=
        linearStageMu_pos hk hq0 hqa hq1
          htR0 hcapR hjR
      have hstartup :=
        linearStageStartupIndex_clears hk hq0 hqa hq1
          htR0 hcapR hjR
      have hlinear := hcut _ hinv.1 hinv.2.2.2
      have hnext1 :
          transport * linearD transport kappa R tR j ≤ 1 :=
        (mul_le_of_le_one_left hinv.1.le htransport1).trans
          hinv.2.2.1
      have hwindow :
          transport * linearD transport kappa R tR j ≤
            Terras.quadraticWindowDensityRate
              (linearTolerance kappa R tR j) :=
        (mul_le_of_le_one_left hinv.1.le htransport1).trans
          hinv.2.1
      have hnext :=
        envelopeGood_dense_one_linear_stage
          (lambda := linearLambda q j)
          (q := q)
          (delta := linearTolerance kappa R tR j)
          (zeta := linearTolerance kappa R tR j)
          (t := linearTolerance kappa R tR (j + 1))
          (mu := linearMu q kappa R tR j)
          (M₀ :=
            linearStartupIndex q (linearLambda q j))
          (eta := asymptoticEta transport)
          (transport := transport)
          hprev hl0 hl1 htj0.le htj1 htj0 htj1
          hbudget rfl hmu0 hstartup heta0 heta1
          htransport0 hlinear hwindow hnext1
      simpa only [linearLambda_succ, linearC_succ,
        linearD_succ] using hnext

end

end OptimizedLinearPullback

end CollatzEndpointTransport
