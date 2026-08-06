/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik
-/
import CollatzEndpointTransport.QuadraticAppendix.QuantitativeQuadraticStage

/-!
# Quantitative Quadratic Schedule

The actual stage schedule and density recurrence of the quadratic bootstrap.

This file does not replace the recurrence by a generic majorant.  It defines
`lambda_j`, `t_j`, `mu_j`, the startup index `M0_j`, and the exact `C_j,D_j`
that arise from `envelopeGood_dense_one_stage`, then proves that the concrete
envelope set at every stage has those density parameters.
-/

namespace CollatzEndpointTransport

namespace QuantitativeDensity

open scoped Real

noncomputable section

def stageLambda (q : ℝ) (j : ℕ) : ℝ :=
  a0 * q ^ j

def stageTolerance (R : ℕ) (tR : ℝ) (j : ℕ) : ℝ :=
  kappa ^ (R - j) * tR

def stageMu (q : ℝ) (R : ℕ) (tR : ℝ) (j : ℕ) : ℝ :=
  stageLambda q j * (q - a0) -
    stageTolerance R tR j * (1 - stageLambda q j)

def stageStartupA (q : ℝ) : ℝ :=
  4 * (1 + bConst) / (3 * (q - a0))

def stageStartupIndex (q lambda : ℝ) : ℕ :=
  ⌈stageStartupA q / lambda⌉₊

def stageD (R : ℕ) (tR : ℝ) : ℕ → ℝ
  | 0 => min (stageTolerance R tR 0)
      (Terras.quadraticWindowDensityRate (stageTolerance R tR 0))
  | j + 1 => quadraticStageExponent (stageD R tR j)

def stageC (q : ℝ) : ℕ → ℝ
  | 0 => Terras.quadraticWindowFixedGlobalConstant
  | j + 1 =>
      quadraticPullbackGlobalConstant * (stageC q j + 1) +
        Terras.quadraticWindowFixedGlobalConstant +
        (2 : ℝ) ^ stageStartupIndex q (stageLambda q j)

@[simp] theorem stageLambda_zero (q : ℝ) :
    stageLambda q 0 = a0 := by simp [stageLambda]

theorem stageLambda_succ (q : ℝ) (j : ℕ) :
    stageLambda q (j + 1) = q * stageLambda q j := by
  simp [stageLambda, pow_succ]
  ring

theorem stageTolerance_succ
    {R j : ℕ} {tR : ℝ} (hj : j < R) :
    stageTolerance R tR j =
      kappa * stageTolerance R tR (j + 1) := by
  unfold stageTolerance
  have hsub : R - j = (R - (j + 1)) + 1 := by omega
  rw [hsub, pow_succ]
  ring

@[simp] theorem stageD_zero (R : ℕ) (tR : ℝ) :
    stageD R tR 0 =
      min (stageTolerance R tR 0)
        (Terras.quadraticWindowDensityRate
          (stageTolerance R tR 0)) := rfl

@[simp] theorem stageD_succ (R : ℕ) (tR : ℝ) (j : ℕ) :
    stageD R tR (j + 1) =
      quadraticStageExponent (stageD R tR j) := rfl

@[simp] theorem stageC_zero (q : ℝ) :
    stageC q 0 = Terras.quadraticWindowFixedGlobalConstant := rfl

@[simp] theorem stageC_succ (q : ℝ) (j : ℕ) :
    stageC q (j + 1) =
      quadraticPullbackGlobalConstant * (stageC q j + 1) +
        Terras.quadraticWindowFixedGlobalConstant +
        (2 : ℝ) ^ stageStartupIndex q (stageLambda q j) := rfl

theorem kappa_le_one : kappa ≤ 1 := by
  linarith [kappa_pos, kappa_lt_sixteenth]

theorem stageLambda_pos
    {q : ℝ} (hq : 0 < q) (j : ℕ) :
    0 < stageLambda q j := by
  unfold stageLambda
  exact mul_pos a0_pos (pow_pos hq j)

theorem stageLambda_lt_one
    {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (j : ℕ) :
    stageLambda q j < 1 := by
  have hpow : q ^ j ≤ 1 := pow_le_one₀ hq0.le hq1.le
  unfold stageLambda
  nlinarith [a0_pos, a0_lt_one]

theorem stageTolerance_pos
    {R j : ℕ} {tR : ℝ} (htR : 0 < tR) :
    0 < stageTolerance R tR j := by
  unfold stageTolerance
  exact mul_pos (pow_pos kappa_pos _) htR

theorem stageTolerance_le_terminal
    {R j : ℕ} {tR : ℝ} (htR : 0 ≤ tR) :
    stageTolerance R tR j ≤ tR := by
  unfold stageTolerance
  have hkpow : kappa ^ (R - j) ≤ 1 :=
    pow_le_one₀ kappa_pos.le kappa_le_one
  nlinarith [pow_nonneg kappa_pos.le (R - j)]

theorem stageTolerance_mono
    {R j : ℕ} {tR : ℝ} (hj : j < R) (htR : 0 ≤ tR) :
    stageTolerance R tR j ≤ stageTolerance R tR (j + 1) := by
  rw [stageTolerance_succ hj]
  have hnext : 0 ≤ stageTolerance R tR (j + 1) := by
    unfold stageTolerance
    exact mul_nonneg (pow_nonneg kappa_pos.le _) htR
  exact mul_le_of_le_one_left hnext kappa_le_one

theorem stageLambda_terminal_le
    {q : ℝ} {R j : ℕ}
    (hq0 : 0 < q) (hq1 : q < 1) (hj : j ≤ R) :
    stageLambda q R ≤ stageLambda q j := by
  unfold stageLambda
  have hp : q ^ R ≤ q ^ j :=
    pow_le_pow_of_le_one hq0.le hq1.le hj
  exact mul_le_mul_of_nonneg_left hp a0_pos.le

theorem stage_cap_of_terminal
    {q tR : ℝ} {R j : ℕ}
    (hq0 : 0 < q) (hqa : a0 < q) (hq1 : q < 1)
    (htR0 : 0 ≤ tR)
    (hcapR : tR ≤ cq q * stageLambda q R)
    (hj : j < R) :
    stageTolerance R tR (j + 1) ≤
      cq q * stageLambda q (j + 1) := by
  have ht := stageTolerance_le_terminal (R := R) (j := j + 1) htR0
  have hlam := stageLambda_terminal_le hq0 hq1 (Nat.succ_le_iff.mpr hj)
  have hcq := (cq_pos hq0 hqa).le
  exact ht.trans (hcapR.trans (mul_le_mul_of_nonneg_left hlam hcq))

theorem stage_tolerance_budget
    {R j : ℕ} {tR : ℝ}
    (hj : j < R) (htNext : stageTolerance R tR (j + 1) ≤ 1)
    (htR : 0 < tR) :
    stageTolerance R tR j + stageTolerance R tR j +
        stageTolerance R tR j * stageTolerance R tR j ≤
      stageTolerance R tR (j + 1) := by
  rw [stageTolerance_succ hj]
  have hnext0 := stageTolerance_pos (R := R) (j := j + 1) htR
  have hk0 := kappa_pos
  have hk1 := kappa_lt_sixteenth
  let x := stageTolerance R tR (j + 1)
  have hx0 : 0 ≤ x := by exact hnext0.le
  have hx2 : x ^ 2 ≤ x := by
    dsimp [x]
    nlinarith [sq_nonneg (stageTolerance R tR (j + 1))]
  have hksq0 : 0 ≤ kappa ^ 2 := sq_nonneg kappa
  have hquad : kappa ^ 2 * x ^ 2 ≤ kappa ^ 2 * x :=
    mul_le_mul_of_nonneg_left hx2 hksq0
  have hcoef : 2 * kappa + kappa ^ 2 ≤ 1 := by
    nlinarith [sq_nonneg kappa]
  have hlin : (2 * kappa + kappa ^ 2) * x ≤ x :=
    mul_le_of_le_one_left hx0 hcoef
  dsimp [x] at hquad hlin
  nlinarith

theorem stage_small_tolerance
    {q tR : ℝ} {R j : ℕ}
    (hq0 : 0 < q) (hqa : a0 < q) (hq1 : q < 1)
    (htR0 : 0 < tR)
    (hcapR : tR ≤ cq q * stageLambda q R)
    (hj : j < R) :
    stageTolerance R tR j ≤
      stageLambda q j * (q - a0) / 4 := by
  have hcap := stage_cap_of_terminal hq0 hqa hq1 htR0.le hcapR hj
  rw [stageTolerance_succ hj]
  have hmul := mul_le_mul_of_nonneg_left hcap kappa_pos.le
  calc
    kappa * stageTolerance R tR (j + 1)
        ≤ kappa * (cq q * stageLambda q (j + 1)) := hmul
    _ = stageLambda q j * (q - a0) / 4 := by
      rw [stageLambda_succ]
      have hid := kappa_mul_cq_mul q hq0
      calc
        kappa * (cq q * (q * stageLambda q j))
            = (kappa * cq q * q) * stageLambda q j := by ring
        _ = ((q - a0) / 4) * stageLambda q j := by rw [hid]
        _ = stageLambda q j * (q - a0) / 4 := by ring

theorem stageMu_lower
    {q tR : ℝ} {R j : ℕ}
    (hq0 : 0 < q) (hqa : a0 < q) (hq1 : q < 1)
    (htR0 : 0 < tR)
    (hcapR : tR ≤ cq q * stageLambda q R)
    (hj : j < R) :
    3 * (stageLambda q j * (q - a0)) / 4 ≤
      stageMu q R tR j := by
  have hsmall :=
    stage_small_tolerance hq0 hqa hq1 htR0 hcapR hj
  have hlam0 := stageLambda_pos hq0 j
  have hlam1 := stageLambda_lt_one hq0 hq1 j
  unfold stageMu
  have hfactor : 0 ≤ 1 - stageLambda q j := by linarith
  have hupper0 :
      0 ≤ stageLambda q j * (q - a0) / 4 :=
    div_nonneg (mul_nonneg hlam0.le (sub_nonneg.mpr hqa.le)) (by norm_num)
  have hprod :
      stageTolerance R tR j * (1 - stageLambda q j) ≤
        (stageLambda q j * (q - a0) / 4) * 1 := by
    exact mul_le_mul hsmall (by linarith) hfactor hupper0
  nlinarith

theorem stageMu_pos
    {q tR : ℝ} {R j : ℕ}
    (hq0 : 0 < q) (hqa : a0 < q) (hq1 : q < 1)
    (htR0 : 0 < tR)
    (hcapR : tR ≤ cq q * stageLambda q R)
    (hj : j < R) :
    0 < stageMu q R tR j := by
  have hlo := stageMu_lower hq0 hqa hq1 htR0 hcapR hj
  have hprod :
      0 < stageLambda q j * (q - a0) :=
    mul_pos (stageLambda_pos hq0 j) (by linarith)
  nlinarith

theorem stageStartupIndex_clears
    {q tR : ℝ} {R j : ℕ}
    (hq0 : 0 < q) (hqa : a0 < q) (hq1 : q < 1)
    (htR0 : 0 < tR)
    (hcapR : tR ≤ cq q * stageLambda q R)
    (hj : j < R) :
    (1 + bConst) / stageMu q R tR j ≤
      (stageStartupIndex q (stageLambda q j) : ℝ) := by
  have hmu := stageMu_lower hq0 hqa hq1 htR0 hcapR hj
  have hmu0 := stageMu_pos hq0 hqa hq1 htR0 hcapR hj
  have hlam0 := stageLambda_pos hq0 j
  have hqa0 : 0 < q - a0 := sub_pos.mpr hqa
  have hbase0 :
      0 < 3 * (stageLambda q j * (q - a0)) / 4 := by positivity
  have hbound :
      (1 + bConst) / stageMu q R tR j ≤
        stageStartupA q / stageLambda q j := by
    have hleft : 0 < 1 + bConst := by linarith [bConst_pos]
    calc
      (1 + bConst) / stageMu q R tR j
          ≤ (1 + bConst) /
              (3 * (stageLambda q j * (q - a0)) / 4) :=
        div_le_div_of_nonneg_left hleft.le hbase0 hmu
      _ = stageStartupA q / stageLambda q j := by
        unfold stageStartupA
        field_simp [ne_of_gt hqa0, ne_of_gt hlam0]
        ring
  exact hbound.trans (Nat.le_ceil _)

theorem stageD_invariants
    {R : ℕ} {tR : ℝ} (htR0 : 0 < tR) (htR1 : tR ≤ 1) :
    ∀ j : ℕ, j ≤ R →
      0 < stageD R tR j ∧
        stageD R tR j ≤ stageTolerance R tR j ∧
        stageD R tR j ≤ 1 := by
  intro j hj
  induction j with
  | zero =>
      have ht0 := stageTolerance_pos (R := R) (j := 0) htR0
      have ht1 := (stageTolerance_le_terminal
        (R := R) (j := 0) htR0.le).trans htR1
      have hwindow :=
        Terras.initialWindowGood_dense_quadratic_fixed ht0 ht1
      simp only [stageD_zero]
      exact ⟨lt_min ht0 hwindow.D_pos, min_le_left _ _,
        (min_le_right _ _).trans hwindow.D_le_one⟩
  | succ j ih =>
      have hjR : j < R := by omega
      have hprev := ih (by omega)
      have htmono :=
        stageTolerance_mono hjR htR0.le
      have hstep := quadraticExponentInvariantStep
        hprev.1.le hprev.2.2 hprev.2.1 htmono
        quadraticStageExponentConstant_pos.le
        quadraticStageExponentConstant_le_one
      rw [stageD_succ]
      exact ⟨quadraticStageExponent_pos hprev.1,
        hstep.2.2.1, hstep.2.2.2⟩

/-- **Concrete quadratic stage induction.**

At every stage the actual envelope set has exactly the recursively defined
`C_j,D_j`; no abstract `Y_{j+1} ≤ A Y_j²` surrogate appears in this
statement. -/
theorem envelopeGood_dense_stage
    {q tR : ℝ} {R : ℕ}
    (hq0 : 0 < q) (hqa : a0 < q) (hq1 : q < 1)
    (htR0 : 0 < tR) (htR1 : tR ≤ 1)
    (hcapR : tR ≤ cq q * stageLambda q R) :
    ∀ j : ℕ, j ≤ R →
      IsCDDense
        (EnvelopeGood (stageLambda q j) (stageTolerance R tR j))
        (stageC q j) (stageD R tR j) := by
  intro j hj
  induction j with
  | zero =>
      have ht0 := stageTolerance_pos (R := R) (j := 0) htR0
      have ht1 := (stageTolerance_le_terminal
        (R := R) (j := 0) htR0.le).trans htR1
      have hbase :=
        Terras.initialWindowGood_dense_quadratic_fixed ht0 ht1
      have hD0 :=
        (stageD_invariants (R := R) htR0 htR1 0 (by omega)).1
      have hdegraded := hbase.degrade_exponent hD0 (min_le_right _ _)
      simpa [stageLambda_zero, EnvelopeGood_a0, stageC_zero, stageD_zero]
        using hdegraded
  | succ j ih =>
      have hjR : j < R := by omega
      have hprev := ih (by omega)
      have hinv :=
        stageD_invariants (R := R) htR0 htR1 j (by omega)
      have htj0 := stageTolerance_pos (R := R) (j := j) htR0
      have htj1 := (stageTolerance_le_terminal
        (R := R) (j := j) htR0.le).trans htR1
      have htNext1 := (stageTolerance_le_terminal
        (R := R) (j := j + 1) htR0.le).trans htR1
      have hl0 := stageLambda_pos hq0 j
      have hl1 := stageLambda_lt_one hq0 hq1 j
      have hbudget := stage_tolerance_budget hjR htNext1 htR0
      have hmu0 :=
        stageMu_pos hq0 hqa hq1 htR0 hcapR hjR
      have hstartup :=
        stageStartupIndex_clears hq0 hqa hq1 htR0 hcapR hjR
      have hnext := envelopeGood_dense_one_stage
        (lambda := stageLambda q j)
        (q := q)
        (delta := stageTolerance R tR j)
        (zeta := stageTolerance R tR j)
        (t := stageTolerance R tR (j + 1))
        (mu := stageMu q R tR j)
        (M₀ := stageStartupIndex q (stageLambda q j))
        hprev hinv.2.1 hl0 hl1 htj0.le htj1 htj0 htj1
        hbudget rfl hmu0 hstartup
      simpa only [stageLambda_succ, stageC_succ, stageD_succ] using hnext

end

end QuantitativeDensity

end CollatzEndpointTransport
