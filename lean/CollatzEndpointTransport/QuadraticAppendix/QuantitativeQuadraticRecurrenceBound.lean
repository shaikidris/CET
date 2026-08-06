/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik
-/
import CollatzEndpointTransport.QuadraticAppendix.QuantitativeQuadraticScheduleBounds

/-!
# Quantitative Quadratic Recurrence Bound

The scalar estimate for the concrete quadratic stage recurrence.

The principal theorem bounds the two quantities consumed by the final
shell-dependent argument:

  log (1 / D_R) + log (C_R + 2)
    <= K_q * 2^R * (1 + R + log (1 / t_R)).

Unlike `quadraticMajorant_iterate`, the statement below refers directly to
`stageC`, `stageD`, `stageLambda`, and `stageTolerance`.
-/

namespace CollatzEndpointTransport

namespace QuantitativeDensity

open scoped Real

noncomputable section

set_option maxHeartbeats 1000000

def windowExponentConstant : ℝ :=
  Terras.maximalBarrierC0 / Real.log 2

def lemmaSevenTwoConstant (q : ℝ) : ℝ :=
  16 +
    |Real.log quadraticStageExponentConstant| +
    |Real.log windowExponentConstant| +
    4 * |Real.log kappa| +
    |Real.log stagePrefactorK| +
    |Real.log (Terras.quadraticWindowFixedGlobalConstant + 1)| +
    4 * stageStartupB q / a0

theorem windowExponentConstant_pos : 0 < windowExponentConstant := by
  exact div_pos Terras.maximalBarrierC0_pos log_two_pos

theorem windowExponentConstant_le_one :
    windowExponentConstant ≤ 1 := by
  unfold windowExponentConstant
  exact (div_le_one log_two_pos).2
    Terras.maximalBarrierC0_lt_log_two.le

theorem lemmaSevenTwoConstant_pos
    {q : ℝ} (hqa : a0 < q) :
    0 < lemmaSevenTwoConstant q := by
  unfold lemmaSevenTwoConstant
  have hstartup :
      0 < 4 * stageStartupB q / a0 :=
    div_pos (mul_pos (by norm_num) (stageStartupB_pos hqa)) a0_pos
  have h₁ : 0 ≤ |Real.log quadraticStageExponentConstant| := abs_nonneg _
  have h₂ : 0 ≤ |Real.log windowExponentConstant| := abs_nonneg _
  have h₃ : 0 ≤ 4 * |Real.log kappa| := mul_nonneg (by norm_num) (abs_nonneg _)
  have h₄ : 0 ≤ |Real.log stagePrefactorK| := abs_nonneg _
  have h₅ :
      0 ≤ |Real.log (Terras.quadraticWindowFixedGlobalConstant + 1)| :=
    abs_nonneg _
  linarith

theorem stageTolerance_zero_eq
    (R : ℕ) (tR : ℝ) :
    stageTolerance R tR 0 = kappa ^ R * tR := by
  simp [stageTolerance]

theorem stageD_zero_exact
    {R : ℕ} {tR : ℝ}
    (htR0 : 0 < tR) (htR1 : tR ≤ 1) :
    stageD R tR 0 =
      windowExponentConstant * (kappa ^ R * tR) ^ 2 := by
  have ht0 := stageTolerance_pos (R := R) (j := 0) htR0
  have ht01 :=
    (stageTolerance_le_terminal (R := R) (j := 0) htR0.le).trans htR1
  have hwindow :
      Terras.quadraticWindowDensityRate (stageTolerance R tR 0) ≤
        stageTolerance R tR 0 := by
    have hrate :
        Terras.quadraticWindowDensityRate (stageTolerance R tR 0) =
          windowExponentConstant * (stageTolerance R tR 0) ^ 2 := by
      unfold Terras.quadraticWindowDensityRate windowExponentConstant
      ring
    rw [hrate]
    have htSq :
        (stageTolerance R tR 0) ^ 2 ≤
          stageTolerance R tR 0 := by
      nlinarith [sq_nonneg (stageTolerance R tR 0)]
    exact (mul_le_mul_of_nonneg_right
      windowExponentConstant_le_one (sq_nonneg _)).trans
      (by simpa using htSq)
  rw [stageD_zero, min_eq_right hwindow, stageTolerance_zero_eq]
  unfold Terras.quadraticWindowDensityRate windowExponentConstant
  ring

theorem stageD_pos_all
    {R : ℕ} {tR : ℝ}
    (htR0 : 0 < tR) (htR1 : tR ≤ 1) (j : ℕ) :
    0 < stageD R tR j := by
  by_cases hj : j ≤ R
  · exact (stageD_invariants htR0 htR1 j hj).1
  · induction j with
    | zero =>
        simp at hj
    | succ j ih =>
        rw [stageD_succ]
        exact quadraticStageExponent_pos
          (by
            by_cases hjR : j ≤ R
            · exact (stageD_invariants htR0 htR1 j hjR).1
            · exact ih hjR)

theorem half_lt_a0 : (1 : ℝ) / 2 < a0 := by
  unfold a0
  linarith [Terras.lg3_one_lt]

theorem half_lt_q {q : ℝ} (hqa : a0 < q) :
    (1 : ℝ) / 2 < q :=
  half_lt_a0.trans hqa

theorem inv_stageLambda_le_two_pow
    {q : ℝ} (hqa : a0 < q) (hq1 : q < 1) (R : ℕ) :
    (stageLambda q R)⁻¹ ≤ (2 / a0) * (2 : ℝ) ^ R := by
  have hq0 : 0 < q := a0_pos.trans hqa
  have hhalfq : (1 : ℝ) / 2 ≤ q := (half_lt_q hqa).le
  have hpow :
      ((1 : ℝ) / 2) ^ R ≤ q ^ R :=
    pow_le_pow_left₀ (by norm_num) hhalfq R
  have hqpow0 : 0 < q ^ R := pow_pos hq0 R
  have hinv :
      (q ^ R)⁻¹ ≤ (((1 : ℝ) / 2) ^ R)⁻¹ :=
    (inv_le_inv₀ hqpow0
      (by positivity : 0 < ((1 : ℝ) / 2) ^ R)).2 hpow
  have hinvHalf :
      (((1 : ℝ) / 2) ^ R)⁻¹ = (2 : ℝ) ^ R := by
    rw [← inv_pow]
    norm_num
  have ha0inv : a0⁻¹ ≤ 2 / a0 := by
    rw [show (2 : ℝ) / a0 = 2 * a0⁻¹ by ring]
    nlinarith [inv_pos.mpr a0_pos]
  unfold stageLambda
  rw [mul_inv_rev]
  calc
    (q ^ R)⁻¹ * a0⁻¹
        ≤ (((1 : ℝ) / 2) ^ R)⁻¹ * a0⁻¹ :=
      mul_le_mul_of_nonneg_right hinv (inv_pos.mpr a0_pos).le
    _ = a0⁻¹ * (2 : ℝ) ^ R := by
      rw [hinvHalf]
      ring
    _ ≤ (2 / a0) * (2 : ℝ) ^ R :=
      mul_le_mul_of_nonneg_right ha0inv (by positivity)

theorem log_inv_stageD_le
    {R : ℕ} {tR : ℝ}
    (htR0 : 0 < tR) (htR1 : tR ≤ 1) :
    Real.log (1 / stageD R tR R) ≤
      (8 +
          |Real.log quadraticStageExponentConstant| +
          |Real.log windowExponentConstant| +
          4 * |Real.log kappa|) *
        (2 : ℝ) ^ R *
        (1 + R + Real.log (1 / tR)) := by
  have hD0 := stageD_zero_exact (R := R) htR0 htR1
  have hc0 := quadraticStageExponentConstant_pos
  have hw0 := windowExponentConstant_pos
  have hk0 := kappa_pos
  have ht0 : 0 < kappa ^ R * tR := mul_pos (pow_pos hk0 R) htR0
  have hDR0 := stageD_pos_all (R := R) htR0 htR1 R
  have htRle : 1 ≤ 1 / tR := by
    rw [one_div]
    exact (one_le_inv₀ htR0).2 htR1
  have hlogt : 0 ≤ Real.log (1 / tR) :=
    Real.log_nonneg htRle
  have hfac : 0 ≤ 1 + (R : ℝ) + Real.log (1 / tR) := by positivity
  have hlogExact :
      Real.log (1 / stageD R tR R) =
        -(quadraticWeight R : ℝ) *
            Real.log quadraticStageExponentConstant -
          (2 ^ R : ℕ) * Real.log windowExponentConstant -
          2 * (2 ^ R : ℕ) * (R : ℝ) * Real.log kappa +
          2 * (2 ^ R : ℕ) * Real.log (1 / tR) := by
    rw [stageD_exact, hD0, one_div, Real.log_inv,
      Real.log_mul (pow_ne_zero _ hc0.ne')
        (pow_ne_zero _ (mul_pos hw0 (sq_pos_of_pos ht0)).ne'),
      Real.log_pow, Real.log_pow,
      Real.log_mul hw0.ne' (pow_ne_zero _ ht0.ne'),
      Real.log_pow,
      Real.log_mul (pow_ne_zero _ hk0.ne') htR0.ne',
      Real.log_pow]
    rw [show Real.log (1 / tR) = -Real.log tR by
      rw [one_div, Real.log_inv]]
    push_cast
    ring
  have hweight :
      (quadraticWeight R : ℝ) ≤ (2 : ℝ) ^ R := by
    have hwNat : quadraticWeight R ≤ 2 ^ R := by
      have hexact := quadraticWeight_add_one R
      omega
    exact_mod_cast hwNat
  have hpowRnonneg : 0 ≤ (2 : ℝ) ^ R := by positivity
  have hweight0 : 0 ≤ (quadraticWeight R : ℝ) := by positivity
  have hfactorOne :
      (1 : ℝ) ≤ 1 + (R : ℝ) + Real.log (1 / tR) := by
    linarith [(Nat.cast_nonneg R : (0 : ℝ) ≤ R)]
  have hweightTerm :
      -(quadraticWeight R : ℝ) *
          Real.log quadraticStageExponentConstant ≤
        |Real.log quadraticStageExponentConstant| *
          (2 : ℝ) ^ R *
          (1 + R + Real.log (1 / tR)) := by
    have hneg := neg_le_abs (Real.log quadraticStageExponentConstant)
    have h₁ :=
      mul_le_mul_of_nonneg_left hneg hweight0
    have h₂ :
        (quadraticWeight R : ℝ) *
            |Real.log quadraticStageExponentConstant| ≤
          ((2 : ℝ) ^ R) *
            |Real.log quadraticStageExponentConstant| :=
      mul_le_mul_of_nonneg_right hweight
        (abs_nonneg _)
    have h₃ :=
      mul_le_mul_of_nonneg_left hfactorOne
        (mul_nonneg
          (abs_nonneg (Real.log quadraticStageExponentConstant))
          hpowRnonneg)
    nlinarith [h₁, h₂, h₃]
  have hwindowTerm :
      -(2 ^ R : ℕ) * Real.log windowExponentConstant ≤
        |Real.log windowExponentConstant| * (2 : ℝ) ^ R *
          (1 + R + Real.log (1 / tR)) := by
    have hneg := neg_le_abs (Real.log windowExponentConstant)
    have h₁ :=
      mul_le_mul_of_nonneg_left hneg hpowRnonneg
    have h₂ :=
      mul_le_mul_of_nonneg_left hfactorOne
        (mul_nonneg
          (abs_nonneg (Real.log windowExponentConstant))
          hpowRnonneg)
    push_cast at h₁ ⊢
    nlinarith
  have hkappaTerm :
      -(2 * (2 ^ R : ℕ) * (R : ℝ) * Real.log kappa) ≤
        4 * |Real.log kappa| * (2 : ℝ) ^ R *
          (1 + R + Real.log (1 / tR)) := by
    have hR0 : 0 ≤ (R : ℝ) := Nat.cast_nonneg R
    have hneg := neg_le_abs (Real.log kappa)
    have hcoef : 0 ≤ 2 * (2 : ℝ) ^ R * (R : ℝ) := by positivity
    have h₁ := mul_le_mul_of_nonneg_left hneg hcoef
    have hRfac :
        (R : ℝ) ≤ 1 + R + Real.log (1 / tR) := by linarith
    have h₂ :=
      mul_le_mul_of_nonneg_left hRfac
        (mul_nonneg (by positivity : 0 ≤ 4 * |Real.log kappa|)
          hpowRnonneg)
    push_cast at h₁ ⊢
    nlinarith
  have htTerm :
      2 * (2 ^ R : ℕ) * Real.log (1 / tR) ≤
        8 * (2 : ℝ) ^ R *
          (1 + R + Real.log (1 / tR)) := by
    have hlogFac :
        Real.log (1 / tR) ≤
          1 + R + Real.log (1 / tR) := by
      linarith [(Nat.cast_nonneg R : (0 : ℝ) ≤ R)]
    have h₂ :=
      mul_le_mul_of_nonneg_left hlogFac
        (by positivity : 0 ≤ 8 * (2 : ℝ) ^ R)
    push_cast at h₂ ⊢
    nlinarith [mul_nonneg hpowRnonneg hlogt]
  rw [hlogExact]
  nlinarith [hweightTerm, hwindowTerm, hkappaTerm, htTerm]

theorem log_stageC_add_two_le
    {q : ℝ} {R : ℕ}
    (hqa : a0 < q) (hq1 : q < 1) :
    Real.log (stageC q R + 2) ≤
      (8 +
          |Real.log stagePrefactorK| +
          |Real.log (Terras.quadraticWindowFixedGlobalConstant + 1)| +
          4 * stageStartupB q / a0) *
        (2 : ℝ) ^ R *
        (1 + R) := by
  have hq0 : 0 < q := a0_pos.trans hqa
  have hC := stageC_terminal_bound (R := R) hq0 hqa hq1
  let E := Real.exp (stageStartupB q / stageLambda q R)
  let W := Terras.quadraticWindowFixedGlobalConstant + 1
  let Bnd := (stagePrefactorK * E) ^ R * W
  have hCpos := stageC_pos q R
  have hEpos : 0 < E := Real.exp_pos _
  have hWpos : 0 < W := by
    dsimp [W]
    linarith [quadraticWindowFixedGlobalConstant_pos']
  have hKpos := stagePrefactorK_pos
  have hboundPos : 0 < Bnd :=
    mul_pos (pow_pos (mul_pos hKpos hEpos) R) hWpos
  have hCB : stageC q R + 1 ≤ Bnd := by
    simpa [Bnd, E, W] using hC
  have htwoC :
      stageC q R + 2 ≤
        2 * Bnd := by
    have hC1 : 1 ≤ stageC q R + 1 := by linarith
    have hB1 : 1 ≤ Bnd := hC1.trans hCB
    linarith [hCB]
  have hlogDirect :
      Real.log (stageC q R + 2) ≤
        Real.log (2 * Bnd) :=
    Real.strictMonoOn_log.monotoneOn
      (Set.mem_Ioi.mpr (by linarith : 0 < stageC q R + 2))
      (Set.mem_Ioi.mpr (mul_pos (by norm_num) hboundPos))
      htwoC
  dsimp [Bnd] at hlogDirect
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0)
      (mul_ne_zero (pow_ne_zero _ (mul_pos hKpos hEpos).ne') hWpos.ne'),
    Real.log_mul (pow_ne_zero _ (mul_pos hKpos hEpos).ne') hWpos.ne',
    Real.log_pow,
    Real.log_mul hKpos.ne' hEpos.ne',
    Real.log_exp] at hlogDirect
  have hinvLambda := inv_stageLambda_le_two_pow hqa hq1 R
  have hstartup0 := (stageStartupB_pos hqa).le
  have hstartup :
      stageStartupB q / stageLambda q R ≤
        (2 * stageStartupB q / a0) * (2 : ℝ) ^ R := by
    rw [div_eq_mul_inv]
    calc
      stageStartupB q * (stageLambda q R)⁻¹
          ≤ stageStartupB q * ((2 / a0) * (2 : ℝ) ^ R) :=
        mul_le_mul_of_nonneg_left hinvLambda hstartup0
      _ = (2 * stageStartupB q / a0) * (2 : ℝ) ^ R := by ring
  have hlogK : Real.log stagePrefactorK ≤ |Real.log stagePrefactorK| :=
    le_abs_self _
  have hlogW :
      Real.log W ≤ |Real.log W| := le_abs_self _
  have hRpowNat : (R : ℕ) ≤ (2 : ℕ) ^ R := by
    exact Nat.le_of_lt R.lt_two_pow_self
  have hRpow : (R : ℝ) ≤ (2 : ℝ) ^ R := by
    exact_mod_cast hRpowNat
  have hpow0 : 0 ≤ (2 : ℝ) ^ R := by positivity
  have hR0 : 0 ≤ (R : ℝ) := Nat.cast_nonneg R
  have hconst0 :
      0 ≤ stageStartupB q / a0 :=
    (div_pos (stageStartupB_pos hqa) a0_pos).le
  have hRlogK :
      (R : ℝ) * Real.log stagePrefactorK ≤
        (R : ℝ) * |Real.log stagePrefactorK| :=
    mul_le_mul_of_nonneg_left hlogK hR0
  have hRstartup :
      (R : ℝ) * (stageStartupB q / stageLambda q R) ≤
        (R : ℝ) *
          ((2 * stageStartupB q / a0) * (2 : ℝ) ^ R) :=
    mul_le_mul_of_nonneg_left hstartup hR0
  dsimp [E, W] at hlogDirect hlogW
  have hpow1 : (1 : ℝ) ≤ (2 : ℝ) ^ R := by
    exact_mod_cast Nat.one_le_two_pow (n := R)
  have hF1 : (1 : ℝ) ≤ 1 + (R : ℝ) := by
    linarith [(Nat.cast_nonneg R : (0 : ℝ) ≤ R)]
  have hunit :
      (1 : ℝ) ≤ (2 : ℝ) ^ R * (1 + (R : ℝ)) := by
      have h := mul_le_mul hpow1 hF1 zero_le_one
        (by positivity : 0 ≤ (2 : ℝ) ^ R)
      simpa using h
  have hlogTwo :
      Real.log 2 ≤ (2 : ℝ) ^ R * (1 + (R : ℝ)) :=
    (Real.log_two_lt_d9.trans (by norm_num : (0.6931471808 : ℝ) < 1)).le.trans hunit
  have hKterm :
      (R : ℝ) * Real.log stagePrefactorK ≤
        |Real.log stagePrefactorK| * (2 : ℝ) ^ R *
          (1 + (R : ℝ)) := by
    calc
      (R : ℝ) * Real.log stagePrefactorK
          ≤ (R : ℝ) * |Real.log stagePrefactorK| := hRlogK
      _ ≤ |Real.log stagePrefactorK| * (2 : ℝ) ^ R *
            (1 + (R : ℝ)) := by
        have habs := abs_nonneg (Real.log stagePrefactorK)
        have hRle :
            (R : ℝ) ≤ (2 : ℝ) ^ R * (1 + (R : ℝ)) := by
          nlinarith [hRpow, hpow0]
        nlinarith
  have hstartupTerm :
      (R : ℝ) * (stageStartupB q / stageLambda q R) ≤
        (4 * stageStartupB q / a0) * (2 : ℝ) ^ R *
          (1 + (R : ℝ)) := by
    calc
      (R : ℝ) * (stageStartupB q / stageLambda q R)
          ≤ (R : ℝ) *
              ((2 * stageStartupB q / a0) * (2 : ℝ) ^ R) :=
        hRstartup
      _ ≤ (4 * stageStartupB q / a0) * (2 : ℝ) ^ R *
            (1 + (R : ℝ)) := by
        let X := (stageStartupB q / a0) * (2 : ℝ) ^ R
        have hX : 0 ≤ X := by
          dsimp [X]
          exact mul_nonneg hconst0 hpow0
        calc
          (R : ℝ) * ((2 * stageStartupB q / a0) * (2 : ℝ) ^ R)
              = 2 * (R : ℝ) * X := by
                dsimp [X]
                ring
          _ ≤ 4 * X * (1 + (R : ℝ)) := by nlinarith
          _ = (4 * stageStartupB q / a0) * (2 : ℝ) ^ R *
                (1 + (R : ℝ)) := by
                dsimp [X]
                ring
  have hWterm :
      Real.log (Terras.quadraticWindowFixedGlobalConstant + 1) ≤
        |Real.log (Terras.quadraticWindowFixedGlobalConstant + 1)| *
          (2 : ℝ) ^ R * (1 + (R : ℝ)) := by
    calc
      Real.log (Terras.quadraticWindowFixedGlobalConstant + 1)
          ≤ |Real.log
              (Terras.quadraticWindowFixedGlobalConstant + 1)| := hlogW
      _ ≤ _ := by
        have habs := abs_nonneg
          (Real.log (Terras.quadraticWindowFixedGlobalConstant + 1))
        have hmul :=
          mul_le_mul_of_nonneg_left hunit habs
        simpa [mul_assoc] using hmul
  have hDirectParts :
      Real.log (stageC q R + 2) ≤
        Real.log 2 +
          (R : ℝ) * Real.log stagePrefactorK +
          (R : ℝ) * (stageStartupB q / stageLambda q R) +
          Real.log (Terras.quadraticWindowFixedGlobalConstant + 1) := by
    convert hlogDirect using 1 <;> ring
  calc
    Real.log (stageC q R + 2)
        ≤ Real.log 2 +
            (R : ℝ) * Real.log stagePrefactorK +
            (R : ℝ) * (stageStartupB q / stageLambda q R) +
            Real.log (Terras.quadraticWindowFixedGlobalConstant + 1) :=
      hDirectParts
    _ ≤ ((2 : ℝ) ^ R * (1 + (R : ℝ))) +
          (|Real.log stagePrefactorK| * (2 : ℝ) ^ R *
            (1 + (R : ℝ))) +
          ((4 * stageStartupB q / a0) * (2 : ℝ) ^ R *
            (1 + (R : ℝ))) +
          (|Real.log (Terras.quadraticWindowFixedGlobalConstant + 1)| *
            (2 : ℝ) ^ R * (1 + (R : ℝ))) :=
      add_le_add (add_le_add (add_le_add hlogTwo hKterm) hstartupTerm) hWterm
    _ ≤ (8 +
          |Real.log stagePrefactorK| +
          |Real.log (Terras.quadraticWindowFixedGlobalConstant + 1)| +
          4 * stageStartupB q / a0) *
        (2 : ℝ) ^ R * (1 + R) := by
      have hnonneg :
          0 ≤ (2 : ℝ) ^ R * (1 + (R : ℝ)) := by positivity
      nlinarith

/-- **Bootstrap bound for the actual quadratic recurrence.** -/
theorem concrete_quadratic_bootstrap_bound
    {q tR : ℝ} {R : ℕ}
    (hqa : a0 < q) (hq1 : q < 1)
    (htR0 : 0 < tR) (htR1 : tR ≤ 1) :
    Real.log (1 / stageD R tR R) +
        Real.log (stageC q R + 2) ≤
      lemmaSevenTwoConstant q * (2 : ℝ) ^ R *
        (1 + R + Real.log (1 / tR)) := by
  have hD := log_inv_stageD_le (R := R) htR0 htR1
  have hC := log_stageC_add_two_le (R := R) hqa hq1
  have hlogt :
      0 ≤ Real.log (1 / tR) := by
    apply Real.log_nonneg
    rw [one_div]
    exact (one_le_inv₀ htR0).2 htR1
  have hR0 : 0 ≤ (R : ℝ) := Nat.cast_nonneg R
  have hpow0 : 0 ≤ (2 : ℝ) ^ R := by positivity
  let A :=
    8 + |Real.log quadraticStageExponentConstant| +
      |Real.log windowExponentConstant| + 4 * |Real.log kappa|
  let B :=
    8 + |Real.log stagePrefactorK| +
      |Real.log (Terras.quadraticWindowFixedGlobalConstant + 1)| +
      4 * stageStartupB q / a0
  have hF :
      1 + (R : ℝ) ≤ 1 + R + Real.log (1 / tR) := by
    linarith
  have hB0 : 0 ≤ B := by
    dsimp [B]
    have hstartup :
        0 ≤ 4 * stageStartupB q / a0 :=
      div_nonneg
        (mul_nonneg (by norm_num) (stageStartupB_pos hqa).le)
        a0_pos.le
    nlinarith [abs_nonneg (Real.log stagePrefactorK),
      abs_nonneg
        (Real.log (Terras.quadraticWindowFixedGlobalConstant + 1))]
  have hC' :
      Real.log (stageC q R + 2) ≤
        B * (2 : ℝ) ^ R *
          (1 + R + Real.log (1 / tR)) := by
    exact hC.trans
      (mul_le_mul_of_nonneg_left hF
        (mul_nonneg hB0 hpow0))
  calc
    Real.log (1 / stageD R tR R) +
          Real.log (stageC q R + 2)
        ≤ A * (2 : ℝ) ^ R *
              (1 + R + Real.log (1 / tR)) +
            B * (2 : ℝ) ^ R *
              (1 + R + Real.log (1 / tR)) :=
      add_le_add hD hC'
    _ = lemmaSevenTwoConstant q * (2 : ℝ) ^ R *
          (1 + R + Real.log (1 / tR)) := by
      unfold lemmaSevenTwoConstant
      dsimp [A, B]
      ring

end

end QuantitativeDensity

end CollatzEndpointTransport
