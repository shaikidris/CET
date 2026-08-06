/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik
-/
import CollatzEndpointTransport.Linear.OptimizedLinearPowerShellVanishing
import CollatzEndpointTransport.Common.QuantitativeEndpoint

/-!
# Optimized Linear Power Budget

Terminal endpoint budget for the optimized linear power schedule.

For a requested orbit exponent

  epsilon_M = (M+4)^(-delta),

the terminal envelope parameters are negligible provided

  delta < u = s log(1/q).

The remaining floor loss is negligible when `delta < 1`.  Both statements
are proved as actual limits and then combined into the exact deterministic
endpoint budget.
-/

namespace CollatzEndpointTransport

namespace OptimizedLinearPullback

open scoped Real Topology

noncomputable section

open QuantitativeDensity

def powerShellExponent (delta : ℝ) (M : ℕ) : ℝ :=
  powerShellScale M ^ (-delta)

def powerShellBudget
    (q kappa s delta : ℝ) (M : ℕ) : Prop :=
  (M : ℝ) *
        (linearLambda q (powerR s M) +
          powerTR kappa q s M) +
      bConst + 1 + powerTR kappa q s M ≤
    (M : ℝ) * powerShellExponent delta M

theorem powerShellExponent_pos (delta : ℝ) (M : ℕ) :
    0 < powerShellExponent delta M :=
  Real.rpow_pos_of_pos (powerShellScale_pos M) _

theorem powerLambda_upper
    {q s : ℝ}
    (hq0 : 0 < q) (hq1 : q < 1)
    (hs : 0 < s) (M : ℕ) :
    linearLambda q (powerR s M) ≤
      a0 * powerShellScale M ^ (-powerU q s) := by
  unfold linearLambda powerR
  exact mul_le_mul_of_nonneg_left
    (power_q_pow_upper hq0 hq1 hs M) a0_pos.le

theorem powerTerminalDriftRatio_tendsto_zero
    {q kappa s delta : ℝ}
    (hk : KappaAdmissible kappa)
    (hq0 : 0 < q) (hqa : a0 < q) (hq1 : q < 1)
    (hs : 0 < s)
    (hdeltaU : delta < powerU q s) :
    Filter.Tendsto
      (fun M =>
        (linearLambda q (powerR s M) +
            powerTR kappa q s M) /
          powerShellExponent delta M)
      Filter.atTop (nhds 0) := by
  have hgap : 0 < powerU q s - delta :=
    sub_pos.mpr hdeltaU
  have hcq0 : 0 ≤ cq kappa q := by
    unfold cq
    exact div_nonneg (sub_nonneg.mpr hqa.le)
      (mul_nonneg
        (mul_nonneg (by norm_num) hk.1.le) hq0.le)
  have hmodel :
      Filter.Tendsto
        (fun M =>
          ((1 + cq kappa q) * a0) *
            powerShellScale M ^
              (-(powerU q s - delta)))
        Filter.atTop (nhds 0) := by
    simpa [Function.comp_apply] using
      ((tendsto_rpow_neg_atTop hgap).comp
        powerShellScale_tendsto_atTop).const_mul
          ((1 + cq kappa q) * a0)
  have hnonneg :
      ∀ M,
        0 ≤
          (linearLambda q (powerR s M) +
              powerTR kappa q s M) /
            powerShellExponent delta M := by
    intro M
    exact div_nonneg
      (add_nonneg
        (linearLambda_pos hq0 _).le
        (powerTerminalTolerance_pos hk hq0 hqa _).le)
      (powerShellExponent_pos delta M).le
  have hupper :
      ∀ M,
        (linearLambda q (powerR s M) +
              powerTR kappa q s M) /
            powerShellExponent delta M ≤
          ((1 + cq kappa q) * a0) *
            powerShellScale M ^
              (-(powerU q s - delta)) := by
    intro M
    have hlam := powerLambda_upper hq0 hq1 hs M
    have ht :=
      powerTerminalTolerance_schedule_upper hk hq0 hqa hq1 hs M
    have hsum :
        linearLambda q (powerR s M) +
            powerTR kappa q s M ≤
          (1 + cq kappa q) * a0 *
            powerShellScale M ^ (-powerU q s) := by
      have hadd := add_le_add hlam ht
      simpa [powerTR, powerR] using
        hadd.trans_eq (by ring)
    have heps0 := powerShellExponent_pos delta M
    have hdiv :=
      div_le_div_of_nonneg_right hsum heps0.le
    calc
      (linearLambda q (powerR s M) +
              powerTR kappa q s M) /
            powerShellExponent delta M
          ≤
        ((1 + cq kappa q) * a0 *
              powerShellScale M ^ (-powerU q s)) /
            powerShellExponent delta M := hdiv
      _ = ((1 + cq kappa q) * a0) *
            powerShellScale M ^
              (-(powerU q s - delta)) := by
        unfold powerShellExponent
        calc
          ((1 + cq kappa q) * a0 *
                powerShellScale M ^ (-powerU q s)) /
              powerShellScale M ^ (-delta)
              =
            ((1 + cq kappa q) * a0) *
              (powerShellScale M ^ (-powerU q s) /
                powerShellScale M ^ (-delta)) := by ring
          _ = ((1 + cq kappa q) * a0) *
              powerShellScale M ^
                ((-powerU q s) - (-delta)) := by
            rw [← Real.rpow_sub (powerShellScale_pos M)]
          _ = _ := by congr 2 <;> ring
  exact squeeze_zero hnonneg hupper hmodel

theorem powerTerminalFloorRatio_tendsto_zero
    {q kappa s delta : ℝ}
    (hk : KappaAdmissible kappa)
    (hq0 : 0 < q) (hqa : a0 < q)
    (hdelta1 : delta < 1) :
    Filter.Tendsto
      (fun M =>
        (bConst + 1 + powerTR kappa q s M) /
          ((M : ℝ) * powerShellExponent delta M))
      Filter.atTop (nhds 0) := by
  have hgap : 0 < 1 - delta := sub_pos.mpr hdelta1
  have hbase :
      Filter.Tendsto
        (fun M =>
          powerShellScale M ^
            (-(1 - delta)))
        Filter.atTop (nhds 0) :=
    (tendsto_rpow_neg_atTop hgap).comp
      powerShellScale_tendsto_atTop
  have hmodel :=
    hbase.const_mul (2 * (bConst + 2))
  have hM4 :
      ∀ᶠ M : ℕ in Filter.atTop, 4 ≤ M :=
    Filter.eventually_atTop.2 ⟨4, fun _ h => h⟩
  have hnonneg :
      ∀ᶠ M : ℕ in Filter.atTop,
        0 ≤
          (bConst + 1 + powerTR kappa q s M) /
            ((M : ℝ) * powerShellExponent delta M) := by
    filter_upwards [hM4] with M hM
    exact div_nonneg
      (by
        have ht := powerTerminalTolerance_pos hk hq0 hqa (powerR s M)
        have ht' : 0 < powerTR kappa q s M := by
          simpa [powerTR] using ht
        linarith [bConst_pos, ht'])
      (mul_nonneg (Nat.cast_nonneg M)
        (powerShellExponent_pos delta M).le)
  have hupper :
      ∀ᶠ M : ℕ in Filter.atTop,
        (bConst + 1 + powerTR kappa q s M) /
            ((M : ℝ) * powerShellExponent delta M) ≤
          2 * (bConst + 2) *
            powerShellScale M ^ (-(1 - delta)) := by
    filter_upwards [hM4] with M hM4M
    have ht1 :=
      powerTerminalTolerance_le_one hk hq0 hqa (powerR s M)
    have hM0 : (0 : ℝ) < M := by
      exact_mod_cast (show 0 < M by omega)
    have hMhalf :
        powerShellScale M / 2 ≤ (M : ℝ) := by
      unfold powerShellScale
      have hM4R : (4 : ℝ) ≤ M := by exact_mod_cast hM4M
      linarith
    have hnum :
        bConst + 1 + powerTR kappa q s M ≤ bConst + 2 := by
      unfold powerTR
      linarith
    have hden :
        1 / (M : ℝ) ≤ 2 / powerShellScale M := by
      have h :=
        one_div_le_one_div_of_le
          (div_pos (powerShellScale_pos M) (by norm_num)) hMhalf
      simpa [one_div_div] using h
    have hepsInv :
        (powerShellExponent delta M)⁻¹ =
          powerShellScale M ^ delta := by
      unfold powerShellExponent
      rw [Real.rpow_neg (powerShellScale_pos M).le, inv_inv]
    have horiginal :
        (bConst + 1 + powerTR kappa q s M) /
              ((M : ℝ) * powerShellExponent delta M)
            =
          (bConst + 1 + powerTR kappa q s M) *
            (powerShellScale M ^ delta * (M : ℝ)⁻¹) := by
      rw [div_eq_mul_inv, mul_inv_rev, hepsInv]
    rw [horiginal]
    have hnum0 :
        0 ≤ bConst + 1 + powerTR kappa q s M := by
      have ht := powerTerminalTolerance_pos hk hq0 hqa (powerR s M)
      have ht' : 0 < powerTR kappa q s M := by
        simpa [powerTR] using ht
      linarith [bConst_pos, ht']
    calc
      (bConst + 1 + powerTR kappa q s M) *
            (powerShellScale M ^ delta * (M : ℝ)⁻¹)
          ≤ (bConst + 2) *
            (powerShellScale M ^ delta * (M : ℝ)⁻¹) :=
        mul_le_mul_of_nonneg_right hnum
          (mul_nonneg
            (Real.rpow_nonneg (powerShellScale_pos M).le _)
            (inv_nonneg.mpr hM0.le))
      _ ≤ (bConst + 2) *
            (powerShellScale M ^ delta *
              (2 / powerShellScale M)) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left
            (by simpa [one_div] using hden)
            (Real.rpow_nonneg (powerShellScale_pos M).le _))
          (by linarith [bConst_pos])
      _ = 2 * (bConst + 2) *
            powerShellScale M ^ (-(1 - delta)) := by
        calc
          (bConst + 2) *
                (powerShellScale M ^ delta *
                  (2 / powerShellScale M))
              =
            2 * (bConst + 2) *
              (powerShellScale M ^ delta /
                powerShellScale M) := by ring
          _ = 2 * (bConst + 2) *
              powerShellScale M ^ (delta - 1) := by
            rw [show
                powerShellScale M ^ delta /
                    powerShellScale M =
                  powerShellScale M ^ (delta - 1) by
              calc
                powerShellScale M ^ delta / powerShellScale M
                    =
                  powerShellScale M ^ delta /
                    powerShellScale M ^ (1 : ℝ) := by
                      rw [Real.rpow_one]
                _ = powerShellScale M ^ (delta - 1) :=
                  (Real.rpow_sub (powerShellScale_pos M) _ _).symm]
          _ = _ := by
            congr 1
            congr 1
            ring
  exact squeeze_zero' hnonneg hupper (by simpa using hmodel)

theorem powerShellBudget_eventually
    {q kappa s delta : ℝ}
    (hk : KappaAdmissible kappa)
    (hq0 : 0 < q) (hqa : a0 < q) (hq1 : q < 1)
    (hs : 0 < s)
    (hdeltaU : delta < powerU q s)
    (hdelta1 : delta < 1) :
    ∀ᶠ M : ℕ in Filter.atTop,
      powerShellBudget q kappa s delta M := by
  have hdrift :=
    powerTerminalDriftRatio_tendsto_zero
      hk hq0 hqa hq1 hs hdeltaU
  have hfloor :=
    powerTerminalFloorRatio_tendsto_zero
      (q := q) (kappa := kappa) (s := s)
      hk hq0 hqa hdelta1
  have hsum := hdrift.add hfloor
  have hone :
      ∀ᶠ M : ℕ in Filter.atTop,
        (linearLambda q (powerR s M) +
              powerTR kappa q s M) /
              powerShellExponent delta M +
            (bConst + 1 + powerTR kappa q s M) /
              ((M : ℝ) * powerShellExponent delta M) < 1 := by
    have hdist :=
      (Metric.tendsto_atTop.1 hsum) 1 zero_lt_one
    filter_upwards [Filter.eventually_atTop.2 hdist] with M hM
    rw [Real.dist_eq] at hM
    have habs :
        |(linearLambda q (powerR s M) +
                powerTR kappa q s M) /
                powerShellExponent delta M +
              (bConst + 1 + powerTR kappa q s M) /
                ((M : ℝ) * powerShellExponent delta M)| < 1 := by
      simpa [sub_zero] using hM
    exact lt_of_le_of_lt (le_abs_self _) habs
  have hMpos :
      ∀ᶠ M : ℕ in Filter.atTop, 0 < M :=
    Filter.eventually_atTop.2 ⟨1, fun _ h => by omega⟩
  filter_upwards [hone, hMpos] with M hratio hM
  have heps := powerShellExponent_pos delta M
  unfold powerShellBudget
  have hden :
      0 < (M : ℝ) * powerShellExponent delta M :=
    mul_pos (by exact_mod_cast hM) heps
  have hid :
      ((M : ℝ) *
            (linearLambda q (powerR s M) +
              powerTR kappa q s M) +
          bConst + 1 + powerTR kappa q s M) /
          ((M : ℝ) * powerShellExponent delta M)
        =
      (linearLambda q (powerR s M) +
            powerTR kappa q s M) /
          powerShellExponent delta M +
        (bConst + 1 + powerTR kappa q s M) /
          ((M : ℝ) * powerShellExponent delta M) := by
    field_simp
    ring
  rw [← hid] at hratio
  exact (div_le_one hden).mp hratio.le

end

end OptimizedLinearPullback

end CollatzEndpointTransport
