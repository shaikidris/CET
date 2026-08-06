/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik
-/
import CollatzEndpointTransport.QuadraticAppendix.Shared.QuantitativeBasePullbackDensity
import CollatzEndpointTransport.QuadraticAppendix.QuantitativeQuadraticPullbackOrbit
import CollatzEndpointTransport.Common.TerrasMaximalBarrierDensity

/-!
# Quantitative Quadratic Pullback Density

Quadratic quantitative pullback.

This file assembles:

* the weakened-but-sufficient cone density `D/5`;
* the exact base-map fiber estimate;
* the maximal parity-barrier shell tail;
* the deterministic orbit-to-cone bridge.

The result is the strengthened pullback exponent `c * D^2` with no
`D^(-2)` prefactor.
-/

namespace CollatzEndpointTransport

namespace QuantitativeDensity

open scoped Real

noncomputable section

def quadraticPullbackShellRate (D : ℝ) : ℝ :=
  D ^ 2 / 288

def quadraticPullbackStartupConstant : ℝ :=
  146 * Real.exp (1 / 8)

def quadraticPullbackGlobalConstant : ℝ :=
  2 * quadraticPullbackStartupConstant /
    (2 * Real.exp (-(1 / 288 : ℝ)) - 1)

theorem quadraticPullbackShellRate_pos {D : ℝ} (hD : 0 < D) :
    0 < quadraticPullbackShellRate D := by
  unfold quadraticPullbackShellRate
  positivity

theorem quadraticPullbackStartupConstant_pos :
    0 < quadraticPullbackStartupConstant := by
  unfold quadraticPullbackStartupConstant
  positivity

/-- The concrete cone/base composition contributes the `144 C` term. -/
theorem card_shellBad_baseCone_le_quadratic
    {S : Set ℕ} {C D : ℝ} {M : ℕ}
    (hS : IsCDDense S C D) :
    ((shellBad
        (basePullback (quadraticPullAlpha D)
          (coneCore 2 (quadraticPullEtaPrime D) S))
        M).card : ℝ) ≤
      144 * C * (2 ^ M : ℕ) *
        (3 : ℝ) ^ (-(1 / 12 : ℝ) * D * M) := by
  have hD0 := hS.D_pos
  have hD1 := hS.D_le_one
  have hCone :
      IsCDDense (coneCore 2 (quadraticPullEtaPrime D) S)
        (12 * C) (D / 5) := by
    have hraw :=
      coneCore_dense_weakened hS
        (quadraticPullEtaPrime_pos hD0)
        (by unfold quadraticPullEtaPrime; linarith)
    convert hraw using 1 <;>
      unfold quadraticPullEtaPrime <;> ring
  have hbase :=
    card_shellBad_basePullback_le_rpow
      (M := M) hCone
      (quadraticPullAlpha_pos hD0 hD1).le
      (quadraticPullAlpha_le_half hD0.le)
  have hAlpha := quadraticPullAlpha_ge_five_twelfths hD1
  have hDM0 : 0 ≤ D * (M : ℝ) :=
    mul_nonneg hD0.le (Nat.cast_nonneg M)
  have hExp :
      -(D / 5) * quadraticPullAlpha D * M ≤
        -(1 / 12 : ℝ) * D * M := by
    have hmul :
        (1 / 12 : ℝ) * D * M ≤
          (D / 5) * quadraticPullAlpha D * M := by
      calc
        (1 / 12 : ℝ) * D * M =
            (D * M) * (5 / 12) / 5 := by ring
        _ ≤ (D * M) * quadraticPullAlpha D / 5 := by gcongr
        _ = (D / 5) * quadraticPullAlpha D * M := by ring
    linarith
  have hpow :
      (3 : ℝ) ^ (-(D / 5) * quadraticPullAlpha D * M) ≤
        (3 : ℝ) ^ (-(1 / 12 : ℝ) * D * M) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) hExp
  calc
    ((shellBad
        (basePullback (quadraticPullAlpha D)
          (coneCore 2 (quadraticPullEtaPrime D) S))
        M).card : ℝ)
        ≤ 12 * (12 * C) * (2 ^ M : ℕ) *
          (3 : ℝ) ^ (-(D / 5) * quadraticPullAlpha D * M) := by
            simpa using hbase
    _ ≤ 12 * (12 * C) * (2 ^ M : ℕ) *
          (3 : ℝ) ^ (-(1 / 12 : ℝ) * D * M) := by
      have hcoef :
          0 ≤ (12 : ℝ) * (12 * C) * ((2 ^ M : ℕ) : ℝ) :=
        mul_nonneg
          (mul_nonneg (by norm_num)
            (mul_nonneg (by norm_num) hS.C_pos.le))
          (Nat.cast_nonneg _)
      exact mul_le_mul_of_nonneg_left hpow hcoef
    _ = 144 * C * (2 ^ M : ℕ) *
          (3 : ℝ) ^ (-(1 / 12 : ℝ) * D * M) := by ring

/-- The live pullback barrier is exactly the concrete MB1 barrier after
the substitution `t = D*log_2(3)/12`. -/
theorem card_shellPullbackBarrierBad_le
    {D : ℝ} {M : ℕ} (hD : 0 ≤ D) :
    ((Terras.shellMaximalParityBad M (pullbackBarrierHeight D M)).card : ℝ) ≤
      2 * Real.exp (-(quadraticPullbackShellRate D * M)) *
        (2 : ℝ) ^ M := by
  let t := D * lg3 / 12
  have ht : 0 ≤ t := by
    dsimp [t]
    exact div_nonneg (mul_nonneg hD lg3_pos.le) (by norm_num)
  have hheight :
      Terras.maximalBarrierHeight t M = pullbackBarrierHeight D M := by
    unfold Terras.maximalBarrierHeight pullbackBarrierHeight
      quadraticPullEta
    dsimp [t]
    field_simp [ne_of_gt lg3_pos]
    ring
  have hrate :
      Terras.maximalBarrierC0 * t ^ 2 =
        quadraticPullbackShellRate D := by
    unfold Terras.maximalBarrierC0 quadraticPullbackShellRate
    dsimp [t]
    field_simp [ne_of_gt lg3_pos]
    ring
  rw [← hheight, ← hrate]
  exact Terras.card_shellMaximalParityBad_le_concrete ht

/-- On startup-valid shells, every true pullback failure is either a
base/cone failure or a maximal-barrier failure. -/
theorem shellBad_collatzPullback_subset_quadratic_union
    {S : Set ℕ} {D : ℝ} {M : ℕ}
    (hD0 : 0 < D) (hD1 : D ≤ 1) (hstart : 36 ≤ D * M) :
    shellBad (collatzPullback S) M ⊆
      shellBad
        (basePullback (quadraticPullAlpha D)
          (coneCore 2 (quadraticPullEtaPrime D) S)) M ∪
      Terras.shellMaximalParityBad M (pullbackBarrierHeight D M) := by
  classical
  intro n hn
  rw [shellBad, Finset.mem_filter] at hn
  by_contra hnot
  rw [Finset.mem_union, not_or] at hnot
  have hbase :
      baseMapAt (quadraticPullAlpha D) M n ∈
        coneCore 2 (quadraticPullEtaPrime D) S := by
    have hgood :
        n ∈ basePullback (quadraticPullAlpha D)
          (coneCore 2 (quadraticPullEtaPrime D) S) := by
      by_contra hnGood
      apply hnot.1
      rw [shellBad, Finset.mem_filter]
      exact ⟨hn.1, hnGood⟩
    have hlog : Nat.log 2 n = M :=
      Terras.log_two_eq_of_mem_dyadicShell hn.1
    simpa [basePullback, baseMap, hlog] using hgood
  have hreg :
      Terras.MaximalParityRegular n M (pullbackBarrierHeight D M) := by
    by_contra hnReg
    apply hnot.2
    rw [Terras.shellMaximalParityBad, Finset.mem_filter]
    exact ⟨hn.1, hnReg⟩
  have hmem :=
    quadratic_witness_implies_collatzPullback_on_shell
      hD0 hD1 hstart hn.1 hbase hreg
  exact hn.2 hmem

/-- The linear-in-`D` base/cone exponential is faster than the quadratic
barrier rate throughout `0<D<=1`. -/
theorem baseCone_rpow_le_quadratic_exp
    {D : ℝ} {M : ℕ} (hD0 : 0 ≤ D) (hD1 : D ≤ 1) :
    (3 : ℝ) ^ (-(1 / 12 : ℝ) * D * M) ≤
      Real.exp (-(quadraticPullbackShellRate D * M)) := by
  have hlog23 : Real.log 2 ≤ Real.log 3 :=
    Real.log_le_log (by norm_num) (by norm_num)
  have hcoeff :
      (1 / 288 : ℝ) ≤ (1 / 12 : ℝ) * Real.log 3 := by
    nlinarith [Real.log_two_gt_d9]
  have hDM0 : 0 ≤ D * (M : ℝ) :=
    mul_nonneg hD0 (Nat.cast_nonneg M)
  have hrate :
      quadraticPullbackShellRate D * M ≤
        (1 / 12 : ℝ) * D * M * Real.log 3 := by
    unfold quadraticPullbackShellRate
    calc
      D ^ 2 / 288 * (M : ℝ) =
          (D * M) * (D * (1 / 288 : ℝ)) := by ring
      _ ≤ (D * M) * (1 * (1 / 288 : ℝ)) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hD1 (by norm_num)) hDM0
      _ ≤ (D * M) * ((1 / 12 : ℝ) * Real.log 3) := by
        exact mul_le_mul_of_nonneg_left (by simpa using hcoeff) hDM0
      _ = (1 / 12 : ℝ) * D * M * Real.log 3 := by ring
  rw [Real.rpow_def_of_pos (by norm_num)]
  apply Real.exp_le_exp.2
  nlinarith

/-- Startup-valid shell estimate, before absorbing the finite startup
range. -/
theorem card_shellBad_collatzPullback_le_quadratic_of_startup
    {S : Set ℕ} {C D : ℝ} {M : ℕ}
    (hS : IsCDDense S C D) (hstart : 36 ≤ D * M) :
    ((shellBad (collatzPullback S) M).card : ℝ) ≤
      146 * (C + 1) *
        Real.exp (-(quadraticPullbackShellRate D * M)) *
        (2 : ℝ) ^ M := by
  have hsub :=
    shellBad_collatzPullback_subset_quadratic_union
      (S := S) hS.D_pos hS.D_le_one hstart
  have hcardNat :
      (shellBad (collatzPullback S) M).card ≤
        (shellBad
          (basePullback (quadraticPullAlpha D)
            (coneCore 2 (quadraticPullEtaPrime D) S))
          M).card +
        (Terras.shellMaximalParityBad M
          (pullbackBarrierHeight D M)).card :=
    le_trans (Finset.card_le_card hsub)
      (Finset.card_union_le _ _)
  have hcard :
      ((shellBad (collatzPullback S) M).card : ℝ) ≤
        ((shellBad
          (basePullback (quadraticPullAlpha D)
            (coneCore 2 (quadraticPullEtaPrime D) S))
          M).card : ℝ) +
        ((Terras.shellMaximalParityBad M
          (pullbackBarrierHeight D M)).card : ℝ) := by
    exact_mod_cast hcardNat
  have hbase := card_shellBad_baseCone_le_quadratic
    (M := M) hS
  have hbaseExp :=
    baseCone_rpow_le_quadratic_exp (M := M) hS.D_pos.le hS.D_le_one
  have hbase' :
      ((shellBad
        (basePullback (quadraticPullAlpha D)
          (coneCore 2 (quadraticPullEtaPrime D) S))
        M).card : ℝ) ≤
        144 * C * (2 ^ M : ℕ) *
          Real.exp (-(quadraticPullbackShellRate D * M)) := by
    exact hbase.trans
      (mul_le_mul_of_nonneg_left hbaseExp
        (mul_nonneg
          (mul_nonneg (by norm_num) hS.C_pos.le)
          (Nat.cast_nonneg _)))
  have hbarrier :=
    card_shellPullbackBarrierBad_le
      (M := M) hS.D_pos.le
  have hQ :
      0 ≤ Real.exp (-(quadraticPullbackShellRate D * M)) *
        (2 : ℝ) ^ M := by positivity
  calc
    ((shellBad (collatzPullback S) M).card : ℝ)
        ≤ ((shellBad
          (basePullback (quadraticPullAlpha D)
            (coneCore 2 (quadraticPullEtaPrime D) S))
          M).card : ℝ) +
          ((Terras.shellMaximalParityBad M
            (pullbackBarrierHeight D M)).card : ℝ) := hcard
    _ ≤ 144 * C * (2 ^ M : ℕ) *
          Real.exp (-(quadraticPullbackShellRate D * M)) +
        2 * Real.exp (-(quadraticPullbackShellRate D * M)) *
          (2 : ℝ) ^ M :=
      add_le_add hbase' hbarrier
    _ ≤ 146 * (C + 1) *
          Real.exp (-(quadraticPullbackShellRate D * M)) *
          (2 : ℝ) ^ M := by
      have hcoef : 144 * C + 2 ≤ 146 * (C + 1) := by
        linarith [hS.C_pos]
      have hmul := mul_le_mul_of_nonneg_right hcoef hQ
      norm_num only [Nat.cast_pow, Nat.cast_ofNat]
      ring_nf at hmul ⊢
      exact hmul

theorem one_le_quadraticPullback_startup_factor
    {C D : ℝ} {M : ℕ}
    (hC : 0 < C) (hD0 : 0 < D) (hD1 : D ≤ 1)
    (hsmall : ¬36 ≤ D * M) :
    1 ≤ quadraticPullbackStartupConstant * (C + 1) *
      Real.exp (-(quadraticPullbackShellRate D * M)) := by
  have hDM : D * (M : ℝ) < 36 := lt_of_not_ge hsmall
  have hrate :
      quadraticPullbackShellRate D * M < 1 / 8 := by
    unfold quadraticPullbackShellRate
    have hmul :
        D * (D * (M : ℝ)) < D * 36 :=
      mul_lt_mul_of_pos_left hDM hD0
    have hD36 : D * 36 ≤ 1 * 36 :=
      mul_le_mul_of_nonneg_right hD1 (by norm_num)
    have hDsqM : D ^ 2 * (M : ℝ) < 36 := by
      calc
        D ^ 2 * (M : ℝ) = D * (D * (M : ℝ)) := by ring
        _ < D * 36 := hmul
        _ ≤ 1 * 36 := hD36
        _ = 36 := by norm_num
    nlinarith
  have hexp :
      1 ≤ Real.exp
        (1 / 8 - quadraticPullbackShellRate D * M) :=
    Real.one_le_exp (by linarith)
  have hcoef : 1 ≤ 146 * (C + 1) := by
    nlinarith
  calc
    1 ≤ 146 * (C + 1) *
        Real.exp (1 / 8 - quadraticPullbackShellRate D * M) := by
      nlinarith [Real.exp_pos
        (1 / 8 - quadraticPullbackShellRate D * M)]
    _ = quadraticPullbackStartupConstant * (C + 1) *
        Real.exp (-(quadraticPullbackShellRate D * M)) := by
      unfold quadraticPullbackStartupConstant
      rw [show
        1 / 8 - quadraticPullbackShellRate D * M =
          1 / 8 + (-(quadraticPullbackShellRate D * M)) by ring,
        Real.exp_add]
      ring

/-- All-shell quadratic pullback estimate. -/
theorem card_shellBad_collatzPullback_le_quadratic
    {S : Set ℕ} {C D : ℝ} {M : ℕ}
    (hS : IsCDDense S C D) :
    ((shellBad (collatzPullback S) M).card : ℝ) ≤
      quadraticPullbackStartupConstant * (C + 1) *
        Real.exp (-(quadraticPullbackShellRate D * M)) *
        (2 : ℝ) ^ M := by
  classical
  by_cases hstart : 36 ≤ D * M
  · have hlarge :=
      card_shellBad_collatzPullback_le_quadratic_of_startup
        (M := M) hS hstart
    have hK :
        (146 : ℝ) ≤ quadraticPullbackStartupConstant := by
      unfold quadraticPullbackStartupConstant
      have hone := Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 1 / 8)
      nlinarith
    exact hlarge.trans (by
      have hrest :
          0 ≤ (C + 1) *
            Real.exp (-(quadraticPullbackShellRate D * M)) *
            (2 : ℝ) ^ M := by
        exact mul_nonneg
          (mul_nonneg (by linarith [hS.C_pos]) (Real.exp_pos _).le)
          (by positivity)
      simpa [mul_assoc] using mul_le_mul_of_nonneg_right hK hrest)
  · have hcardNat :
        (shellBad (collatzPullback S) M).card ≤ 2 ^ M := by
      calc
        (shellBad (collatzPullback S) M).card
            ≤ (dyadicShell M).card := by
          apply Finset.card_le_card
          intro n hn
          rw [shellBad, Finset.mem_filter] at hn
          exact hn.1
        _ = 2 ^ M := by
          rw [dyadicShell, Nat.card_Ico, pow_succ]
          omega
    have hcard :
        ((shellBad (collatzPullback S) M).card : ℝ) ≤
          (2 : ℝ) ^ M := by exact_mod_cast hcardNat
    have hfactor :=
      one_le_quadraticPullback_startup_factor
        hS.C_pos hS.D_pos hS.D_le_one hstart
    calc
      ((shellBad (collatzPullback S) M).card : ℝ)
          ≤ (2 : ℝ) ^ M := hcard
      _ = 1 * (2 : ℝ) ^ M := by ring
      _ ≤ (quadraticPullbackStartupConstant * (C + 1) *
          Real.exp (-(quadraticPullbackShellRate D * M))) *
          (2 : ℝ) ^ M :=
        mul_le_mul_of_nonneg_right hfactor (by positivity)
      _ = _ := by ring

theorem quadraticPullbackShellRate_lt_log_two
    {D : ℝ} (hD0 : 0 ≤ D) (hD1 : D ≤ 1) :
    quadraticPullbackShellRate D < Real.log 2 := by
  have hDsq : D ^ 2 ≤ 1 := by nlinarith [sq_nonneg D]
  unfold quadraticPullbackShellRate
  nlinarith [Real.log_two_gt_d9]

theorem quadraticPullbackFixedDenominator_pos :
    0 < 2 * Real.exp (-(1 / 288 : ℝ)) - 1 := by
  have hsmall : (1 / 288 : ℝ) < Real.log 2 := by
    nlinarith [Real.log_two_gt_d9]
  have h2 : Real.exp (-Real.log 2) = (2 : ℝ)⁻¹ := by
    rw [Real.exp_neg, Real.exp_log (by norm_num)]
  have h :
      Real.exp (-Real.log 2) <
        Real.exp (-(1 / 288 : ℝ)) :=
    Real.exp_lt_exp.2 (by linarith)
  rw [h2] at h
  linarith

end

end QuantitativeDensity

end CollatzEndpointTransport
