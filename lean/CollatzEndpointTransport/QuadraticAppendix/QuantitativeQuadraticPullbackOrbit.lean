/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik
-/
import CollatzEndpointTransport.QuadraticAppendix.Shared.QuantitativePullbackOrbit
import CollatzEndpointTransport.QuadraticAppendix.QuantitativeQuadraticPullbackParameters
import CollatzEndpointTransport.Common.TerrasAffineMaximalBarrier

/-!
# Quantitative Quadratic Pullback Orbit

Deterministic orbit-to-cone bridge for the quadratic pullback.

The old proof used separate parity and affine-correction good sets. Here one
maximal parity barrier supplies both conditions.
-/

namespace CollatzEndpointTransport

namespace QuantitativeDensity

open scoped Real

noncomputable section

def pullbackBarrierHeight (D : ℝ) (M : ℕ) : ℝ :=
  quadraticPullEta D * M / 2

theorem pullbackBarrierHeight_nonneg
    {D : ℝ} {M : ℕ} (hD : 0 ≤ D) :
    0 ≤ pullbackBarrierHeight D M := by
  unfold pullbackBarrierHeight
  exact div_nonneg
    (mul_nonneg (by unfold quadraticPullEta; positivity) (Nat.cast_nonneg M))
    (by norm_num)

/-- The maximal barrier gives the exact lower floor condition and a sharper
terminal excess bound. -/
theorem terminal_bounds_of_maximalBarrier
    {D : ℝ} {M n : ℕ}
    (hD0 : 0 < D) (hD1 : D ≤ 1)
    (hreg :
      Terras.MaximalParityRegular n M (pullbackBarrierHeight D M)) :
    ⌊quadraticPullAlpha D * M⌋₊ ≤ Terras.oddCount M n ∧
      (pullbackOddExcess (quadraticPullAlpha D) M n : ℝ) <
        3 * quadraticPullEta D * M / 2 + 1 := by
  have hbounds := hreg M le_rfl
  have hlower := (abs_le.mp hbounds).1
  have hupper := (abs_le.mp hbounds).2
  have heta0 : 0 < quadraticPullEta D := quadraticPullEta_pos hD0
  have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  have hJfloor :
      (⌊quadraticPullAlpha D * M⌋₊ : ℝ) ≤ quadraticPullAlpha D * M := by
    apply Nat.floor_le
    exact mul_nonneg (quadraticPullAlpha_pos hD0 hD1).le hM0
  have hJreal :
      (⌊quadraticPullAlpha D * M⌋₊ : ℝ) ≤ Terras.oddCount M n := by
    have halpha :
        quadraticPullAlpha D = 1 / 2 - quadraticPullEta D := rfl
    rw [halpha] at hJfloor
    unfold pullbackBarrierHeight at hlower
    rw [halpha]
    nlinarith
  have hJ : ⌊quadraticPullAlpha D * M⌋₊ ≤ Terras.oddCount M n := by
    exact_mod_cast hJreal
  refine ⟨hJ, ?_⟩
  have hfloorLt :
      quadraticPullAlpha D * M <
        (⌊quadraticPullAlpha D * M⌋₊ : ℝ) + 1 :=
    Nat.lt_floor_add_one _
  have hLcast :
      (pullbackOddExcess (quadraticPullAlpha D) M n : ℝ) =
        (Terras.oddCount M n : ℝ) -
          ⌊quadraticPullAlpha D * M⌋₊ := by
    unfold pullbackOddExcess
    rw [Nat.cast_sub hJ]
  rw [hLcast]
  have halpha :
      quadraticPullAlpha D = 1 / 2 - quadraticPullEta D := rfl
  rw [halpha] at hfloorLt
  unfold pullbackBarrierHeight at hupper
  rw [halpha]
  nlinarith

theorem pullback_excess_le_cone_depth_of_maximalBarrier
    {D : ℝ} {M n : ℕ}
    (hD0 : 0 < D) (hD1 : D ≤ 1)
    (hstart : 36 ≤ D * M)
    (hnShell : n ∈ dyadicShell M)
    (hreg :
      Terras.MaximalParityRegular n M (pullbackBarrierHeight D M)) :
    (pullbackOddExcess (quadraticPullAlpha D) M n : ℝ) ≤
      quadraticPullEtaPrime D *
        Nat.log 3 (baseMapAt (quadraticPullAlpha D) M n) := by
  have hbounds :=
    terminal_bounds_of_maximalBarrier hD0 hD1 hreg
  have hLsharp :
      (pullbackOddExcess (quadraticPullAlpha D) M n : ℝ) ≤
        3 * quadraticPullEta D * M / 2 + 1 :=
    le_of_lt hbounds.2
  have hstartup :=
    quadratic_pull_cone_depth_startup hD0 hD1
      (Nat.cast_nonneg M) hstart
  let J : ℕ := ⌊quadraticPullAlpha D * M⌋₊
  have hJbase :
      3 ^ J ≤ baseMapAt (quadraticPullAlpha D) M n := by
    have hrange :=
      baseMapAt_range
        (alpha := quadraticPullAlpha D) (M := M) (n := n) hnShell
    simpa [J, baseNumeratorScale] using hrange.1
  have hJlog :
      J ≤ Nat.log 3 (baseMapAt (quadraticPullAlpha D) M n) :=
    Nat.le_log_of_pow_le (by norm_num) hJbase
  have hfloorLt :
      quadraticPullAlpha D * M < (J : ℝ) + 1 := by
    dsimp [J]
    exact Nat.lt_floor_add_one _
  have hetaPrime0 : 0 < quadraticPullEtaPrime D :=
    quadraticPullEtaPrime_pos hD0
  have hJreal :
      (J : ℝ) ≤ Nat.log 3 (baseMapAt (quadraticPullAlpha D) M n) := by
    exact_mod_cast hJlog
  calc
    (pullbackOddExcess (quadraticPullAlpha D) M n : ℝ)
        ≤ 3 * quadraticPullEta D * M / 2 + 1 := hLsharp
    _ ≤ 3 * quadraticPullEta D * M / 2 + 1 + 1 / 128 := by norm_num
    _ ≤ quadraticPullEtaPrime D *
          (quadraticPullAlpha D * M - 1) := hstartup
    _ ≤ quadraticPullEtaPrime D * J := by
      apply mul_le_mul_of_nonneg_left _ hetaPrime0.le
      linarith
    _ ≤ quadraticPullEtaPrime D *
          Nat.log 3 (baseMapAt (quadraticPullAlpha D) M n) :=
      mul_le_mul_of_nonneg_left hJreal hetaPrime0.le

theorem affine_constant_times_three_neg_three_halves_lt_one :
    (2 + Real.sqrt 3) * (3 : ℝ) ^ (-(3 : ℝ) / 2) < 1 := by
  have hs0 : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg 3
  have hs2 : (Real.sqrt 3) ^ 2 = (3 : ℝ) := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  have hs1 : 1 < Real.sqrt 3 := by nlinarith
  have hpow :
      (3 : ℝ) ^ ((3 : ℝ) / 2) =
        (Real.sqrt 3) ^ (3 : ℕ) := by
    rw [Real.rpow_div_two_eq_sqrt _ (by norm_num)]
    exact Real.rpow_natCast _ _
  rw [show -(3 : ℝ) / 2 = -((3 : ℝ) / 2) by ring,
    Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 3), hpow]
  rw [mul_inv_lt_iff₀ (by positivity : 0 < (Real.sqrt 3) ^ (3 : ℕ))]
  nlinarith [mul_self_pos.mpr (ne_of_gt (lt_trans zero_lt_one hs1))]

/-- The finite geometric affine bound is already below one after extracting
the deterministic `3^J` factor. -/
theorem terminal_correction_lt_one_of_maximalBarrier
    {D : ℝ} {M n : ℕ}
    (hD0 : 0 < D) (hD1 : D ≤ 1)
    (hstart : 36 ≤ D * M)
    (hreg :
      Terras.MaximalParityRegular n M (pullbackBarrierHeight D M)) :
    Terras.affineCorrection M n *
        (3 : ℝ) ^ ⌊quadraticPullAlpha D * M⌋₊ < 1 := by
  have hcorr :=
    Terras.affineCorrection_scaled_le_maximal
      (n := n) (M := M) (k := M)
      (h := pullbackBarrierHeight D M)
      (pullbackBarrierHeight_nonneg hD0.le) le_rfl hreg
  have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  have hJfloor :
      (⌊quadraticPullAlpha D * M⌋₊ : ℝ) ≤ quadraticPullAlpha D * M := by
    apply Nat.floor_le
    exact mul_nonneg (quadraticPullAlpha_pos hD0 hD1).le hM0
  have hExp :
      (⌊quadraticPullAlpha D * M⌋₊ : ℝ) - (M : ℝ) / 2 ≤
        -quadraticPullEta D * M := by
    have halpha :
        quadraticPullAlpha D = 1 / 2 - quadraticPullEta D := rfl
    rw [halpha] at hJfloor
    rw [halpha]
    nlinarith
  have hratio :
      (3 : ℝ) ^ ⌊quadraticPullAlpha D * M⌋₊ /
          (3 : ℝ) ^ ((M : ℝ) / 2) ≤
        (3 : ℝ) ^ (-quadraticPullEta D * M) := by
    rw [← Real.rpow_natCast, ← Real.rpow_sub (by norm_num)]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hExp
  have hcorrJ :
      Terras.affineCorrection M n *
          (3 : ℝ) ^ ⌊quadraticPullAlpha D * M⌋₊ ≤
        (2 + Real.sqrt 3) *
          (3 : ℝ) ^
            (pullbackBarrierHeight D M - quadraticPullEta D * M) := by
    have hhalfPos : 0 < (3 : ℝ) ^ ((M : ℝ) / 2) := by positivity
    have hrewrite :
        Terras.affineCorrection M n *
            (3 : ℝ) ^ ⌊quadraticPullAlpha D * M⌋₊ =
          (Terras.affineCorrection M n *
              (3 : ℝ) ^ ((M : ℝ) / 2)) *
            ((3 : ℝ) ^ ⌊quadraticPullAlpha D * M⌋₊ /
              (3 : ℝ) ^ ((M : ℝ) / 2)) := by
      field_simp
      ring
    rw [hrewrite]
    calc
      _ ≤ ((2 + Real.sqrt 3) *
          (3 : ℝ) ^ (pullbackBarrierHeight D M)) *
          (3 : ℝ) ^ (-quadraticPullEta D * M) :=
        mul_le_mul hcorr hratio (by positivity) (by positivity)
      _ = (2 + Real.sqrt 3) *
          (3 : ℝ) ^
            (pullbackBarrierHeight D M - quadraticPullEta D * M) := by
        rw [Real.rpow_sub (by norm_num)]
        rw [show -quadraticPullEta D * M =
            -(quadraticPullEta D * M) by ring,
          Real.rpow_neg (by norm_num)]
        ring
  have hEtaM :
      (3 : ℝ) / 2 ≤ quadraticPullEta D * M / 2 := by
    unfold quadraticPullEta
    nlinarith
  have hneg :
      pullbackBarrierHeight D M - quadraticPullEta D * M ≤
        -(3 : ℝ) / 2 := by
    unfold pullbackBarrierHeight
    nlinarith
  have hpow :
      (3 : ℝ) ^
          (pullbackBarrierHeight D M - quadraticPullEta D * M) ≤
        (3 : ℝ) ^ (-(3 : ℝ) / 2) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) hneg
  exact hcorrJ.trans_lt
    ((mul_le_mul_of_nonneg_left hpow (by positivity)).trans_lt
      affine_constant_times_three_neg_three_halves_lt_one)

/-- Shell-local quadratic witness inclusion in the true Collatz pullback. -/
theorem quadratic_witness_implies_collatzPullback_on_shell
    {S : Set ℕ} {D : ℝ} {M n : ℕ}
    (hD0 : 0 < D) (hD1 : D ≤ 1)
    (hstart : 36 ≤ D * M)
    (hnShell : n ∈ dyadicShell M)
    (hbase :
      baseMapAt (quadraticPullAlpha D) M n ∈
        coneCore 2 (quadraticPullEtaPrime D) S)
    (hreg :
      Terras.MaximalParityRegular n M (pullbackBarrierHeight D M)) :
    n ∈ collatzPullback S := by
  have hbounds :=
    terminal_bounds_of_maximalBarrier hD0 hD1 hreg
  have hdepth :=
    pullback_excess_le_cone_depth_of_maximalBarrier
      hD0 hD1 hstart hnShell hreg
  have hcorr :=
    terminal_correction_lt_one_of_maximalBarrier
      hD0 hD1 hstart hreg
  have hterminal :
      (Terras.T^[M]) n ∈ S :=
    base_cone_implies_terminal_mem
      hbase hdepth hbounds.1 hcorr
  have hlog : Nat.log 2 n = M :=
    Terras.log_two_eq_of_mem_dyadicShell hnShell
  rw [mem_collatzPullback, hlog]
  exact hterminal

end

end QuantitativeDensity

end CollatzEndpointTransport
