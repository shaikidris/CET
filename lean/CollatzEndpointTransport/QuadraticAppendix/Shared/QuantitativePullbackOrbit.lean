/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik
-/
import CollatzEndpointTransport.QuadraticAppendix.Shared.QuantitativeBasePullback
import CollatzEndpointTransport.Common.TerrasAffineIterate

/-!
# Quantitative Pullback Orbit

Deterministic orbit-to-cone decomposition for the quantitative pullback.

Put

  J = floor (alpha * M),
  S = oddCount M n,
  L = S - J,
  b = floor (3^J n / 2^M).

The exact affine iterate identity shows that, whenever `J <= S` and the
terminal affine correction satisfies `r_M(n) * 3^J < 1`,

  T^M(n) = 3^L * b + i,       0 <= i < 2 * 3^L.

Thus the true orbit endpoint is one of the affine descendants covered by the
robust cone based at `b`.  This file proves only that deterministic integer
statement.  The parity and correction good sets discharge its two hypotheses
in the subsequent pullback assembly.
-/

namespace CollatzEndpointTransport

namespace QuantitativeDensity

open scoped Real

noncomputable section

/-- The excess number of odd steps above the deterministic exponent. -/
def pullbackOddExcess (alpha : ℝ) (M n : ℕ) : ℕ :=
  Terras.oddCount M n - ⌊alpha * M⌋₊

/-- Exact addition formula for the odd count once the deterministic exponent
is below it. -/
theorem floor_add_pullbackOddExcess
    {alpha : ℝ} {M n : ℕ}
    (hJ : ⌊alpha * M⌋₊ ≤ Terras.oddCount M n) :
    ⌊alpha * M⌋₊ + pullbackOddExcess alpha M n =
      Terras.oddCount M n := by
  unfold pullbackOddExcess
  omega

/-- **Deterministic orbit-to-cone remainder decomposition.**

The conclusion is an equality in `Nat`, not merely a real approximation.
The factor `2` comes from adding the two fractional contributions:
the quotient remainder of `3^J n / 2^M`, and the affine correction.
-/
theorem exists_iterate_eq_baseMapAt_mul_pow_add
    {alpha : ℝ} {M n : ℕ}
    (hJ : ⌊alpha * M⌋₊ ≤ Terras.oddCount M n)
    (hcorr :
      Terras.affineCorrection M n * (3 : ℝ) ^ ⌊alpha * M⌋₊ < 1) :
    ∃ i : ℕ,
      (Terras.T^[M]) n =
          3 ^ pullbackOddExcess alpha M n * baseMapAt alpha M n + i ∧
        i < 2 * 3 ^ pullbackOddExcess alpha M n := by
  let J : ℕ := ⌊alpha * M⌋₊
  let S : ℕ := Terras.oddCount M n
  let L : ℕ := pullbackOddExcess alpha M n
  let A : ℕ := 3 ^ J
  let B : ℕ := 2 ^ M
  let q : ℕ := baseMapAt alpha M n
  let z : ℕ := (Terras.T^[M]) n
  have hB : 0 < B := by
    dsimp [B]
    positivity
  have hS : J + L = S := by
    dsimp [J, S, L]
    exact floor_add_pullbackOddExcess hJ
  have hq :
      q * B ≤ A * n ∧ A * n < (q + 1) * B := by
    dsimp [q, A, B, J]
    exact (baseMapAt_eq_iff
      (alpha := alpha) (M := M) (n := n)
      (y := baseMapAt alpha M n)).1 rfl
  have hqLowerR :
      (q : ℝ) ≤ ((A * n : ℕ) : ℝ) / B := by
    have hqR : (q : ℝ) * B ≤ (A * n : ℕ) := by
      exact_mod_cast hq.1
    exact (le_div_iff₀ (by exact_mod_cast hB)).2 (by
      simpa [mul_comm] using hqR)
  have hqUpperR :
      ((A * n : ℕ) : ℝ) / B < (q : ℝ) + 1 := by
    have hqR : ((A * n : ℕ) : ℝ) < ((q + 1) * B : ℕ) := by
      exact_mod_cast hq.2
    apply (div_lt_iff₀ (by exact_mod_cast hB)).2
    simpa [Nat.cast_add, mul_comm] using hqR
  have hcorr0 : 0 ≤ Terras.affineCorrection M n * (3 : ℝ) ^ J :=
    mul_nonneg (Terras.affineCorrection_nonneg M n)
      (by positivity)
  have hz :
      (z : ℝ) =
        (((A * n : ℕ) : ℝ) / B +
            Terras.affineCorrection M n * (3 : ℝ) ^ J) *
          (3 : ℝ) ^ L := by
    have hAffine := Terras.iterate_eq_affineCorrection M n
    change (((Terras.T^[M]) n : ℕ) : ℝ) = _
    rw [hAffine]
    have hpow :
        (3 : ℝ) ^ Terras.oddCount M n =
          (3 : ℝ) ^ J * (3 : ℝ) ^ L := by
      rw [← pow_add, hS]
    rw [hpow]
    dsimp [A, B]
    push_cast
    field_simp
    ring
  have hzLowerR :
      ((3 ^ L * q : ℕ) : ℝ) ≤ z := by
    rw [hz]
    have hbracket :
        (q : ℝ) ≤
          ((A * n : ℕ) : ℝ) / B +
            Terras.affineCorrection M n * (3 : ℝ) ^ J := by
      linarith
    simpa [Nat.cast_mul, Nat.cast_pow, mul_comm] using
      (mul_le_mul_of_nonneg_right hbracket (by positivity : 0 ≤ (3 : ℝ) ^ L))
  have hzUpperR :
      (z : ℝ) < ((3 ^ L * (q + 2) : ℕ) : ℝ) := by
    rw [hz]
    have hbracket :
        ((A * n : ℕ) : ℝ) / B +
            Terras.affineCorrection M n * (3 : ℝ) ^ J <
          (q : ℝ) + 2 := by
      linarith
    simpa [Nat.cast_mul, Nat.cast_add, Nat.cast_pow, mul_comm] using
      (mul_lt_mul_of_pos_right hbracket (by positivity : 0 < (3 : ℝ) ^ L))
  have hzLower : 3 ^ L * q ≤ z := by
    exact_mod_cast hzLowerR
  have hzUpper : z < 3 ^ L * (q + 2) := by
    exact_mod_cast hzUpperR
  refine ⟨z - 3 ^ L * q, ?_, ?_⟩
  · have heqLocal :
        z = 3 ^ L * q + (z - 3 ^ L * q) := by
      omega
    simpa [z, q, L] using heqLocal
  · have hmul :
        3 ^ L * (q + 2) = 3 ^ L * q + 2 * 3 ^ L := by
      rw [Nat.mul_add]
      omega
    rw [hmul] at hzUpper
    have hboundLocal :
        z - 3 ^ L * q < 2 * 3 ^ L := by
      omega
    simpa [L] using hboundLocal

/-- Terminal parity regularity supplies both the lower exponent needed for
the quotient decomposition and the upper bound on the excess exponent. -/
theorem terminal_oddCount_and_excess_bounds
    {eta alpha : ℝ} {M n : ℕ}
    (hetaHalf : eta ≤ 1 / 2)
    (halpha : alpha = 1 / 2 - eta)
    (hlog : Nat.log 2 n = M)
    (hparity : n ∈ Terras.parityGood eta) :
    ⌊alpha * M⌋₊ ≤ Terras.oddCount M n ∧
      (pullbackOddExcess alpha M n : ℝ) <
        2 * eta * M + 1 := by
  have htol : Terras.parityTol eta = eta :=
    min_eq_left hetaHalf
  have hreg :
      Terras.PrefixTwoSidedRegular n (M / 2) M eta := by
    rw [Terras.parityGood, Set.mem_setOf_eq, hlog, htol] at hparity
    exact hparity
  subst alpha
  have hterminal :=
    hreg M (Nat.div_le_self M 2) le_rfl
  have hterminalBounds := abs_le.mp hterminal
  have halphaNonneg : 0 ≤ (1 / 2 - eta) * M := by
    exact mul_nonneg (sub_nonneg.mpr hetaHalf) (Nat.cast_nonneg M)
  have hfloorLe :
      (⌊(1 / 2 - eta) * M⌋₊ : ℝ) ≤ (1 / 2 - eta) * M :=
    Nat.floor_le halphaNonneg
  have hJReal :
      (⌊(1 / 2 - eta) * M⌋₊ : ℝ) ≤ Terras.oddCount M n := by
    calc
      (⌊(1 / 2 - eta) * M⌋₊ : ℝ) ≤ (1 / 2 - eta) * M := hfloorLe
      _ ≤ Terras.oddCount M n := by
        nlinarith [hterminalBounds.1]
  have hJ : ⌊(1 / 2 - eta) * M⌋₊ ≤ Terras.oddCount M n := by
    exact_mod_cast hJReal
  refine ⟨hJ, ?_⟩
  have hfloorLt :
      (1 / 2 - eta) * M <
        (⌊(1 / 2 - eta) * M⌋₊ : ℝ) + 1 :=
    Nat.lt_floor_add_one _
  have hLcast :
      (pullbackOddExcess (1 / 2 - eta) M n : ℝ) =
        (Terras.oddCount M n : ℝ) - ⌊(1 / 2 - eta) * M⌋₊ := by
    unfold pullbackOddExcess
    rw [Nat.cast_sub hJ]
  rw [hLcast]
  nlinarith [hterminalBounds.2]

/-- The deterministic remainder decomposition is exactly compatible with
the robust cone definition. -/
theorem base_cone_implies_terminal_mem
    {S : Set ℕ} {etaPrime alpha : ℝ} {M n : ℕ}
    (hbase : baseMapAt alpha M n ∈ coneCore 2 etaPrime S)
    (hdepth :
      (pullbackOddExcess alpha M n : ℝ) ≤
        etaPrime * Nat.log 3 (baseMapAt alpha M n))
    (hJ : ⌊alpha * M⌋₊ ≤ Terras.oddCount M n)
    (hcorr :
      Terras.affineCorrection M n * (3 : ℝ) ^ ⌊alpha * M⌋₊ < 1) :
    (Terras.T^[M]) n ∈ S := by
  obtain ⟨i, hiEq, hi⟩ :=
    exists_iterate_eq_baseMapAt_mul_pow_add hJ hcorr
  rw [hiEq]
  exact hbase.2
    (pullbackOddExcess alpha M n) hdepth i (by
      simpa [Nat.mul_comm] using hi)

/-- The audited startup inequality forces the parity excess to fit within
the available base-3 cone depth. -/
theorem pullback_excess_le_cone_depth
    {D : ℝ} {M n : ℕ}
    (hD0 : 0 < D) (hD1 : D ≤ 1)
    (hstart : 14 ≤ D * M)
    (hnShell : n ∈ dyadicShell M)
    (hparity : n ∈ Terras.parityGood (pullEta D)) :
    (pullbackOddExcess (pullAlpha D) M n : ℝ) ≤
      pullEtaPrime D *
        Nat.log 3 (baseMapAt (pullAlpha D) M n) := by
  have hlog : Nat.log 2 n = M :=
    Terras.log_two_eq_of_mem_dyadicShell hnShell
  have hetaHalf : pullEta D ≤ 1 / 2 :=
    pullEta_le_half hD1
  have hparityBounds :=
    terminal_oddCount_and_excess_bounds
      hetaHalf (by rfl) hlog hparity
  have hstartup :=
    pull_cone_depth_startup hD0 hD1
      (Nat.cast_nonneg M) hstart
  let J : ℕ := ⌊pullAlpha D * M⌋₊
  have hJbase :
      3 ^ J ≤ baseMapAt (pullAlpha D) M n := by
    have hrange :=
      baseMapAt_range
        (alpha := pullAlpha D) (M := M) (n := n) hnShell
    simpa [J, baseNumeratorScale] using hrange.1
  have hJlog :
      J ≤ Nat.log 3 (baseMapAt (pullAlpha D) M n) :=
    Nat.le_log_of_pow_le (by norm_num) hJbase
  have hfloorLt :
      pullAlpha D * M < (J : ℝ) + 1 := by
    dsimp [J]
    exact Nat.lt_floor_add_one _
  have hetaPrime0 : 0 < pullEtaPrime D :=
    pullEtaPrime_pos hD0
  have hJreal :
      (J : ℝ) ≤ Nat.log 3 (baseMapAt (pullAlpha D) M n) := by
    exact_mod_cast hJlog
  calc
    (pullbackOddExcess (pullAlpha D) M n : ℝ)
        ≤ 2 * pullEta D * M + 1 :=
      hparityBounds.2.le
    _ ≤ 2 * pullEta D * M + 1 + 1 / 128 := by norm_num
    _ ≤ pullEtaPrime D * (pullAlpha D * M - 1) := hstartup
    _ ≤ pullEtaPrime D * J := by
      apply mul_le_mul_of_nonneg_left _ hetaPrime0.le
      linarith
    _ ≤ pullEtaPrime D *
          Nat.log 3 (baseMapAt (pullAlpha D) M n) :=
      mul_le_mul_of_nonneg_left hJreal hetaPrime0.le

/-- The terminal affine correction occupies less than one unit after the
deterministic `3^J` factor is extracted. -/
theorem terminal_correction_lt_one
    {D : ℝ} {M n : ℕ}
    (hD0 : 0 < D) (hD1 : D ≤ 1)
    (hstart : 14 ≤ D * M)
    (hnShell : n ∈ dyadicShell M)
    (hcorrGood :
      n ∈ Terras.affineCorrectionGood (pullCorrectionTol D)) :
    Terras.affineCorrection M n *
        (3 : ℝ) ^ ⌊pullAlpha D * M⌋₊ < 1 := by
  let eta : ℝ := pullEta D
  let tol : ℝ := pullCorrectionTol D
  let J : ℕ := ⌊pullAlpha D * M⌋₊
  have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  have hDMleM : D * M ≤ (M : ℝ) := by simpa using mul_le_mul_of_nonneg_right hD1 hM0
  have hM14 : (14 : ℝ) ≤ M := hstart.trans hDMleM
  have hMone : (1 : ℝ) ≤ M := by linarith
  have hlog : Nat.log 2 n = M :=
    Terras.log_two_eq_of_mem_dyadicShell hnShell
  have hscaled :
      Terras.affineCorrection M n *
          (3 : ℝ) ^ ((M : ℝ) / 2) <
        (n : ℝ) ^ tol := by
    rw [Terras.affineCorrectionGood, Set.mem_setOf_eq] at hcorrGood
    simpa [tol] using hcorrGood M (by simp [hlog])
  have heta0 : 0 < eta := by
    dsimp [eta]
    exact pullEta_pos hD0
  have htol0 : 0 < tol := by
    dsimp [tol]
    exact pullCorrectionTol_pos hD0
  have hJfloor :
      (J : ℝ) ≤ pullAlpha D * M := by
    dsimp [J]
    apply Nat.floor_le
    exact mul_nonneg (pullAlpha_pos hD0 hD1).le hM0
  have hJexp :
      (J : ℝ) ≤ (M : ℝ) / 2 - eta * M := by
    dsimp [eta]
    unfold pullAlpha at hJfloor
    nlinarith
  have hthreeJ :
      (3 : ℝ) ^ J ≤
        (3 : ℝ) ^ ((M : ℝ) / 2) *
          (3 : ℝ) ^ (-eta * M) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add (by norm_num)]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    linarith
  have hcorr0 : 0 ≤ Terras.affineCorrection M n :=
    Terras.affineCorrection_nonneg M n
  have hnegPow : 0 < (3 : ℝ) ^ (-eta * M) := by positivity
  have hnUpperNat : n < 2 ^ (M + 1) := by
    exact (Finset.mem_Ico.mp (by simpa [dyadicShell] using hnShell)).2
  have hnUpper : (n : ℝ) ≤ ((2 ^ (M + 1) : ℕ) : ℝ) := by
    exact_mod_cast hnUpperNat.le
  have hnNonneg : (0 : ℝ) ≤ n := by positivity
  have hnPow :
      (n : ℝ) ^ tol ≤
        (2 : ℝ) ^ (tol * (M + 1)) := by
    calc
      (n : ℝ) ^ tol ≤ (((2 ^ (M + 1) : ℕ) : ℝ)) ^ tol :=
        Real.rpow_le_rpow hnNonneg hnUpper htol0.le
      _ = (2 : ℝ) ^ (tol * (M + 1)) := by
        push_cast
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
        congr 1
        rw [Nat.cast_add, Nat.cast_one]
        ring
  have hexponent :
      tol * (M + 1) + QuantitativeDensity.lg3 * (-eta * M) ≤ 0 := by
    dsimp [tol, eta]
    rw [pullCorrectionTol_eq]
    unfold pullEta
    have hlg0 := lg3_pos
    nlinarith
  calc
    Terras.affineCorrection M n * (3 : ℝ) ^ J
        ≤ Terras.affineCorrection M n *
            ((3 : ℝ) ^ ((M : ℝ) / 2) *
              (3 : ℝ) ^ (-eta * M)) :=
      mul_le_mul_of_nonneg_left hthreeJ hcorr0
    _ = (Terras.affineCorrection M n *
            (3 : ℝ) ^ ((M : ℝ) / 2)) *
          (3 : ℝ) ^ (-eta * M) := by ring
    _ < (n : ℝ) ^ tol * (3 : ℝ) ^ (-eta * M) :=
      mul_lt_mul_of_pos_right hscaled hnegPow
    _ ≤ (2 : ℝ) ^ (tol * (M + 1)) *
          (3 : ℝ) ^ (-eta * M) :=
      mul_le_mul_of_nonneg_right hnPow hnegPow.le
    _ = (2 : ℝ) ^
          (tol * (M + 1) + lg3 * (-eta * M)) := by
      rw [Terras.three_rpow_eq_two_rpow_lg3, ← Real.rpow_add (by norm_num)]
    _ ≤ (2 : ℝ) ^ (0 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) hexponent
    _ = 1 := by norm_num

/-- **Concrete shell-local pullback inclusion.**

At every post-startup dyadic scale, the three generated good conditions force
membership in the true Collatz pullback.  No density estimate appears here.
-/
theorem pullbackWitnessSet_subset_collatzPullback_on_shell
    {S : Set ℕ} {D : ℝ} {M n : ℕ}
    (hD0 : 0 < D) (hD1 : D ≤ 1)
    (hstart : 14 ≤ D * M)
    (hnShell : n ∈ dyadicShell M)
    (hnWitness :
      n ∈ pullbackWitnessSet S
        (pullEta D) (pullEtaPrime D) (pullAlpha D)
        (pullCorrectionTol D)) :
    n ∈ collatzPullback S := by
  have hlog : Nat.log 2 n = M :=
    Terras.log_two_eq_of_mem_dyadicShell hnShell
  obtain ⟨hbase, hparity, hcorrGood⟩ :=
    mem_pullbackWitnessSet.mp hnWitness
  have hbaseAt :
      baseMapAt (pullAlpha D) M n ∈
        coneCore 2 (pullEtaPrime D) S := by
    simpa [baseMap, hlog] using hbase
  have hparityBounds :=
    terminal_oddCount_and_excess_bounds
      (pullEta_le_half hD1)
      (by rfl) hlog hparity
  have hdepth :=
    pullback_excess_le_cone_depth
      hD0 hD1 hstart hnShell hparity
  have hcorr :=
    terminal_correction_lt_one
      hD0 hD1 hstart hnShell hcorrGood
  have hterminal :
      (Terras.T^[M]) n ∈ S :=
    base_cone_implies_terminal_mem
      hbaseAt hdepth hparityBounds.1 hcorr
  rw [mem_collatzPullback, hlog]
  exact hterminal

end

end QuantitativeDensity

end CollatzEndpointTransport
