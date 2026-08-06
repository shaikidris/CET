/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik
-/
import CollatzEndpointTransport.Linear.FixedTotalCriticalMoment
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.Convex.Slope
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.List.DropRight

/-!
# Central Renyi Core

Parameter inequalities for the central higher-Renyi fixed-total argument.

For `0 < theta < 1`, the admissible central composition proportion is

  alpha(theta) = (2^theta - 1) / (3^theta - 1).

The proof needs this proportion to lie strictly between `1/2` and
`log 2 / log 3`.  The first inequality is strict concavity of `x^theta`;
the second is strict convexity of `exp` after passing to logarithmic
coordinates.
-/

namespace CollatzEndpointTransport

namespace FixedTotal

open scoped Real

noncomputable section

/-- Central composition threshold for the `(1 + theta)`-moment. -/
def centralRenyiAlpha (theta : ℝ) : ℝ :=
  ((2 : ℝ) ^ theta - 1) / ((3 : ℝ) ^ theta - 1)

theorem one_lt_two_rpow
    {theta : ℝ} (htheta : 0 < theta) :
    1 < (2 : ℝ) ^ theta := by
  simpa using Real.one_lt_rpow (by norm_num : (1 : ℝ) < 2) htheta

theorem one_lt_three_rpow
    {theta : ℝ} (htheta : 0 < theta) :
    1 < (3 : ℝ) ^ theta := by
  simpa using Real.one_lt_rpow (by norm_num : (1 : ℝ) < 3) htheta

theorem centralRenyiAlpha_den_pos
    {theta : ℝ} (htheta : 0 < theta) :
    0 < (3 : ℝ) ^ theta - 1 := by
  linarith [one_lt_three_rpow htheta]

theorem centralRenyiAlpha_pos
    {theta : ℝ} (htheta : 0 < theta) :
    0 < centralRenyiAlpha theta := by
  unfold centralRenyiAlpha
  exact div_pos (by linarith [one_lt_two_rpow htheta])
    (centralRenyiAlpha_den_pos htheta)

/-- Strict concavity places the central threshold above one half. -/
theorem one_half_lt_centralRenyiAlpha
    {theta : ℝ} (htheta0 : 0 < theta) (htheta1 : theta < 1) :
    (1 / 2 : ℝ) < centralRenyiAlpha theta := by
  have hconc :=
    (Real.strictConcaveOn_rpow htheta0 htheta1).2
      (show (1 : ℝ) ∈ Set.Ici 0 by norm_num)
      (show (3 : ℝ) ∈ Set.Ici 0 by norm_num)
      (by norm_num : (1 : ℝ) ≠ 3)
      (show 0 < (1 / 2 : ℝ) by norm_num)
      (show 0 < (1 / 2 : ℝ) by norm_num)
      (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
  have hconc' :
      (1 / 2 : ℝ) * (1 : ℝ) ^ theta +
          (1 / 2 : ℝ) * (3 : ℝ) ^ theta <
        (2 : ℝ) ^ theta := by
    convert hconc using 1 <;> norm_num [smul_eq_mul]
  rw [Real.one_rpow] at hconc'
  unfold centralRenyiAlpha
  rw [div_lt_div_iff₀ (by norm_num : (0 : ℝ) < 2)
    (centralRenyiAlpha_den_pos htheta0)]
  linarith

/-- The exponential secant slope `(exp x - 1) / x` is strictly increasing
on the positive real axis. -/
theorem exp_sub_one_div_lt
    {x y : ℝ} (hx : 0 < x) (hxy : x < y) :
    (Real.exp x - 1) / x < (Real.exp y - 1) / y := by
  have hy : 0 < y := hx.trans hxy
  simpa using
    strictConvexOn_exp.secant_strict_mono
      (show (0 : ℝ) ∈ Set.univ by simp)
      (show x ∈ Set.univ by simp)
      (show y ∈ Set.univ by simp)
      hx.ne' hy.ne' hxy

/-- The central threshold remains below the multiplicative drift boundary. -/
theorem centralRenyiAlpha_lt_log_ratio
    {theta : ℝ} (htheta0 : 0 < theta) :
    centralRenyiAlpha theta < Real.log 2 / Real.log 3 := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hxy : theta * Real.log 2 < theta * Real.log 3 :=
    mul_lt_mul_of_pos_left (Real.strictMonoOn_log (by norm_num) (by norm_num)
      (by norm_num)) htheta0
  have hslope := exp_sub_one_div_lt (mul_pos htheta0 hlog2) hxy
  have hexp2 : Real.exp (theta * Real.log 2) = (2 : ℝ) ^ theta := by
    simp [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2), mul_comm]
  have hexp3 : Real.exp (theta * Real.log 3) = (3 : ℝ) ^ theta := by
    simp [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3), mul_comm]
  rw [hexp2, hexp3] at hslope
  unfold centralRenyiAlpha
  rw [div_lt_div_iff₀ (centralRenyiAlpha_den_pos htheta0) hlog3]
  rw [div_lt_div_iff₀ (mul_pos htheta0 hlog2) (mul_pos htheta0 hlog3)] at hslope
  nlinarith

theorem centralRenyiAlpha_mem
    {theta : ℝ} (htheta0 : 0 < theta) (htheta1 : theta < 1) :
    centralRenyiAlpha theta ∈
      Set.Ioo (1 / 2 : ℝ) (Real.log 2 / Real.log 3) :=
  ⟨one_half_lt_centralRenyiAlpha htheta0 htheta1,
    centralRenyiAlpha_lt_log_ratio htheta0⟩

/-- Slack between a chosen central window and the admissible proportion. -/
def centralRenyiGap (theta eta : ℝ) : ℝ :=
  centralRenyiAlpha theta - (1 / 2 + eta)

/-- A fixed proportion strictly inside the admissible geometric range. -/
def centralRenyiPiStar (theta eta : ℝ) : ℝ :=
  centralRenyiAlpha theta - centralRenyiGap theta eta / 2

theorem centralRenyiGap_pos
    {theta eta : ℝ}
    (heta : eta < centralRenyiAlpha theta - 1 / 2) :
    0 < centralRenyiGap theta eta := by
  unfold centralRenyiGap
  linarith

theorem centralRenyiPiStar_lt_alpha
    {theta eta : ℝ}
    (heta : eta < centralRenyiAlpha theta - 1 / 2) :
    centralRenyiPiStar theta eta < centralRenyiAlpha theta := by
  unfold centralRenyiPiStar
  linarith [centralRenyiGap_pos heta]

theorem one_half_add_eta_lt_centralRenyiPiStar
    {theta eta : ℝ}
    (heta : eta < centralRenyiAlpha theta - 1 / 2) :
    1 / 2 + eta < centralRenyiPiStar theta eta := by
  unfold centralRenyiPiStar centralRenyiGap
  linarith

/-- Geometric ratio controlling the reverse-spend moment. -/
def centralRenyiRatio (theta pi : ℝ) : ℝ :=
  (3 : ℝ) ^ theta * pi / ((2 : ℝ) ^ theta - 1 + pi)

theorem centralRenyiRatio_den_pos
    {theta pi : ℝ} (htheta : 0 < theta) (hpi : 0 < pi) :
    0 < (2 : ℝ) ^ theta - 1 + pi := by
  linarith [one_lt_two_rpow htheta]

theorem centralRenyiRatio_den_pos_of_nonneg
    {theta pi : ℝ} (htheta : 0 < theta) (hpi : 0 ≤ pi) :
    0 < (2 : ℝ) ^ theta - 1 + pi := by
  linarith [one_lt_two_rpow htheta]

/-- The reverse-spend ratio is increasing in the separator proportion. -/
theorem centralRenyiRatio_mono
    {theta pi rho : ℝ}
    (htheta : 0 < theta) (hpi : 0 ≤ pi) (hpirho : pi ≤ rho) :
    centralRenyiRatio theta pi ≤ centralRenyiRatio theta rho := by
  have hrho : 0 ≤ rho := hpi.trans hpirho
  have htwo : 0 < (2 : ℝ) ^ theta - 1 := by
    linarith [one_lt_two_rpow htheta]
  have hthree : 0 < (3 : ℝ) ^ theta := by positivity
  have hdenPi := centralRenyiRatio_den_pos_of_nonneg htheta hpi
  have hdenRho := centralRenyiRatio_den_pos_of_nonneg htheta hrho
  unfold centralRenyiRatio
  rw [div_le_div_iff₀ hdenPi hdenRho]
  nlinarith [mul_nonneg hthree.le htwo.le]

/-- Every positive proportion below `centralRenyiAlpha` gives a strictly
contracting reverse-spend geometric series. -/
theorem centralRenyiRatio_lt_one
    {theta pi : ℝ}
    (htheta : 0 < theta) (hpi : 0 < pi)
    (hpialpha : pi < centralRenyiAlpha theta) :
    centralRenyiRatio theta pi < 1 := by
  have hden := centralRenyiRatio_den_pos htheta hpi
  have hthree : 0 < (3 : ℝ) ^ theta - 1 :=
    centralRenyiAlpha_den_pos htheta
  have hscaled :
      ((3 : ℝ) ^ theta - 1) * pi < (2 : ℝ) ^ theta - 1 := by
    unfold centralRenyiAlpha at hpialpha
    simpa [mul_comm] using (lt_div_iff₀ hthree).mp hpialpha
  unfold centralRenyiRatio
  rw [div_lt_one hden]
  linarith

/-- Exact reverse-spend critical curve.  The earlier one-way theorem is the
direction used by the central-window proof; this equivalence records that
the threshold `centralRenyiAlpha` is sharp for the geometric kernel. -/
theorem centralRenyiRatio_lt_one_iff
    {theta pi : ℝ}
    (htheta : 0 < theta) (hpi : 0 < pi) :
    centralRenyiRatio theta pi < 1 ↔
      pi < centralRenyiAlpha theta := by
  have hden := centralRenyiRatio_den_pos htheta hpi
  have hthree : 0 < (3 : ℝ) ^ theta - 1 :=
    centralRenyiAlpha_den_pos htheta
  unfold centralRenyiRatio centralRenyiAlpha
  rw [div_lt_one hden, lt_div_iff₀ hthree]
  constructor <;> intro h <;> nlinarith

@[simp]
theorem centralRenyiAlpha_one :
    centralRenyiAlpha 1 = 1 / 2 := by
  norm_num [centralRenyiAlpha]

@[simp]
theorem centralRenyiRatio_one_half_one :
    centralRenyiRatio 1 (1 / 2) = 1 := by
  norm_num [centralRenyiRatio]

/-- Unrestricted reverse-spend reproduction ratio. -/
def unrestrictedReverseSpendRatio (theta : ℝ) : ℝ :=
  (3 : ℝ) ^ theta / ((2 : ℝ) ^ (1 + theta) - 1)

/-- The unrestricted reverse-spend ratio is exactly the centered
specialization of the cohort reproduction kernel. -/
theorem centralRenyiRatio_one_half_eq_unrestrictedReverseSpendRatio
    {theta : ℝ} (htheta : 0 < theta) :
    centralRenyiRatio theta (1 / 2) =
      unrestrictedReverseSpendRatio theta := by
  have hden1 : 0 < (2 : ℝ) ^ theta - 1 + 1 / 2 :=
    centralRenyiRatio_den_pos htheta (by norm_num)
  have hpow : (2 : ℝ) ^ (1 + theta) = 2 * (2 : ℝ) ^ theta := by
    rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_one]
  have hdenEq :
      (2 : ℝ) ^ (1 + theta) - 1 =
        2 * ((2 : ℝ) ^ theta - 1 + 1 / 2) := by
    rw [hpow]
    ring
  unfold centralRenyiRatio unrestrictedReverseSpendRatio
  rw [hdenEq]
  field_simp [hden1.ne']

@[simp]
theorem unrestrictedReverseSpendRatio_one :
    unrestrictedReverseSpendRatio 1 = 1 := by
  norm_num [unrestrictedReverseSpendRatio]

theorem centralRenyiPiStar_pos
    {theta eta : ℝ}
    (htheta0 : 0 < theta) (htheta1 : theta < 1)
    (heta0 : 0 < eta)
    (heta1 : eta < centralRenyiAlpha theta - 1 / 2) :
    0 < centralRenyiPiStar theta eta := by
  linarith [one_half_add_eta_lt_centralRenyiPiStar heta1]

theorem centralRenyiRatio_piStar_lt_one
    {theta eta : ℝ}
    (htheta0 : 0 < theta) (htheta1 : theta < 1)
    (heta0 : 0 < eta)
    (heta1 : eta < centralRenyiAlpha theta - 1 / 2) :
    centralRenyiRatio theta (centralRenyiPiStar theta eta) < 1 := by
  exact centralRenyiRatio_lt_one htheta0
    (centralRenyiPiStar_pos htheta0 htheta1 heta0 heta1)
    (centralRenyiPiStar_lt_alpha heta1)

end

end FixedTotal

end CollatzEndpointTransport
/-
Exact composition-level combinatorics for central fixed-total moments.

The two-child recursion for positive compositions gives Pascal's recurrence
for the number of compositions of `N` with `s` parts.  This file records the
closed form needed to normalize the central fixed-total law.
-/

namespace CollatzEndpointTransport

namespace FixedTotal

open Nat Finset

noncomputable section

theorem card_fixedSet_eq_indicator_sum
    (N s : ℕ) :
    (fixedSet N s).card =
      ∑ c : Composition N, if c.length = s then 1 else 0 := by
  simp [fixedSet]

theorem fixedSet_zero
    (N : ℕ) (hN : 0 < N) :
    fixedSet N 0 = ∅ := by
  ext c
  simp only [fixedSet, mem_filter, mem_univ, true_and, not_mem_empty, iff_false]
  exact Nat.ne_of_gt (c.length_pos_of_pos hN)

/-- Pascal recurrence for fixed-length positive compositions. -/
theorem card_fixedSet_succ
    (N s : ℕ) (hN : 0 < N) (hs : 0 < s) :
    (fixedSet (N + 1) s).card =
      (fixedSet N s).card + (fixedSet N (s - 1)).card := by
  rw [card_fixedSet_eq_indicator_sum, card_fixedSet_eq_indicator_sum,
    card_fixedSet_eq_indicator_sum]
  let e := compositionSuccEquiv N hN
  have he :=
    (Equiv.sum_comp e
      (fun c : Composition (N + 1) => if c.length = s then 1 else 0)).symm
  rw [Fintype.sum_sum_type] at he
  dsimp [e, compositionSuccEquiv] at he
  rw [he]
  simp only [increaseFirst_length, prependOne_length]
  apply congrArg₂ (· + ·) rfl
  apply Fintype.sum_congr
  intro c
  by_cases hlen : c.length + 1 = s
  · have hpred : c.length = s - 1 := by omega
    rw [if_pos hlen, if_pos hpred]
  · have hpred : c.length ≠ s - 1 := by
      intro h
      have hlenPos := c.length_pos_of_pos hN
      omega
    rw [if_neg hlen, if_neg hpred]

/-- A composition of `N` has `s` parts in exactly `choose (N-1) (s-1)` ways. -/
theorem card_fixedSet
    (N s : ℕ) (hN : 0 < N) (hs : 0 < s) :
    (fixedSet N s).card = (N - 1).choose (s - 1) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hN)
  induction k generalizing s with
  | zero =>
      have hlength : ∀ c : Composition 1, c.length = 1 := by
        intro c
        have hpos := c.length_pos_of_pos (by norm_num)
        have hle := c.length_le
        omega
      by_cases hs1 : s = 1
      · subst s
        simp [fixedSet, hlength, composition_card]
      · have hset : fixedSet 1 s = ∅ := by
          ext c
          have hne : (1 : ℕ) ≠ s := Ne.symm hs1
          simp [fixedSet, hlength c, hne]
        have hslt : 1 < s := by omega
        rw [hset]
        simp [Nat.choose_eq_zero_of_lt (by omega : 0 < s - 1)]
  | succ k ih =>
      by_cases hs1 : s = 1
      · subst s
        rw [card_fixedSet_succ (k + 1) 1 (by omega) (by omega)]
        rw [fixedSet_zero (k + 1) (by omega)]
        simp [ih 1 (by omega)]
      · have hsPred : 0 < s - 1 := by omega
        obtain ⟨t, rfl⟩ : ∃ t, s = t + 2 := by
          use s - 2
          omega
        rw [card_fixedSet_succ (k + 1) (t + 2) (by omega) (by omega)]
        rw [ih (t + 2) (by omega) (by omega),
          ih (t + 2 - 1) (by omega) (by omega)]
        simp only [Nat.succ_eq_add_one, Nat.add_sub_cancel]
        have hsub1 : t + 2 - 1 = t + 1 := by omega
        rw [hsub1, Nat.add_one_sub_one]
        have hchoose := Nat.choose_succ_succ k t
        simpa [Nat.succ_eq_add_one, Nat.add_comm] using hchoose.symm

end

end FixedTotal

end CollatzEndpointTransport
/-
Higher-Renyi quotient-order estimate for fixed-total residue fibers.

The sharp paper constant is unnecessary for the density exponent.  The
same upper-half argument used at the critical square-root order gives a
uniform factor four for every exponent in `(0,1]`.
-/

namespace CollatzEndpointTransport

namespace FixedTotal

open Nat Finset
open scoped Real

noncomputable section

/-- Cardinality versus a positive real power of distinct nonnegative
integers.  The constant is uniform for `0 < theta <= 1`. -/
theorem card_mul_rpow_card_le_four_sum_rpow_succ
    (S : Finset ℕ) {theta : ℝ}
    (htheta0 : 0 < theta) (htheta1 : theta ≤ 1) :
    (S.card : ℝ) * (S.card : ℝ) ^ theta ≤
      4 * ∑ q ∈ S, ((q + 1 : ℕ) : ℝ) ^ theta := by
  let h := S.card / 2
  let high := S.filter fun q => h ≤ q
  have hhigh : S.card - S.card / 2 ≤ high.card := by
    simpa [h, high] using half_card_le_card_filter_half S
  have hcard : S.card ≤ 2 * high.card := by omega
  have hscale : S.card ≤ 2 * (h + 1) := by
    dsimp [h]
    omega
  have hscaleR : (S.card : ℝ) ≤ 2 * (h + 1) := by
    exact_mod_cast hscale
  have hpowTwo : (2 : ℝ) ^ theta ≤ 2 := by
    simpa using
      (Real.rpow_le_rpow_of_exponent_le
        (by norm_num : (1 : ℝ) ≤ 2) htheta1)
  have hpow : (S.card : ℝ) ^ theta ≤
      2 * ((h + 1 : ℕ) : ℝ) ^ theta := by
    have hmono :=
      Real.rpow_le_rpow (by positivity : (0 : ℝ) ≤ S.card)
        hscaleR htheta0.le
    calc
      (S.card : ℝ) ^ theta
          ≤ (2 * ((h + 1 : ℕ) : ℝ)) ^ theta := by
            convert hmono using 1 <;> norm_num
      _ = (2 : ℝ) ^ theta * ((h + 1 : ℕ) : ℝ) ^ theta := by
        rw [Real.mul_rpow] <;> positivity
      _ ≤ 2 * ((h + 1 : ℕ) : ℝ) ^ theta :=
        mul_le_mul_of_nonneg_right hpowTwo
          (Real.rpow_nonneg (by positivity) _)
  have hcardR : (S.card : ℝ) ≤ 2 * high.card := by
    exact_mod_cast hcard
  have hprod :
      (S.card : ℝ) * (S.card : ℝ) ^ theta ≤
        4 * (high.card : ℝ) * ((h + 1 : ℕ) : ℝ) ^ theta := by
    calc
      (S.card : ℝ) * (S.card : ℝ) ^ theta
          ≤ (2 * high.card : ℝ) * (S.card : ℝ) ^ theta :=
        mul_le_mul_of_nonneg_right hcardR
          (Real.rpow_nonneg (by positivity) _)
      _ ≤ (2 * high.card : ℝ) *
          (2 * ((h + 1 : ℕ) : ℝ) ^ theta) :=
        mul_le_mul_of_nonneg_left hpow (by positivity)
      _ = 4 * (high.card : ℝ) * ((h + 1 : ℕ) : ℝ) ^ theta := by
        ring
  have hsumHigh :
      (high.card : ℝ) * ((h + 1 : ℕ) : ℝ) ^ theta ≤
        ∑ q ∈ high, ((q + 1 : ℕ) : ℝ) ^ theta := by
    calc
      (high.card : ℝ) * ((h + 1 : ℕ) : ℝ) ^ theta =
          ∑ _q ∈ high, ((h + 1 : ℕ) : ℝ) ^ theta := by simp
      _ ≤ ∑ q ∈ high, ((q + 1 : ℕ) : ℝ) ^ theta := by
        apply Finset.sum_le_sum
        intro q hq
        apply Real.rpow_le_rpow (by positivity) _ htheta0.le
        exact_mod_cast Nat.add_le_add_right (Finset.mem_filter.mp hq).2 1
  have hsumSubset :
      ∑ q ∈ high, ((q + 1 : ℕ) : ℝ) ^ theta ≤
        ∑ q ∈ S, ((q + 1 : ℕ) : ℝ) ^ theta := by
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.filter_subset _ _)
      (fun q _ _ => Real.rpow_nonneg (by positivity) _)
  calc
    (S.card : ℝ) * (S.card : ℝ) ^ theta
        ≤ 4 * (high.card : ℝ) * ((h + 1 : ℕ) : ℝ) ^ theta := hprod
    _ ≤ 4 * ∑ q ∈ high, ((q + 1 : ℕ) : ℝ) ^ theta := by
      simpa [mul_assoc] using
        mul_le_mul_of_nonneg_left hsumHigh (by norm_num : (0 : ℝ) ≤ 4)
    _ ≤ 4 * ∑ q ∈ S, ((q + 1 : ℕ) : ℝ) ^ theta :=
      mul_le_mul_of_nonneg_left hsumSubset (by norm_num)

/-- Higher-order quotient estimate in one residue fiber. -/
theorem residueFiber_renyi_bound
    {alpha : Type*} [DecidableEq alpha]
    (W : Finset alpha) (A : alpha → ℕ) (m : ℕ) (a : Fin m)
    {theta : ℝ} (htheta0 : 0 < theta) (htheta1 : theta ≤ 1)
    (hm : 0 < m) (hA : Set.InjOn A W) :
    (m : ℝ) ^ theta *
        ((residueFiber W A m a).card : ℝ) *
        ((residueFiber W A m a).card : ℝ) ^ theta ≤
      4 * ∑ x ∈ residueFiber W A m a,
        ((m + A x : ℕ) : ℝ) ^ theta := by
  let F := residueFiber W A m a
  let Q := F.image fun x => A x / m
  have hqinj : Set.InjOn (fun x => A x / m) F :=
    quotient_injective_on_residueFiber hA
  have hcardQ : Q.card = F.card := Finset.card_image_iff.mpr hqinj
  have hbase :=
    card_mul_rpow_card_le_four_sum_rpow_succ Q htheta0 htheta1
  rw [hcardQ] at hbase
  have hscaled :
      (m : ℝ) ^ theta * (F.card : ℝ) * (F.card : ℝ) ^ theta ≤
        4 * ∑ q ∈ Q, ((m * (q + 1) : ℕ) : ℝ) ^ theta := by
    calc
      (m : ℝ) ^ theta * (F.card : ℝ) * (F.card : ℝ) ^ theta =
          (m : ℝ) ^ theta *
            ((F.card : ℝ) * (F.card : ℝ) ^ theta) := by ring
      _ ≤ (m : ℝ) ^ theta *
          (4 * ∑ q ∈ Q, ((q + 1 : ℕ) : ℝ) ^ theta) :=
        mul_le_mul_of_nonneg_left hbase
          (Real.rpow_nonneg (by positivity) _)
      _ = 4 * ((m : ℝ) ^ theta *
          ∑ q ∈ Q, ((q + 1 : ℕ) : ℝ) ^ theta) := by ring
      _ = 4 * ∑ q ∈ Q,
          (m : ℝ) ^ theta * ((q + 1 : ℕ) : ℝ) ^ theta := by
        rw [Finset.mul_sum]
      _ = 4 * ∑ q ∈ Q, ((m * (q + 1) : ℕ) : ℝ) ^ theta := by
        apply congrArg (fun x : ℝ => 4 * x)
        apply Finset.sum_congr rfl
        intro q hq
        rw [show (((m * (q + 1) : ℕ) : ℝ)) =
            (m : ℝ) * ((q + 1 : ℕ) : ℝ) by norm_num [Nat.cast_mul]]
        rw [Real.mul_rpow] <;> positivity
  have hrewrite :
      ∑ q ∈ Q, ((m * (q + 1) : ℕ) : ℝ) ^ theta =
        ∑ x ∈ F, ((m * (A x / m + 1) : ℕ) : ℝ) ^ theta := by
    rw [show Q = F.image (fun x => A x / m) by rfl]
    rw [Finset.sum_image hqinj]
  rw [hrewrite] at hscaled
  refine hscaled.trans ?_
  apply mul_le_mul_of_nonneg_left ?_ (by norm_num)
  apply Finset.sum_le_sum
  intro x hx
  apply Real.rpow_le_rpow (by positivity) _ htheta0.le
  have hdiv : m * (A x / m) ≤ A x := Nat.mul_div_le (A x) m
  have hnat : m * (A x / m + 1) ≤ m + A x := by
    calc
      m * (A x / m + 1) = m * (A x / m) + m := by
        rw [Nat.mul_add, Nat.mul_one]
      _ ≤ A x + m := Nat.add_le_add_right hdiv m
      _ = m + A x := Nat.add_comm _ _
  exact_mod_cast hnat

/-- Summed higher-order quotient estimate over all residue fibers. -/
theorem residueFibers_renyi_bound
    {alpha : Type*} [DecidableEq alpha]
    (W : Finset alpha) (A : alpha → ℕ) (m : ℕ)
    {theta : ℝ} (htheta0 : 0 < theta) (htheta1 : theta ≤ 1)
    (hm : 0 < m) (hA : Set.InjOn A W) :
    (m : ℝ) ^ theta *
        (∑ a : Fin m,
          ((residueFiber W A m a).card : ℝ) *
            ((residueFiber W A m a).card : ℝ) ^ theta) ≤
      4 * ∑ x ∈ W, ((m + A x : ℕ) : ℝ) ^ theta := by
  calc
    (m : ℝ) ^ theta *
          (∑ a : Fin m,
            ((residueFiber W A m a).card : ℝ) *
              ((residueFiber W A m a).card : ℝ) ^ theta) =
        ∑ a : Fin m,
          (m : ℝ) ^ theta *
            ((residueFiber W A m a).card : ℝ) *
            ((residueFiber W A m a).card : ℝ) ^ theta := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a ha
      ring
    _ ≤ ∑ a : Fin m,
        4 * ∑ x ∈ residueFiber W A m a,
          ((m + A x : ℕ) : ℝ) ^ theta := by
      apply Finset.sum_le_sum
      intro a ha
      exact residueFiber_renyi_bound W A m a htheta0 htheta1 hm hA
    _ = 4 * ∑ x ∈ W, ((m + A x : ℕ) : ℝ) ^ theta := by
      rw [← Finset.mul_sum, sum_residueFiber W A m hm]

end

end FixedTotal

end CollatzEndpointTransport
/-
Higher-Renyi fixed-total moment interface.

This module packages the quotient-order theorem at an arbitrary exponent
`0 < theta <= 1`.  The central reverse-spend estimate will supply the
upper bound for the source-side sum appearing here.
-/

namespace CollatzEndpointTransport

namespace FixedTotal

open Nat Finset
open scoped Real

noncomputable section

local instance centralMomentCompositionDecidableEq (N : ℕ) :
    DecidableEq (Composition N) :=
  Classical.decEq _

/-- Unnormalised fixed-level `(1 + theta)` residue moment. -/
def fixedRenyiNumerator (N s : ℕ) (theta : ℝ) : ℝ :=
  ((3 ^ s : ℕ) : ℝ) ^ theta *
    ∑ a : Fin (3 ^ s),
      (fixedFiberCard N s a : ℝ) *
        (fixedFiberCard N s a : ℝ) ^ theta

theorem fixedRenyiNumerator_nonneg
    (N s : ℕ) (theta : ℝ) :
    0 ≤ fixedRenyiNumerator N s theta := by
  unfold fixedRenyiNumerator
  positivity

/-- Normalized fixed-total residue moment.  Empty levels contribute zero. -/
def fixedRenyiMoment (N s : ℕ) (theta : ℝ) : ℝ :=
  fixedRenyiNumerator N s theta /
    ((fixedSet N s).card : ℝ) ^ (1 + theta)

/-- Source-side moment of `3^s + A(k)` at one composition level. -/
def fixedLiftMoment (N s : ℕ) (theta : ℝ) : ℝ :=
  ∑ c ∈ fixedSet N s,
    (((3 ^ s + syracuseNumerator c : ℕ) : ℝ) ^ theta)

theorem fixedRenyiNumerator_le
    (N s : ℕ) {theta : ℝ}
    (htheta0 : 0 < theta) (htheta1 : theta ≤ 1) :
    fixedRenyiNumerator N s theta ≤
      4 * fixedLiftMoment N s theta := by
  have hm : 0 < 3 ^ s := pow_pos (by norm_num) _
  simpa [fixedRenyiNumerator, fixedLiftMoment, fixedFiberCard,
    Nat.cast_pow] using
    residueFibers_renyi_bound
      (fixedSet N s) syracuseNumerator (3 ^ s)
      htheta0 htheta1 hm (syracuseNumerator_injOn_fixedSet N s)

theorem fixedRenyiMoment_le
    (N s : ℕ) {theta : ℝ}
    (htheta0 : 0 < theta) (htheta1 : theta ≤ 1) :
    fixedRenyiMoment N s theta ≤
      4 * fixedLiftMoment N s theta /
        ((fixedSet N s).card : ℝ) ^ (1 + theta) := by
  unfold fixedRenyiMoment
  exact div_le_div_of_nonneg_right
    (fixedRenyiNumerator_le N s htheta0 htheta1)
    (Real.rpow_nonneg (by positivity) _)

theorem fixedRenyiMoment_nonneg
    (N s : ℕ) (theta : ℝ) :
    0 ≤ fixedRenyiMoment N s theta := by
  unfold fixedRenyiMoment fixedRenyiNumerator
  positivity

end

end FixedTotal

end CollatzEndpointTransport
/-
The binomial mass at its own mean.

For `0 <= k <= n`, the Bernoulli parameter `k / n` makes the `k`-th
binomial mass a mode.  We work with the integer-scaled masses

  choose n j * k^j * (n-k)^(n-j),

so the proof has no division or endpoint exceptions.  The resulting
`1 / (n+1)` lower bound is the conditioning loss used by the central
higher-Renyi fixed-total argument.
-/

namespace CollatzEndpointTransport

namespace FixedTotal

open Nat Finset

/-- Binomial mass with the common denominator `n^n` removed. -/
def scaledBinomialMass (n k j : ℕ) : ℕ :=
  n.choose j * k ^ j * (n - k) ^ (n - j)

/-- Cross-multiplied ratio identity for two consecutive scaled masses. -/
theorem scaledBinomialMass_succ_cross
    {n k j : ℕ} (hj : j < n) :
    scaledBinomialMass n k (j + 1) * ((j + 1) * (n - k)) =
      scaledBinomialMass n k j * ((n - j) * k) := by
  have hsub : n - j = (n - (j + 1)) + 1 := by omega
  have hchoose := Nat.choose_succ_right_eq n j
  unfold scaledBinomialMass
  calc
    n.choose (j + 1) * k ^ (j + 1) * (n - k) ^ (n - (j + 1)) *
          ((j + 1) * (n - k)) =
        (n.choose (j + 1) * (j + 1)) *
          (k ^ j * k) * ((n - k) ^ (n - (j + 1)) * (n - k)) := by
            rw [pow_succ]
            ring
    _ = (n.choose j * (n - j)) *
          (k ^ j * k) * ((n - k) ^ (n - (j + 1)) * (n - k)) := by
            rw [hchoose]
    _ = n.choose j * k ^ j * (n - k) ^ (n - j) * ((n - j) * k) := by
            rw [hsub, pow_succ]
            ring

/-- The scaled masses increase strictly up to the mean index. -/
theorem scaledBinomialMass_le_succ_of_lt_mean
    {n k j : ℕ} (hk : k < n) (hj : j < k) :
    scaledBinomialMass n k j ≤ scaledBinomialMass n k (j + 1) := by
  have hnk : 0 < n - k := Nat.sub_pos_of_lt hk
  have hfactor : 0 < (j + 1) * (n - k) := Nat.mul_pos (Nat.succ_pos _) hnk
  have hcoef : (j + 1) * (n - k) ≤ (n - j) * k := by
    calc
      (j + 1) * (n - k) ≤ k * (n - k) :=
        Nat.mul_le_mul_right _ (Nat.succ_le_of_lt hj)
      _ ≤ k * (n - j) :=
        Nat.mul_le_mul_left _ (Nat.sub_le_sub_left hj.le n)
      _ = (n - j) * k := Nat.mul_comm _ _
  apply Nat.le_of_mul_le_mul_right _ hfactor
  calc
    scaledBinomialMass n k j * ((j + 1) * (n - k))
        ≤ scaledBinomialMass n k j * ((n - j) * k) := by
          exact Nat.mul_le_mul_left _ hcoef
    _ = scaledBinomialMass n k (j + 1) * ((j + 1) * (n - k)) := by
          symm
          exact scaledBinomialMass_succ_cross (hj.trans hk)

/-- The scaled masses decrease after the mean index. -/
theorem scaledBinomialMass_succ_le_of_mean_le
    {n k j : ℕ} (hjn : j < n) (hkj : k ≤ j) :
    scaledBinomialMass n k (j + 1) ≤ scaledBinomialMass n k j := by
  have hkn : k < n := lt_of_le_of_lt hkj hjn
  have hnk : 0 < n - k := Nat.sub_pos_of_lt hkn
  have hfactor : 0 < (j + 1) * (n - k) := Nat.mul_pos (Nat.succ_pos _) hnk
  have hcoef : (n - j) * k ≤ (j + 1) * (n - k) := by
    calc
      (n - j) * k ≤ (n - k) * k :=
        Nat.mul_le_mul_right _ (Nat.sub_le_sub_left hkj n)
      _ ≤ (n - k) * (j + 1) :=
        Nat.mul_le_mul_left _ (hkj.trans (Nat.le_succ j))
      _ = (j + 1) * (n - k) := Nat.mul_comm _ _
  apply Nat.le_of_mul_le_mul_right _ hfactor
  calc
    scaledBinomialMass n k (j + 1) * ((j + 1) * (n - k))
        = scaledBinomialMass n k j * ((n - j) * k) :=
          scaledBinomialMass_succ_cross hjn
    _ ≤ scaledBinomialMass n k j * ((j + 1) * (n - k)) := by
          exact Nat.mul_le_mul_left _ hcoef

/-- Every scaled binomial mass is bounded by the mass at its mean index. -/
theorem scaledBinomialMass_le_mode
    {n k j : ℕ} (hk : k ≤ n) (hj : j ≤ n) :
    scaledBinomialMass n k j ≤ scaledBinomialMass n k k := by
  by_cases hk0 : k = 0
  · subst k
    by_cases hj0 : j = 0
    · subst j
      rfl
    · simp [scaledBinomialMass, hj0]
  by_cases hknEq : k = n
  · subst k
    rcases lt_or_eq_of_le hj with hjn | rfl
    · have hsub : 0 < n - j := Nat.sub_pos_of_lt hjn
      simp [scaledBinomialMass, Nat.zero_pow hsub]
    · rfl
  have hkn : k < n := lt_of_le_of_ne hk hknEq
  rcases le_total j k with hjk | hkj
  · have hwalk : ∀ d : ℕ, j + d ≤ k →
        scaledBinomialMass n k j ≤ scaledBinomialMass n k (j + d) := by
      intro d
      induction d with
      | zero => simp
      | succ d ih =>
          intro hd
          have hd' : j + d ≤ k := by omega
          exact (ih hd').trans
            (scaledBinomialMass_le_succ_of_lt_mean hkn (by omega))
    simpa [Nat.add_sub_of_le hjk] using hwalk (k - j) (by omega)
  · have hwalk : ∀ d : ℕ, k + d ≤ j →
        scaledBinomialMass n k (k + d) ≤ scaledBinomialMass n k k := by
      intro d
      induction d with
      | zero => simp
      | succ d ih =>
          intro hd
          have hd' : k + d ≤ j := by omega
          exact (scaledBinomialMass_succ_le_of_mean_le
            (n := n) (k := k) (j := k + d)
            (by omega) (by omega)).trans (ih hd')
    simpa [Nat.add_sub_of_le hkj] using hwalk (j - k) (by omega)

/-- The sum of the scaled masses is exactly `n^n`. -/
theorem sum_scaledBinomialMass (n k : ℕ) (hk : k ≤ n) :
    ∑ j ∈ range (n + 1), scaledBinomialMass n k j = n ^ n := by
  have hbin :
      (k + (n - k)) ^ n =
        ∑ m ∈ range (n + 1),
          k ^ m * (n - k) ^ (n - m) * n.choose m :=
    add_pow k (n - k) n
  rw [Nat.add_sub_of_le hk] at hbin
  rw [hbin]
  apply sum_congr rfl
  intro j hj
  simp only [scaledBinomialMass]
  ac_rfl

/-- Integer form of the binomial-mass-at-the-mean lower bound. -/
theorem pow_le_succ_mul_scaledBinomialMass
    {n k : ℕ} (hk : k ≤ n) :
    n ^ n ≤ (n + 1) * scaledBinomialMass n k k := by
  rw [← sum_scaledBinomialMass n k hk]
  calc
    ∑ j ∈ range (n + 1), scaledBinomialMass n k j
        ≤ ∑ _j ∈ range (n + 1), scaledBinomialMass n k k := by
          apply sum_le_sum
          intro j hj
          exact scaledBinomialMass_le_mode hk (Nat.le_of_lt_succ (mem_range.mp hj))
    _ = (n + 1) * scaledBinomialMass n k k := by simp

/-- Real-valued probability form used in the terminal-pattern comparison. -/
theorem one_div_succ_le_binomial_mass_at_mean
    {n k : ℕ} (hn : 0 < n) (hk : k ≤ n) :
    (1 : ℝ) / (n + 1) ≤
      (n.choose k : ℝ) *
        ((k : ℝ) / n) ^ k *
        (((n - k : ℕ) : ℝ) / n) ^ (n - k) := by
  have hpow : 0 < (n : ℝ) ^ n := by positivity
  have hscaled := pow_le_succ_mul_scaledBinomialMass hk
  have heq :
      (n.choose k : ℝ) *
          ((k : ℝ) / n) ^ k *
          (((n - k : ℕ) : ℝ) / n) ^ (n - k) =
        (scaledBinomialMass n k k : ℝ) / (n : ℝ) ^ n := by
    rw [div_pow, div_pow]
    field_simp [show (n : ℝ) ≠ 0 by positivity]
    unfold scaledBinomialMass
    push_cast
    rw [Nat.cast_sub hk]
    rw [← pow_add, Nat.add_sub_of_le hk]
  rw [heq]
  apply (div_le_div_iff₀
    (show (0 : ℝ) < n + 1 by positivity) hpow).2
  norm_num
  have hscaledR :
      ((n ^ n : ℕ) : ℝ) ≤
        (((n + 1) * scaledBinomialMass n k k : ℕ) : ℝ) := by
    exact_mod_cast hscaled
  norm_num at hscaledR
  simpa [mul_comm] using hscaledR

/-- One term of a binomial expansion with nonnegative parameters summing
to one is at most one. -/
theorem binomial_term_le_one
    {n k : ℕ} {p q : ℝ}
    (hk : k ≤ n) (hp : 0 ≤ p) (hq : 0 ≤ q) (hpq : p + q = 1) :
    (n.choose k : ℝ) * p ^ k * q ^ (n - k) ≤ 1 := by
  have hbin :
      (p + q) ^ n =
        ∑ j ∈ range (n + 1),
          p ^ j * q ^ (n - j) * (n.choose j : ℝ) :=
    add_pow p q n
  have hmem : k ∈ range (n + 1) := mem_range.mpr (Nat.lt_succ_of_le hk)
  calc
    (n.choose k : ℝ) * p ^ k * q ^ (n - k) =
        p ^ k * q ^ (n - k) * (n.choose k : ℝ) := by ring
    _ ≤ ∑ j ∈ range (n + 1),
        p ^ j * q ^ (n - j) * (n.choose j : ℝ) := by
          exact single_le_sum
            (s := range (n + 1))
            (f := fun j => p ^ j * q ^ (n - j) * (n.choose j : ℝ))
            (fun j hj => by positivity) hmem
    _ = (p + q) ^ n := hbin.symm
    _ = 1 := by simp [hpq]

/-- Conditional terminal-pattern comparison in pure binomial form.

Here `n = N-1`, `k = s-1`, `r` separator positions and `D-r`
nonseparator positions have been prescribed. -/
theorem terminal_choose_ratio_le
    {n k D r : ℕ}
    (hn : 0 < n) (hk0 : 0 < k) (hkn : k < n)
    (hrk : r ≤ k) (hrD : r ≤ D)
    (hDr : D - r ≤ n - k) :
    ((n - D).choose (k - r) : ℝ) / (n.choose k : ℝ) ≤
      (n + 1 : ℝ) *
        ((k : ℝ) / n) ^ r *
        (((n - k : ℕ) : ℝ) / n) ^ (D - r) := by
  have hDn : D ≤ n := by omega
  have hres : k - r ≤ n - D := by omega
  let p : ℝ := (k : ℝ) / n
  let q : ℝ := ((n - k : ℕ) : ℝ) / n
  let base : ℝ := p ^ (k - r) * q ^ ((n - D) - (k - r))
  let pat : ℝ := p ^ r * q ^ (D - r)
  have hp : 0 < p := by dsimp [p]; positivity
  have hq : 0 < q := by
    dsimp [q]
    have : 0 < n - k := Nat.sub_pos_of_lt hkn
    positivity
  have hpq : p + q = 1 := by
    dsimp [p, q]
    rw [Nat.cast_sub hkn.le]
    field_simp
  have hbase : 0 < base := by dsimp [base]; positivity
  have hpat : 0 ≤ pat := by dsimp [pat]; positivity
  have hresMass : ((n - D).choose (k - r) : ℝ) * base ≤ 1 := by
    simpa [base, mul_assoc] using
      binomial_term_le_one hres hp.le hq.le hpq
  have hdenMass :
      (1 : ℝ) / (n + 1) ≤
        (n.choose k : ℝ) * p ^ k * q ^ (n - k) := by
    simpa [p, q] using
      one_div_succ_le_binomial_mass_at_mean hn hkn.le
  have hpowP : p ^ k = p ^ (k - r) * p ^ r := by
    rw [← pow_add, Nat.sub_add_cancel hrk]
  have hpowQ :
      q ^ (n - k) =
        q ^ ((n - D) - (k - r)) * q ^ (D - r) := by
    rw [← pow_add]
    congr 1
    omega
  have hdenOne :
      1 ≤ (n + 1 : ℝ) * (n.choose k : ℝ) * base * pat := by
    have h := (div_le_iff₀ (show (0 : ℝ) < n + 1 by positivity)).mp hdenMass
    dsimp [base, pat]
    rw [hpowP, hpowQ] at h
    nlinarith
  have hcross :
      ((n - D).choose (k - r) : ℝ) * base ≤
        ((n + 1 : ℝ) * p ^ r * q ^ (D - r) *
          (n.choose k : ℝ)) * base := by
    calc
      ((n - D).choose (k - r) : ℝ) * base ≤ 1 := hresMass
      _ ≤ (n + 1 : ℝ) * (n.choose k : ℝ) * base * pat := hdenOne
      _ = ((n + 1 : ℝ) * p ^ r * q ^ (D - r) *
          (n.choose k : ℝ)) * base := by
            dsimp [pat]
            ring
  have hnum :
      ((n - D).choose (k - r) : ℝ) ≤
        (n + 1 : ℝ) * p ^ r * q ^ (D - r) *
          (n.choose k : ℝ) := by
    exact (mul_le_mul_right hbase).mp hcross
  have hchoose : 0 < (n.choose k : ℝ) := by
    exact_mod_cast Nat.choose_pos hkn.le
  apply (div_le_iff₀ hchoose).2
  simpa [p, q, mul_assoc] using hnum

end FixedTotal

end CollatzEndpointTransport
/-
Terminal blocks of fixed-total positive compositions.

The central higher-Renyi estimate only needs one structural count: fixing a
terminal block list leaves at most `choose (N-1-D) (s-1-r)` possible
prefixes.  This module proves that count by an explicit injective prefix map.
-/

namespace CollatzEndpointTransport

namespace FixedTotal

open Nat Finset
open scoped NNReal

noncomputable section

local instance terminalCompositionDecidableEq (N : ℕ) :
    DecidableEq (Composition N) :=
  Classical.decEq _

/-- The final `r` blocks of a composition. -/
def terminalBlocks {N : ℕ} (c : Composition N) (r : ℕ) : List ℕ :=
  c.blocks.drop (c.length - r)

/-- The blocks preceding the final `r` blocks. -/
def initialBlocks {N : ℕ} (c : Composition N) (r : ℕ) : List ℕ :=
  c.blocks.take (c.length - r)

/-- Total dyadic spend in the final `r` blocks. -/
def reverseSpend {N : ℕ} (c : Composition N) (r : ℕ) : ℕ :=
  (terminalBlocks c r).sum

/-- A prefix of the reversed block list has exactly the corresponding
terminal spend in the forward block list. -/
theorem sum_take_reverse_eq_reverseSpend
    {N : ℕ} (c : Composition N) (r : ℕ) :
    (c.blocks.reverse.take r).sum = reverseSpend c r := by
  have hrtake := List.rtake_eq_reverse_take_reverse c.blocks r
  have hsum := congrArg List.sum hrtake
  simpa [List.rtake, terminalBlocks, List.sum_reverse] using hsum.symm

theorem initialBlocks_append_terminalBlocks
    {N : ℕ} (c : Composition N) (r : ℕ) :
    initialBlocks c r ++ terminalBlocks c r = c.blocks := by
  exact List.take_append_drop (c.length - r) c.blocks

theorem terminalBlocks_length
    {N : ℕ} (c : Composition N) {r : ℕ} (hr : r ≤ c.length) :
    (terminalBlocks c r).length = r := by
  unfold terminalBlocks
  rw [List.length_drop]
  change r ≤ c.blocks.length at hr
  change c.blocks.length - (c.blocks.length - r) = r
  omega

theorem initialBlocks_length
    {N : ℕ} (c : Composition N) (r : ℕ) :
    (initialBlocks c r).length = c.length - r := by
  unfold initialBlocks
  rw [List.length_take]
  change min (c.blocks.length - r) c.blocks.length = c.blocks.length - r
  exact min_eq_left (Nat.sub_le _ _)

theorem reverseSpend_le
    {N : ℕ} (c : Composition N) (r : ℕ) :
    reverseSpend c r ≤ N := by
  have hsum := List.sum_take_add_sum_drop c.blocks (c.length - r)
  have hle : (c.blocks.drop (c.length - r)).sum ≤ c.blocks.sum := by
    omega
  simpa [reverseSpend, terminalBlocks, c.blocks_sum] using hle

/-- A proper terminal segment has spend strictly below the total. -/
theorem reverseSpend_lt_of_lt_length
    {N : ℕ} (c : Composition N) {r : ℕ} (hr : r < c.length) :
    reverseSpend c r < N := by
  have hlen : 0 < (initialBlocks c r).length := by
    rw [initialBlocks_length]
    omega
  have hone : ∀ i ∈ initialBlocks c r, 1 ≤ i := by
    intro i hi
    exact c.blocks_pos (List.mem_of_mem_take hi)
  have hsumPos : 0 < (initialBlocks c r).sum :=
    hlen.trans_le (List.length_le_sum_of_one_le _ hone)
  have hsum := congrArg List.sum (initialBlocks_append_terminalBlocks c r)
  simp only [List.sum_append, c.blocks_sum] at hsum
  unfold reverseSpend
  omega

theorem terminalBlocks_pos
    {N : ℕ} (c : Composition N) (r : ℕ) :
    ∀ d ∈ terminalBlocks c r, 0 < d := by
  intro d hd
  exact c.blocks_pos (List.mem_of_mem_drop hd)

/-- Prefix composition obtained by removing the final `r` blocks. -/
def initialComposition
    {N : ℕ} (c : Composition N) (r : ℕ) :
    Composition (N - reverseSpend c r) where
  blocks := initialBlocks c r
  blocks_pos := by
    intro i hi
    exact c.blocks_pos (List.mem_of_mem_take hi)
  blocks_sum := by
    have hsum := List.sum_take_add_sum_drop c.blocks (c.length - r)
    rw [c.blocks_sum] at hsum
    unfold initialBlocks reverseSpend terminalBlocks
    omega

@[simp]
theorem initialComposition_length
    {N : ℕ} (c : Composition N) (r : ℕ) :
    (initialComposition c r).length = c.length - r := by
  change (initialBlocks c r).length = c.length - r
  exact initialBlocks_length c r

/-- Fixed-length compositions having the prescribed terminal block list. -/
def terminalFiber (N s r : ℕ) (d : List ℕ) : Finset (Composition N) :=
  (fixedSet N s).filter fun c => terminalBlocks c r = d

theorem mem_terminalFiber_iff
    {N s r : ℕ} {d : List ℕ} {c : Composition N} :
    c ∈ terminalFiber N s r d ↔
      c.length = s ∧ terminalBlocks c r = d := by
  simp [terminalFiber, fixedSet]

/-- Transport a composition across an equality of its total. -/
def castComposition {A B : ℕ} (h : A = B) (c : Composition A) : Composition B :=
  h ▸ c

@[simp]
theorem castComposition_blocks
    {A B : ℕ} (h : A = B) (c : Composition A) :
    (castComposition h c).blocks = c.blocks := by
  subst B
  rfl

@[simp]
theorem castComposition_length
    {A B : ℕ} (h : A = B) (c : Composition A) :
    (castComposition h c).length = c.length := by
  subst B
  rfl

/-- Prefix map from one terminal fiber into the corresponding fixed-total
prefix level. -/
def terminalPrefixMap
    {N s r : ℕ} (d : List ℕ)
    (c : {c : Composition N // c ∈ terminalFiber N s r d}) :
    FixedComposition (N - d.sum) (s - r) := by
  have hc := (mem_terminalFiber_iff.mp c.2)
  have hspend : reverseSpend c.1 r = d.sum := by
    unfold reverseSpend
    rw [hc.2]
  let p : Composition (N - reverseSpend c.1 r) := initialComposition c.1 r
  have htotal : N - reverseSpend c.1 r = N - d.sum := by rw [hspend]
  have hlength : p.length = s - r := by
    simpa [p, hc.1] using initialComposition_length c.1 r
  refine ⟨castComposition htotal p, ?_⟩
  simpa using hlength

theorem terminalPrefixMap_injective
    {N s r : ℕ} (d : List ℕ) :
    Function.Injective (terminalPrefixMap (N := N) (s := s) (r := r) d) := by
  intro c₁ c₂ h
  apply Subtype.ext
  apply Composition.ext
  have hblocks := congrArg (fun p => p.1.blocks) h
  have hc₁ := (mem_terminalFiber_iff.mp c₁.2)
  have hc₂ := (mem_terminalFiber_iff.mp c₂.2)
  have hinit : initialBlocks c₁.1 r = initialBlocks c₂.1 r := by
    simpa [terminalPrefixMap, initialComposition] using hblocks
  calc
    c₁.1.blocks = initialBlocks c₁.1 r ++ terminalBlocks c₁.1 r :=
      (initialBlocks_append_terminalBlocks c₁.1 r).symm
    _ = initialBlocks c₂.1 r ++ terminalBlocks c₂.1 r := by
      rw [hinit, hc₁.2, hc₂.2]
    _ = c₂.1.blocks := initialBlocks_append_terminalBlocks c₂.1 r

/-- A prescribed terminal list leaves at most the number of compatible
fixed-total prefixes. -/
theorem card_terminalFiber_le
    {N s r : ℕ} (d : List ℕ) :
    (terminalFiber N s r d).card ≤
      (fixedSet (N - d.sum) (s - r)).card := by
  have hcard := Fintype.card_le_of_injective
    (terminalPrefixMap (N := N) (s := s) (r := r) d)
    (terminalPrefixMap_injective (N := N) (s := s) (r := r) d)
  have htarget :
      Fintype.card (FixedComposition (N - d.sum) (s - r)) =
        (fixedSet (N - d.sum) (s - r)).card := by
    exact Fintype.card_of_subtype (fixedSet (N - d.sum) (s - r))
      (by intro c; simp [fixedSet])
  rw [htarget] at hcard
  simpa [Fintype.card_coe] using hcard

/-- Stars-and-bars form of the terminal-fiber upper bound. -/
theorem card_terminalFiber_le_choose
    {N s r : ℕ} (d : List ℕ)
    (hprefixTotal : 0 < N - d.sum) (hprefixLength : 0 < s - r) :
    (terminalFiber N s r d).card ≤
      (N - d.sum - 1).choose (s - r - 1) := by
  calc
    (terminalFiber N s r d).card ≤
        (fixedSet (N - d.sum) (s - r)).card := card_terminalFiber_le d
    _ = (N - d.sum - 1).choose (s - r - 1) :=
      card_fixedSet (N - d.sum) (s - r) hprefixTotal hprefixLength

/-- Block lists of fixed-total, fixed-length compositions. -/
def fixedBlockSet (D r : ℕ) : Finset (List ℕ) :=
  (fixedSet D r).image fun c => c.blocks

theorem card_fixedBlockSet (D r : ℕ) :
    (fixedBlockSet D r).card = (fixedSet D r).card := by
  unfold fixedBlockSet
  rw [Finset.card_image_of_injective]
  intro c₁ c₂ h
  apply Composition.ext
  exact h

/-- All terminal block lists occurring at one fixed-total level. -/
def terminalPatternImage (N s r : ℕ) : Finset (List ℕ) :=
  (fixedSet N s).image fun c => terminalBlocks c r

/-- Terminal block lists occurring at level `(N,s)`, restricted to total
spend `D`. -/
def terminalPatternSet (N s r D : ℕ) : Finset (List ℕ) :=
  (terminalPatternImage N s r).filter fun d => d.sum = D

/-- Partition a composition sum by its exact terminal block list. -/
theorem sum_by_terminalBlocks
    {R : Type*} [CommSemiring R]
    {N s r : ℕ} (f : List ℕ → R) :
    (∑ c ∈ fixedSet N s, f (terminalBlocks c r)) =
      ∑ d ∈ terminalPatternImage N s r,
        (terminalFiber N s r d).card * f d := by
  calc
    (∑ c ∈ fixedSet N s, f (terminalBlocks c r)) =
        ∑ d ∈ terminalPatternImage N s r,
          ∑ c ∈ terminalFiber N s r d,
            f (terminalBlocks c r) := by
      symm
      exact Finset.sum_fiberwise_of_maps_to
        (fun c hc => Finset.mem_image.mpr ⟨c, hc, rfl⟩)
        (fun c => f (terminalBlocks c r))
    _ = ∑ d ∈ terminalPatternImage N s r,
        (terminalFiber N s r d).card * f d := by
      apply Finset.sum_congr rfl
      intro d hd
      calc
        (∑ c ∈ terminalFiber N s r d,
            f (terminalBlocks c r)) =
            ∑ _c ∈ terminalFiber N s r d, f d := by
          apply Finset.sum_congr rfl
          intro c hc
          rw [(mem_terminalFiber_iff.mp hc).2]
        _ = (terminalFiber N s r d).card * f d := by simp

/-- Partition terminal patterns by their total reverse spend. -/
theorem sum_terminalPatterns_by_spend
    {R : Type*} [CommSemiring R]
    {N s r : ℕ} (f : ℕ → List ℕ → R) :
    (∑ d ∈ terminalPatternImage N s r, f d.sum d) =
      ∑ D ∈ range (N + 1),
        ∑ d ∈ terminalPatternSet N s r D, f D d := by
  calc
    (∑ d ∈ terminalPatternImage N s r, f d.sum d) =
        ∑ D ∈ range (N + 1),
          ∑ d ∈ terminalPatternSet N s r D, f d.sum d := by
      symm
      simpa [terminalPatternSet] using
        (Finset.sum_fiberwise_of_maps_to
          (s := terminalPatternImage N s r)
          (t := range (N + 1))
          (g := fun d : List ℕ => d.sum)
          (fun d hd => by
            rcases Finset.mem_image.mp hd with ⟨c, hc, rfl⟩
            apply Finset.mem_range.mpr
            exact Nat.lt_succ_of_le (reverseSpend_le (N := N) c r))
          (fun d : List ℕ => f d.sum d))
    _ = ∑ D ∈ range (N + 1),
        ∑ d ∈ terminalPatternSet N s r D, f D d := by
      apply Finset.sum_congr rfl
      intro D hD
      apply Finset.sum_congr rfl
      intro d hd
      rw [(Finset.mem_filter.mp hd).2]

theorem terminalPatternSet_subset_fixedBlockSet
    {N s r D : ℕ} (hr : r ≤ s) :
    terminalPatternSet N s r D ⊆ fixedBlockSet D r := by
  intro d hd
  rcases Finset.mem_filter.mp hd with ⟨hdImage, hdSum⟩
  rcases Finset.mem_image.mp hdImage with ⟨c, hc, rfl⟩
  have hcLength : c.length = s := (Finset.mem_filter.mp hc).2
  let suffix : Composition D := {
    blocks := terminalBlocks c r
    blocks_pos := by
      intro x hx
      exact terminalBlocks_pos c r x hx
    blocks_sum := hdSum
  }
  apply Finset.mem_image.mpr
  refine ⟨suffix, ?_, ?_⟩
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  change (terminalBlocks c r).length = r
  exact terminalBlocks_length c (by simpa [hcLength] using hr)
  · rfl

theorem card_terminalPatternSet_le
    {N s r D : ℕ} (hr : r ≤ s) :
    (terminalPatternSet N s r D).card ≤ (fixedSet D r).card := by
  calc
    (terminalPatternSet N s r D).card ≤ (fixedBlockSet D r).card :=
      Finset.card_le_card (terminalPatternSet_subset_fixedBlockSet hr)
    _ = (fixedSet D r).card := card_fixedBlockSet D r

theorem card_terminalPatternSet_le_choose
    {N s r D : ℕ} (hr : r ≤ s) (hD : 0 < D) (hr0 : 0 < r) :
    (terminalPatternSet N s r D).card ≤ (D - 1).choose (r - 1) := by
  calc
    (terminalPatternSet N s r D).card ≤ (fixedSet D r).card :=
      card_terminalPatternSet_le hr
    _ = (D - 1).choose (r - 1) := card_fixedSet D r hD hr0

theorem terminalPatternSet_spend_pos
    {N s r D : ℕ} (hr0 : 0 < r) (hrs : r ≤ s)
    {d : List ℕ} (hd : d ∈ terminalPatternSet N s r D) :
    0 < D := by
  rcases Finset.mem_filter.mp hd with ⟨hdImage, hdSum⟩
  rcases Finset.mem_image.mp hdImage with ⟨c, hc, hdc⟩
  have hcLength : c.length = s := (Finset.mem_filter.mp hc).2
  have hdLength : d.length = r := by
    rw [← hdc]
    exact terminalBlocks_length c (by simpa [hcLength] using hrs)
  have hdPos : ∀ i ∈ d, 1 ≤ i := by
    intro i hi
    rw [← hdc] at hi
    exact terminalBlocks_pos c r i hi
  have hlenSum := List.length_le_sum_of_one_le d hdPos
  rw [hdLength, hdSum] at hlenSum
  omega

theorem terminalPatternSet_spend_lt
    {N s r D : ℕ} (hrs : r < s)
    {d : List ℕ} (hd : d ∈ terminalPatternSet N s r D) :
    D < N := by
  rcases Finset.mem_filter.mp hd with ⟨hdImage, hdSum⟩
  rcases Finset.mem_image.mp hdImage with ⟨c, hc, hdc⟩
  have hcLength : c.length = s := (Finset.mem_filter.mp hc).2
  have hspend : reverseSpend c r = D := by
    unfold reverseSpend
    rw [hdc, hdSum]
  rw [← hspend]
  exact reverseSpend_lt_of_lt_length c (by omega)

/-- Positivity of the terminal blocks and of the remaining prefix gives
the two stars-and-bars spend bounds. -/
theorem terminalPatternSet_spend_bounds
    {N s r D : ℕ} (hrs : r ≤ s)
    {d : List ℕ} (hd : d ∈ terminalPatternSet N s r D) :
    r ≤ D ∧ s - r ≤ N - D := by
  rcases Finset.mem_filter.mp hd with ⟨hdImage, hdSum⟩
  rcases Finset.mem_image.mp hdImage with ⟨c, hc, hdc⟩
  have hcLength : c.length = s := (Finset.mem_filter.mp hc).2
  have hdLength : d.length = r := by
    rw [← hdc]
    exact terminalBlocks_length c (by simpa [hcLength] using hrs)
  have hdPos : ∀ i ∈ d, 1 ≤ i := by
    intro i hi
    rw [← hdc] at hi
    exact terminalBlocks_pos c r i hi
  have hterminal := List.length_le_sum_of_one_le d hdPos
  have hinitialPos : ∀ i ∈ initialBlocks c r, 1 ≤ i := by
    intro i hi
    exact c.blocks_pos (List.mem_of_mem_take hi)
  have hinitial :=
    List.length_le_sum_of_one_le (initialBlocks c r) hinitialPos
  have hsum := congrArg List.sum (initialBlocks_append_terminalBlocks c r)
  simp only [List.sum_append, c.blocks_sum] at hsum
  rw [initialBlocks_length, hcLength] at hinitial
  rw [hdLength, hdSum] at hterminal
  rw [hdc, hdSum] at hsum
  omega

theorem terminalPatternSet_eq_empty_of_spend_lt
    {N s r D : ℕ} (hrs : r ≤ s) (hDr : D < r) :
    terminalPatternSet N s r D = ∅ := by
  apply Finset.eq_empty_iff_forall_not_mem.mpr
  intro d hd
  have hbounds := terminalPatternSet_spend_bounds hrs hd
  omega

end

end FixedTotal

end CollatzEndpointTransport
