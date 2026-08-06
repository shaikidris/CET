/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik
-/
import CollatzEndpointTransport.Common.TerrasMaximalInitialWindow
import CollatzEndpointTransport.Common.TerrasInitialWindowDensity

/-!
# Terras Maximal Initial Window Density

Quadratic-density form of the strengthened initial logarithmic window.
-/

namespace CollatzEndpointTransport

namespace Terras

open Nat Finset
open scoped Real

noncomputable section

def quadraticWindowShellConstant : ℝ :=
  2 * Real.exp (4 * maximalBarrierC0)

theorem quadraticWindowShellConstant_pos :
    0 < quadraticWindowShellConstant := by
  unfold quadraticWindowShellConstant
  positivity

theorem maximalBarrierC0_lt_log_two :
    maximalBarrierC0 < Real.log 2 := by
  have hlg : 1 < QuantitativeDensity.lg3 := lg3_one_lt
  have hc : maximalBarrierC0 < 1 / 2 := by
    unfold maximalBarrierC0
    have hsq : 1 < QuantitativeDensity.lg3 ^ 2 := by nlinarith
    rw [div_lt_iff₀ (by positivity)]
    nlinarith
  nlinarith [Real.log_two_gt_d9]

theorem shellInitialWindowBad_subset_maximal
    {M : ℕ} {t : ℝ}
    (ht : 0 < t) (hM : 4 ≤ M) (hstart : 2 ≤ t * M) :
    shellInitialWindowBad M t ⊆
      shellMaximalParityBad M (maximalBarrierHeight t M) := by
  classical
  intro n hn
  rw [shellInitialWindowBad, Finset.mem_filter] at hn
  rw [shellMaximalParityBad, Finset.mem_filter]
  refine ⟨hn.1, ?_⟩
  intro hreg
  rcases hn.2 with ⟨k, hkM, hfail⟩
  have henv :=
    orbit_envelope_of_maximalBarrier ht hM hstart hkM hn.1 hreg
  rcases hfail with hlower | hupper
  · exact (not_lt_of_ge henv.1) hlower
  · exact (not_lt_of_ge henv.2) hupper

theorem quadratic_startup_exponent_le
    {M : ℕ} {t : ℝ}
    (ht0 : 0 < t) (ht1 : t ≤ 1)
    (hsmall : ¬(4 ≤ M ∧ 2 ≤ t * M)) :
    maximalBarrierC0 * t ^ 2 * M ≤ 4 * maximalBarrierC0 := by
  have hc := maximalBarrierC0_pos.le
  rcases not_and_or.mp hsmall with hM | htM
  · have hMR : (M : ℝ) ≤ 4 := by
      exact_mod_cast (by omega : M ≤ 4)
    have ht2 : t ^ 2 ≤ (1 : ℝ) := by nlinarith [sq_nonneg t]
    have hprod : t ^ 2 * (M : ℝ) ≤ 1 * 4 :=
      mul_le_mul ht2 hMR (Nat.cast_nonneg M) (by norm_num)
    nlinarith
  · have htMR : t * (M : ℝ) ≤ 2 := le_of_not_ge htM
    have hprod :
        t * (t * (M : ℝ)) ≤ 1 * 2 :=
      mul_le_mul ht1 htMR (mul_nonneg ht0.le (Nat.cast_nonneg M))
        (by norm_num)
    nlinarith

theorem one_le_quadratic_startup_factor
    {M : ℕ} {t : ℝ}
    (ht0 : 0 < t) (ht1 : t ≤ 1)
    (hsmall : ¬(4 ≤ M ∧ 2 ≤ t * M)) :
    1 ≤ quadraticWindowShellConstant *
      Real.exp (-(maximalBarrierC0 * t ^ 2 * M)) := by
  have hexp := quadratic_startup_exponent_le ht0 ht1 hsmall
  have hnonneg :
      0 ≤ 4 * maximalBarrierC0 -
        maximalBarrierC0 * t ^ 2 * (M : ℝ) := by linarith
  unfold quadraticWindowShellConstant
  have hone :
      1 ≤ Real.exp
        (4 * maximalBarrierC0 -
          maximalBarrierC0 * t ^ 2 * (M : ℝ)) :=
    Real.one_le_exp hnonneg
  calc
    1 ≤ 2 * Real.exp
        (4 * maximalBarrierC0 -
          maximalBarrierC0 * t ^ 2 * (M : ℝ)) := by nlinarith
    _ = 2 * Real.exp (4 * maximalBarrierC0) *
        Real.exp (-(maximalBarrierC0 * t ^ 2 * (M : ℝ))) := by
      rw [show
        4 * maximalBarrierC0 -
            maximalBarrierC0 * t ^ 2 * (M : ℝ) =
          4 * maximalBarrierC0 +
            (-(maximalBarrierC0 * t ^ 2 * (M : ℝ))) by ring,
        Real.exp_add]
      ring

/-- All-shell quadratic exceptional count. The startup shells are absorbed
into one absolute constant; no inverse power of `t` appears. -/
theorem card_shellInitialWindowBad_le_quadratic
    {M : ℕ} {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) :
    ((shellInitialWindowBad M t).card : ℝ) ≤
      quadraticWindowShellConstant *
        Real.exp (-(maximalBarrierC0 * t ^ 2 * M)) *
        (2 : ℝ) ^ M := by
  classical
  by_cases hlarge : 4 ≤ M ∧ 2 ≤ t * M
  · have hsubset :=
      shellInitialWindowBad_subset_maximal ht0 hlarge.1 hlarge.2
    have hcard :
        (shellInitialWindowBad M t).card ≤
          (shellMaximalParityBad M (maximalBarrierHeight t M)).card :=
      Finset.card_le_card hsubset
    have hcardR :
        ((shellInitialWindowBad M t).card : ℝ) ≤
          ((shellMaximalParityBad M
            (maximalBarrierHeight t M)).card : ℝ) := by exact_mod_cast hcard
    have htail :=
      card_shellMaximalParityBad_le_concrete (M := M) (t := t) ht0.le
    calc
      ((shellInitialWindowBad M t).card : ℝ)
          ≤ ((shellMaximalParityBad M
            (maximalBarrierHeight t M)).card : ℝ) := hcardR
      _ ≤ 2 * Real.exp (-(maximalBarrierC0 * t ^ 2 * M)) *
          (2 : ℝ) ^ M := htail
      _ ≤ quadraticWindowShellConstant *
          Real.exp (-(maximalBarrierC0 * t ^ 2 * M)) *
          (2 : ℝ) ^ M := by
        have hK : (2 : ℝ) ≤ quadraticWindowShellConstant := by
          unfold quadraticWindowShellConstant
          have := Real.one_le_exp
            (mul_nonneg (show (0 : ℝ) ≤ 4 by norm_num)
              maximalBarrierC0_pos.le)
          nlinarith
        gcongr
  · have hcard :
        (shellInitialWindowBad M t).card ≤
          (Finset.Ico (2 ^ M) (2 ^ (M + 1))).card := by
      apply Finset.card_le_card
      intro n hn
      rw [shellInitialWindowBad, Finset.mem_filter] at hn
      exact hn.1
    have hcardR :
        ((shellInitialWindowBad M t).card : ℝ) ≤ (2 : ℝ) ^ M := by
      have hshellCard :
          (Finset.Ico (2 ^ M) (2 ^ (M + 1))).card = 2 ^ M := by
        rw [Nat.card_Ico, pow_succ]
        omega
      rw [hshellCard] at hcard
      exact_mod_cast hcard
    have hfactor := one_le_quadratic_startup_factor ht0 ht1 hlarge
    calc
      ((shellInitialWindowBad M t).card : ℝ) ≤ (2 : ℝ) ^ M := hcardR
      _ = 1 * (2 : ℝ) ^ M := by ring
      _ ≤ (quadraticWindowShellConstant *
          Real.exp (-(maximalBarrierC0 * t ^ 2 * M))) *
          (2 : ℝ) ^ M :=
        mul_le_mul_of_nonneg_right hfactor (by positivity)
      _ = _ := by ring

def quadraticWindowDensityRate (t : ℝ) : ℝ :=
  maximalBarrierC0 * t ^ 2 / Real.log 2

def quadraticWindowGlobalConstant (t : ℝ) : ℝ :=
  2 * quadraticWindowShellConstant /
    (2 * Real.exp (-(maximalBarrierC0 * t ^ 2)) - 1)

def quadraticWindowFixedGlobalConstant : ℝ :=
  2 * quadraticWindowShellConstant /
    (2 * Real.exp (-maximalBarrierC0) - 1)

/-- The existing global orbit-envelope set now has a quadratic density
exponent and an absolute shell prefactor. -/
theorem initialWindowGood_dense_quadratic
    {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) :
    QuantitativeDensity.IsCDDense (initialWindowGood t)
      (quadraticWindowGlobalConstant t)
      (quadraticWindowDensityRate t) := by
  have hc : 0 < maximalBarrierC0 * t ^ 2 :=
    mul_pos maximalBarrierC0_pos (sq_pos_of_pos ht0)
  have hclt : maximalBarrierC0 * t ^ 2 < Real.log 2 := by
    have ht2 : t ^ 2 ≤ 1 := by nlinarith [sq_nonneg t]
    have hle :
        maximalBarrierC0 * t ^ 2 ≤ maximalBarrierC0 :=
      mul_le_of_le_one_right maximalBarrierC0_pos.le ht2
    exact hle.trans_lt maximalBarrierC0_lt_log_two
  unfold quadraticWindowGlobalConstant quadraticWindowDensityRate
  apply QuantitativeDensity.isCDDense_of_shell_bound
    quadraticWindowShellConstant_pos hc hclt
  intro M
  rw [shellBad_initialWindowGood]
  simpa [mul_assoc] using
    (card_shellInitialWindowBad_le_quadratic (M := M) ht0 ht1)

/-- Uniform-constant form of MB3. The denominator is minimized at `t = 1`,
so the density prefactor can be chosen independently of the tolerance. -/
theorem initialWindowGood_dense_quadratic_fixed
    {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) :
    QuantitativeDensity.IsCDDense (initialWindowGood t)
      quadraticWindowFixedGlobalConstant
      (quadraticWindowDensityRate t) := by
  have hExact := initialWindowGood_dense_quadratic ht0 ht1
  apply hExact.mono_constant
  have ht2 : t ^ 2 ≤ 1 := by
    nlinarith [sq_nonneg t]
  have hrateLe :
      maximalBarrierC0 * t ^ 2 ≤ maximalBarrierC0 :=
    mul_le_of_le_one_right maximalBarrierC0_pos.le ht2
  have hhalf : (1 : ℝ) / 2 < Real.exp (-maximalBarrierC0) := by
    have hExpLog : Real.exp (-Real.log 2) = (1 : ℝ) / 2 := by
      rw [Real.exp_neg, Real.exp_log (by norm_num)]
      norm_num
    rw [← hExpLog]
    exact Real.exp_lt_exp.2 (by linarith [maximalBarrierC0_lt_log_two])
  have hdenFixed :
      0 < 2 * Real.exp (-maximalBarrierC0) - 1 := by
    linarith
  have hdenLe :
      2 * Real.exp (-maximalBarrierC0) - 1 ≤
        2 * Real.exp (-(maximalBarrierC0 * t ^ 2)) - 1 := by
    have hExp :
        Real.exp (-maximalBarrierC0) ≤
          Real.exp (-(maximalBarrierC0 * t ^ 2)) :=
      Real.exp_le_exp.2 (neg_le_neg hrateLe)
    linarith
  have hnum : 0 ≤ 2 * quadraticWindowShellConstant :=
    mul_nonneg (by norm_num) quadraticWindowShellConstant_pos.le
  unfold quadraticWindowGlobalConstant quadraticWindowFixedGlobalConstant
  exact div_le_div_of_nonneg_left hnum hdenFixed hdenLe

end

end Terras

end CollatzEndpointTransport
