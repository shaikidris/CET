/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik
-/
import CollatzEndpointTransport.QuadraticAppendix.QuantitativeQuadraticTheoremB

/-!
# Quantitative Quadratic Stopping Time

Lower-envelope survival corollary for the quadratic Collatz theorem.

The development deliberately avoids defining a finite total stopping time
for every integer.  Instead it proves the stronger assumption-free relation:
on the scheduled good set, no iterate through an explicit horizon equals
`1`.  Any first hitting time of `1`, if one exists, must therefore be later.
-/

namespace CollatzEndpointTransport

namespace QuantitativeDensity

open scoped Real Topology

noncomputable section

/-- The part of an envelope horizon for which the lower envelope remains
strictly above `1`. -/
def envelopeSurvivalHorizon (lambda t : ℝ) (n : ℕ) : ℕ :=
  ⌊(1 - lambda - t) * (Nat.log 2 n : ℝ) / bConst⌋₊

/-- The public Theorem-B survival horizon.  It depends only on the displayed
shell exponent, not on the internal choices of `q`, `s`, or stage count. -/
def theoremBSurvivalHorizon (a : ℝ) (n : ℕ) : ℕ :=
  ⌊(1 - theoremBShellExponent a (Nat.log 2 n)) *
      (Nat.log 2 n : ℝ) / bConst⌋₊

/-- The exact lower-envelope survival event used by the public corollary. -/
def quantitativeSurvivalSet (a : ℝ) : Set ℕ :=
  {n | ∀ k : ℕ, k ≤ theoremBSurvivalHorizon a n →
    (1 : ℝ) < (((Terras.T^[k]) n : ℕ) : ℝ)}

/-- Membership in the lower envelope keeps every iterate through the
survival horizon strictly above `1`. -/
theorem one_lt_iterate_of_le_envelopeSurvivalHorizon
    {n M k : ℕ} {lambda t : ℝ}
    (hn : 0 < n) (hM : M = Nat.log 2 n) (hM0 : 0 < M)
    (hlambda : 0 < lambda) (ht0 : 0 ≤ t)
    (hsum : lambda + t < 1)
    (hgood : n ∈ EnvelopeGood lambda t)
    (hk : k ≤ envelopeSurvivalHorizon lambda t n) :
    (1 : ℝ) < (((Terras.T^[k]) n : ℕ) : ℝ) := by
  have hb := bConst_pos
  have hbne : bConst ≠ 0 := ne_of_gt hb
  have ht1 : t < 1 := by linarith
  have harg0 :
      0 ≤ (1 - lambda - t) * (M : ℝ) / bConst := by
    exact div_nonneg
      (mul_nonneg (by linarith) (Nat.cast_nonneg M)) hb.le
  have hkReal :
      (k : ℝ) ≤ (1 - lambda - t) * (M : ℝ) / bConst := by
    have hkFloor :
        (k : ℝ) ≤ (envelopeSurvivalHorizon lambda t n : ℝ) := by
      exact_mod_cast hk
    have hfloor :
        (envelopeSurvivalHorizon lambda t n : ℝ) ≤
          (1 - lambda - t) * (M : ℝ) / bConst := by
      subst M
      unfold envelopeSurvivalHorizon
      exact Nat.floor_le harg0
    exact hkFloor.trans hfloor
  have hkEnvelope :
      k ≤ envelopeHorizon lambda n := by
    apply hk.trans
    unfold envelopeSurvivalHorizon envelopeHorizon
    apply Nat.floor_mono
    apply div_le_div_of_nonneg_right _ hb.le
    have hMR : 0 ≤ (Nat.log 2 n : ℝ) := Nat.cast_nonneg _
    nlinarith
  have hlower :=
    (mem_EnvelopeGood.mp hgood k hkEnvelope).1
  have hscaleExp :
      -(1 - lambda - t) * (M : ℝ) ≤
        -bConst * (k : ℝ) := by
    have hmul :=
      mul_le_mul_of_nonneg_left hkReal hb.le
    field_simp [hbne] at hmul
    nlinarith
  have hscale :
      (2 : ℝ) ^ (-(1 - lambda - t) * (M : ℝ)) ≤
        Terras.centralOrbitScale k := by
    rw [Terras.centralOrbitScale_eq_two_rpow_neg_b]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hscaleExp
  have hnLowerNat : 2 ^ M ≤ n := by
    subst M
    exact Nat.pow_log_le_self 2 hn.ne'
  have hnLower : (2 : ℝ) ^ M ≤ (n : ℝ) := by
    exact_mod_cast hnLowerNat
  have hnPow :
      ((2 : ℝ) ^ M) ^ (1 - t) ≤ (n : ℝ) ^ (1 - t) :=
    Real.rpow_le_rpow (by positivity) hnLower (by linarith)
  have hmodel :
      (2 : ℝ) ^ ((lambda : ℝ) * M) ≤
        Terras.centralOrbitScale k * (n : ℝ) ^ (1 - t) := by
    calc
      (2 : ℝ) ^ ((lambda : ℝ) * M)
          = (2 : ℝ) ^ (-(1 - lambda - t) * (M : ℝ)) *
              ((2 : ℝ) ^ M) ^ (1 - t) := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num),
              ← Real.rpow_add (by norm_num)]
            congr 1
            push_cast
            ring
      _ ≤ Terras.centralOrbitScale k * (n : ℝ) ^ (1 - t) :=
        mul_le_mul hscale hnPow
          (Real.rpow_nonneg (by positivity) _)
          (Terras.centralOrbitScale_pos k).le
  have hpowOne :
      (1 : ℝ) < (2 : ℝ) ^ ((lambda : ℝ) * M) :=
    Real.one_lt_rpow (by norm_num) (mul_pos hlambda (by exact_mod_cast hM0))
  exact hpowOne.trans_le (hmodel.trans hlower)

/-- The shell budget leaves the public survival horizon inside the exact
lower-envelope horizon. -/
theorem theoremBSurvivalHorizon_le_envelopeSurvivalHorizon
    {q s a : ℝ} {n M : ℕ}
    (hM : M = Nat.log 2 n) (hM0 : 0 < M)
    (ht0 : 0 ≤ theoremBShellTolerance q s M)
    (hbudget : theoremBShellBudget q s a M) :
    theoremBSurvivalHorizon a n ≤
      envelopeSurvivalHorizon
        (theoremBShellLambda q s M)
        (theoremBShellTolerance q s M) n := by
  have hb := bConst_pos
  have hMreal : 0 < (M : ℝ) := by exact_mod_cast hM0
  have hstrict :
      theoremBShellLambda q s M + theoremBShellTolerance q s M <
        theoremBShellExponent a M := by
    unfold theoremBShellBudget at hbudget
    have hpositive : 0 < bConst + 1 + theoremBShellTolerance q s M := by
      linarith [bConst_pos]
    nlinarith
  subst M
  unfold theoremBSurvivalHorizon envelopeSurvivalHorizon
  apply Nat.floor_mono
  apply div_le_div_of_nonneg_right _ hb.le
  exact mul_le_mul_of_nonneg_right (by linarith)
    (Nat.cast_nonneg (Nat.log 2 n))

/-- The generated Theorem-B set has no hit of `1` through the public
survival horizon. -/
theorem theoremBSet_subset_survival
    {q s a : ℝ}
    (hq0 : 0 < q) (hqa : a0 < q) (hq1 : q < 1)
    (ha0 : 0 < a) :
    theoremBSet q s a ⊆ quantitativeSurvivalSet a := by
  intro n hn
  obtain ⟨hbudget, hM4, hgood⟩ := mem_theoremBSet_data hn
  let M := Nat.log 2 n
  have hn0 : 0 < n := by
    by_contra hn
    have hnz : n = 0 := Nat.eq_zero_of_not_pos hn
    subst n
    simp [M] at hM4
  have hM0 : 0 < M := by omega
  have hlambda :
      0 < theoremBShellLambda q s M :=
    theoremBShellLambda_pos hq0 s M
  have ht0 :
      0 ≤ theoremBShellTolerance q s M :=
    (theoremBShellTolerance_pos hq0 hqa s M).le
  have hsum :
      theoremBShellLambda q s M +
          theoremBShellTolerance q s M < 1 := by
    have hstrict :
        theoremBShellLambda q s M +
            theoremBShellTolerance q s M <
          theoremBShellExponent a M := by
      unfold theoremBShellBudget at hbudget
      have hpositive :
          0 < bConst + 1 + theoremBShellTolerance q s M := by
        linarith [bConst_pos]
      have hMreal : 0 < (M : ℝ) := by exact_mod_cast hM0
      nlinarith
    have hlogEight : 1 < Real.log 8 := by
      have hlogTwo := Real.log_two_gt_d9
      rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
      norm_num
      nlinarith
    have hfinalOne : 1 < finalShellLog M := by
      unfold finalShellLog
      apply hlogEight.trans_le
      apply Real.strictMonoOn_log.monotoneOn
        (Set.mem_Ioi.mpr (by norm_num : (0 : ℝ) < 8))
        (Set.mem_Ioi.mpr (by positivity : 0 < (M : ℝ) + 4))
      exact_mod_cast (by omega : 8 ≤ M + 4)
    have hepsOne :
        theoremBShellExponent a M < 1 := by
      unfold theoremBShellExponent
      exact Real.rpow_lt_one_of_one_lt_of_neg hfinalOne (neg_neg_of_pos ha0)
    exact hstrict.trans hepsOne
  have hgood' :
      n ∈ EnvelopeGood
        (theoremBShellLambda q s M)
        (theoremBShellTolerance q s M) := by
    simpa [explicitShellEnvelope, theoremBShellLambda,
      theoremBShellTolerance, M, stageTolerance] using hgood
  intro k hk
  apply one_lt_iterate_of_le_envelopeSurvivalHorizon
    hn0 rfl hM0 hlambda ht0 hsum hgood'
  exact hk.trans
    (theoremBSurvivalHorizon_le_envelopeSurvivalHorizon
      rfl hM0 ht0 hbudget)

/-- The survival event has natural density one for every admissible
Theorem-B exponent. -/
theorem quantitativeQuadraticSurvival
    {a : ℝ} (ha0 : 0 < a)
    (ha : a < quadraticHeadlineExponent) :
    HasNaturalDensityOne
      {n | ∀ k : ℕ, k ≤ theoremBSurvivalHorizon a n →
        (1 : ℝ) < (((Terras.T^[k]) n : ℕ) : ℝ)} := by
  let q := theoremBChoiceQ a
  let s := theoremBChoiceS a q
  have hq := theoremBChoiceQ_properties ha0 ha
  have hs := theoremBChoiceS_properties ha0 hq.1 hq.2.2.1 hq.2.2.2
  apply hasNaturalDensityOne_mono
    (theoremBSet_subset_survival hq.1 hq.2.1 hq.2.2.1 ha0)
  exact theoremBSet_hasNaturalDensityOne
    hq.1 hq.2.1 hq.2.2.1 hs.1 hs.2.2 hs.2.1

/-- Any actual hit of `1` occurs after the certified survival horizon.  This
relational form is meaningful whether or not the orbit eventually hits `1`. -/
theorem one_hitting_time_gt_theoremBSurvivalHorizon
    {a : ℝ} {n tau : ℕ}
    (hn : n ∈ quantitativeSurvivalSet a)
    (htau : (Terras.T^[tau]) n = 1) :
    theoremBSurvivalHorizon a n < tau := by
  by_contra h
  have hle : tau ≤ theoremBSurvivalHorizon a n := Nat.le_of_not_gt h
  have hsurvive := hn tau hle
  simpa [htau] using hsurvive

end

end QuantitativeDensity

end CollatzEndpointTransport
