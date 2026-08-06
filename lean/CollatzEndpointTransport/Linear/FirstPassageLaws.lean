/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik
-/
import CollatzEndpointTransport.Linear.OptimizedLinearDescentAssembly
import CollatzEndpointTransport.Linear.OptimizedLinearParameterChoice
import CollatzEndpointTransport.Common.QuantitativeCollatzDefs

/-!
# Uniform quantitative first-passage profile

First-passage times for the literal half-Collatz map and the abstract
two-sided envelope bounds behind the uniform profile.

The first-passage time `collatzFirstPassage B n` is the least `k` with
`collatzIter k n ≤ B`, totalized as `0` when no such iterate exists.  On the
density-one envelope sets used below the defining set is nonempty, so
the totalization is invisible there.

The two envelope lemmas give the pointwise first-passage bounds: inside
`EnvelopeGood lambda t`, every iterate strictly below the
critical real time `((1 - t) log n - log B) / (bConst * log 2)` stays above
`B`, while the ceiling of `((1 + t) log n - log B) / (bConst * log 2)` is a
genuine descent witness whenever it lies within the envelope horizon. The
pointwise profile theorem makes the error uniform in the target exponent.
The final theorem assembles its two asymptotic specializations on one common
density-one set.
-/

namespace CollatzEndpointTransport

namespace QuantitativeCollatzMain

open scoped Real Topology

open QuantitativeDensity

noncomputable section

/-- The first-passage time of the literal half-Collatz orbit below the real
threshold `B`: the least `k` with `collatzIter k n ≤ B`, totalized as `0`
when the orbit never dips below `B`. -/
def collatzFirstPassage (B : ℝ) (n : ℕ) : ℕ := by
  classical
  exact if h : ∃ k : ℕ, (collatzIter k n : ℝ) ≤ B then Nat.find h else 0

theorem collatzFirstPassage_eq_find {B : ℝ} {n : ℕ}
    (h : ∃ k : ℕ, (collatzIter k n : ℝ) ≤ B) :
    collatzFirstPassage B n = Nat.find h := by
  classical
  unfold collatzFirstPassage
  rw [dif_pos h]

/-- The first-passage time is attained whenever the defining set is
nonempty. -/
theorem collatzFirstPassage_spec {B : ℝ} {n : ℕ}
    (h : ∃ k : ℕ, (collatzIter k n : ℝ) ≤ B) :
    (collatzIter (collatzFirstPassage B n) n : ℝ) ≤ B := by
  classical
  rw [collatzFirstPassage_eq_find h]
  exact Nat.find_spec h

/-- Any iterate below `B` majorizes the first-passage time. -/
theorem collatzFirstPassage_le_of_exists {B : ℝ} {n k : ℕ}
    (hk : (collatzIter k n : ℝ) ≤ B) :
    collatzFirstPassage B n ≤ k := by
  classical
  rw [collatzFirstPassage_eq_find ⟨k, hk⟩]
  exact Nat.find_min' ⟨k, hk⟩ hk

/-- **Upper first-passage bound from the two-sided envelope.**  If `n` lies in
`EnvelopeGood lambda t` and the candidate time
`⌈((1 + t) log n − log B)/(bConst · log 2)⌉₊` is within the envelope
horizon, then that iterate is already at most `B`.  This is the upper branch
of (17.9). -/
theorem exists_iterate_le_of_mem_EnvelopeGood
    {lambda t B : ℝ} {n : ℕ}
    (hn : n ∈ EnvelopeGood lambda t)
    (hn0 : 0 < n) (hB : 0 < B)
    (hkH : ⌈(((1 + t) * Real.log n - Real.log B) /
        (bConst * Real.log 2))⌉₊ ≤ envelopeHorizon lambda n) :
    (collatzIter (⌈(((1 + t) * Real.log n - Real.log B) /
        (bConst * Real.log 2))⌉₊) n : ℝ) ≤ B := by
  classical
  set k := ⌈(((1 + t) * Real.log n - Real.log B) /
      (bConst * Real.log 2))⌉₊ with hk
  obtain ⟨-, hupper⟩ := (mem_EnvelopeGood.mp hn) k hkH
  have hb : 0 < bConst * Real.log 2 :=
    mul_pos bConst_pos (Real.log_pos (by norm_num))
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  have hkX : (((1 + t) * Real.log n - Real.log B) /
      (bConst * Real.log 2)) ≤ (k : ℝ) := Nat.le_ceil _
  have hkey : (bConst * Real.log 2) * (k : ℝ) ≥
      (1 + t) * Real.log n - Real.log B := by
    have hmul := mul_le_mul_of_nonneg_left hkX hb.le
    rwa [mul_div_cancel₀ _ hb.ne'] at hmul
  have hscale : Terras.centralOrbitScale k * (n : ℝ) ^ (1 + t) ≤ B := by
    rw [Terras.centralOrbitScale_eq_two_rpow_neg_b,
      Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2),
      Real.rpow_def_of_pos hnR, ← Real.exp_add, ← Real.exp_log hB]
    apply Real.exp_le_exp.mpr
    have hlin : Real.log 2 * (-bConst * (k : ℝ)) +
        Real.log n * (1 + t) ≤ Real.log B := by
      have hre : Real.log 2 * (-bConst * (k : ℝ)) =
          -((bConst * Real.log 2) * (k : ℝ)) := by ring
      rw [hre]
      linarith [hkey]
    exact hlin
  calc (collatzIter k n : ℝ)
      = ((Terras.T^[k]) n : ℝ) := by rw [collatzIter_eq_terras]
    _ ≤ Terras.centralOrbitScale k * (n : ℝ) ^ (1 + t) := hupper
    _ ≤ B := hscale

/-- **Lower first-passage bound from the two-sided envelope.**  Strictly
below the critical real time
`((1 − t) log n − log B)/(bConst · log 2)` and within the envelope horizon,
no iterate is at most `B`.  This is the lower branch of (17.9). -/
theorem not_le_of_mem_EnvelopeGood_of_lt
    {lambda t B : ℝ} {n m : ℕ}
    (hn : n ∈ EnvelopeGood lambda t)
    (hn0 : 0 < n) (hB : 0 < B)
    (hmH : m ≤ envelopeHorizon lambda n)
    (hm : (m : ℝ) < (((1 - t) * Real.log n - Real.log B) /
      (bConst * Real.log 2))) :
    ¬ (collatzIter m n : ℝ) ≤ B := by
  classical
  intro hmle
  obtain ⟨hlow, -⟩ := (mem_EnvelopeGood.mp hn) m hmH
  have hb : 0 < bConst * Real.log 2 :=
    mul_pos bConst_pos (Real.log_pos (by norm_num))
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  have hm' : (bConst * Real.log 2) * (m : ℝ) <
      (1 - t) * Real.log n - Real.log B := by
    have hmul := mul_lt_mul_of_pos_left hm hb
    rwa [mul_div_cancel₀ _ hb.ne'] at hmul
  have hgt : B < Terras.centralOrbitScale m * (n : ℝ) ^ (1 - t) := by
    rw [← Real.exp_log hB, Terras.centralOrbitScale_eq_two_rpow_neg_b,
      Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2),
      Real.rpow_def_of_pos hnR, ← Real.exp_add]
    apply Real.exp_lt_exp.mpr
    have hre : Real.log 2 * (-bConst * (m : ℝ)) =
        -((bConst * Real.log 2) * (m : ℝ)) := by ring
    rw [hre]
    linarith [hm']
  have hiter : (collatzIter m n : ℝ) =
      ((Terras.T^[m]) n : ℝ) := by rw [collatzIter_eq_terras]
  linarith [hlow, hgt, hmle, hiter]

/-- The terminal endpoint budget also places the upper critical first-passage
time inside the exact floor-defined envelope horizon. -/
theorem ceil_upperCriticalTime_le_envelopeHorizon
    {lambda t y : ℝ} {n M : ℕ}
    (hn0 : 0 < n) (hM : M = Nat.log 2 n)
    (hy0 : 0 ≤ y)
    (hbudget :
      (M : ℝ) * (lambda + t) + bConst + 1 + t ≤ (M : ℝ) * y) :
    ⌈(((1 + t - y) * Real.log n) / (bConst * Real.log 2))⌉₊ ≤
      envelopeHorizon lambda n := by
  have hb : 0 < bConst := bConst_pos
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  have hnUpperNat : n < 2 ^ (M + 1) := by
    subst M
    exact Nat.lt_pow_succ_log_self (by norm_num) n
  have hnUpper : (n : ℝ) ≤ (2 : ℝ) ^ (M + 1) := by
    exact_mod_cast hnUpperNat.le
  have hlogUpper :
      Real.log n ≤ ((M : ℝ) + 1) * Real.log 2 := by
    have h := Real.strictMonoOn_log.monotoneOn
      (Set.mem_Ioi.mpr hnR)
      (Set.mem_Ioi.mpr (by positivity : 0 < (2 : ℝ) ^ (M + 1)))
      hnUpper
    rw [Real.log_pow] at h
    push_cast at h
    simpa [mul_comm] using h
  rw [Nat.ceil_le]
  by_cases hcoef : 0 ≤ 1 + t - y
  · have hnormalized :
        Real.log n / Real.log 2 ≤ (M : ℝ) + 1 := by
      exact (div_le_iff₀ hlog2).2 (by simpa [mul_comm] using hlogUpper)
    have hraw :
        (1 + t - y) * ((M : ℝ) + 1) ≤
          (1 - lambda) * (M : ℝ) - bConst := by
      nlinarith
    have hscaled :
        (1 + t - y) / bConst * (Real.log n / Real.log 2) ≤
          ((1 - lambda) * (M : ℝ) - bConst) / bConst := by
      calc
        (1 + t - y) / bConst * (Real.log n / Real.log 2)
            ≤ (1 + t - y) / bConst * ((M : ℝ) + 1) := by
              exact mul_le_mul_of_nonneg_left hnormalized
                (div_nonneg hcoef hb.le)
        _ = ((1 + t - y) * ((M : ℝ) + 1)) / bConst := by ring
        _ ≤ ((1 - lambda) * (M : ℝ) - bConst) / bConst :=
          div_le_div_of_nonneg_right hraw hb.le
    have hcritical :
        ((1 + t - y) * Real.log n) / (bConst * Real.log 2) ≤
          (1 - lambda) * (M : ℝ) / bConst - 1 := by
      calc
        ((1 + t - y) * Real.log n) / (bConst * Real.log 2)
            = (1 + t - y) / bConst *
                (Real.log n / Real.log 2) := by
                  field_simp [hb.ne', hlog2.ne']
        _ ≤ ((1 - lambda) * (M : ℝ) - bConst) / bConst := hscaled
        _ = (1 - lambda) * (M : ℝ) / bConst - 1 := by
              field_simp [hb.ne']
    calc
      ((1 + t - y) * Real.log n) / (bConst * Real.log 2)
          ≤ (1 - lambda) * (M : ℝ) / bConst - 1 := hcritical
      _ ≤ (envelopeHorizon lambda n : ℝ) := by
        subst M
        exact (Nat.sub_one_lt_floor
          ((1 - lambda) * (Nat.log 2 n : ℝ) / bConst)).le
  · have hcoef' : 1 + t - y ≤ 0 := le_of_not_ge hcoef
    have hlog0 : 0 ≤ Real.log n :=
      Real.log_nonneg (by exact_mod_cast hn0)
    have hcritical :
        ((1 + t - y) * Real.log n) / (bConst * Real.log 2) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonpos_of_nonneg hcoef' hlog0)
        (mul_nonneg hb.le hlog2.le)
    exact hcritical.trans (Nat.cast_nonneg _)

/-- Packaged upper bound: within the envelope horizon, the first-passage time
is at most the ceiling of the upper critical time. -/
theorem collatzFirstPassage_le_ceil_of_mem_EnvelopeGood
    {lambda t B : ℝ} {n : ℕ}
    (hn : n ∈ EnvelopeGood lambda t)
    (hn0 : 0 < n) (hB : 0 < B)
    (hkH : ⌈(((1 + t) * Real.log n - Real.log B) /
        (bConst * Real.log 2))⌉₊ ≤ envelopeHorizon lambda n) :
    collatzFirstPassage B n ≤ ⌈(((1 + t) * Real.log n - Real.log B) /
        (bConst * Real.log 2))⌉₊ :=
  collatzFirstPassage_le_of_exists
    (exists_iterate_le_of_mem_EnvelopeGood hn hn0 hB hkH)

/-- Packaged lower bound: whenever the orbit dips below `B` and the
first-passage time is within the envelope horizon, the first-passage time
majorizes the lower critical time. -/
theorem le_collatzFirstPassage_of_mem_EnvelopeGood
    {lambda t B : ℝ} {n : ℕ}
    (hn : n ∈ EnvelopeGood lambda t)
    (hn0 : 0 < n) (hB : 0 < B)
    (hex : ∃ k : ℕ, (collatzIter k n : ℝ) ≤ B)
    (hτH : collatzFirstPassage B n ≤ envelopeHorizon lambda n) :
    ((1 - t) * Real.log n - Real.log B) / (bConst * Real.log 2) ≤
      (collatzFirstPassage B n : ℝ) := by
  by_contra hlt
  push_neg at hlt
  exact not_le_of_mem_EnvelopeGood_of_lt hn hn0 hB hτH hlt
    (collatzFirstPassage_spec hex)

/-- **Literal first-passage squeeze for a power threshold.** Under the exact
terminal budget with target exponent `y`, the first passage below `n ^ y`
lies between the lower critical real time and the ceiling of the upper one.
This is the pointwise first-passage profile extracted from the envelope. -/
theorem collatzFirstPassage_rpow_bounds_of_mem_EnvelopeGood
    {lambda t y : ℝ} {n M : ℕ}
    (hn : n ∈ EnvelopeGood lambda t)
    (hn0 : 0 < n) (hM : M = Nat.log 2 n)
    (hy0 : 0 ≤ y)
    (hbudget :
      (M : ℝ) * (lambda + t) + bConst + 1 + t ≤ (M : ℝ) * y) :
    (∃ k : ℕ, (collatzIter k n : ℝ) ≤ (n : ℝ) ^ y) ∧
      ((1 - t - y) * Real.log n) / (bConst * Real.log 2) ≤
          (collatzFirstPassage ((n : ℝ) ^ y) n : ℝ) ∧
        collatzFirstPassage ((n : ℝ) ^ y) n ≤
          ⌈(((1 + t - y) * Real.log n) /
            (bConst * Real.log 2))⌉₊ := by
  have hB : 0 < (n : ℝ) ^ y :=
    Real.rpow_pos_of_pos (by exact_mod_cast hn0) y
  have hkH := ceil_upperCriticalTime_le_envelopeHorizon
    hn0 hM hy0 hbudget
  have hkH' :
      ⌈(((1 + t) * Real.log n - Real.log ((n : ℝ) ^ y)) /
        (bConst * Real.log 2))⌉₊ ≤ envelopeHorizon lambda n := by
    convert hkH using 1
    rw [Real.log_rpow (by exact_mod_cast hn0 : (0 : ℝ) < n)]
    ring_nf
  have hupper := collatzFirstPassage_le_ceil_of_mem_EnvelopeGood
    hn hn0 hB hkH'
  have hex : ∃ k : ℕ, (collatzIter k n : ℝ) ≤ (n : ℝ) ^ y :=
    ⟨_, exists_iterate_le_of_mem_EnvelopeGood hn hn0 hB hkH'⟩
  have hτH :
      collatzFirstPassage ((n : ℝ) ^ y) n ≤ envelopeHorizon lambda n :=
    hupper.trans hkH'
  refine ⟨hex, ?_, ?_⟩
  · convert le_collatzFirstPassage_of_mem_EnvelopeGood hn hn0 hB hex hτH using 1
    rw [Real.log_rpow (by exact_mod_cast hn0 : (0 : ℝ) < n)]
    ring_nf
  · convert hupper using 1
    rw [Real.log_rpow (by exact_mod_cast hn0 : (0 : ℝ) < n)]
    ring_nf

/-- **Uniform quantitative first-passage error.** Under the same terminal
budget, every power threshold `n ^ y` with `y ≤ 1` has first-passage time
within `t * log n / (bConst * log 2) + 1` of the deterministic drift time.
The bound is pointwise in `y`, so one envelope controls all admissible target
exponents simultaneously. -/
theorem abs_collatzFirstPassage_sub_rpow_drift_le_of_mem_EnvelopeGood
    {lambda t y : ℝ} {n M : ℕ}
    (hn : n ∈ EnvelopeGood lambda t)
    (hn0 : 0 < n) (hM : M = Nat.log 2 n)
    (ht0 : 0 ≤ t) (hy0 : 0 ≤ y) (hy1 : y ≤ 1)
    (hbudget :
      (M : ℝ) * (lambda + t) + bConst + 1 + t ≤ (M : ℝ) * y) :
    |(collatzFirstPassage ((n : ℝ) ^ y) n : ℝ) -
        ((1 - y) * Real.log n) / (bConst * Real.log 2)| ≤
      (t * Real.log n) / (bConst * Real.log 2) + 1 := by
  obtain ⟨-, hlower, hupper⟩ :=
    collatzFirstPassage_rpow_bounds_of_mem_EnvelopeGood
      hn hn0 hM hy0 hbudget
  have hb : 0 < bConst * Real.log 2 :=
    mul_pos bConst_pos (Real.log_pos (by norm_num))
  have hlog : 0 ≤ Real.log n := by
    apply Real.log_nonneg
    exact_mod_cast hn0
  have hcoef : 0 ≤ 1 + t - y := by linarith
  let X := ((1 + t - y) * Real.log n) / (bConst * Real.log 2)
  have hX0 : 0 ≤ X := by
    dsimp [X]
    exact div_nonneg (mul_nonneg hcoef hlog) hb.le
  have hcast :
      (collatzFirstPassage ((n : ℝ) ^ y) n : ℝ) ≤ (⌈X⌉₊ : ℝ) := by
    exact_mod_cast hupper
  have hupperReal :
      (collatzFirstPassage ((n : ℝ) ^ y) n : ℝ) ≤ X + 1 :=
    hcast.trans (Nat.ceil_lt_add_one hX0).le
  have hlower' :
      ((1 - y) * Real.log n) / (bConst * Real.log 2) -
          (t * Real.log n) / (bConst * Real.log 2) ≤
        (collatzFirstPassage ((n : ℝ) ^ y) n : ℝ) := by
    calc
      ((1 - y) * Real.log n) / (bConst * Real.log 2) -
            (t * Real.log n) / (bConst * Real.log 2) =
          ((1 - t - y) * Real.log n) /
            (bConst * Real.log 2) := by ring
      _ ≤ (collatzFirstPassage ((n : ℝ) ^ y) n : ℝ) := hlower
  have hupper' :
      (collatzFirstPassage ((n : ℝ) ^ y) n : ℝ) ≤
        ((1 - y) * Real.log n) / (bConst * Real.log 2) +
          (t * Real.log n) / (bConst * Real.log 2) + 1 := by
    calc
      (collatzFirstPassage ((n : ℝ) ^ y) n : ℝ) ≤ X + 1 := hupperReal
      _ = ((1 - y) * Real.log n) / (bConst * Real.log 2) +
            (t * Real.log n) / (bConst * Real.log 2) + 1 := by
          dsimp [X]
          ring
  have herror0 :
      0 ≤ (t * Real.log n) / (bConst * Real.log 2) :=
    div_nonneg (mul_nonneg ht0 hlog) hb.le
  rw [abs_le]
  constructor <;> linarith

/-- Abstract squeeze theorem for first-passage ratios. The Collatz-specific
work is isolated in the eventual pointwise bounds; once the tolerance and
target exponents converge, the normalized first-passage time has the expected
drift limit. -/
theorem collatzFirstPassage_ratio_tendsto_of_eventually_bounds
    {l : Filter ℕ} {t y : ℕ → ℝ} {y0 : ℝ}
    (hlog : Filter.Tendsto (fun n : ℕ => Real.log n) l Filter.atTop)
    (ht : Filter.Tendsto t l (nhds 0))
    (hy : Filter.Tendsto y l (nhds y0))
    (hcoef : ∀ᶠ n : ℕ in l, 0 ≤ 1 + t n - y n)
    (hbounds : ∀ᶠ n : ℕ in l,
      ((1 - t n - y n) * Real.log n) / (bConst * Real.log 2) ≤
          (collatzFirstPassage ((n : ℝ) ^ (y n)) n : ℝ) ∧
        collatzFirstPassage ((n : ℝ) ^ (y n)) n ≤
          ⌈(((1 + t n - y n) * Real.log n) /
            (bConst * Real.log 2))⌉₊) :
    Filter.Tendsto
      (fun n : ℕ =>
        (collatzFirstPassage ((n : ℝ) ^ (y n)) n : ℝ) / Real.log n)
      l (nhds ((1 - y0) / (bConst * Real.log 2))) := by
  have hc : 0 < bConst * Real.log 2 :=
    mul_pos bConst_pos (Real.log_pos (by norm_num))
  have hlogPos : ∀ᶠ n : ℕ in l, 0 < Real.log n :=
    hlog.eventually (Filter.eventually_gt_atTop 0)
  have hlowerT :
      Filter.Tendsto
        (fun n => (1 - t n - y n) / (bConst * Real.log 2))
        l (nhds ((1 - y0) / (bConst * Real.log 2))) := by
    convert ((tendsto_const_nhds.sub ht).sub hy).div_const
      (bConst * Real.log 2) using 1
    all_goals ring_nf
  have hinvLog :
      Filter.Tendsto (fun n : ℕ => (Real.log n)⁻¹) l (nhds 0) :=
    hlog.inv_tendsto_atTop
  have hupperT :
      Filter.Tendsto
        (fun n =>
          (1 + t n - y n) / (bConst * Real.log 2) +
            (Real.log n)⁻¹)
        l (nhds ((1 - y0) / (bConst * Real.log 2))) := by
    convert (((tendsto_const_nhds.add ht).sub hy).div_const
      (bConst * Real.log 2)).add hinvLog using 1
    all_goals ring_nf
  have hsandwich : ∀ᶠ n : ℕ in l,
      (1 - t n - y n) / (bConst * Real.log 2) ≤
          (collatzFirstPassage ((n : ℝ) ^ (y n)) n : ℝ) / Real.log n ∧
        (collatzFirstPassage ((n : ℝ) ^ (y n)) n : ℝ) / Real.log n ≤
          (1 + t n - y n) / (bConst * Real.log 2) +
            (Real.log n)⁻¹ := by
    filter_upwards [hcoef, hbounds, hlogPos] with n hcoefn hboundn hlogn
    constructor
    · rw [le_div_iff₀ hlogn]
      convert hboundn.1 using 1
      all_goals ring_nf
    · rw [div_le_iff₀ hlogn]
      have hcast :
          (collatzFirstPassage ((n : ℝ) ^ (y n)) n : ℝ) ≤
            (⌈(((1 + t n - y n) * Real.log n) /
              (bConst * Real.log 2))⌉₊ : ℝ) := by
        exact_mod_cast hboundn.2
      have hceil := Nat.ceil_lt_add_one (show
        0 ≤ ((1 + t n - y n) * Real.log n) /
          (bConst * Real.log 2) by positivity)
      calc
        (collatzFirstPassage ((n : ℝ) ^ (y n)) n : ℝ)
            ≤ (⌈(((1 + t n - y n) * Real.log n) /
                (bConst * Real.log 2))⌉₊ : ℝ) := hcast
        _ ≤ ((1 + t n - y n) * Real.log n) /
              (bConst * Real.log 2) + 1 := hceil.le
        _ = ((1 + t n - y n) / (bConst * Real.log 2) +
              (Real.log n)⁻¹) * Real.log n := by
            field_simp [hc.ne', hlogn.ne']
            ring
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    hlowerT hupperT (hsandwich.mono fun _ h => h.1)
      (hsandwich.mono fun _ h => h.2)

/-- The dyadic shell index tends to infinity with the initial value. -/
theorem natLog_two_tendsto_atTop :
    Filter.Tendsto (Nat.log 2) Filter.atTop Filter.atTop := by
  refine Filter.tendsto_atTop.2 fun M => ?_
  refine Filter.eventually_atTop.2 ⟨2 ^ M, ?_⟩
  intro n hn
  exact Nat.le_log_of_pow_le (by norm_num) hn

/-- The terminal full-envelope tolerance tends to zero along the initial
value, after substituting its dyadic shell index. -/
theorem powerEnvelopeTolerance_nat_tendsto_zero
    {q kappa s : ℝ}
    (hk : OptimizedLinearPullback.KappaAdmissible kappa)
    (hq0 : 0 < q) (hqa : a0 < q) (hq1 : q < 1) (hs : 0 < s) :
    Filter.Tendsto
      (fun n => OptimizedLinearPullback.powerTR kappa q s (Nat.log 2 n))
      Filter.atTop (nhds 0) := by
  have hM := OptimizedLinearPullback.powerTerminalTolerance_tendsto_zero
    hk hq0 hqa hq1 hs
  simpa [OptimizedLinearPullback.powerTR, OptimizedLinearPullback.powerR] using
    hM.comp natLog_two_tendsto_atTop

/-- The shell exponent used by the full-envelope construction is bounded by
the literal natural-log exponent in the paper. -/
theorem powerShellExponent_le_log_rpow_neg
    {delta : ℝ} {n M : ℕ}
    (hdelta0 : 0 ≤ delta)
    (hM : M = Nat.log 2 n) (hM4 : 4 ≤ M) :
    OptimizedLinearPullback.powerShellExponent delta M ≤
      (Real.log n) ^ (-delta) := by
  have hlog := OptimizedLinearPullback.log_le_powerShellScale hM hM4
  unfold OptimizedLinearPullback.powerShellExponent
  exact Real.rpow_le_rpow_of_nonpos hlog.1 hlog.2 (by linarith)

/-- The quantitative profile bound on the exact generated full-envelope set.
Every target exponent above the terminal shell exponent is controlled on the
same orbit, with an error independent of the chosen target exponent. -/
theorem powerDescentSet_firstPassage_profile_bound
    {q kappa s delta y : ℝ} {n : ℕ}
    (hk : OptimizedLinearPullback.KappaAdmissible kappa)
    (hq0 : 0 < q) (hqa : a0 < q)
    (hn : n ∈ OptimizedLinearPullback.powerDescentSet q kappa s delta)
    (hy0 : 0 ≤ y)
    (hyShell :
      OptimizedLinearPullback.powerShellExponent delta (Nat.log 2 n) ≤ y)
    (hy1 : y ≤ 1) :
    |(collatzFirstPassage ((n : ℝ) ^ y) n : ℝ) -
        ((1 - y) * Real.log n) / (bConst * Real.log 2)| ≤
      (OptimizedLinearPullback.powerTR kappa q s (Nat.log 2 n) *
          Real.log n) / (bConst * Real.log 2) + 1 := by
  obtain ⟨hbudget, hM4, hgood⟩ :=
    OptimizedLinearPullback.mem_powerDescentSet_data hn
  have hbudget' :
      (Nat.log 2 n : ℝ) *
            (OptimizedLinearPullback.linearLambda q
                (OptimizedLinearPullback.powerR s (Nat.log 2 n)) +
              OptimizedLinearPullback.powerTR kappa q s (Nat.log 2 n)) +
          bConst + 1 +
            OptimizedLinearPullback.powerTR kappa q s (Nat.log 2 n) ≤
        (Nat.log 2 n : ℝ) * y :=
    hbudget.trans
      (mul_le_mul_of_nonneg_left hyShell (Nat.cast_nonneg _))
  have hn0 : 0 < n := by
    by_contra hn0
    have : n = 0 := Nat.eq_zero_of_not_pos hn0
    subst n
    simp at hM4
  have ht0 :
      0 ≤ OptimizedLinearPullback.powerTR kappa q s (Nat.log 2 n) := by
    simpa [OptimizedLinearPullback.powerTR] using
      (OptimizedLinearPullback.powerTerminalTolerance_pos
        hk hq0 hqa (OptimizedLinearPullback.powerR s (Nat.log 2 n))).le
  apply abs_collatzFirstPassage_sub_rpow_drift_le_of_mem_EnvelopeGood
    (n := n) (M := Nat.log 2 n)
  · simpa [OptimizedLinearPullback.powerEnvelope] using hgood
  · exact hn0
  · rfl
  · exact ht0
  · exact hy0
  · exact hy1
  · exact hbudget'

/-- On the full-envelope density-one set, any nonnegative target exponent
that dominates the terminal shell exponent receives the literal pointwise
first-passage squeeze. -/
theorem powerDescentSet_eventually_firstPassage_bounds
    {q kappa s delta : ℝ} {y : ℕ → ℝ}
    (hy0 : ∀ᶠ n : ℕ in Filter.atTop, 0 ≤ y n)
    (hyShell : ∀ᶠ n : ℕ in Filter.atTop,
      OptimizedLinearPullback.powerShellExponent delta (Nat.log 2 n) ≤ y n) :
    ∀ᶠ n : ℕ in
        Filter.atTop ⊓ Filter.principal
          (OptimizedLinearPullback.powerDescentSet q kappa s delta),
      (∃ k : ℕ, (collatzIter k n : ℝ) ≤ (n : ℝ) ^ (y n)) ∧
        ((1 - OptimizedLinearPullback.powerTR kappa q s (Nat.log 2 n) - y n) *
            Real.log n) / (bConst * Real.log 2) ≤
            (collatzFirstPassage ((n : ℝ) ^ (y n)) n : ℝ) ∧
          collatzFirstPassage ((n : ℝ) ^ (y n)) n ≤
            ⌈(((1 + OptimizedLinearPullback.powerTR kappa q s (Nat.log 2 n) -
                y n) * Real.log n) / (bConst * Real.log 2))⌉₊ := by
  rw [Filter.eventually_inf_principal]
  filter_upwards [hy0, hyShell] with n hyn0 hynShell
  intro hn
  obtain ⟨hbudget, hM4, hgood⟩ :=
    OptimizedLinearPullback.mem_powerDescentSet_data hn
  have hbudget' :
      (Nat.log 2 n : ℝ) *
            (OptimizedLinearPullback.linearLambda q
                (OptimizedLinearPullback.powerR s (Nat.log 2 n)) +
              OptimizedLinearPullback.powerTR kappa q s (Nat.log 2 n)) +
          bConst + 1 +
            OptimizedLinearPullback.powerTR kappa q s (Nat.log 2 n) ≤
        (Nat.log 2 n : ℝ) * y n := by
    exact hbudget.trans
      (mul_le_mul_of_nonneg_left hynShell (Nat.cast_nonneg _))
  have hn0 : 0 < n := by
    by_contra hn0
    have : n = 0 := Nat.eq_zero_of_not_pos hn0
    subst n
    simp at hM4
  apply collatzFirstPassage_rpow_bounds_of_mem_EnvelopeGood
    (n := n) (M := Nat.log 2 n)
  · simpa [OptimizedLinearPullback.powerEnvelope] using hgood
  · exact hn0
  · rfl
  · exact hyn0
  · exact hbudget'

/-- First-passage ratio law on one parameterized full-envelope set. This is
the reusable assembly theorem behind both first-passage limits. -/
theorem powerDescentSet_firstPassage_ratio_tendsto
    {q kappa s delta y0 : ℝ} {y : ℕ → ℝ}
    (hk : OptimizedLinearPullback.KappaAdmissible kappa)
    (hq0 : 0 < q) (hqa : a0 < q) (hq1 : q < 1) (hs : 0 < s)
    (hy0lt : y0 < 1)
    (hy : Filter.Tendsto y Filter.atTop (nhds y0))
    (hyNonneg : ∀ᶠ n : ℕ in Filter.atTop, 0 ≤ y n)
    (hyShell : ∀ᶠ n : ℕ in Filter.atTop,
      OptimizedLinearPullback.powerShellExponent delta (Nat.log 2 n) ≤ y n) :
    Filter.Tendsto
      (fun n : ℕ =>
        (collatzFirstPassage ((n : ℝ) ^ (y n)) n : ℝ) / Real.log n)
      (Filter.atTop ⊓ Filter.principal
        (OptimizedLinearPullback.powerDescentSet q kappa s delta))
      (nhds ((1 - y0) / (bConst * Real.log 2))) := by
  let l : Filter ℕ := Filter.atTop ⊓ Filter.principal
    (OptimizedLinearPullback.powerDescentSet q kappa s delta)
  have hlogNat :
      Filter.Tendsto (fun n : ℕ => Real.log n)
        Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlog :
      Filter.Tendsto (fun n : ℕ => Real.log n) l Filter.atTop :=
    hlogNat.mono_left inf_le_left
  have ht :
      Filter.Tendsto
        (fun n => OptimizedLinearPullback.powerTR kappa q s (Nat.log 2 n))
        l (nhds 0) :=
    (powerEnvelopeTolerance_nat_tendsto_zero hk hq0 hqa hq1 hs).mono_left
      inf_le_left
  have hy' : Filter.Tendsto y l (nhds y0) := hy.mono_left inf_le_left
  have hcoefT :
      Filter.Tendsto
        (fun n =>
          1 + OptimizedLinearPullback.powerTR kappa q s (Nat.log 2 n) - y n)
        l (nhds (1 - y0)) := by
    convert (tendsto_const_nhds.add ht).sub hy' using 1
    all_goals ring_nf
  have hcoef : ∀ᶠ n : ℕ in l,
      0 ≤ 1 + OptimizedLinearPullback.powerTR kappa q s (Nat.log 2 n) -
        y n := by
    have hpos := hcoefT.eventually (Ioi_mem_nhds (sub_pos.mpr hy0lt))
    exact hpos.mono fun _ h => h.le
  exact collatzFirstPassage_ratio_tendsto_of_eventually_bounds
    hlog ht hy' hcoef
      ((powerDescentSet_eventually_firstPassage_bounds hyNonneg hyShell).mono
        fun _ h => h.2)

/-- The shell exponent tends to zero after substituting the dyadic shell of
the initial value. -/
theorem powerShellExponent_nat_tendsto_zero
    {delta : ℝ} (hdelta0 : 0 < delta) :
    Filter.Tendsto
      (fun n => OptimizedLinearPullback.powerShellExponent delta (Nat.log 2 n))
      Filter.atTop (nhds 0) := by
  have hM :
      Filter.Tendsto
        (OptimizedLinearPullback.powerShellExponent delta)
        Filter.atTop (nhds 0) := by
    simpa [OptimizedLinearPullback.powerShellExponent, Function.comp_apply]
      using ((tendsto_rpow_neg_atTop hdelta0).comp
        OptimizedLinearPullback.powerShellScale_tendsto_atTop)
  exact hM.comp natLog_two_tendsto_atTop

/-- Exact identification of the drift first-passage constant used in the
paper. -/
theorem inv_bConst_log_two_eq_two_div_log_four_thirds :
    1 / (bConst * Real.log 2) = 2 / Real.log (4 / 3) := by
  have hlog2ne : Real.log 2 ≠ 0 :=
    ne_of_gt (Real.log_pos (by norm_num))
  have hid : 2 * (bConst * Real.log 2) = Real.log (4 / 3) := by
    unfold bConst a0 lg3 Real.logb
    rw [Real.log_div (by norm_num : (4 : ℝ) ≠ 0)
      (by norm_num : (3 : ℝ) ≠ 0)]
    have hlog4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
      calc
        Real.log (4 : ℝ) = Real.log ((2 : ℝ) ^ 2) := by norm_num
        _ = 2 * Real.log 2 := by rw [Real.log_pow]; norm_num
    rw [hlog4]
    field_simp [hlog2ne]
    ring
  rw [← hid]
  field_simp [bConst_pos.ne', hlog2ne]

/-- **First-passage limit specializations.** For every admissible
shrinking-target exponent and every fixed power scale, one natural-density-one
set supports both first-passage limits and both hitting times are eventually
defined there. -/
theorem collatz_almost_all_first_passage_laws
    {delta x : ℝ}
    (hdelta0 : 0 < delta)
    (hdelta : delta < OptimizedLinearPullback.linearHeadlineExponent)
    (hx0 : 0 < x) (hx1 : x < 1) :
    ∃ A : Set ℕ,
      NaturalDensityOne A ∧
        (∀ᶠ n : ℕ in Filter.atTop ⊓ Filter.principal A,
          ∃ k : ℕ,
            (collatzIter k n : ℝ) ≤
              Real.exp ((Real.log n) ^ (1 - delta))) ∧
        (∀ᶠ n : ℕ in Filter.atTop ⊓ Filter.principal A,
          ∃ k : ℕ, (collatzIter k n : ℝ) ≤ (n : ℝ) ^ x) ∧
        Filter.Tendsto
          (fun n : ℕ =>
            (collatzFirstPassage
              (Real.exp ((Real.log n) ^ (1 - delta))) n : ℝ) /
                Real.log n)
          (Filter.atTop ⊓ Filter.principal A)
          (nhds (2 / Real.log (4 / 3))) ∧
        Filter.Tendsto
          (fun n : ℕ =>
            (collatzFirstPassage ((n : ℝ) ^ x) n : ℝ) / Real.log n)
          (Filter.atTop ⊓ Filter.principal A)
          (nhds ((1 - x) * (2 / Real.log (4 / 3)))) := by
  obtain ⟨q, transport, kappa, s,
      hq0, hqa, hq1, htransport0, htransportLimit,
      hk, hs, hdeltaU, huw⟩ :=
    OptimizedLinearPullback.exists_optimized_linear_parameters hdelta0 hdelta
  let A := OptimizedLinearPullback.powerDescentSet q kappa s delta
  let ydelta : ℕ → ℝ := fun n => (Real.log n) ^ (-delta)
  let l : Filter ℕ := Filter.atTop ⊓ Filter.principal A
  have htransport1 : transport < 1 :=
    htransportLimit.trans OptimizedLinearPullback.asymptoticRateLimit_lt_one
  have hw := OptimizedLinearPullback.powerW_pos
    hq0 hq1 htransport0 htransport1 hk hs
  have hdelta1 : delta < 1 := by linarith
  have hAinternal : QuantitativeDensity.HasNaturalDensityOne A := by
    dsimp [A]
    exact OptimizedLinearPullback.powerDescentSet_hasNaturalDensityOne
      hq0 hqa hq1 htransport0 htransportLimit hk hs
      huw hdeltaU hdelta1
  have hA : NaturalDensityOne A := by
    rw [naturalDensityOne_iff_internal]
    exact hAinternal
  have hlogNat :
      Filter.Tendsto (fun n : ℕ => Real.log n)
        Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hyDelta : Filter.Tendsto ydelta Filter.atTop (nhds 0) := by
    simpa [ydelta, Function.comp_apply] using
      (tendsto_rpow_neg_atTop hdelta0).comp hlogNat
  have hyDeltaNonneg : ∀ᶠ n : ℕ in Filter.atTop, 0 ≤ ydelta n := by
    filter_upwards [Filter.eventually_ge_atTop 2] with n hn2
    exact Real.rpow_nonneg
      (Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega))) _
  have hM4 : ∀ᶠ n : ℕ in Filter.atTop, 4 ≤ Nat.log 2 n :=
    natLog_two_tendsto_atTop.eventually (Filter.eventually_ge_atTop 4)
  have hyDeltaShell : ∀ᶠ n : ℕ in Filter.atTop,
      OptimizedLinearPullback.powerShellExponent delta (Nat.log 2 n) ≤
        ydelta n := by
    filter_upwards [hM4] with n hn4
    exact powerShellExponent_le_log_rpow_neg hdelta0.le rfl hn4
  have hDeltaData := powerDescentSet_eventually_firstPassage_bounds
    (q := q) (kappa := kappa) (s := s) (delta := delta)
    (y := ydelta) hyDeltaNonneg hyDeltaShell
  have hDeltaRpow := powerDescentSet_firstPassage_ratio_tendsto
    (q := q) (kappa := kappa) (s := s) (delta := delta)
    (y := ydelta) (y0 := 0) hk hq0 hqa hq1 hs zero_lt_one
    hyDelta hyDeltaNonneg hyDeltaShell
  have hShellTendsto := powerShellExponent_nat_tendsto_zero hdelta0
  have hxShell : ∀ᶠ n : ℕ in Filter.atTop,
      OptimizedLinearPullback.powerShellExponent delta (Nat.log 2 n) ≤ x := by
    have hlt := hShellTendsto.eventually (Iio_mem_nhds hx0)
    exact hlt.mono fun _ h => h.le
  have hxNonneg : ∀ᶠ _n : ℕ in Filter.atTop, 0 ≤ x :=
    Filter.Eventually.of_forall fun _ => hx0.le
  have hxData := powerDescentSet_eventually_firstPassage_bounds
    (q := q) (kappa := kappa) (s := s) (delta := delta)
    (y := fun _ => x) hxNonneg hxShell
  have hxRpow := powerDescentSet_firstPassage_ratio_tendsto
    (q := q) (kappa := kappa) (s := s) (delta := delta)
    (y := fun _ => x) (y0 := x) hk hq0 hqa hq1 hs hx1
    tendsto_const_nhds hxNonneg hxShell
  have hthreshold : ∀ᶠ n : ℕ in Filter.atTop,
      (n : ℝ) ^ ydelta n =
        Real.exp ((Real.log n) ^ (1 - delta)) := by
    filter_upwards [Filter.eventually_ge_atTop 2] with n hn2
    have hnR : (0 : ℝ) < n := by positivity
    have hlog : 0 < Real.log n :=
      Real.log_pos (by exact_mod_cast (show 1 < n by omega))
    rw [Real.rpow_def_of_pos hnR]
    congr 1
    dsimp [ydelta]
    calc
      Real.log n * (Real.log n) ^ (-delta)
          = (Real.log n) ^ (1 : ℝ) *
              (Real.log n) ^ (-delta) := by rw [Real.rpow_one]
      _ = (Real.log n) ^ ((1 : ℝ) + (-delta)) := by
            rw [← Real.rpow_add hlog]
      _ = (Real.log n) ^ (1 - delta) := by ring_nf
  have hthreshold' : ∀ᶠ n : ℕ in l,
      (n : ℝ) ^ ydelta n =
        Real.exp ((Real.log n) ^ (1 - delta)) :=
    hthreshold.filter_mono inf_le_left
  have hDeltaExists : ∀ᶠ n : ℕ in l,
      ∃ k : ℕ,
        (collatzIter k n : ℝ) ≤
          Real.exp ((Real.log n) ^ (1 - delta)) := by
    filter_upwards [hDeltaData, hthreshold'] with n hnData hnThreshold
    simpa [← hnThreshold] using hnData.1
  have hxExists : ∀ᶠ n : ℕ in l,
      ∃ k : ℕ, (collatzIter k n : ℝ) ≤ (n : ℝ) ^ x :=
    hxData.mono fun _ h => h.1
  have hDeltaLiteral :
      Filter.Tendsto
        (fun n : ℕ =>
          (collatzFirstPassage
            (Real.exp ((Real.log n) ^ (1 - delta))) n : ℝ) /
              Real.log n)
        l (nhds (2 / Real.log (4 / 3))) := by
    have hcongr :
        (fun n : ℕ =>
          (collatzFirstPassage ((n : ℝ) ^ ydelta n) n : ℝ) /
            Real.log n) =ᶠ[l]
        (fun n : ℕ =>
          (collatzFirstPassage
            (Real.exp ((Real.log n) ^ (1 - delta))) n : ℝ) /
              Real.log n) := by
      filter_upwards [hthreshold'] with n hn
      rw [hn]
    have h := hDeltaRpow.congr' hcongr
    have hlimit :
        (1 - 0) / (bConst * Real.log 2) = 2 / Real.log (4 / 3) := by
      simpa using inv_bConst_log_two_eq_two_div_log_four_thirds
    rw [hlimit] at h
    exact h
  have hxLiteral :
      Filter.Tendsto
        (fun n : ℕ =>
          (collatzFirstPassage ((n : ℝ) ^ x) n : ℝ) / Real.log n)
        l (nhds ((1 - x) * (2 / Real.log (4 / 3)))) := by
    have hlimit :
        (1 - x) / (bConst * Real.log 2) =
          (1 - x) * (2 / Real.log (4 / 3)) := by
      calc
        (1 - x) / (bConst * Real.log 2) =
            (1 - x) * (1 / (bConst * Real.log 2)) := by ring
        _ = (1 - x) * (2 / Real.log (4 / 3)) := by
          rw [inv_bConst_log_two_eq_two_div_log_four_thirds]
    rw [hlimit] at hxRpow
    simpa using hxRpow
  exact ⟨A, hA, hDeltaExists, hxExists, hDeltaLiteral, hxLiteral⟩

end

end QuantitativeCollatzMain

end CollatzEndpointTransport
