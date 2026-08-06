/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik
-/
import CollatzEndpointTransport.Common.QuantitativeDensity

/-!
# Shell To Global Density

Shell-to-global transport: per-shell exceptional fractions become
`(C,D)`-density on the positive integers.

This is the bridge between the retained maximal-barrier and pullback shell
estimates on `[2^M, 2^(M+1))` and the density interface `IsCDDense` consumed by
the scalar bootstrap.

The conversion is exact and is the reason the two exponent conventions differ:

  shell rate   exp (-c * M)     with M = log_2 N
  density      N^(1 - c / log 2)

so a shell exponent `c` becomes a density exponent `D = c / log 2`. The
hypothesis `c < log 2` is what keeps `D <= 1`; it is exactly the statement
that the exceptional count does not outgrow the shell it lives in.

The retained initial-window, maximal-barrier, and pullback estimates factor
through this lemma, so it is stated for an arbitrary set `S` and arbitrary
constants rather than for one application.
-/

namespace CollatzEndpointTransport

namespace QuantitativeDensity

open scoped Real

noncomputable section

/-- The dyadic shell `[2^M, 2^(M+1))`. -/
def dyadicShell (M : ℕ) : Finset ℕ :=
  Finset.Ico (2 ^ M) (2 ^ (M + 1))

/-- Nonmembers of `S` in the `M`-th dyadic shell. -/
def shellBad (S : Set ℕ) (M : ℕ) : Finset ℕ := by
  classical
  exact (dyadicShell M).filter (fun n => n ∉ S)

/-- Every positive `n <= N` lies in a dyadic shell of index at most
`Nat.log 2 N`. -/
theorem badPrefix_subset_biUnion (S : Set ℕ) (N : ℕ) :
    badPrefix S N ⊆
      (Finset.range (Nat.log 2 N + 1)).biUnion (shellBad S) := by
  classical
  intro n hn
  rw [badPrefix, Finset.mem_filter, positivePrefix, Finset.mem_Icc] at hn
  obtain ⟨⟨hn1, hnN⟩, hnS⟩ := hn
  have hn0 : n ≠ 0 := by omega
  refine Finset.mem_biUnion.2 ⟨Nat.log 2 n, ?_, ?_⟩
  · exact Finset.mem_range.2
      (Nat.lt_succ_of_le (Nat.log_mono_right hnN))
  · rw [shellBad, Finset.mem_filter, dyadicShell, Finset.mem_Ico]
    exact ⟨⟨Nat.pow_log_le_self 2 hn0,
      Nat.lt_pow_succ_log_self (by norm_num) n⟩, hnS⟩

/-- Cardinality form of the shell decomposition. -/
theorem card_badPrefix_le_sum (S : Set ℕ) (N : ℕ) :
    (badPrefix S N).card ≤
      ∑ M ∈ Finset.range (Nat.log 2 N + 1), (shellBad S M).card := by
  classical
  calc
    (badPrefix S N).card
        ≤ ((Finset.range (Nat.log 2 N + 1)).biUnion (shellBad S)).card :=
      Finset.card_le_card (badPrefix_subset_biUnion S N)
    _ ≤ ∑ M ∈ Finset.range (Nat.log 2 N + 1), (shellBad S M).card :=
      Finset.card_biUnion_le

/-- **Shell-to-global density transport.**

If the exceptional fraction of every dyadic shell is at most
`K * exp (-c * M)`, and the shell rate `c` is below `log 2`, then the
exceptional set is `(C,D)`-dense-complemented with

  D = c / log 2,      C = 2 K / (2 * exp (-c) - 1).

The constant is explicit and the geometric series is summed exactly; no
asymptotic step occurs. -/
theorem isCDDense_of_shell_bound
    {S : Set ℕ} {K c : ℝ}
    (hK : 0 < K) (hc : 0 < c) (hclt : c < Real.log 2)
    (hshell : ∀ M : ℕ,
      ((shellBad S M).card : ℝ) ≤ K * Real.exp (-c * M) * 2 ^ M) :
    IsCDDense S (2 * K / (2 * Real.exp (-c) - 1)) (c / Real.log 2) := by
  classical
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set r : ℝ := 2 * Real.exp (-c) with hr_def
  -- `c < log 2` is exactly `r > 1`
  have hr1 : 1 < r := by
    have h2 : Real.exp (-Real.log 2) = (2 : ℝ)⁻¹ := by
      rw [Real.exp_neg, Real.exp_log (by norm_num)]
    have h : Real.exp (-Real.log 2) < Real.exp (-c) :=
      Real.exp_lt_exp.2 (by linarith)
    rw [h2] at h
    rw [hr_def]
    linarith
  have hrpos : 0 < r := by linarith
  have hrm1 : 0 < r - 1 := by linarith
  refine ⟨by positivity, by positivity, ?_, ?_⟩
  · rw [div_le_one hlog2]; exact le_of_lt hclt
  intro N hN
  set L := Nat.log 2 N with hL_def
  -- (1) shell decomposition
  have hsum := card_badPrefix_le_sum S N
  have hsumR : ((badPrefix S N).card : ℝ) ≤
      ∑ M ∈ Finset.range (L + 1), ((shellBad S M).card : ℝ) := by
    exact_mod_cast hsum
  -- (2) each shell by hypothesis, giving a geometric series in `r`
  have hgeom : ∑ M ∈ Finset.range (L + 1), ((shellBad S M).card : ℝ) ≤
      K * ∑ M ∈ Finset.range (L + 1), r ^ M := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro M _
    have hrw : K * r ^ M = K * Real.exp (-c * M) * 2 ^ M := by
      rw [hr_def, mul_pow, ← Real.exp_nat_mul]
      ring_nf
    rw [hrw]
    exact hshell M
  -- (3) sum the geometric series exactly
  have hgs : ∑ M ∈ Finset.range (L + 1), r ^ M = (r ^ (L + 1) - 1) / (r - 1) :=
    geom_sum_eq (by linarith) _
  have hgs' : ∑ M ∈ Finset.range (L + 1), r ^ M ≤ r ^ (L + 1) / (r - 1) := by
    rw [hgs]
    gcongr
    linarith
  -- (4) transport `r ^ (L+1)` to a power of `N`
  have hNL : (2 : ℝ) ^ L ≤ (N : ℝ) := by
    exact_mod_cast Nat.pow_log_le_self 2 hN.ne'
  have hLN : (N : ℝ) < 2 ^ (L + 1) := by
    exact_mod_cast Nat.lt_pow_succ_log_self (by norm_num) N
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hpow2 : (2 : ℝ) ^ (L + 1) ≤ 2 * N := by
    rw [pow_succ]
    nlinarith [hNL]
  have hexp : Real.exp (-c) ^ (L + 1) ≤ (N : ℝ) ^ (-(c / Real.log 2)) := by
    have hlnN : Real.log N ≤ ((L : ℝ) + 1) * Real.log 2 := by
      have h := Real.log_le_log hNpos (le_of_lt hLN)
      rwa [Real.log_pow, Nat.cast_add, Nat.cast_one] at h
    rw [← Real.exp_nat_mul, Real.rpow_def_of_pos hNpos]
    apply Real.exp_le_exp.2
    have hmul : c / Real.log 2 * Real.log N ≤ ((L : ℝ) + 1) * c := by
      have h := mul_le_mul_of_nonneg_left hlnN
        (le_of_lt (div_pos hc hlog2))
      calc c / Real.log 2 * Real.log N
          ≤ c / Real.log 2 * (((L : ℝ) + 1) * Real.log 2) := h
        _ = ((L : ℝ) + 1) * c := by field_simp; ring
    push_cast
    nlinarith [hmul]
  have hrL : r ^ (L + 1) ≤ 2 * N * (N : ℝ) ^ (-(c / Real.log 2)) := by
    rw [hr_def, mul_pow]
    have h1 : (0 : ℝ) ≤ Real.exp (-c) ^ (L + 1) := by positivity
    have h2 : (0 : ℝ) ≤ (2 : ℝ) ^ (L + 1) := by positivity
    calc
      (2 : ℝ) ^ (L + 1) * Real.exp (-c) ^ (L + 1)
          ≤ (2 * N) * Real.exp (-c) ^ (L + 1) :=
            mul_le_mul_of_nonneg_right hpow2 h1
      _ ≤ (2 * N) * (N : ℝ) ^ (-(c / Real.log 2)) := by
            apply mul_le_mul_of_nonneg_left hexp (by positivity)
  -- (5) assemble, using `N * N^(-D) = N^(1-D)`
  have hNrpow : (N : ℝ) * (N : ℝ) ^ (-(c / Real.log 2)) =
      (N : ℝ) ^ (1 - c / Real.log 2) := by
    rw [show (1 : ℝ) - c / Real.log 2 = 1 + -(c / Real.log 2) by ring,
      Real.rpow_add hNpos, Real.rpow_one]
  calc
    ((badPrefix S N).card : ℝ)
        ≤ K * ∑ M ∈ Finset.range (L + 1), r ^ M := hsumR.trans hgeom
    _ ≤ K * (r ^ (L + 1) / (r - 1)) := by
          exact mul_le_mul_of_nonneg_left hgs' (le_of_lt hK)
    _ ≤ K * ((2 * N * (N : ℝ) ^ (-(c / Real.log 2))) / (r - 1)) := by
          gcongr
    _ = 2 * K / (r - 1) * ((N : ℝ) * (N : ℝ) ^ (-(c / Real.log 2))) := by
          field_simp; ring
    _ = 2 * K / (r - 1) * (N : ℝ) ^ (1 - c / Real.log 2) := by rw [hNrpow]

end

end QuantitativeDensity

end CollatzEndpointTransport
