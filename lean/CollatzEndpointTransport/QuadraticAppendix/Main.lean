/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik
-/
import CollatzEndpointTransport.QuadraticAppendix.QuantitativeQuadraticCorollaries
import CollatzEndpointTransport.QuadraticAppendix.QuantitativeQuadraticExceptionalCountThreeQuarter
import CollatzEndpointTransport.Common.QuantitativeCollatzDefs

/-!
# Referee-facing quadratic API

Referee-facing API for the quantitative natural-density Collatz theorem.

This file deliberately exposes the mathematical objects in the theorem
statement:

* the half-Collatz map;
* its iterates and literal orbit minimum;
* natural density one through exceptional prefix proportions;
* the explicit admissible exponent;
* Proposition A and Theorem B.

The proof imports the audited implementation, but no bootstrap schedule,
envelope, cone, or pullback object occurs in the public statements.
-/

namespace CollatzEndpointTransport

namespace QuantitativeCollatzMain

open scoped Real Topology

noncomputable section

/-- The endpoint of the admissible exponent range:
`log(2 / log_2 3) / log 2 = 0.335551...`. -/
def admissibleExponent : ℝ :=
  Real.log (2 / Real.logb 2 3) / Real.log 2

theorem admissibleExponent_eq_internal :
    admissibleExponent =
      QuantitativeDensity.quadraticHeadlineExponent := by
  rw [QuantitativeDensity.quadraticHeadlineExponent_eq]
  rfl

/-- The literal event appearing in Theorem B. Values at the finitely many
small inputs where real logarithms use totalized library conventions are
irrelevant to the natural-density statement. -/
def quantitativeDescentSet (a C : ℝ) : Set ℕ :=
  {n |
    (collatzMin n : ℝ) ≤
      Real.exp
        (C * Real.log n /
          (Real.log (Real.log n)) ^ a)}

/-- Theorem B's descent event with an explicit iterate witness no later than
`log(n) / (b * log 2)`, where `b = 1 - log_2(sqrt 3)`. -/
def quantitativeTimedDescentSet (a C : ℝ) : Set ℕ :=
  {n | ∃ k : ℕ,
    (k : ℝ) ≤
        Real.log n /
          (QuantitativeDensity.bConst * Real.log 2) ∧
      (k : ℝ) < (6953 / 1000 : ℝ) * Real.log n ∧
      (collatzIter k n : ℝ) ≤
        Real.exp
          (C * Real.log n /
            (Real.log (Real.log n)) ^ a)}

/-- Public exceptional count in the positive prefix `[1,N]`. -/
def exceptionalCount (S : Set ℕ) (N : ℕ) : ℕ := by
    classical
    exact ((Finset.Icc 1 N).filter (fun n => n ∉ S)).card

/-- Exact horizon through which the quantitative lower envelope keeps the
Collatz orbit strictly above `1`. -/
def quantitativeSurvivalHorizon (a : ℝ) (n : ℕ) : ℕ :=
  QuantitativeDensity.theoremBSurvivalHorizon a n

/-- The assumption-free survival event: no iterate through the explicit
horizon has reached `1`. -/
def quantitativeSurvivalSet (a : ℝ) : Set ℕ :=
  {n | ∀ k : ℕ, k ≤ quantitativeSurvivalHorizon a n →
    1 < collatzIter k n}

/-- **Theorem B (referee-facing form).** For every exponent below the explicit
endpoint, the literal Collatz orbit minimum satisfies the displayed
quantitative bound on a set of natural density one. -/
theorem collatz_quantitative_natural_density_descent
    {a : ℝ} (ha0 : 0 < a) (ha : a < admissibleExponent) :
    NaturalDensityOne (quantitativeDescentSet a 1) := by
  have ha' :
      a < QuantitativeDensity.quadraticHeadlineExponent := by
    rwa [admissibleExponent_eq_internal] at ha
  have hB :=
    QuantitativeDensity.quantitativeQuadraticTheoremB_one ha0 ha'
  rw [naturalDensityOne_iff_internal]
  apply QuantitativeDensity.hasNaturalDensityOne_mono
    (S := QuantitativeDensity.quantitativeTheoremBSet a 1)
    (U := quantitativeDescentSet a 1) ?_ hB
  intro n hn
  obtain ⟨k, hk⟩ := hn
  change (collatzMin n : ℝ) ≤
    Real.exp
      (1 * Real.log n /
        (Real.log (Real.log n)) ^ a)
  rw [collatzMin_eq_terras]
  exact Terras.cast_Tmin_le_of_exists_iterate_cast_le ⟨k, hk⟩

/-- **Corollary B.1 (bounded witness time).** The same quantitative descent
is witnessed by an actual iterate before the explicit logarithmic horizon. -/
theorem collatz_quantitative_natural_density_descent_timed
    {a : ℝ} (ha0 : 0 < a) (ha : a < admissibleExponent) :
    NaturalDensityOne (quantitativeTimedDescentSet a 1) := by
  have ha' :
      a < QuantitativeDensity.quadraticHeadlineExponent := by
    rwa [admissibleExponent_eq_internal] at ha
  have hB :=
    QuantitativeDensity.quantitativeQuadraticTheoremB_timed ha0 ha'
  rw [naturalDensityOne_iff_internal]
  apply QuantitativeDensity.hasNaturalDensityOne_mono
    (S := QuantitativeDensity.quantitativeTimedTheoremBSet a 1)
    (U := quantitativeTimedDescentSet a 1) ?_ hB
  intro n hn
  obtain ⟨k, htime, htimeDecimal, hvalue⟩ := hn
  refine ⟨k, htime, htimeDecimal, ?_⟩
  simpa [collatzIter] using hvalue

/-- **Corollary B.2 (quantitative exceptional count).** The exceptional set
has an explicit `3/4`-power stretched-exponential bound with conservative
constants `6` and `1/128`. -/
theorem collatz_quantitative_exceptional_count
    {a : ℝ} (ha0 : 0 < a) (ha : a < admissibleExponent) :
    ∃ N₀ : ℕ, ∀ N, N₀ ≤ N →
      (exceptionalCount (quantitativeDescentSet a 1) N : ℝ) ≤
        6 * N *
          Real.exp
            (-(1 / 128 : ℝ) *
              (Real.log N) ^ ((3 : ℝ) / 4)) := by
  apply Filter.eventually_atTop.1
  have ha' :
      a < QuantitativeDensity.quadraticHeadlineExponent := by
    rwa [admissibleExponent_eq_internal] at ha
  have hrate :=
    QuantitativeDensity.quantitativeQuadraticTheoremB_exceptional_count_threeQuarter
      ha0 ha'
  filter_upwards [hrate] with N hN
  have hgood :
      QuantitativeDensity.quantitativeTheoremBSet a 1 ⊆
        quantitativeDescentSet a 1 := by
    intro n hn
    obtain ⟨k, hk⟩ := hn
    change (collatzMin n : ℝ) ≤
      Real.exp
        (1 * Real.log n /
          (Real.log (Real.log n)) ^ a)
    rw [collatzMin_eq_terras]
    exact Terras.cast_Tmin_le_of_exists_iterate_cast_le ⟨k, hk⟩
  have hsub :
      QuantitativeDensity.badPrefix
          (quantitativeDescentSet a 1) N ⊆
        QuantitativeDensity.badPrefix
          (QuantitativeDensity.quantitativeTheoremBSet a 1) N := by
    intro n hn
    simp only [QuantitativeDensity.badPrefix,
      QuantitativeDensity.positivePrefix, Finset.mem_filter,
      Finset.mem_Icc] at hn ⊢
    exact ⟨hn.1, fun hinternal => hn.2 (hgood hinternal)⟩
  have hcard :
      (exceptionalCount (quantitativeDescentSet a 1) N : ℝ) ≤
        ((QuantitativeDensity.badPrefix
          (QuantitativeDensity.quantitativeTheoremBSet a 1) N).card :
            ℝ) := by
    unfold exceptionalCount
    exact_mod_cast Finset.card_le_card hsub
  exact hcard.trans hN

/-- **Lower-envelope survival corollary.** On a natural-density-one set, no
Collatz iterate through the explicit horizon has reached `1`. -/
theorem collatz_quantitative_natural_density_survival
    {a : ℝ} (ha0 : 0 < a) (ha : a < admissibleExponent) :
    NaturalDensityOne (quantitativeSurvivalSet a) := by
  have ha' :
      a < QuantitativeDensity.quadraticHeadlineExponent := by
    rwa [admissibleExponent_eq_internal] at ha
  have hsurvive :=
    QuantitativeDensity.quantitativeQuadraticSurvival ha0 ha'
  rw [naturalDensityOne_iff_internal]
  apply QuantitativeDensity.hasNaturalDensityOne_mono
    (S := QuantitativeDensity.quantitativeSurvivalSet a)
    (U := quantitativeSurvivalSet a) ?_ hsurvive
  intro n hn k hk
  have h := hn k hk
  exact_mod_cast h

/-- The survival corollary has the same strengthened exceptional-count rate
as Theorem B. -/
theorem collatz_quantitative_survival_exceptional_count
    {a : ℝ} (ha0 : 0 < a) (ha : a < admissibleExponent) :
    ∃ N₀ : ℕ, ∀ N, N₀ ≤ N →
      (exceptionalCount (quantitativeSurvivalSet a) N : ℝ) ≤
        6 * N *
          Real.exp
            (-(1 / 128 : ℝ) *
              (Real.log N) ^ ((3 : ℝ) / 4)) := by
  apply Filter.eventually_atTop.1
  have ha' :
      a < QuantitativeDensity.quadraticHeadlineExponent := by
    rwa [admissibleExponent_eq_internal] at ha
  have hrate :=
    QuantitativeDensity.quantitativeQuadraticSurvival_exceptional_count_threeQuarter
      ha0 ha'
  filter_upwards [hrate] with N hN
  have hsub :
      QuantitativeDensity.badPrefix
          (quantitativeSurvivalSet a) N ⊆
        QuantitativeDensity.badPrefix
          (QuantitativeDensity.quantitativeSurvivalSet a) N := by
    intro n hn
    simp only [QuantitativeDensity.badPrefix,
      QuantitativeDensity.positivePrefix, Finset.mem_filter,
      Finset.mem_Icc] at hn ⊢
    exact ⟨hn.1, fun hinternal => hn.2 (by
      intro k hk
      have h := hinternal k hk
      exact_mod_cast h)⟩
  have hcard :
      (exceptionalCount (quantitativeSurvivalSet a) N : ℝ) ≤
        ((QuantitativeDensity.badPrefix
          (QuantitativeDensity.quantitativeSurvivalSet a) N).card :
            ℝ) := by
    unfold exceptionalCount
    exact_mod_cast Finset.card_le_card hsub
  exact hcard.trans hN

/-- Any actual first or later hit of `1` lies beyond the certified horizon.
No assumption that every orbit reaches `1` is used. -/
theorem collatz_one_hitting_time_gt_quantitativeSurvivalHorizon
    {a : ℝ} {n tau : ℕ}
    (hn : n ∈ quantitativeSurvivalSet a)
    (htau : collatzIter tau n = 1) :
    quantitativeSurvivalHorizon a n < tau := by
  by_contra h
  have hle : tau ≤ quantitativeSurvivalHorizon a n := Nat.le_of_not_gt h
  have hsurvive := hn tau hle
  omega

/-- Compatibility form retaining an existential positive threshold
coefficient. The witness is `1`. -/
theorem collatz_quantitative_natural_density_descent_exists_constant
    {a : ℝ} (ha0 : 0 < a) (ha : a < admissibleExponent) :
    ∃ C : ℝ, 0 < C ∧
      NaturalDensityOne (quantitativeDescentSet a C) :=
  ⟨1, zero_lt_one,
    collatz_quantitative_natural_density_descent ha0 ha⟩

/-- The literal qualitative diagonal-descent statement. -/
def DiagonalDescentStatement : Prop :=
  ∃ eps : ℕ → ℝ,
    (∀ n, 0 < eps n) ∧
      Antitone eps ∧
      Filter.Tendsto eps Filter.atTop (nhds 0) ∧
      NaturalDensityOne
        {n | (collatzMin n : ℝ) ≤ (n : ℝ) ^ eps n}

/-- **Proposition A (referee-facing form).** There is a positive
non-increasing exponent tending to zero for which the literal Collatz orbit
minimum obeys `T_min(n) ≤ n ^ eps(n)` on a natural-density-one set. -/
theorem collatz_diagonal_natural_density_descent :
    DiagonalDescentStatement := by
  obtain ⟨eps, heps0, hepsAnti, hepsLim, hA⟩ :=
    QuantitativeDensity.quantitativeQuadraticPropositionA
  refine ⟨eps, heps0, hepsAnti, hepsLim, ?_⟩
  rw [naturalDensityOne_iff_internal]
  apply QuantitativeDensity.hasNaturalDensityOne_mono
    (S := QuantitativeDensity.propositionASet eps)
    (U := {n | (collatzMin n : ℝ) ≤ (n : ℝ) ^ eps n}) ?_ hA
  intro n hn
  change (collatzMin n : ℝ) ≤ (n : ℝ) ^ eps n
  rw [collatzMin_eq_terras]
  exact hn

end

end QuantitativeCollatzMain

end CollatzEndpointTransport
