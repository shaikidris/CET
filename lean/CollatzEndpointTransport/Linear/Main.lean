/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik
-/
import CollatzEndpointTransport.Linear.OptimizedLinearExceptionalCount
import CollatzEndpointTransport.Linear.EndpointOnlyParameterChoice
import CollatzEndpointTransport.Linear.CentralRenyiEndpointOnly
import CollatzEndpointTransport.Linear.EndpointOnlyFixedPower
import CollatzEndpointTransport.Linear.FirstPassageLaws
import CollatzEndpointTransport.Common.QuantitativeCollatzDefs

/-!
# Referee-facing linear API

Referee-facing API for the central higher-Renyi endpoint-only Collatz theorem.

The statements in this file mention only the literal half-Collatz map, its
orbit minimum, natural density one, and explicit exponent endpoints.  The
central endpoint-only theorem is primary; the critical-moment endpoint theorem
and the full-envelope theorem are retained as companion results. All
fixed-total coding, endpoint moments, nonlinear pullback estimates, and
bootstrap schedules remain behind the imported implementation.

The uniform quantitative first-passage profile and its limit laws are proved
in the dedicated module
`CollatzEndpointTransport.Linear.FirstPassageLaws` and re-exported here. The
first-passage module depends only on the full-envelope implementation and the
common natural-density API, so the public import direction follows the
mathematical dependency graph.
-/

namespace CollatzEndpointTransport

namespace QuantitativeCollatzMain

open scoped Real Topology

noncomputable section

/-- The optimized fixed-total exponent for the full-envelope companion. It equals
`0.06134085341...`; the exact expression is proved by
`linearAdmissibleExponent_eq_paper`. -/
def linearAdmissibleExponent : ℝ :=
  OptimizedLinearPullback.linearHeadlineExponent

theorem linearAdmissibleExponent_pos :
    0 < linearAdmissibleExponent :=
  OptimizedLinearPullback.linearHeadlineExponent_pos

theorem linearAdmissibleExponent_eq_paper :
    linearAdmissibleExponent =
      1 /
        (3 +
          Real.log
              (1 /
                (OptimizedLinearPullback.asymptoticRateLimit *
                  OptimizedLinearPullback.linearKappaLimit ^ 2)) /
            Real.log (1 / QuantitativeDensity.a0)) :=
  OptimizedLinearPullback.linearHeadlineExponent_eq_paper

/-- The stronger exponent available when only logarithmic-block endpoints
are iterated.  Unlike `linearAdmissibleExponent`, this constant does not
pay for a shrinking two-sided envelope between block endpoints. -/
def endpointOnlyAdmissibleExponent : ℝ :=
  OptimizedLinearPullback.endpointHeadlineExponent

theorem endpointOnlyAdmissibleExponent_pos :
    0 < endpointOnlyAdmissibleExponent :=
  OptimizedLinearPullback.endpointHeadlineExponent_pos

theorem endpointOnlyAdmissibleExponent_eq_paper :
    endpointOnlyAdmissibleExponent =
      Real.log (1 / QuantitativeDensity.a0) /
        Real.log (3 / QuantitativeDensity.a0) :=
  OptimizedLinearPullback.endpointHeadlineExponent_eq

/-- The main endpoint-only exponent obtained from the full central
higher-Renyi range `1/2 < theta < 1`. Numerically this is
`0.251245530155874...`. -/
def centralRenyiEndpointAdmissibleExponent : ℝ :=
  OptimizedLinearPullback.centralRenyiEndpointHeadlineExponent

theorem centralRenyiEndpointAdmissibleExponent_pos :
    0 < centralRenyiEndpointAdmissibleExponent :=
  OptimizedLinearPullback.centralRenyiEndpointHeadlineExponent_pos

theorem centralRenyiEndpointAdmissibleExponent_eq_paper :
    centralRenyiEndpointAdmissibleExponent =
      Real.log (1 / QuantitativeDensity.a0) /
        Real.log (2 / QuantitativeDensity.a0) :=
  OptimizedLinearPullback.centralRenyiEndpointHeadlineExponent_eq

/-- The literal stretched-logarithmic descent event used by the Main Theorem
and its full-envelope companion. -/
def stretchedLogDescentSet (delta C : ℝ) : Set ℕ :=
  {n |
    (collatzMin n : ℝ) ≤
      Real.exp (C * (Real.log n) ^ (1 - delta))}

/-- The full-envelope companion's descent event with an explicit iterate
witness. -/
def stretchedLogTimedDescentSet (delta C : ℝ) : Set ℕ :=
  {n | ∃ k : ℕ,
    (k : ℝ) ≤
        Real.log n /
          (QuantitativeDensity.bConst * Real.log 2) ∧
      (k : ℝ) < (6953 / 1000 : ℝ) * Real.log n ∧
      (collatzIter k n : ℝ) ≤
        Real.exp (C * (Real.log n) ^ (1 - delta))}

/-- The endpoint-only timed event.  Its witness has the same explicit
`6.953 * log n` bound, but it does not assert the sharper full-envelope
horizon inequality. -/
def stretchedLogEndpointTimedDescentSet (delta C : ℝ) : Set ℕ :=
  {n | ∃ k : ℕ,
    (k : ℝ) < (6953 / 1000 : ℝ) * Real.log n ∧
      (collatzIter k n : ℝ) ≤
        Real.exp (C * (Real.log n) ^ (1 - delta))}

/-- Literal fixed-power orbit-minimum event used by the quantitative
fixed-power corollary. -/
def fixedPowerDescentSet (alpha K : ℝ) : Set ℕ :=
  {n | n = 0 ∨ (collatzMin n : ℝ) ≤ K * (n : ℝ) ^ alpha}

/-- The explicit exponent in the subpower form of the endpoint theorem. The
clamp only totalizes the formula at the finite initial values outside the
paper's positive-integer asymptotic range. -/
def explicitSubpowerExponent (delta : ℝ) (n : ℕ) : ℝ :=
  (Real.log ((max n 2 : ℕ) : ℝ)) ^ (-delta)

/-- Literal positive-integer event for the explicit subpower form. The disjunct at
`n = 0` reflects that natural-density prefixes count only `1 ≤ n ≤ N`. -/
def explicitSubpowerDescentSet (delta : ℝ) : Set ℕ :=
  {n | n = 0 ∨
    (collatzMin n : ℝ) ≤ (n : ℝ) ^ explicitSubpowerExponent delta n}

theorem explicitSubpowerExponent_pos
    (delta : ℝ) (n : ℕ) :
    0 < explicitSubpowerExponent delta n := by
  apply Real.rpow_pos_of_pos
  apply Real.log_pos
  exact_mod_cast (show 1 < max n 2 by omega)

theorem explicitSubpowerExponent_antitone
    {delta : ℝ} (hdelta : 0 ≤ delta) :
    Antitone (explicitSubpowerExponent delta) := by
  intro n m hnm
  apply Real.rpow_le_rpow_of_exponent_nonpos
  · apply Real.log_pos
    exact_mod_cast (show 1 < max n 2 by omega)
  · apply Real.strictMonoOn_log.monotoneOn
    · exact Set.mem_Ioi.mpr <| by positivity
    · exact Set.mem_Ioi.mpr <| by positivity
    · exact_mod_cast max_le_max hnm (le_refl 2)
  · exact neg_nonpos.mpr hdelta

theorem explicitSubpowerExponent_tendsto_zero
    {delta : ℝ} (hdelta : 0 < delta) :
    Filter.Tendsto (explicitSubpowerExponent delta)
      Filter.atTop (nhds 0) := by
  have hlog :
      Filter.Tendsto (fun n : ℕ => Real.log (n : ℝ))
        Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hpow := (tendsto_rpow_neg_atTop hdelta).comp hlog
  apply hpow.congr'
  filter_upwards [Filter.eventually_ge_atTop 2] with n hn
  simp [explicitSubpowerExponent, max_eq_left hn]

theorem explicitSubpowerExponent_eventually_eq
    (delta : ℝ) :
    ∀ᶠ n : ℕ in Filter.atTop,
      explicitSubpowerExponent delta n = (Real.log n) ^ (-delta) := by
  filter_upwards [Filter.eventually_ge_atTop 2] with n hn
  simp [explicitSubpowerExponent, max_eq_left hn]

theorem internalLinearDescentSet_subset_stretchedLogDescentSet
    (delta C : ℝ) :
    OptimizedLinearPullback.quantitativeLinearDescentSet delta C ⊆
      stretchedLogDescentSet delta C := by
  intro n hn
  obtain ⟨k, hk⟩ := hn
  change (collatzMin n : ℝ) ≤
    Real.exp (C * (Real.log n) ^ (1 - delta))
  rw [collatzMin_eq_terras]
  exact Terras.cast_Tmin_le_of_exists_iterate_cast_le ⟨k, hk⟩

/-- **Full-envelope companion (coefficient-one form).** For every positive
exponent below the full-envelope endpoint, the literal Collatz orbit minimum
satisfies the stretched-logarithmic bound on a set of natural density one. -/
theorem collatz_stretched_log_natural_density_descent
    {delta : ℝ}
    (hdelta0 : 0 < delta)
    (hdelta : delta < linearAdmissibleExponent) :
    NaturalDensityOne (stretchedLogDescentSet delta 1) := by
  have hinternal :
      QuantitativeDensity.HasNaturalDensityOne
        (OptimizedLinearPullback.quantitativeLinearDescentSet delta 1) :=
    OptimizedLinearPullback.quantitativeLinearDescent_one
      hdelta0 hdelta
  rw [naturalDensityOne_iff_internal]
  apply OptimizedLinearPullback.linearHasNaturalDensityOne_mono
    (S := OptimizedLinearPullback.quantitativeLinearDescentSet delta 1)
    (U := stretchedLogDescentSet delta 1) ?_ hinternal
  exact internalLinearDescentSet_subset_stretchedLogDescentSet delta 1

/-- **Critical-moment endpoint-only baseline.** Direct logarithmic-block
endpoint iteration gives the coefficient-one natural-density-one statement
for every exponent below `endpointOnlyAdmissibleExponent = 0.1747195431...`.
-/
theorem collatz_endpoint_only_natural_density_descent
    {delta : ℝ}
    (hdelta0 : 0 < delta)
    (hdelta : delta < endpointOnlyAdmissibleExponent) :
    NaturalDensityOne (stretchedLogDescentSet delta 1) := by
  have hinternal :
      QuantitativeDensity.HasNaturalDensityOne
        (OptimizedLinearPullback.quantitativeLinearDescentSet delta 1) :=
    OptimizedLinearPullback.endpointOnlyTheorem_one
      hdelta0 hdelta
  rw [naturalDensityOne_iff_internal]
  apply OptimizedLinearPullback.linearHasNaturalDensityOne_mono
    (S := OptimizedLinearPullback.quantitativeLinearDescentSet delta 1)
    (U := stretchedLogDescentSet delta 1) ?_ hinternal
  exact internalLinearDescentSet_subset_stretchedLogDescentSet delta 1

/-- **Main Theorem.** The central higher-Renyi fixed-total estimate raises
the coefficient-one natural-density-one range to every exponent below
`log(1/a0) / log(2/a0) = 0.251245530155874...`. -/
theorem collatz_central_renyi_endpoint_natural_density_descent
    {delta : ℝ}
    (hdelta0 : 0 < delta)
    (hdelta : delta < centralRenyiEndpointAdmissibleExponent) :
    NaturalDensityOne (stretchedLogDescentSet delta 1) := by
  have hinternal :
      QuantitativeDensity.HasNaturalDensityOne
        (OptimizedLinearPullback.quantitativeLinearDescentSet delta 1) :=
    OptimizedLinearPullback.centralRenyiEndpointOnlyTheorem_one
      hdelta0 hdelta
  rw [naturalDensityOne_iff_internal]
  apply OptimizedLinearPullback.linearHasNaturalDensityOne_mono
    (S := OptimizedLinearPullback.quantitativeLinearDescentSet delta 1)
    (U := stretchedLogDescentSet delta 1) ?_ hinternal
  exact internalLinearDescentSet_subset_stretchedLogDescentSet delta 1

theorem stretchedLogDescentSet_subset_explicitSubpowerDescentSet
    {delta : ℝ} :
    stretchedLogDescentSet delta 1 ⊆
      explicitSubpowerDescentSet delta := by
  intro n hn
  by_cases hn0 : n = 0
  · exact Or.inl hn0
  right
  by_cases hn2 : 2 ≤ n
  · have hnR : 0 < (n : ℝ) := by exact_mod_cast Nat.zero_lt_of_ne_zero hn0
    have hlog : 0 < Real.log (n : ℝ) := by
      exact Real.log_pos (by exact_mod_cast (show 1 < n by omega))
    have hrewrite :
        (n : ℝ) ^ explicitSubpowerExponent delta n =
          Real.exp ((Real.log n) ^ (1 - delta)) := by
      rw [explicitSubpowerExponent, max_eq_left hn2,
        Real.rpow_def_of_pos hnR]
      congr 1
      rw [show 1 - delta = 1 + (-delta) by ring,
        Real.rpow_add hlog]
      simp
    rw [hrewrite]
    simpa [stretchedLogDescentSet] using hn
  · have hn1 : n = 1 := by omega
    subst n
    have hmin : collatzMin 1 ≤ 1 := by
      simpa [collatzIter] using collatzMin_le_iterate 1 0
    have hminR : (collatzMin 1 : ℝ) ≤ 1 := by exact_mod_cast hmin
    simpa using hminR

/-- **Explicit subpower form of the endpoint theorem.** The main result may be
written with the explicit positive antitone exponent
`(log n) ^ (-delta)` outside a finite initial interval. -/
theorem collatz_explicit_subpower_natural_density_descent
    {delta : ℝ}
    (hdelta0 : 0 < delta)
    (hdelta : delta < centralRenyiEndpointAdmissibleExponent) :
    NaturalDensityOne (explicitSubpowerDescentSet delta) := by
  rw [naturalDensityOne_iff_internal]
  apply OptimizedLinearPullback.linearHasNaturalDensityOne_mono
    (S := stretchedLogDescentSet delta 1)
    (U := explicitSubpowerDescentSet delta)
    stretchedLogDescentSet_subset_explicitSubpowerDescentSet
  rw [← naturalDensityOne_iff_internal]
  exact collatz_central_renyi_endpoint_natural_density_descent
    hdelta0 hdelta

/-- Certified twelve-decimal corollary of the Main Theorem. The strict
comparison with the exact endpoint is proved from rational Taylor bounds for
the logarithm. -/
theorem collatz_central_renyi_endpoint_decimal_natural_density_descent
    {delta : ℝ}
    (hdelta0 : 0 < delta)
    (hdelta : delta < (251245530155 / 10 ^ 12 : ℝ)) :
    NaturalDensityOne (stretchedLogDescentSet delta 1) :=
  collatz_central_renyi_endpoint_natural_density_descent hdelta0
    (hdelta.trans
      OptimizedLinearPullback.centralRenyiEndpointDecimal_lt_headline)

/-- **Main-theorem exceptional count.** Throughout the full central
higher-Renyi range, the complement has a stretched-exponential prefix
majorant with some positive exponent `sigma`. -/
theorem collatz_central_renyi_endpoint_exceptional_count
    {delta : ℝ}
    (hdelta0 : 0 < delta)
    (hdelta : delta < centralRenyiEndpointAdmissibleExponent) :
    ∃ sigma c : ℝ,
      0 < sigma ∧ sigma ≤ 1 ∧ 0 < c ∧
      ∀ᶠ N : ℕ in Filter.atTop,
        ((QuantitativeDensity.badPrefix
          (stretchedLogDescentSet delta 1) N).card : ℝ) ≤
          5 * N * Real.exp (-c * (Real.log N) ^ sigma) := by
  obtain ⟨sigma, c, hsigma0, hsigma1, hc0, hcount⟩ :=
    OptimizedLinearPullback.centralRenyiEndpointOnlyTheorem_exceptional_count
      hdelta0 hdelta
  refine ⟨sigma, c, hsigma0, hsigma1, hc0, ?_⟩
  filter_upwards [hcount] with N hN
  have hsub :
      QuantitativeDensity.badPrefix
          (stretchedLogDescentSet delta 1) N ⊆
        QuantitativeDensity.badPrefix
          (OptimizedLinearPullback.quantitativeLinearDescentSet delta 1) N := by
    intro n hn
    simp only [QuantitativeDensity.badPrefix,
      Finset.mem_filter] at hn ⊢
    exact ⟨hn.1, fun hgood =>
      hn.2 (internalLinearDescentSet_subset_stretchedLogDescentSet
        delta 1 hgood)⟩
  have hcard :
      ((QuantitativeDensity.badPrefix
        (stretchedLogDescentSet delta 1) N).card : ℝ) ≤
      ((QuantitativeDensity.badPrefix
        (OptimizedLinearPullback.quantitativeLinearDescentSet delta 1)
        N).card : ℝ) := by
    exact_mod_cast Finset.card_le_card hsub
  exact hcard.trans hN

/-- **Optimized Main-theorem exceptional count.** Every exponent below
`1 - delta / centralRenyiEndpointAdmissibleExponent` is available in the
stretched-exponential prefix majorant. -/
theorem collatz_central_renyi_endpoint_exceptional_count_at_exponent
    {delta sigma : ℝ}
    (hdelta0 : 0 < delta)
    (hdelta : delta < centralRenyiEndpointAdmissibleExponent)
    (hsigma0 : 0 < sigma)
    (hsigma :
      sigma < 1 - delta / centralRenyiEndpointAdmissibleExponent) :
    ∃ c : ℝ,
      0 < c ∧
      ∀ᶠ N : ℕ in Filter.atTop,
        ((QuantitativeDensity.badPrefix
          (stretchedLogDescentSet delta 1) N).card : ℝ) ≤
          5 * N * Real.exp (-c * (Real.log N) ^ sigma) := by
  obtain ⟨c, hc0, hcount⟩ :=
    OptimizedLinearPullback.centralRenyiEndpointOnlyTheorem_exceptional_count_at_exponent
      hdelta0 hdelta hsigma0 hsigma
  refine ⟨c, hc0, ?_⟩
  filter_upwards [hcount] with N hN
  have hsub :
      QuantitativeDensity.badPrefix
          (stretchedLogDescentSet delta 1) N ⊆
        QuantitativeDensity.badPrefix
          (OptimizedLinearPullback.quantitativeLinearDescentSet delta 1) N := by
    intro n hn
    simp only [QuantitativeDensity.badPrefix,
      Finset.mem_filter] at hn ⊢
    exact ⟨hn.1, fun hgood =>
      hn.2 (internalLinearDescentSet_subset_stretchedLogDescentSet
        delta 1 hgood)⟩
  have hcard :
      ((QuantitativeDensity.badPrefix
        (stretchedLogDescentSet delta 1) N).card : ℝ) ≤
      ((QuantitativeDensity.badPrefix
        (OptimizedLinearPullback.quantitativeLinearDescentSet delta 1)
        N).card : ℝ) := by
    exact_mod_cast Finset.card_le_card hsub
  exact hcard.trans hN

/-- **Timed Main Theorem.** Throughout the full central higher-Renyi range,
the coefficient-one descent is witnessed by an actual iterate before
`6.953 * log n`. -/
theorem collatz_central_renyi_endpoint_natural_density_descent_timed
    {delta : ℝ}
    (hdelta0 : 0 < delta)
    (hdelta : delta < centralRenyiEndpointAdmissibleExponent) :
    NaturalDensityOne (stretchedLogEndpointTimedDescentSet delta 1) := by
  rw [naturalDensityOne_iff_internal]
  simpa [stretchedLogEndpointTimedDescentSet,
    OptimizedLinearPullback.quantitativeEndpointTimedDescentSet,
    collatzIter] using
    OptimizedLinearPullback.centralRenyiEndpointOnlyTheorem_timed
      hdelta0 hdelta

/-- **Timed Main-Theorem exceptional count.** The set of integers up to `N`
for which no coefficient-one descent witness occurs before `6.953 * log n`
has a stretched-exponential prefix majorant. -/
theorem collatz_central_renyi_endpoint_timed_exceptional_count
    {delta : ℝ}
    (hdelta0 : 0 < delta)
    (hdelta : delta < centralRenyiEndpointAdmissibleExponent) :
    ∃ sigma c : ℝ,
      0 < sigma ∧ sigma ≤ 1 ∧ 0 < c ∧
      ∀ᶠ N : ℕ in Filter.atTop,
        ((QuantitativeDensity.badPrefix
          (stretchedLogEndpointTimedDescentSet delta 1) N).card : ℝ) ≤
          5 * N * Real.exp (-c * (Real.log N) ^ sigma) := by
  simpa [stretchedLogEndpointTimedDescentSet,
    OptimizedLinearPullback.quantitativeEndpointTimedDescentSet,
    collatzIter] using
    OptimizedLinearPullback.centralRenyiEndpointOnlyTheorem_timed_exceptional_count
      hdelta0 hdelta

/-- **Power-saving fixed-power descent.** For every `beta` above the
reciprocal Main-Theorem endpoint, the power constant and density coefficient
are uniform over `0 < alpha < 1`; only the density prefactor depends on
`alpha`. -/
theorem collatz_central_renyi_fixed_power_density
    {beta : ℝ}
    (hbeta : centralRenyiEndpointAdmissibleExponent⁻¹ < beta) :
    ∃ K c : ℝ,
      0 < K ∧ 0 < c ∧
      ∀ alpha : ℝ, 0 < alpha → alpha < 1 →
        ∃ C : ℝ, 0 < C ∧
          QuantitativeDensity.IsCDDense
            (fixedPowerDescentSet alpha K) C (c * alpha ^ beta) := by
  have hbeta' :
      OptimizedLinearPullback.fixedPowerDensityExponentLimit < beta := by
    rw [OptimizedLinearPullback.fixedPowerDensityExponentLimit_eq]
    exact hbeta
  obtain ⟨K, c, hK, hc, hdense⟩ :=
    OptimizedLinearPullback.centralRenyi_fixedPower_density hbeta'
  refine ⟨K, c, hK, hc, ?_⟩
  intro alpha ha0 ha1
  obtain ⟨C, hC, hset⟩ := hdense alpha ha0 ha1
  refine ⟨C, hC, ?_⟩
  simpa [fixedPowerDescentSet,
    OptimizedLinearPullback.endpointFixedPowerSet,
    collatzMin_eq_terras] using hset

/-- **Companion exceptional-count corollary.** The complement of the
full-envelope theorem has a quantitative
stretched-exponential prefix bound whose exponent is strictly larger than
the orbit exponent `delta`. -/
theorem collatz_stretched_log_exceptional_count
    {delta : ℝ}
    (hdelta0 : 0 < delta)
    (hdelta : delta < linearAdmissibleExponent) :
    ∃ sigma c : ℝ,
      delta < sigma ∧ sigma ≤ 1 ∧ 0 < c ∧
      ∀ᶠ N : ℕ in Filter.atTop,
        ((QuantitativeDensity.badPrefix
          (stretchedLogDescentSet delta 1) N).card : ℝ) ≤
          5 * N * Real.exp (-c * (Real.log N) ^ sigma) := by
  obtain ⟨sigma, c, hsigma, hsigma1, hc, hcount⟩ :=
    OptimizedLinearPullback.quantitativeLinearDescent_exceptional_count
      hdelta0 hdelta
  refine ⟨sigma, c, hsigma, hsigma1, hc, ?_⟩
  filter_upwards [hcount] with N hN
  have hsub :
      QuantitativeDensity.badPrefix
          (stretchedLogDescentSet delta 1) N ⊆
        QuantitativeDensity.badPrefix
          (OptimizedLinearPullback.quantitativeLinearDescentSet delta 1) N := by
    intro n hn
    simp only [QuantitativeDensity.badPrefix,
      Finset.mem_filter] at hn ⊢
    exact ⟨hn.1, fun hgood =>
      hn.2 (internalLinearDescentSet_subset_stretchedLogDescentSet
        delta 1 hgood)⟩
  have hcard :
      ((QuantitativeDensity.badPrefix
        (stretchedLogDescentSet delta 1) N).card : ℝ) ≤
      ((QuantitativeDensity.badPrefix
        (OptimizedLinearPullback.quantitativeLinearDescentSet delta 1)
        N).card : ℝ) := by
    exact_mod_cast Finset.card_le_card hsub
  exact hcard.trans hN

/-- **Timed full-envelope companion.** The coefficient-one
stretched-logarithmic descent is witnessed by an actual iterate before
`6.953 * log n`. -/
theorem collatz_stretched_log_natural_density_descent_timed
    {delta : ℝ}
    (hdelta0 : 0 < delta)
    (hdelta : delta < linearAdmissibleExponent) :
    NaturalDensityOne (stretchedLogTimedDescentSet delta 1) := by
  rw [naturalDensityOne_iff_internal]
  simpa [stretchedLogTimedDescentSet,
    OptimizedLinearPullback.quantitativeTimedLinearDescentSet,
    collatzIter] using
    OptimizedLinearPullback.quantitativeLinearDescent_timed
      hdelta0 hdelta

/-- The full-envelope companion's existential-constant formulation follows
from its stronger coefficient-one theorem. -/
theorem collatz_stretched_log_natural_density_descent_exists_constant
    {delta : ℝ}
    (hdelta0 : 0 < delta)
    (hdelta : delta < linearAdmissibleExponent) :
    ∃ C : ℝ, 0 < C ∧
      NaturalDensityOne (stretchedLogDescentSet delta C) :=
  ⟨1, by norm_num,
    collatz_stretched_log_natural_density_descent hdelta0 hdelta⟩

end

end QuantitativeCollatzMain

end CollatzEndpointTransport
