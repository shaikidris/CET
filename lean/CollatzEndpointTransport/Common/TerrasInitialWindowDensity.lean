/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik
-/
import CollatzEndpointTransport.Common.AffineCorrectionDensity
import CollatzEndpointTransport.Common.TerrasInitialWindow

/-!
# Terras Initial Window Density

Global initial-window predicate and its exact dyadic-shell complement.

The quantitative density estimate is supplied by the stronger maximal-barrier
module `TerrasMaximalInitialWindowDensity.lean`.
-/

namespace CollatzEndpointTransport

namespace Terras

open Nat Finset
open scoped Real

noncomputable section

/-- Every time through the dyadic scale of `n` satisfies the two-sided orbit
envelope. -/
def initialWindowGood (t : ℝ) : Set ℕ :=
  {n | ∀ k : ℕ, k ≤ Nat.log 2 n →
    centralOrbitScale k * (n : ℝ) ^ (1 - t) ≤ ((T^[k]) n : ℝ) ∧
      ((T^[k]) n : ℝ) ≤
        centralOrbitScale k * (n : ℝ) ^ (1 + t)}

/-- The abstract shell complement of `initialWindowGood` is exactly the
finite-shell failure set. -/
theorem shellBad_initialWindowGood (t : ℝ) (M : ℕ) :
    QuantitativeDensity.shellBad (initialWindowGood t) M =
      shellInitialWindowBad M t := by
  classical
  ext n
  constructor
  · intro hn
    rw [QuantitativeDensity.shellBad, Finset.mem_filter] at hn
    have hlog := log_two_eq_of_mem_dyadicShell hn.1
    rw [initialWindowGood, Set.mem_setOf_eq] at hn
    push_neg at hn
    rcases hn.2 with ⟨k, hk, hfail⟩
    rw [shellInitialWindowBad, Finset.mem_filter]
    refine ⟨by simpa [QuantitativeDensity.dyadicShell] using hn.1, k, ?_, ?_⟩
    · simpa [hlog] using hk
    · by_cases hlower :
          centralOrbitScale k * (n : ℝ) ^ (1 - t) ≤ ((T^[k]) n : ℝ)
      · exact Or.inr (hfail hlower)
      · exact Or.inl (lt_of_not_ge hlower)
  · intro hn
    rw [shellInitialWindowBad, Finset.mem_filter] at hn
    have hnShell : n ∈ QuantitativeDensity.dyadicShell M := by
      simpa [QuantitativeDensity.dyadicShell] using hn.1
    have hlog := log_two_eq_of_mem_dyadicShell hnShell
    rw [QuantitativeDensity.shellBad, Finset.mem_filter]
    refine ⟨hnShell, ?_⟩
    rw [initialWindowGood, Set.mem_setOf_eq]
    push_neg
    rcases hn.2 with ⟨k, hk, hfail⟩
    refine ⟨k, by simpa [hlog] using hk, ?_⟩
    intro hlower
    rcases hfail with hfail | hfail
    · exact False.elim ((not_lt_of_ge hlower) hfail)
    · exact hfail

end


end Terras

end CollatzEndpointTransport
