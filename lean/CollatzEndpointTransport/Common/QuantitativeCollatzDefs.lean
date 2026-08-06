/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik
-/
import CollatzEndpointTransport.Common.TerrasOrbitMinimum
import CollatzEndpointTransport.Common.VaryingShellDensity

/-!
# Quantitative Collatz Defs

Shared referee-facing definitions for the quantitative Collatz theorems.

This module is intentionally independent of either the quadratic or linear
bootstrap.  It exposes the literal half-Collatz map, its attained orbit
minimum, and the natural-density-one predicate used by both public theorem
files.
-/

namespace CollatzEndpointTransport

namespace QuantitativeCollatzMain

open scoped Real Topology

noncomputable section

/-- The half-Collatz map used in the paper:
`n / 2` for even `n`, and `(3n + 1) / 2` for odd `n`. -/
def collatz (n : ℕ) : ℕ :=
  if n % 2 = 0 then n / 2 else (3 * n + 1) / 2

/-- The `k`-th iterate of the explicitly defined half-Collatz map. -/
def collatzIter (k n : ℕ) : ℕ :=
  (collatz^[k]) n

/-- The Collatz orbit of every starting value contains at least one value. -/
theorem collatzOrbitValueExists (n : ℕ) :
    ∃ m : ℕ, ∃ k : ℕ, collatzIter k n = m :=
  ⟨n, 0, rfl⟩

/-- The literal minimum value attained by the forward Collatz orbit. -/
def collatzMin (n : ℕ) : ℕ := by
    classical
    exact Nat.find (collatzOrbitValueExists n)

theorem collatz_eq_terras (n : ℕ) :
    collatz n = Terras.T n := by
  rfl

theorem collatzIter_eq_terras (k n : ℕ) :
    collatzIter k n = (Terras.T^[k]) n := by
  rfl

/-- The public orbit minimum is attained by an actual Collatz iterate. -/
theorem collatzMin_attained (n : ℕ) :
    ∃ k : ℕ, collatzIter k n = collatzMin n := by
  classical
  exact Nat.find_spec (collatzOrbitValueExists n)

theorem collatzMin_le_iterate (n k : ℕ) :
    collatzMin n ≤ collatzIter k n := by
  classical
  exact Nat.find_min' (collatzOrbitValueExists n) ⟨k, rfl⟩

/-- The public orbit minimum agrees with the minimum used internally. -/
theorem collatzMin_eq_terras (n : ℕ) :
    collatzMin n = Terras.Tmin n := by
  apply le_antisymm
  · obtain ⟨k, hk⟩ := Terras.Tmin_attained n
    calc
      collatzMin n ≤ collatzIter k n := collatzMin_le_iterate n k
      _ = Terras.Tmin n := by simpa [collatzIter] using hk
  · obtain ⟨k, hk⟩ := collatzMin_attained n
    calc
      Terras.Tmin n ≤ (Terras.T^[k]) n := Terras.Tmin_le_iterate n k
      _ = collatzMin n := by simpa [collatzIter] using hk

/-- The literal-minimum inequality is exactly an existential iterate
inequality for the explicitly defined Collatz map. -/
theorem collatzMin_le_iff_exists_iterate_le (n B : ℕ) :
    collatzMin n ≤ B ↔ ∃ k : ℕ, collatzIter k n ≤ B := by
  constructor
  · intro h
    obtain ⟨k, hk⟩ := collatzMin_attained n
    exact ⟨k, by simpa [hk] using h⟩
  · rintro ⟨k, hk⟩
    exact (collatzMin_le_iterate n k).trans hk

/-- A set has natural density one when the proportion of its complement in
`[1,N]` tends to zero. Membership of `0` is irrelevant. -/
def NaturalDensityOne (S : Set ℕ) : Prop := by
    classical
    exact
      Filter.Tendsto
        (fun N : ℕ =>
          ((((Finset.Icc 1 N).filter (fun n => n ∉ S)).card : ℕ) : ℝ) / N)
        Filter.atTop (nhds 0)

theorem naturalDensityOne_iff_internal {S : Set ℕ} :
    NaturalDensityOne S ↔
      QuantitativeDensity.HasNaturalDensityOne S := by
  unfold NaturalDensityOne QuantitativeDensity.HasNaturalDensityOne
  unfold QuantitativeDensity.badPrefix QuantitativeDensity.positivePrefix
  rfl

end

end QuantitativeCollatzMain

end CollatzEndpointTransport
