/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik
-/
import CollatzEndpointTransport.Common.TerrasOrbitEnvelope

/-!
# Terras Orbit Minimum

The literal minimum of a Collatz orbit.

The main quantitative theorem was first stated using an existential iterate,
which is the most convenient proof interface.  This file packages the
well-ordering step showing that this is exactly the usual `T_min`.
-/

namespace CollatzEndpointTransport

namespace Terras

noncomputable section

def orbitValueExists (n : ℕ) :
    ∃ m : ℕ, ∃ k : ℕ, (T^[k]) n = m :=
  ⟨n, 0, rfl⟩

/-- The least value attained by the forward orbit of `n`. -/
def Tmin (n : ℕ) : ℕ := by
    classical
    exact Nat.find (orbitValueExists n)

theorem Tmin_attained (n : ℕ) :
    ∃ k : ℕ, (T^[k]) n = Tmin n := by
    classical
    exact Nat.find_spec (orbitValueExists n)

theorem Tmin_le_iterate (n k : ℕ) :
    Tmin n ≤ (T^[k]) n := by
    classical
    exact Nat.find_min' (orbitValueExists n) ⟨k, rfl⟩

/-- The literal minimum formulation is equivalent to an existential
iterate bound. -/
theorem Tmin_le_iff_exists_iterate_le
    (n B : ℕ) :
    Tmin n ≤ B ↔ ∃ k : ℕ, (T^[k]) n ≤ B := by
  constructor
  · intro h
    obtain ⟨k, hk⟩ := Tmin_attained n
    exact ⟨k, by simpa [hk] using h⟩
  · rintro ⟨k, hk⟩
    exact (Tmin_le_iterate n k).trans hk

/-- Real-valued version used by the quantitative endpoint. -/
theorem cast_Tmin_le_of_exists_iterate_cast_le
    {n : ℕ} {B : ℝ}
    (h : ∃ k : ℕ, (((T^[k]) n : ℕ) : ℝ) ≤ B) :
    (Tmin n : ℝ) ≤ B := by
  obtain ⟨k, hk⟩ := h
  exact (by exact_mod_cast Tmin_le_iterate n k : (Tmin n : ℝ) ≤ (T^[k]) n).trans hk

end

end Terras

end CollatzEndpointTransport
