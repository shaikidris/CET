/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik
-/
import CollatzEndpointTransport.Common.AffineCorrection
import CollatzEndpointTransport.Common.ShellToGlobalDensity

/-!
# Affine Correction Density

Retained affine-correction predicate and dyadic-shell scale bridge.

The old standalone prefix-union density estimate was superseded by the
maximal-barrier initial-window theorem.  These two declarations remain live in
the fixed-total pullback and quadratic companion interfaces.
-/

namespace CollatzEndpointTransport

namespace Terras

open Nat Finset
open scoped Real

noncomputable section

/-- Global set on which every correction time up to the dyadic scale of `n`
satisfies the target bound. -/
def affineCorrectionGood (t : ℝ) : Set ℕ :=
  {n | ∀ k : ℕ, k ≤ Nat.log 2 n →
    affineCorrection k n * (3 : ℝ) ^ ((k : ℝ) / 2) < (n : ℝ) ^ t}

/-- The dyadic scale of every member of shell `M` is exactly `M`. -/
theorem log_two_eq_of_mem_dyadicShell
    {n M : ℕ} (hn : n ∈ QuantitativeDensity.dyadicShell M) :
    Nat.log 2 n = M := by
  rw [QuantitativeDensity.dyadicShell, Finset.mem_Ico] at hn
  exact Nat.log_eq_of_pow_le_of_lt_pow hn.1 hn.2

end


end Terras

end CollatzEndpointTransport
