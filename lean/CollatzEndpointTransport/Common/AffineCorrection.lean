/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik
-/
import CollatzEndpointTransport.Common.TerrasParityBijection

/-!
# Affine Correction

Exact affine-correction definitions for the half-Collatz iterate.

The retained maximal-barrier argument needs the correction itself, its
nonnegativity, and the elementary `0/1` parity-digit bounds.  The earlier
prefix-union correction envelope was superseded by the stronger uniform
geometric estimate in `TerrasAffineMaximalBarrier.lean`.
-/

namespace CollatzEndpointTransport

namespace Terras

open Nat Finset

/-- The `0/1` parity digit at time `i`, viewed in `ℝ`. -/
def parityDigitR (n i : ℕ) : ℝ :=
  if parityBit ((T^[i]) n) then 1 else 0

theorem parityDigitR_nonneg (n i : ℕ) : 0 ≤ parityDigitR n i := by
  cases h : parityBit ((T^[i]) n) <;> simp [parityDigitR, h]

theorem parityDigitR_le_one (n i : ℕ) : parityDigitR n i ≤ 1 := by
  cases h : parityBit ((T^[i]) n) <;> simp [parityDigitR, h]

/-- One summand of the affine correction. -/
noncomputable def affineCorrectionTerm (k n i : ℕ) : ℝ :=
  parityDigitR n i /
    ((3 : ℝ) ^ oddCount (i + 1) n * (2 : ℝ) ^ (k - i))

/-- The affine correction `r_k(n)`. -/
noncomputable def affineCorrection (k n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range k, affineCorrectionTerm k n i

theorem affineCorrectionTerm_nonneg (k n i : ℕ) :
    0 ≤ affineCorrectionTerm k n i := by
  unfold affineCorrectionTerm
  exact div_nonneg (parityDigitR_nonneg n i) (by positivity)

theorem affineCorrection_nonneg (k n : ℕ) :
    0 ≤ affineCorrection k n := by
  exact Finset.sum_nonneg fun i _ => affineCorrectionTerm_nonneg k n i

end Terras

end CollatzEndpointTransport
