/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik
-/
import CollatzEndpointTransport.Common.TerrasOrbitEnvelope

/-!
# Terras Initial Window

Definitions shared by the maximal-barrier initial logarithmic window.

The former prefix-union proof of the same window has been removed.  The
stronger retained proof is `TerrasMaximalInitialWindow.lean`.
-/

namespace CollatzEndpointTransport

namespace Terras

open Nat Finset
open scoped Real

/-- Two-sided parity regularity over the horizon interval `[k0,M]`. -/
def PrefixTwoSidedRegular (n k0 M : ℕ) (eta : ℝ) : Prop :=
  ∀ H : ℕ, k0 ≤ H → H ≤ M →
    |(oddCount H n : ℝ) - (H : ℝ) / 2| ≤ eta * H

/-- Points in shell `M` where the two-sided initial-window orbit envelope
fails at some time `k ≤ M`. -/
noncomputable def shellInitialWindowBad (M : ℕ) (t : ℝ) : Finset ℕ :=
  (Finset.Ico (2 ^ M) (2 ^ (M + 1))).filter
    (fun n =>
      ∃ k : ℕ, k ≤ M ∧
        (((T^[k]) n : ℝ) <
            centralOrbitScale k * (n : ℝ) ^ (1 - t) ∨
          centralOrbitScale k * (n : ℝ) ^ (1 + t) <
            ((T^[k]) n : ℝ)))

end Terras

end CollatzEndpointTransport
