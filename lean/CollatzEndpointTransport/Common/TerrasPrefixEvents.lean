/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik
-/
import Mathlib.Algebra.Order.Floor
import CollatzEndpointTransport.Common.TerrasShellRepetition

/-!
# Terras Prefix Events

Single-horizon Terras parity-tail events used by the fixed-total central-window
estimate.  The superseded union over all prefix horizons is intentionally not
retained.
-/

namespace CollatzEndpointTransport

namespace Terras

open Nat Finset

/-- Integer lower-tail cutoff corresponding to `(1/2 - t)H`. -/
noncomputable def parityLowerCutoff (t : ℝ) (H : ℕ) : ℕ :=
  ⌊(1 / 2 - t) * H⌋₊

theorem parityLowerCutoff_cast_le
    {t : ℝ} (htHalf : t ≤ 1 / 2) (H : ℕ) :
    (parityLowerCutoff t H : ℝ) ≤ (1 / 2 - t) * H := by
  exact Nat.floor_le
    (mul_nonneg (sub_nonneg.mpr htHalf) (Nat.cast_nonneg H))

/-- Lower-tail bad points at one prefix horizon. -/
noncomputable def shellLowerPrefixBad
    (M H : ℕ) (t : ℝ) : Finset ℕ :=
  (Finset.Ico (2 ^ M) (2 ^ (M + 1))).filter
    (fun n => oddCount H n ≤ parityLowerCutoff t H)

/-- Symmetric upper-tail bad points at one prefix horizon. -/
noncomputable def shellUpperPrefixBad
    (M H : ℕ) (t : ℝ) : Finset ℕ :=
  (Finset.Ico (2 ^ M) (2 ^ (M + 1))).filter
    (fun n => H - parityLowerCutoff t H ≤ oddCount H n)

/-- The two-sided bad parity event at one prefix horizon. -/
noncomputable def shellParityPrefixBadAt
    (M H : ℕ) (t : ℝ) : Finset ℕ :=
  shellLowerPrefixBad M H t ∪ shellUpperPrefixBad M H t

/-- One horizon contributes at most twice the one-sided Hoeffding tail. -/
theorem card_shellParityPrefixBadAt_le
    {M H : ℕ} {t : ℝ} (hHM : H ≤ M)
    (ht0 : 0 ≤ t) (htHalf : t ≤ 1 / 2) :
    ((shellParityPrefixBadAt M H t).card : ℝ) ≤
      (2 : ℝ) ^ M * (2 * Real.exp (-2 * t ^ 2 * H)) := by
  have hcut :
      (parityLowerCutoff t H : ℝ) ≤ (1 / 2 - t) * H :=
    parityLowerCutoff_cast_le htHalf H
  have hlower :
      ((shellLowerPrefixBad M H t).card : ℝ) ≤
        (2 : ℝ) ^ M * Real.exp (-2 * t ^ 2 * H) := by
    simpa only [shellLowerPrefixBad] using
      card_dyadic_shell_oddCount_le_hoeffding hHM ht0 hcut
  have hupper :
      ((shellUpperPrefixBad M H t).card : ℝ) ≤
        (2 : ℝ) ^ M * Real.exp (-2 * t ^ 2 * H) := by
    simpa only [shellUpperPrefixBad] using
      card_dyadic_shell_oddCount_ge_sub_le_hoeffding hHM ht0 hcut
  have hcardNat :
      (shellParityPrefixBadAt M H t).card ≤
        (shellLowerPrefixBad M H t).card +
          (shellUpperPrefixBad M H t).card := by
    exact Finset.card_union_le _ _
  have hcardReal :
      ((shellParityPrefixBadAt M H t).card : ℝ) ≤
        (shellLowerPrefixBad M H t).card +
          (shellUpperPrefixBad M H t).card := by
    exact_mod_cast hcardNat
  calc
    ((shellParityPrefixBadAt M H t).card : ℝ) ≤
        (shellLowerPrefixBad M H t).card +
          (shellUpperPrefixBad M H t).card := hcardReal
    _ ≤ (2 : ℝ) ^ M * Real.exp (-2 * t ^ 2 * H) +
          (2 : ℝ) ^ M * Real.exp (-2 * t ^ 2 * H) :=
      add_le_add hlower hupper
    _ = (2 : ℝ) ^ M * (2 * Real.exp (-2 * t ^ 2 * H)) := by ring

end Terras

end CollatzEndpointTransport
