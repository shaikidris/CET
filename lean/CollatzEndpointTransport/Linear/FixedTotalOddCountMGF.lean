/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik
-/
import CollatzEndpointTransport.Linear.FixedTotalShellCoding
import Mathlib.Data.Nat.Choose.Sum

/-!
# Fixed Total Odd Count MGF

Exact odd-count generating function for the fixed-total shell coding.

This is the nonlinear-rate input.  It is an identity, not a concentration
estimate:

  sum_x q^(oddCount x) = (1 + q)^M.

After division by `2^M`, substituting `q = 3^(-D)` produces the rate
`psi(D) = -log ((1 + 3^(-D))/2)`.
-/

namespace CollatzEndpointTransport

namespace FixedTotal

open Nat Finset

noncomputable section

/-- Source codes at a fixed odd-count level. -/
def sourceOddLevel (M s : ℕ) : Finset (SourceCode M) :=
  Finset.univ.filter fun x => sourceCodeOddCount x = s

theorem sourceCodeOddCount_le
    {M : ℕ} (x : SourceCode M) :
    sourceCodeOddCount x ≤ M := by
  rw [← listOddCount_sourceCodeList]
  have hle :
      listOddCount (sourceCodeList x) ≤
        (sourceCodeList x).length := by
    induction sourceCodeList x with
    | nil => simp
    | cons b bs ih =>
        cases b <;> simp [listOddCount_cons, ih] <;> omega
  simpa [sourceCodeList_length] using hle

/-- The exact binomial cardinality of a source-code odd-count level. -/
theorem card_sourceOddLevel
    (M s : ℕ) :
    (sourceOddLevel M s).card = M.choose s := by
  classical
  have hcard :
      (sourceOddLevel M s).card =
        (Finset.univ.filter
          (fun r : Fin (2 ^ M) =>
            Terras.oddCount M (r : ℕ) = s)).card := by
    apply Finset.card_bij
        (fun x _ => sourceCodeEquivResidue M x)
    · intro x hx
      simp only [sourceOddLevel, Finset.mem_filter,
        Finset.mem_univ, true_and] at hx ⊢
      simpa [oddCount_sourceCodeEquivResidue] using hx
    · intro x hx y hy hxy
      exact (sourceCodeEquivResidue M).injective hxy
    · intro r hr
      let x : SourceCode M :=
        (sourceCodeEquivResidue M).symm r
      refine ⟨x, ?_, ?_⟩
      · rw [sourceOddLevel, Finset.mem_filter]
        refine ⟨Finset.mem_univ _, ?_⟩
        have happly :
            sourceCodeEquivResidue M x = r :=
          (sourceCodeEquivResidue M).apply_symm_apply r
        have hrOdd :=
          (Finset.mem_filter.mp hr).2
        rw [← oddCount_sourceCodeEquivResidue M x, happly]
        exact hrOdd
      · exact (sourceCodeEquivResidue M).apply_symm_apply r
  rw [hcard, Terras.card_residues_with_oddCount]

/-- Exact shell odd-count moment-generating polynomial. -/
theorem sum_pow_sourceCodeOddCount
    (M : ℕ) (q : ℝ) :
    (∑ x : SourceCode M, q ^ sourceCodeOddCount x) =
      (1 + q) ^ M := by
  classical
  have hmap :
      ∀ x ∈ (Finset.univ : Finset (SourceCode M)),
        sourceCodeOddCount x ∈ Finset.range (M + 1) := by
    intro x hx
    exact Finset.mem_range.mpr
      (Nat.lt_succ_of_le (sourceCodeOddCount_le x))
  calc
    (∑ x : SourceCode M, q ^ sourceCodeOddCount x) =
        ∑ s ∈ Finset.range (M + 1),
          ∑ x ∈ sourceOddLevel M s,
            q ^ sourceCodeOddCount x := by
      symm
      simpa [sourceOddLevel] using
        (Finset.sum_fiberwise_of_maps_to
          (s := (Finset.univ : Finset (SourceCode M)))
          (t := Finset.range (M + 1))
          (g := sourceCodeOddCount)
          hmap
          (fun x => q ^ sourceCodeOddCount x))
    _ = ∑ s ∈ Finset.range (M + 1),
          (M.choose s : ℝ) * q ^ s := by
      apply Finset.sum_congr rfl
      intro s hs
      calc
        (∑ x ∈ sourceOddLevel M s,
            q ^ sourceCodeOddCount x) =
            ∑ _x ∈ sourceOddLevel M s, q ^ s := by
          apply Finset.sum_congr rfl
          intro x hx
          rw [(Finset.mem_filter.mp hx).2]
        _ = (sourceOddLevel M s).card * q ^ s := by simp
        _ = (M.choose s : ℝ) * q ^ s := by
          rw [card_sourceOddLevel]
    _ = (q + 1) ^ M := by
      rw [add_pow]
      apply Finset.sum_congr rfl
      intro s hs
      simp [mul_assoc, mul_left_comm, mul_comm]
    _ = (1 + q) ^ M := by ring

/-- Normalized exact odd-count generating function. -/
theorem average_pow_sourceCodeOddCount
    (M : ℕ) (q : ℝ) :
    (∑ x : SourceCode M, q ^ sourceCodeOddCount x) /
        (2 ^ M : ℝ) =
      ((1 + q) / 2) ^ M := by
  rw [sum_pow_sourceCodeOddCount]
  rw [div_pow]

end

end FixedTotal

end CollatzEndpointTransport
