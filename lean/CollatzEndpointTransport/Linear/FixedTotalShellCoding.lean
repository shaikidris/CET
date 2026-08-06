/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik
-/
import CollatzEndpointTransport.Linear.FixedTotalGlobalEndpointMoment
import CollatzEndpointTransport.Common.AffineCorrectionDensity
import CollatzEndpointTransport.Common.QuantitativePullbackDefs

/-!
# Fixed Total Shell Coding

Exact identification of the finite fixed-total source model with a dyadic
Collatz shell.

The source-code equivalence first chooses a residue modulo `2^M`; adding
`2^M` then gives the unique representative in `[2^M, 2^(M+1))`.  This file
packages that observation as an equivalence and transports endpoint-failure
counts to the concrete `collatzPullback` shell complement.
-/

namespace CollatzEndpointTransport

namespace FixedTotal

open Nat Finset

noncomputable section

/-- Adding `2^M` identifies residues modulo `2^M` with the `M`-th dyadic
shell. -/
noncomputable def residueEquivDyadicShell
    (M : ℕ) :
    Fin (2 ^ M) ≃
      {n // n ∈ QuantitativeDensity.dyadicShell M} where
  toFun r := by
    refine ⟨2 ^ M + (r : ℕ), ?_⟩
    unfold QuantitativeDensity.dyadicShell
    rw [Finset.mem_Ico]
    rw [pow_succ]
    omega
  invFun n := by
    refine ⟨(n : ℕ) - 2 ^ M, ?_⟩
    have hn := n.property
    unfold QuantitativeDensity.dyadicShell at hn
    rw [Finset.mem_Ico] at hn
    have hupper : (n : ℕ) < 2 ^ M * 2 := by
      simpa only [pow_succ] using hn.2
    omega
  left_inv r := by
    apply Fin.ext
    simp
  right_inv n := by
    apply Subtype.ext
    have hn := n.property
    unfold QuantitativeDensity.dyadicShell at hn
    rw [Finset.mem_Ico] at hn
    simp only
    omega

/-- Fixed-total source codes are exactly the starts in one dyadic shell. -/
noncomputable def sourceCodeEquivDyadicShell
    (M : ℕ) :
    SourceCode M ≃
      {n // n ∈ QuantitativeDensity.dyadicShell M} :=
  (sourceCodeEquivResidue M).trans (residueEquivDyadicShell M)

theorem sourceCodeEquivDyadicShell_val
    {M : ℕ} (x : SourceCode M) :
    ((sourceCodeEquivDyadicShell M x :
        {n // n ∈ QuantitativeDensity.dyadicShell M}) : ℕ) =
      sourceShellStart x := rfl

/-- Source codes whose shell-length endpoint misses `S`. -/
def sourceEndpointBad (S : Set ℕ) (M : ℕ) :
    Finset (SourceCode M) := by
  classical
  exact Finset.univ.filter fun x => sourceEndpoint x ∉ S

/-- Shell starts whose shell-length endpoint misses `S`. -/
def endpointShellBad (S : Set ℕ) (M : ℕ) : Finset ℕ := by
  classical
  exact (QuantitativeDensity.dyadicShell M).filter
    fun n => (Terras.T^[M]) n ∉ S

theorem card_sourceEndpointBad_eq_endpointShellBad
    (S : Set ℕ) (M : ℕ) :
    (sourceEndpointBad S M).card = (endpointShellBad S M).card := by
  classical
  apply Finset.card_bij
      (fun x _ => sourceShellStart x)
  · intro x hx
    simp only [endpointShellBad, Finset.mem_filter]
    exact
      ⟨by
        simpa [QuantitativeDensity.dyadicShell] using
          sourceShellStart_mem x,
        by
          simpa [sourceEndpoint] using
            (Finset.mem_filter.mp hx).2⟩
  · intro x hx y hy hxy
    have heq :
        sourceCodeEquivDyadicShell M x =
          sourceCodeEquivDyadicShell M y := by
      apply Subtype.ext
      simpa [sourceCodeEquivDyadicShell_val] using hxy
    exact (sourceCodeEquivDyadicShell M).injective heq
  · intro n hn
    have hnPair :
        n ∈ QuantitativeDensity.dyadicShell M ∧
          (Terras.T^[M]) n ∉ S := by
      simpa only [endpointShellBad, Finset.mem_filter] using hn
    have hnShell :
        n ∈ QuantitativeDensity.dyadicShell M :=
      hnPair.1
    let x : SourceCode M :=
      (sourceCodeEquivDyadicShell M).symm ⟨n, hnShell⟩
    refine ⟨x, ?_, ?_⟩
    · rw [sourceEndpointBad, Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      have hx :
          sourceShellStart x = n := by
        have happly :=
          (sourceCodeEquivDyadicShell M).apply_symm_apply
            ⟨n, hnShell⟩
        exact congrArg Subtype.val happly
      simpa [sourceEndpoint, hx] using
        hnPair.2
    · have happly :=
        (sourceCodeEquivDyadicShell M).apply_symm_apply
          ⟨n, hnShell⟩
      exact congrArg Subtype.val happly

theorem shellBad_collatzPullback_eq_endpointShellBad
    (S : Set ℕ) (M : ℕ) :
    QuantitativeDensity.shellBad
        (QuantitativeDensity.collatzPullback S) M =
      endpointShellBad S M := by
  classical
  ext n
  constructor
  · intro hn
    rw [QuantitativeDensity.shellBad, Finset.mem_filter] at hn
    simp only [endpointShellBad, Finset.mem_filter]
    have hlog :=
      Terras.log_two_eq_of_mem_dyadicShell hn.1
    exact
      ⟨hn.1, by
        simpa [QuantitativeDensity.collatzPullback, hlog] using hn.2⟩
  · intro hn
    simp only [endpointShellBad, Finset.mem_filter] at hn
    rw [QuantitativeDensity.shellBad, Finset.mem_filter]
    have hlog :=
      Terras.log_two_eq_of_mem_dyadicShell hn.1
    exact
      ⟨hn.1, by
        simpa [QuantitativeDensity.collatzPullback, hlog] using hn.2⟩

/-- Exact cardinal bridge from source-code endpoint failures to the actual
one-block Collatz pullback complement. -/
theorem card_shellBad_collatzPullback_eq_sourceEndpointBad
    (S : Set ℕ) (M : ℕ) :
    (QuantitativeDensity.shellBad
        (QuantitativeDensity.collatzPullback S) M).card =
      (sourceEndpointBad S M).card := by
  rw [shellBad_collatzPullback_eq_endpointShellBad,
    card_sourceEndpointBad_eq_endpointShellBad]

end

end FixedTotal

end CollatzEndpointTransport
