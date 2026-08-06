/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik
-/
import CollatzEndpointTransport.Linear.FixedTotalSourceCoding

/-!
# Fixed Total Endpoint Bridge

Bridge from fixed-total source codes to actual Collatz shell endpoints.

The source code is first converted to its Terras residue.  Adding `2^M`
chooses the canonical representative in the dyadic shell
`[2^M, 2^(M+1))` without changing the first `M` parity letters.
Consequently both the odd count and the integer affine correction are
exactly the fixed-total observables.
-/

namespace CollatzEndpointTransport

namespace FixedTotal

open Nat Finset

noncomputable section

/-- Canonical shell representative of a fixed-total source code. -/
def sourceShellStart {M : ℕ} (x : SourceCode M) : ℕ :=
  2 ^ M + (sourceCodeEquivResidue M x : ℕ)

/-- Endpoint after the shell-length Collatz window. -/
def sourceEndpoint {M : ℕ} (x : SourceCode M) : ℕ :=
  (Terras.T^[M]) (sourceShellStart x)

/-- Endpoint of the canonical residue representative below `2^M`. -/
def sourceResidueEndpoint {M : ℕ} (x : SourceCode M) : ℕ :=
  (Terras.T^[M]) (sourceCodeEquivResidue M x : ℕ)

theorem sourceShellStart_mem
    {M : ℕ} (x : SourceCode M) :
    2 ^ M ≤ sourceShellStart x ∧
      sourceShellStart x < 2 ^ (M + 1) := by
  constructor
  · simp [sourceShellStart]
  · have hr := (sourceCodeEquivResidue M x).isLt
    rw [pow_succ]
    simp only [sourceShellStart]
    omega

theorem sourceShellStart_modEq_residue
    {M : ℕ} (x : SourceCode M) :
    Nat.ModEq (2 ^ M) (sourceShellStart x)
      (sourceCodeEquivResidue M x : ℕ) := by
  rw [Nat.ModEq]
  have hr := (sourceCodeEquivResidue M x).isLt
  simp [sourceShellStart, Nat.add_mod, Nat.mod_eq_of_lt hr]

theorem parityVec_sourceShellStart
    {M : ℕ} (x : SourceCode M) :
    Terras.parityVec M (sourceShellStart x) = sourceCodeWord x := by
  calc
    Terras.parityVec M (sourceShellStart x) =
        Terras.parityVec M (sourceCodeEquivResidue M x : ℕ) :=
      Terras.parityVec_congr (sourceShellStart_modEq_residue x)
    _ = sourceCodeWord x := parityVec_sourceCodeEquivResidue M x

theorem integerCorrection_sourceShellStart
    {M : ℕ} (x : SourceCode M) :
    Terras.integerCorrection M (sourceShellStart x) =
      sourceCodeCorrection x := by
  rw [← wordCorrection_parityVec]
  rw [parityVec_sourceShellStart, ofFn_sourceCodeWord]
  exact wordCorrection_sourceCodeList x

theorem oddCount_sourceShellStart
    {M : ℕ} (x : SourceCode M) :
    Terras.oddCount M (sourceShellStart x) =
      sourceCodeOddCount x := by
  rw [Terras.oddCount_eq_wordWeight, parityVec_sourceShellStart]
  rw [← listOddCount_ofFn, ofFn_sourceCodeWord,
    listOddCount_sourceCodeList]

/-- Exact integer affine formula for a source code in the dyadic shell. -/
theorem sourceEndpoint_affine
    {M : ℕ} (x : SourceCode M) :
    2 ^ M * sourceEndpoint x =
      3 ^ sourceCodeOddCount x * sourceShellStart x +
        sourceCodeCorrection x := by
  simpa [sourceEndpoint, oddCount_sourceShellStart,
    integerCorrection_sourceShellStart] using
      Terras.pow_two_mul_iterate_eq_affine M (sourceShellStart x)

theorem sourceResidueEndpoint_affine
    {M : ℕ} (x : SourceCode M) :
    2 ^ M * sourceResidueEndpoint x =
      3 ^ sourceCodeOddCount x * (sourceCodeEquivResidue M x : ℕ) +
        sourceCodeCorrection x := by
  simpa [sourceResidueEndpoint,
    oddCount_sourceCodeEquivResidue,
    integerCorrection_sourceCodeEquivResidue] using
      Terras.pow_two_mul_iterate_eq_affine M
        (sourceCodeEquivResidue M x : ℕ)

/-- Exact translation from the canonical residue endpoint to the canonical
shell endpoint. -/
theorem sourceEndpoint_eq_three_pow_add_residueEndpoint
    {M : ℕ} (x : SourceCode M) :
    sourceEndpoint x =
      3 ^ sourceCodeOddCount x + sourceResidueEndpoint x := by
  have hshell := sourceEndpoint_affine x
  have hresidue := sourceResidueEndpoint_affine x
  have hmul :
      2 ^ M * sourceEndpoint x =
        2 ^ M *
          (3 ^ sourceCodeOddCount x + sourceResidueEndpoint x) := by
    calc
      2 ^ M * sourceEndpoint x =
          3 ^ sourceCodeOddCount x * sourceShellStart x +
            sourceCodeCorrection x := hshell
      _ = 3 ^ sourceCodeOddCount x *
              (2 ^ M + (sourceCodeEquivResidue M x : ℕ)) +
            sourceCodeCorrection x := by rw [sourceShellStart]
      _ = 3 ^ sourceCodeOddCount x * 2 ^ M +
            (3 ^ sourceCodeOddCount x *
                (sourceCodeEquivResidue M x : ℕ) +
              sourceCodeCorrection x) := by ring
      _ = 3 ^ sourceCodeOddCount x * 2 ^ M +
            2 ^ M * sourceResidueEndpoint x := by rw [hresidue]
      _ = 2 ^ M *
            (3 ^ sourceCodeOddCount x + sourceResidueEndpoint x) := by ring
  exact Nat.eq_of_mul_eq_mul_left (pow_pos (by norm_num) M) hmul

/-- The canonical residue endpoint occupies exactly one `3^s`-cell. -/
theorem sourceResidueEndpoint_lt_three_pow
    {M s : ℕ} {x : SourceCode M}
    (hs : sourceCodeOddCount x = s) :
    sourceResidueEndpoint x < 3 ^ s := by
  have h := Terras.iterate_lt_three_pow_oddCount
    (n := (sourceCodeEquivResidue M x : ℕ))
    (sourceCodeEquivResidue M x).isLt
  simpa [sourceResidueEndpoint, oddCount_sourceCodeEquivResidue, hs] using h

theorem three_pow_le_sourceEndpoint
    {M s : ℕ} {x : SourceCode M}
    (hs : sourceCodeOddCount x = s) :
    3 ^ s ≤ sourceEndpoint x := by
  rw [sourceEndpoint_eq_three_pow_add_residueEndpoint, hs]
  exact Nat.le_add_right _ _

/-- Sharp endpoint interval at a fixed odd-count level. -/
theorem sourceEndpoint_lt_two_mul_three_pow
    {M s : ℕ} {x : SourceCode M}
    (hs : sourceCodeOddCount x = s) :
    sourceEndpoint x < 2 * 3 ^ s := by
  rw [sourceEndpoint_eq_three_pow_add_residueEndpoint, hs]
  have hres := sourceResidueEndpoint_lt_three_pow (x := x) hs
  omega

theorem sourceEndpoint_pos
    {M : ℕ} (x : SourceCode M) :
    0 < sourceEndpoint x := by
  have haffine := sourceEndpoint_affine x
  have hstart : 0 < sourceShellStart x := by
    have hmem := (sourceShellStart_mem x).1
    have hpow : 0 < 2 ^ M := pow_pos (by norm_num) _
    omega
  have hrhs :
      0 <
        3 ^ sourceCodeOddCount x * sourceShellStart x +
          sourceCodeCorrection x := by
    positivity
  have hlhs : 0 < 2 ^ M * sourceEndpoint x := by
    rw [haffine]
    exact hrhs
  exact Nat.pos_of_mul_pos_left hlhs

/-- Every endpoint at odd-count level `s` lies in the reference range
`[0, 3^(s+1))`. -/
theorem sourceEndpoint_lt_three_pow_succ
    {M s : ℕ} {x : SourceCode M}
    (hs : sourceCodeOddCount x = s) :
    sourceEndpoint x < 3 ^ (s + 1) := by
  have haffine := sourceEndpoint_affine x
  rw [hs] at haffine
  have hstart := (sourceShellStart_mem x).2
  have hcorr :=
    Terras.integerCorrection_lt_scale M (sourceShellStart x)
  rw [integerCorrection_sourceShellStart,
    oddCount_sourceShellStart, hs] at hcorr
  have hpow2 : 0 < 2 ^ M := pow_pos (by norm_num) _
  have hthree : 0 < 3 ^ s := pow_pos (by norm_num) _
  have hstart' :
      sourceShellStart x < 2 ^ M * 2 := by
    simpa only [pow_succ] using hstart
  have hmain :
      3 ^ s * sourceShellStart x <
        3 ^ s * (2 ^ M * 2) :=
    (Nat.mul_lt_mul_left hthree).2 hstart'
  have hsum :
      3 ^ s * sourceShellStart x + sourceCodeCorrection x <
        3 ^ s * (2 ^ M * 2) + 3 ^ s * 2 ^ M :=
    Nat.add_lt_add hmain hcorr
  have hstrict :
      2 ^ M * sourceEndpoint x <
        2 ^ M * 3 ^ (s + 1) := by
    rw [haffine]
    calc
      3 ^ s * sourceShellStart x + sourceCodeCorrection x <
          3 ^ s * (2 ^ M * 2) + 3 ^ s * 2 ^ M := hsum
      _ = 2 ^ M * 3 ^ (s + 1) := by
        rw [pow_succ]
        ring
  exact (Nat.mul_lt_mul_left hpow2).mp <| by
    simpa [mul_assoc, mul_left_comm, mul_comm] using hstrict

theorem sourceEndpoint_collision_modEq_correction
    {M s : ℕ} {x y : SourceCode M}
    (hsx : sourceCodeOddCount x = s)
    (hsy : sourceCodeOddCount y = s)
    (hout : sourceEndpoint x = sourceEndpoint y) :
    Nat.ModEq (3 ^ s) (sourceCodeCorrection x)
      (sourceCodeCorrection y) := by
  have h :=
    Terras.correction_modEq_of_equal_output
      (M := M) (s := s)
      (n₁ := sourceShellStart x) (n₂ := sourceShellStart y)
      (by simpa [oddCount_sourceShellStart] using hsx)
      (by simpa [oddCount_sourceShellStart] using hsy)
      (by simpa [sourceEndpoint] using hout)
  rw [integerCorrection_sourceShellStart,
    integerCorrection_sourceShellStart] at h
  exact h

/-- The residue endpoint is the normalized correction coordinate: after
multiplication by the fixed unit `2^M`, it agrees with the correction modulo
`3^s`. -/
theorem sourceResidueEndpoint_mul_modEq_correction
    {M s : ℕ} {x : SourceCode M}
    (hs : sourceCodeOddCount x = s) :
    Nat.ModEq (3 ^ s)
      (2 ^ M * sourceResidueEndpoint x) (sourceCodeCorrection x) := by
  have h := sourceResidueEndpoint_affine x
  rw [hs] at h
  rw [Nat.ModEq]
  have hmod := congrArg (fun z : ℕ => z % 3 ^ s) h
  simpa [Nat.add_mod, Nat.mul_mod] using hmod

/-- **Exact fixed-level endpoint coordinate.**

At a common odd-count level, two canonical shell endpoints are equal if and
only if their affine corrections agree modulo `3^s`.  Thus the correction
residue is not merely a collision upper bound: it gives the exact endpoint
fibers at every depth. -/
theorem sourceEndpoint_eq_iff_correction_modEq
    {M s : ℕ} {x y : SourceCode M}
    (hsx : sourceCodeOddCount x = s)
    (hsy : sourceCodeOddCount y = s) :
    sourceEndpoint x = sourceEndpoint y ↔
      Nat.ModEq (3 ^ s) (sourceCodeCorrection x)
        (sourceCodeCorrection y) := by
  constructor
  · exact sourceEndpoint_collision_modEq_correction hsx hsy
  · intro hcorr
    have hx := sourceResidueEndpoint_mul_modEq_correction hsx
    have hy := sourceResidueEndpoint_mul_modEq_correction hsy
    have hmul :
        Nat.ModEq (3 ^ s)
          (2 ^ M * sourceResidueEndpoint x)
          (2 ^ M * sourceResidueEndpoint y) :=
      hx.trans (hcorr.trans hy.symm)
    have hcop : Nat.gcd (3 ^ s) (2 ^ M) = 1 :=
      (Nat.Coprime.pow s M
        (by norm_num : Nat.Coprime 3 2)).gcd_eq_one
    have hresMod :
        Nat.ModEq (3 ^ s)
          (sourceResidueEndpoint x) (sourceResidueEndpoint y) :=
      Nat.ModEq.cancel_left_of_coprime hcop hmul
    have hxlt := sourceResidueEndpoint_lt_three_pow (x := x) hsx
    have hylt := sourceResidueEndpoint_lt_three_pow (x := y) hsy
    rw [Nat.ModEq, Nat.mod_eq_of_lt hxlt,
      Nat.mod_eq_of_lt hylt] at hresMod
    rw [sourceEndpoint_eq_three_pow_add_residueEndpoint,
      sourceEndpoint_eq_three_pow_add_residueEndpoint, hsx, hsy, hresMod]

/-- At a fixed first-odd offset and a fixed odd-count level, an endpoint
collision forces a numerator collision modulo `3^s`. -/
theorem sourceEndpoint_collision_modEq_numerator
    {M s : ℕ} (u : Fin M)
    (c d : Composition (M - (u : ℕ)))
    (hc : c.length = s) (hd : d.length = s)
    (hout :
      sourceEndpoint
          (Sum.inr ⟨u, c⟩ : SourceCode M) =
        sourceEndpoint
          (Sum.inr ⟨u, d⟩ : SourceCode M)) :
    Nat.ModEq (3 ^ s) (syracuseNumerator c)
      (syracuseNumerator d) := by
  have hcorr :
      Nat.ModEq (3 ^ s)
        (2 ^ (u : ℕ) * syracuseNumerator c)
        (2 ^ (u : ℕ) * syracuseNumerator d) := by
    simpa [sourceCodeOddCount, sourceCodeCorrection] using
      sourceEndpoint_collision_modEq_correction
        (M := M) (s := s)
        (x := (Sum.inr ⟨u, c⟩ : SourceCode M))
        (y := (Sum.inr ⟨u, d⟩ : SourceCode M))
        hc hd hout
  apply Nat.ModEq.cancel_left_of_coprime
  · exact
      (Nat.Coprime.pow s (u : ℕ)
        (by norm_num : Nat.Coprime 3 2)).gcd_eq_one
  · exact hcorr

end

end FixedTotal

end CollatzEndpointTransport
