/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik
-/
import CollatzEndpointTransport.Common.AffineCorrectionDensity
import CollatzEndpointTransport.Common.TerrasInitialWindow

/-!
# Quantitative Pullback Defs

Concrete definitions for the quantitative one-block Collatz pullback.

This file contains no analytic estimate.  It fixes the objects occurring in
the quantitative one-block pullback so later files cannot
silently change a floor, a logarithmic horizon, or a cone quantifier.

For a set `S` of positive integers:

* `collatzPullback S` tests membership after `Nat.log 2 n` half-Collatz steps;
* `coneCore K eta S` requires all `K * 3^k` affine descendants through
  depth `k <= floor (eta * floor(log_3 n))` to lie in `S`;
* `baseMapAt alpha M` is the deterministic map
  `n |-> floor (3^floor(alpha*M) n / 2^M)`;
* `basePullback alpha S` applies that map at the dyadic scale of `n`.

The concrete witness set is the intersection used in the proof:

  base map lands in the cone core
  AND the terminal parity count is regular
  AND the affine correction is small.

The separate definitions are deliberate.  Cone counting, base-map counting,
and the deterministic orbit-to-cone implication are independent proof
obligations.
-/

namespace CollatzEndpointTransport

namespace Terras

/-- Conservative parity tolerance used by the pullback witness. -/
noncomputable def parityTol (t : ℝ) : ℝ := min t (1 / 2)

/-- Two-sided prefix regularity from half the dyadic horizon to the horizon. -/
def parityGood (t : ℝ) : Set ℕ :=
  {n | PrefixTwoSidedRegular n (Nat.log 2 n / 2) (Nat.log 2 n) (parityTol t)}

end Terras

namespace QuantitativeDensity

open scoped Real

noncomputable section

/-- Pull a set back through one logarithmic half-Collatz block. -/
def collatzPullback (S : Set ℕ) : Set ℕ :=
  {n | (Terras.T^[Nat.log 2 n]) n ∈ S}

/-- The robust base-3 cone inside `S`.

The nested floor is intentional.  The shell proof controls
`k <= floor (eta * j)` on `3^j <= n < 3^(j+1)`, where
`j = floor (log_3 n)`.  The source displays the slightly stronger
`floor (eta * log_3 n)` condition, but that does not follow from the stated
shell union without an additional boundary layer.  The nested-floor core is
exactly what the proof establishes and is sufficient for the pullback.
-/
def coneCore (K : ℕ) (eta : ℝ) (S : Set ℕ) : Set ℕ :=
  {n | 0 < n ∧
    ∀ k : ℕ, (k : ℝ) ≤ eta * Nat.log 3 n →
      ∀ i : ℕ, i < K * 3 ^ k → 3 ^ k * n + i ∈ S}

/-- Shell-local cone used in the counting proof on `[3^j,3^(j+1))`. -/
def shellConeCore (K : ℕ) (eta : ℝ) (j : ℕ) (S : Set ℕ) : Set ℕ :=
  {n | 3 ^ j ≤ n ∧ n < 3 ^ (j + 1) ∧
    ∀ k : ℕ, (k : ℝ) ≤ eta * j →
      ∀ i : ℕ, i < K * 3 ^ k → 3 ^ k * n + i ∈ S}

/-- On a base-3 shell, the global nested-floor cone is exactly the
shell-local cone condition. -/
theorem mem_coneCore_iff_of_mem_three_shell
    {K j n : ℕ} {eta : ℝ} {S : Set ℕ}
    (hn : 3 ^ j ≤ n ∧ n < 3 ^ (j + 1)) :
    n ∈ coneCore K eta S ↔
      0 < n ∧
      ∀ k : ℕ, (k : ℝ) ≤ eta * j →
        ∀ i : ℕ, i < K * 3 ^ k → 3 ^ k * n + i ∈ S := by
  have hnlog : Nat.log 3 n = j :=
    Nat.log_eq_of_pow_le_of_lt_pow hn.1 hn.2
  simp only [coneCore, Set.mem_setOf_eq, hnlog]

/-- Deterministic base map on a fixed dyadic shell. -/
def baseMapAt (alpha : ℝ) (M n : ℕ) : ℕ :=
  (3 ^ ⌊alpha * M⌋₊ * n) / 2 ^ M

/-- Deterministic base map at the dyadic scale of `n`. -/
def baseMap (alpha : ℝ) (n : ℕ) : ℕ :=
  baseMapAt alpha (Nat.log 2 n) n

/-- Pullback through the deterministic base map. -/
def basePullback (alpha : ℝ) (S : Set ℕ) : Set ℕ :=
  {n | baseMap alpha n ∈ S}

/-- The three generated conditions whose intersection forces one-block
membership in `S`, once the scalar startup inequalities hold. -/
def pullbackWitnessSet
    (S : Set ℕ) (eta etaPrime alpha correctionTol : ℝ) : Set ℕ :=
  basePullback alpha (coneCore 2 etaPrime S) ∩
    Terras.parityGood eta ∩
    Terras.affineCorrectionGood correctionTol

@[simp]
theorem mem_collatzPullback {S : Set ℕ} {n : ℕ} :
    n ∈ collatzPullback S ↔ (Terras.T^[Nat.log 2 n]) n ∈ S :=
  Iff.rfl

@[simp]
theorem mem_basePullback {alpha : ℝ} {S : Set ℕ} {n : ℕ} :
    n ∈ basePullback alpha S ↔ baseMap alpha n ∈ S :=
  Iff.rfl

theorem mem_pullbackWitnessSet
    {S : Set ℕ} {eta etaPrime alpha correctionTol : ℝ} {n : ℕ} :
    n ∈ pullbackWitnessSet S eta etaPrime alpha correctionTol ↔
      baseMap alpha n ∈ coneCore 2 etaPrime S ∧
      n ∈ Terras.parityGood eta ∧
      n ∈ Terras.affineCorrectionGood correctionTol := by
  simp only [pullbackWitnessSet, basePullback, Set.mem_inter_iff,
    Set.mem_setOf_eq]
  constructor
  · rintro ⟨⟨hbase, hparity⟩, hcorr⟩
    exact ⟨hbase, hparity, hcorr⟩
  · rintro ⟨hbase, hparity, hcorr⟩
    exact ⟨⟨hbase, hparity⟩, hcorr⟩

end

end QuantitativeDensity

end CollatzEndpointTransport
