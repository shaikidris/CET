/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik
-/
import CollatzEndpointTransport.Linear.FixedTotalActualEndpointMoment

/-!
# Fixed Total Endpoint Target

Exact decomposition of a shell pullback failure by odd-count level and
endpoint fiber.

This is the finite target-facing side of the nonlinear pullback.  No
probability or asymptotic argument occurs here: every source code is grouped
first by its exact odd count and then by its actual Collatz endpoint.
-/

namespace CollatzEndpointTransport

namespace FixedTotal

open Nat Finset

noncomputable section

/-- Bad endpoint values at one odd-count level. -/
def actualLevelBadEndpointSet
    (S : Set ℕ) (M s : ℕ) : Finset ℕ := by
  classical
  exact (actualLevelEndpointSet M s).filter fun y => y ∉ S

/-- Source mass carried by bad endpoint values at one odd-count level. -/
def actualLevelBadMass
    (S : Set ℕ) (M s : ℕ) : ℕ := by
  classical
  exact ∑ y ∈ actualLevelEndpointSet M s,
    if y ∉ S then actualLevelFiberCard M s y else 0

/-- Source codes at one odd-count level whose endpoint misses `S`. -/
def sourceLevelBadSet
    (S : Set ℕ) (M s : ℕ) : Finset (SourceCode M) := by
  classical
  exact (sourceOddLevel M s).filter fun x => sourceEndpoint x ∉ S

theorem actualLevelBadMass_eq_card_filter
    (S : Set ℕ) (M s : ℕ) :
    actualLevelBadMass S M s =
      (sourceLevelBadSet S M s).card := by
  classical
  let W := sourceOddLevel M s
  let f : SourceCode M → ℕ := sourceEndpoint
  have hmaps :
      ∀ x ∈ W, f x ∈ actualLevelEndpointSet M s := by
    intro x hx
    exact Finset.mem_image.mpr ⟨x, hx, rfl⟩
  calc
    actualLevelBadMass S M s =
        ∑ y ∈ actualLevelEndpointSet M s,
          ∑ x ∈ mapFiber W f y,
            if f x ∉ S then 1 else 0 := by
      unfold actualLevelBadMass
      apply Finset.sum_congr rfl
      intro y hy
      by_cases hyS : y ∈ S
      · rw [if_neg (not_not.mpr hyS)]
        symm
        apply Finset.sum_eq_zero
        intro x hx
        have hfx : f x = y := (Finset.mem_filter.mp hx).2
        simp [hfx, hyS]
      · rw [if_pos hyS]
        calc
          actualLevelFiberCard M s y =
              (mapFiber W f y).card := rfl
          _ = ∑ _x ∈ mapFiber W f y, 1 := by simp
          _ = ∑ x ∈ mapFiber W f y,
                if f x ∉ S then 1 else 0 := by
            apply Finset.sum_congr rfl
            intro x hx
            have hfx : f x = y := (Finset.mem_filter.mp hx).2
            simp [hfx, hyS]
    _ = ∑ x ∈ W, if f x ∉ S then 1 else 0 :=
      Finset.sum_fiberwise_of_maps_to hmaps
        (fun x => if f x ∉ S then 1 else 0)
    _ = (sourceLevelBadSet S M s).card := by
      unfold sourceLevelBadSet
      rw [Finset.card_filter]

/-- Exact decomposition of the full source-code failure count. -/
theorem card_sourceEndpointBad_eq_sum_levelBadMass
    (S : Set ℕ) (M : ℕ) :
    (sourceEndpointBad S M).card =
      ∑ s ∈ Finset.range (M + 1),
        actualLevelBadMass S M s := by
  classical
  have hmap :
      ∀ x ∈ (Finset.univ : Finset (SourceCode M)),
        sourceCodeOddCount x ∈ Finset.range (M + 1) := by
    intro x hx
    exact Finset.mem_range.mpr
      (Nat.lt_succ_of_le (sourceCodeOddCount_le x))
  calc
    (sourceEndpointBad S M).card =
        ∑ x : SourceCode M,
          if sourceEndpoint x ∉ S then 1 else 0 := by
      rw [sourceEndpointBad, Finset.card_filter]
    _ = ∑ s ∈ Finset.range (M + 1),
          ∑ x ∈ sourceOddLevel M s,
            if sourceEndpoint x ∉ S then 1 else 0 := by
      symm
      simpa [sourceOddLevel] using
        (Finset.sum_fiberwise_of_maps_to
          (s := (Finset.univ : Finset (SourceCode M)))
          (t := Finset.range (M + 1))
          (g := sourceCodeOddCount)
          hmap
          (fun x => if sourceEndpoint x ∉ S then 1 else 0))
    _ = ∑ s ∈ Finset.range (M + 1),
          actualLevelBadMass S M s := by
      apply Finset.sum_congr rfl
      intro s hs
      rw [actualLevelBadMass_eq_card_filter]
      unfold sourceLevelBadSet
      rw [Finset.card_filter]

theorem actualLevelBadEndpointSet_subset_badPrefix
    (S : Set ℕ) (M s : ℕ) :
    actualLevelBadEndpointSet S M s ⊆
      QuantitativeDensity.badPrefix S (3 ^ (s + 1)) := by
  classical
  intro y hy
  rw [actualLevelBadEndpointSet, Finset.mem_filter] at hy
  rcases Finset.mem_image.mp hy.1 with ⟨x, hx, hxy⟩
  have hsx : sourceCodeOddCount x = s :=
    (Finset.mem_filter.mp hx).2
  have hyPos : 0 < y := by
    rw [← hxy]
    exact sourceEndpoint_pos x
  have hyLt : y < 3 ^ (s + 1) := by
    rw [← hxy]
    exact sourceEndpoint_lt_three_pow_succ hsx
  rw [QuantitativeDensity.badPrefix, Finset.mem_filter,
    QuantitativeDensity.positivePrefix, Finset.mem_Icc]
  exact ⟨⟨hyPos, hyLt.le⟩, hy.2⟩

/-- A `(C,D)`-dense target has at most `C R^(1-D)` bad possible endpoints
at level `s`, where `R=3^(s+1)`. -/
theorem card_actualLevelBadEndpointSet_le
    {S : Set ℕ} {C D : ℝ}
    (hS : QuantitativeDensity.IsCDDense S C D)
    (M s : ℕ) :
    ((actualLevelBadEndpointSet S M s).card : ℝ) ≤
      C * (3 ^ (s + 1) : ℝ) ^ (1 - D) := by
  have hcardNat :
      (actualLevelBadEndpointSet S M s).card ≤
        (QuantitativeDensity.badPrefix S (3 ^ (s + 1))).card :=
    Finset.card_le_card
      (actualLevelBadEndpointSet_subset_badPrefix S M s)
  have hcard :
      ((actualLevelBadEndpointSet S M s).card : ℝ) ≤
        (QuantitativeDensity.badPrefix S (3 ^ (s + 1))).card := by
    exact_mod_cast hcardNat
  have hdense :=
    hS.bad_bound (3 ^ (s + 1)) (by positivity)
  exact hcard.trans (by
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using hdense)

end

end FixedTotal

end CollatzEndpointTransport
