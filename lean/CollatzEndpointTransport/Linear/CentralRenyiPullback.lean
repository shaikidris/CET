/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik
-/
import CollatzEndpointTransport.Linear.CentralRenyiShell
import CollatzEndpointTransport.Linear.FixedTotalNonlinearShell

/-!
# Central Renyi Pullback

The central higher-Renyi Collatz pullback.

This module is the concrete interface between the paper-proved central
fixed-total moment and the existing endpoint-only bootstrap.  Noncentral
source codes are retained explicitly as a discarded remainder; no
probabilistic or asymptotic assumption is introduced.
-/

namespace CollatzEndpointTransport

namespace FixedTotal

open Nat Finset
open scoped Real Topology

noncomputable section

local instance centralPullbackSourceCodeDecidableEq (M : ℕ) :
    DecidableEq (SourceCode M) := Classical.decEq _

/-- Literal source codes at odd-count level `s` retained by the central
moment. -/
def centralLevelSourceSet
    (M s : ℕ) (theta eta : ℝ) : Finset (SourceCode M) := by
  classical
  exact (sourceOddLevel M s).filter fun x =>
    x ∈ centralSourceSet M theta eta

/-- Sigma-family realization of one central source level. -/
def centralLevelPairImage
    (M s : ℕ) (theta eta : ℝ) : Finset (SourceCode M) := by
  classical
  exact ((Finset.univ : Finset (Fin M)).sigma
    (centralLevelCohortSet M s theta eta)).image
      (fun p => (Sum.inr p : SourceCode M))

theorem centralLevelSourceSet_eq_pairImage
    (M s : ℕ) (theta eta : ℝ) :
    centralLevelSourceSet M s theta eta =
      centralLevelPairImage M s theta eta := by
  classical
  ext x
  cases x with
  | inl e => simp [centralLevelSourceSet, centralLevelPairImage,
      centralSourceSet]
  | inr p =>
      rcases p with ⟨u, c⟩
      simp only [centralLevelSourceSet, Finset.mem_filter,
        Finset.mem_univ, true_and, sourceOddLevel, sourceCodeOddCount,
        centralLevelPairImage, Finset.mem_image, Finset.mem_sigma]
      constructor
      · intro hx
        have hadm :
            CentralRenyiAdmissible (M - (u : ℕ)) s theta eta := by
          simpa [hx.1, centralSourceSet] using hx.2
        refine ⟨⟨u, c⟩, ?_, rfl⟩
        simp [centralLevelCohortSet, fixedSet, hadm, hx.1]
      · intro hx
        rcases hx with ⟨p, hp, heq⟩
        have hcohort :
            p.2 ∈ centralLevelCohortSet M s theta eta p.1 := hp
        have hadm :
            CentralRenyiAdmissible (M - (p.1 : ℕ)) s theta eta := by
          by_contra hnot
          simp [centralLevelCohortSet, hnot] at hcohort
        have hlen : p.2.length = s := by
          simpa [centralLevelCohortSet, fixedSet, hadm] using hcohort
        have hpcentral :
            (Sum.inr p : SourceCode M) ∈ centralSourceSet M theta eta := by
          simp [centralSourceSet, hlen, hadm]
        have hodd := congrArg sourceCodeOddCount heq
        have hclen : c.length = s := by
          simpa [sourceCodeOddCount, hlen] using hodd.symm
        rw [heq] at hpcentral
        exact ⟨hclen, by simpa [centralSourceSet] using hpcentral⟩

/-- A mixed fiber is the fiber of the corresponding sigma source. -/
theorem mixedFiberCard_eq_sigmaFiber
    {ι : Type*} {α : ι → Type*} {β : Type*}
    [∀ i, DecidableEq (α i)] [DecidableEq β]
    (U : Finset ι) (W : ∀ i, Finset (α i))
    (f : ∀ i, α i → β) (b : β) :
    mixedFiberCard U W f b =
      (mapFiber (U.sigma W) (fun p => f p.1 p.2) b).card := by
  classical
  unfold mixedFiberCard mapFiber
  rw [Finset.card_filter, Finset.sum_sigma]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.card_filter]

/-- The central mixed fiber is exactly the literal shell-source fiber. -/
theorem centralLevelFiberCard_eq_sourceFiber
    (M s : ℕ) (theta eta : ℝ) (y : ℕ) :
    centralLevelFiberCard M s theta eta y =
      (mapFiber (centralLevelSourceSet M s theta eta)
        sourceEndpoint y).card := by
  classical
  let P := (Finset.univ : Finset (Fin M)).sigma
    (centralLevelCohortSet M s theta eta)
  let e : (Σ u : Fin M, Composition (M - (u : ℕ))) → SourceCode M :=
    fun p => Sum.inr p
  have hsource : centralLevelSourceSet M s theta eta = P.image e := by
    simpa [P, e, centralLevelPairImage] using
      centralLevelSourceSet_eq_pairImage M s theta eta
  rw [hsource]
  have hfilterImage :
      mapFiber (P.image e) sourceEndpoint y =
        (mapFiber P (fun p => cohortEndpoint p.1 p.2) y).image e := by
    ext x
    constructor
    · intro hx
      rw [mapFiber, Finset.mem_filter] at hx
      rcases Finset.mem_image.mp hx.1 with ⟨p, hp, rfl⟩
      rw [Finset.mem_image]
      refine ⟨p, ?_, rfl⟩
      rw [mapFiber, Finset.mem_filter]
      exact ⟨hp, by simpa [e, cohortEndpoint] using hx.2⟩
    · intro hx
      rcases Finset.mem_image.mp hx with ⟨p, hp, rfl⟩
      rw [mapFiber, Finset.mem_filter] at hp ⊢
      exact ⟨Finset.mem_image.mpr ⟨p, hp.1, rfl⟩,
        by simpa [e, cohortEndpoint] using hp.2⟩
  rw [hfilterImage, Finset.card_image_of_injective _]
  · simpa [centralLevelFiberCard, P] using
      mixedFiberCard_eq_sigmaFiber
        (Finset.univ : Finset (Fin M))
        (centralLevelCohortSet M s theta eta)
        (fun u => cohortEndpoint u) y
  · intro p q hpq
    exact Sum.inr.inj hpq

/-- Central source codes whose endpoint misses the target. -/
def centralSourceEndpointBad
    (S : Set ℕ) (M : ℕ) (theta eta : ℝ) :
    Finset (SourceCode M) := by
  classical
  exact (centralSourceSet M theta eta).filter fun x =>
    sourceEndpoint x ∉ S

/-- Bad endpoint values carried by the retained central source at one
odd-count level. -/
def centralLevelBadEndpointSet
    (S : Set ℕ) (M s : ℕ) (theta eta : ℝ) : Finset ℕ := by
  classical
  exact (centralLevelEndpointSet M s theta eta).filter fun y => y ∉ S

/-- Central bad source mass at one odd-count level. -/
def centralLevelBadMass
    (S : Set ℕ) (M s : ℕ) (theta eta : ℝ) : ℕ := by
  classical
  exact ((centralLevelSourceSet M s theta eta).filter fun x =>
    sourceEndpoint x ∉ S).card

theorem sourceEndpoint_mem_centralLevelEndpointSet
    {M s : ℕ} {theta eta : ℝ} {x : SourceCode M}
    (hx : x ∈ centralLevelSourceSet M s theta eta) :
    sourceEndpoint x ∈ centralLevelEndpointSet M s theta eta := by
  classical
  rw [centralLevelSourceSet_eq_pairImage] at hx
  rcases Finset.mem_image.mp hx with ⟨p, hp, rfl⟩
  exact map_mem_mixedTargetSet
    (Finset.univ : Finset (Fin M))
    (centralLevelCohortSet M s theta eta)
    (fun u => cohortEndpoint u)
    (Finset.mem_univ p.1) (Finset.mem_sigma.mp hp).2

theorem centralLevelBadMass_eq_sum_bad
    (S : Set ℕ) (M s : ℕ) (theta eta : ℝ) :
    centralLevelBadMass S M s theta eta =
      ∑ y ∈ centralLevelBadEndpointSet S M s theta eta,
        centralLevelFiberCard M s theta eta y := by
  classical
  let W := centralLevelSourceSet M s theta eta
  let f : SourceCode M → ℕ := sourceEndpoint
  have hmaps :
      ∀ x ∈ W, f x ∈ centralLevelEndpointSet M s theta eta := by
    exact fun x hx => sourceEndpoint_mem_centralLevelEndpointSet hx
  unfold centralLevelBadMass centralLevelBadEndpointSet
  rw [Finset.card_filter]
  rw [show
    (∑ x ∈ W, if f x ∉ S then 1 else 0) =
      ∑ y ∈ centralLevelEndpointSet M s theta eta,
        ∑ x ∈ mapFiber W f y,
          if f x ∉ S then 1 else 0 by
      symm
      exact Finset.sum_fiberwise_of_maps_to hmaps
        (fun x => if f x ∉ S then 1 else 0)]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro y hy
  by_cases hyS : y ∈ S
  · rw [if_neg (not_not.mpr hyS)]
    apply Finset.sum_eq_zero
    intro x hx
    have hfx : f x = y := (Finset.mem_filter.mp hx).2
    rw [if_neg]
    simpa [hfx] using hyS
  · rw [if_pos hyS]
    calc
      ∑ x ∈ mapFiber W f y, (if f x ∉ S then 1 else 0) =
          ∑ _x ∈ mapFiber W f y, 1 := by
        apply Finset.sum_congr rfl
        intro x hx
        have hfx : f x = y := (Finset.mem_filter.mp hx).2
        simp [hfx, hyS]
      _ = (mapFiber W f y).card := by simp
      _ = centralLevelFiberCard M s theta eta y := by
        exact (centralLevelFiberCard_eq_sourceFiber M s theta eta y).symm

theorem centralLevelCohortSet_subset_fixedSet
    {M s : ℕ} {theta eta : ℝ} (u : Fin M) :
    centralLevelCohortSet M s theta eta u ⊆
      fixedSet (M - (u : ℕ)) s := by
  intro c hc
  by_cases hadm : CentralRenyiAdmissible (M - (u : ℕ)) s theta eta
  · simpa [centralLevelCohortSet, hadm] using hc
  · simp [centralLevelCohortSet, hadm] at hc

theorem centralLevelEndpointSet_subset_actual
    (M s : ℕ) (theta eta : ℝ) :
    centralLevelEndpointSet M s theta eta ⊆
      actualLevelEndpointSet M s := by
  classical
  intro y hy
  rw [centralLevelEndpointSet, mixedTargetSet,
    Finset.mem_biUnion] at hy
  rcases hy with ⟨u, hu, hy⟩
  rcases Finset.mem_image.mp hy with ⟨c, hc, rfl⟩
  rw [actualLevelEndpointSet, Finset.mem_image]
  refine ⟨(Sum.inr ⟨u, c⟩ : SourceCode M), ?_, rfl⟩
  rw [sourceOddLevel, Finset.mem_filter]
  have hfixed := centralLevelCohortSet_subset_fixedSet u hc
  have hlen : c.length = s := (Finset.mem_filter.mp hfixed).2
  exact ⟨Finset.mem_univ _, by simpa [sourceCodeOddCount] using hlen⟩

theorem centralLevelBadEndpointSet_subset_actual
    (S : Set ℕ) (M s : ℕ) (theta eta : ℝ) :
    centralLevelBadEndpointSet S M s theta eta ⊆
      actualLevelBadEndpointSet S M s := by
  classical
  intro y hy
  rw [centralLevelBadEndpointSet, Finset.mem_filter] at hy
  rw [actualLevelBadEndpointSet, Finset.mem_filter]
  exact ⟨centralLevelEndpointSet_subset_actual M s theta eta hy.1, hy.2⟩

theorem card_centralLevelBadEndpointSet_le
    {S : Set ℕ} {C D : ℝ}
    (hS : QuantitativeDensity.IsCDDense S C D)
    (M s : ℕ) (theta eta : ℝ) :
    ((centralLevelBadEndpointSet S M s theta eta).card : ℝ) ≤
      C * (3 ^ (s + 1) : ℝ) ^ (1 - D) := by
  have hcard :
      (centralLevelBadEndpointSet S M s theta eta).card ≤
        (actualLevelBadEndpointSet S M s).card :=
    Finset.card_le_card
      (centralLevelBadEndpointSet_subset_actual S M s theta eta)
  have hcardR :
      ((centralLevelBadEndpointSet S M s theta eta).card : ℝ) ≤
        ((actualLevelBadEndpointSet S M s).card : ℝ) := by
    exact_mod_cast hcard
  exact hcardR.trans (card_actualLevelBadEndpointSet_le hS M s)

/-- Raw one-level higher-Renyi heavy/ordinary split. -/
theorem centralLevelBadMass_cast_le_raw
    (S : Set ℕ) (M s : ℕ) (theta eta Q : ℝ)
    (hQ : 0 < Q) (htheta : 0 < theta) (hs : s ≤ M) :
    (centralLevelBadMass S M s theta eta : ℝ) ≤
      Q * ((sourceOddLevel M s).card : ℝ) /
          (3 : ℝ) ^ (s + 1) *
          (centralLevelBadEndpointSet S M s theta eta).card +
        Q ^ (-theta) *
          (((3 : ℝ) ^ (s + 1)) /
            (sourceOddLevel M s).card) ^ theta *
          (∑ y ∈ centralLevelEndpointSet M s theta eta,
            (centralLevelFiberCard M s theta eta y : ℝ) ^
              (1 + theta)) := by
  classical
  have hNnat : 0 < (sourceOddLevel M s).card := by
    rw [card_sourceOddLevel]
    exact Nat.choose_pos hs
  have hN : 0 < ((sourceOddLevel M s).card : ℝ) := by
    exact_mod_cast hNnat
  have hR : 0 < (3 : ℝ) ^ (s + 1) := by positivity
  rw [centralLevelBadMass_eq_sum_bad]
  push_cast
  calc
    (∑ y ∈ centralLevelBadEndpointSet S M s theta eta,
        (centralLevelFiberCard M s theta eta y : ℝ)) ≤
      ∑ y ∈ centralLevelBadEndpointSet S M s theta eta,
        (Q * ((sourceOddLevel M s).card : ℝ) /
            (3 : ℝ) ^ (s + 1) +
          Q ^ (-theta) *
            (((3 : ℝ) ^ (s + 1)) /
              (sourceOddLevel M s).card) ^ theta *
            (centralLevelFiberCard M s theta eta y : ℝ) ^
              (1 + theta)) := by
        apply Finset.sum_le_sum
        intro y hy
        exact fiber_le_ordinary_add_renyi hQ hN hR (by positivity) htheta
    _ = Q * ((sourceOddLevel M s).card : ℝ) /
          (3 : ℝ) ^ (s + 1) *
          (centralLevelBadEndpointSet S M s theta eta).card +
        Q ^ (-theta) *
          (((3 : ℝ) ^ (s + 1)) /
            (sourceOddLevel M s).card) ^ theta *
          (∑ y ∈ centralLevelBadEndpointSet S M s theta eta,
            (centralLevelFiberCard M s theta eta y : ℝ) ^
              (1 + theta)) := by
        rw [Finset.sum_add_distrib]
        congr 1
        · simp only [Finset.sum_const, nsmul_eq_mul]
          ring
        · rw [Finset.mul_sum]
    _ ≤ Q * ((sourceOddLevel M s).card : ℝ) /
          (3 : ℝ) ^ (s + 1) *
          (centralLevelBadEndpointSet S M s theta eta).card +
        Q ^ (-theta) *
          (((3 : ℝ) ^ (s + 1)) /
            (sourceOddLevel M s).card) ^ theta *
          (∑ y ∈ centralLevelEndpointSet M s theta eta,
            (centralLevelFiberCard M s theta eta y : ℝ) ^
              (1 + theta)) := by
        gcongr
        intro y hy
        exact (Finset.mem_filter.mp hy).1

theorem centralLevelRenyiFactor_eq
    (M s : ℕ) (theta eta : ℝ) :
    ((((3 : ℝ) ^ (s + 1)) /
        (sourceOddLevel M s).card) ^ theta) *
      (∑ y ∈ centralLevelEndpointSet M s theta eta,
        (centralLevelFiberCard M s theta eta y : ℝ) ^ (1 + theta)) =
      centralLevelRenyiInformation M s theta eta := by
  unfold centralLevelRenyiInformation
  rw [Real.div_rpow (by positivity) (by positivity)]

/-- One central odd-count level after inserting the target density. -/
theorem centralLevelBadMass_cast_le
    {S : Set ℕ} {C D : ℝ}
    (hS : QuantitativeDensity.IsCDDense S C D)
    (M s : ℕ) (theta eta Q : ℝ)
    (hQ : 0 < Q) (htheta : 0 < theta) (hs : s ≤ M) :
    (centralLevelBadMass S M s theta eta : ℝ) ≤
      C * Q * (sourceOddLevel M s).card *
          (Real.exp (-D * Real.log 3)) ^ (s + 1) +
        Q ^ (-theta) * centralLevelRenyiInformation M s theta eta := by
  have hraw := centralLevelBadMass_cast_le_raw
    S M s theta eta Q hQ htheta hs
  have hcard := card_centralLevelBadEndpointSet_le hS M s theta eta
  calc
    (centralLevelBadMass S M s theta eta : ℝ) ≤
      Q * ((sourceOddLevel M s).card : ℝ) /
          (3 : ℝ) ^ (s + 1) *
          (centralLevelBadEndpointSet S M s theta eta).card +
        Q ^ (-theta) *
          (((3 : ℝ) ^ (s + 1)) /
            (sourceOddLevel M s).card) ^ theta *
          (∑ y ∈ centralLevelEndpointSet M s theta eta,
            (centralLevelFiberCard M s theta eta y : ℝ) ^
              (1 + theta)) := hraw
    _ ≤ Q * ((sourceOddLevel M s).card : ℝ) /
          (3 : ℝ) ^ (s + 1) *
          (C * ((3 : ℝ) ^ (s + 1)) ^ (1 - D)) +
        Q ^ (-theta) *
          (((3 : ℝ) ^ (s + 1)) /
            (sourceOddLevel M s).card) ^ theta *
          (∑ y ∈ centralLevelEndpointSet M s theta eta,
            (centralLevelFiberCard M s theta eta y : ℝ) ^
              (1 + theta)) := by
        gcongr
    _ = C * Q * (sourceOddLevel M s).card *
          (Real.exp (-D * Real.log 3)) ^ (s + 1) +
        Q ^ (-theta) * centralLevelRenyiInformation M s theta eta := by
      rw [show
        Q ^ (-theta) *
              (((3 : ℝ) ^ (s + 1)) /
                (sourceOddLevel M s).card) ^ theta *
              (∑ y ∈ centralLevelEndpointSet M s theta eta,
                (centralLevelFiberCard M s theta eta y : ℝ) ^
                  (1 + theta)) =
            Q ^ (-theta) *
              (((((3 : ℝ) ^ (s + 1)) /
                (sourceOddLevel M s).card) ^ theta) *
              (∑ y ∈ centralLevelEndpointSet M s theta eta,
                (centralLevelFiberCard M s theta eta y : ℝ) ^
                  (1 + theta))) by ring]
      rw [centralLevelRenyiFactor_eq]
      rw [show
        Q * ((sourceOddLevel M s).card : ℝ) /
              (3 : ℝ) ^ (s + 1) *
              (C * ((3 : ℝ) ^ (s + 1)) ^ (1 - D)) =
            C * Q * (sourceOddLevel M s).card *
              ((((3 : ℝ) ^ (s + 1)) ^ (1 - D)) /
                (3 : ℝ) ^ (s + 1)) by ring]
      rw [three_pow_rpow_one_sub_div]

/-- Exact odd-count decomposition of the retained central bad source. -/
theorem card_centralSourceEndpointBad_eq_sum
    (S : Set ℕ) (M : ℕ) (theta eta : ℝ) :
    (centralSourceEndpointBad S M theta eta).card =
      ∑ s ∈ Finset.range (M + 1),
        centralLevelBadMass S M s theta eta := by
  classical
  have hmap :
      ∀ x ∈ centralSourceSet M theta eta,
        sourceCodeOddCount x ∈ Finset.range (M + 1) := by
    intro x hx
    exact Finset.mem_range.mpr
      (Nat.lt_succ_of_le (sourceCodeOddCount_le x))
  calc
    (centralSourceEndpointBad S M theta eta).card =
        ∑ x ∈ centralSourceSet M theta eta,
          if sourceEndpoint x ∉ S then 1 else 0 := by
      rw [centralSourceEndpointBad, Finset.card_filter]
    _ = ∑ s ∈ Finset.range (M + 1),
          ∑ x ∈ (centralSourceSet M theta eta).filter
              (fun x => sourceCodeOddCount x = s),
            if sourceEndpoint x ∉ S then 1 else 0 := by
      symm
      exact Finset.sum_fiberwise_of_maps_to
        (s := centralSourceSet M theta eta)
        (t := Finset.range (M + 1))
        (g := sourceCodeOddCount) hmap
        (fun x => if sourceEndpoint x ∉ S then 1 else 0)
    _ = ∑ s ∈ Finset.range (M + 1),
          centralLevelBadMass S M s theta eta := by
      apply Finset.sum_congr rfl
      intro s hs
      unfold centralLevelBadMass centralLevelSourceSet sourceOddLevel
      rw [Finset.card_filter]
      simp only [Finset.filter_filter]
      apply Finset.sum_congr
      · ext x
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        tauto
      · intro x hx
        rfl

theorem sourceEndpointBad_subset_central_union
    (S : Set ℕ) (M : ℕ) (theta eta : ℝ) :
    sourceEndpointBad S M ⊆
      centralDiscardedSourceSet M theta eta ∪
        centralSourceEndpointBad S M theta eta := by
  classical
  intro x hx
  rw [sourceEndpointBad, Finset.mem_filter] at hx
  by_cases hc : x ∈ centralSourceSet M theta eta
  · exact Finset.mem_union_right _ (by
      rw [centralSourceEndpointBad, Finset.mem_filter]
      exact ⟨hc, hx.2⟩)
  · exact Finset.mem_union_left _
      (mem_centralDiscardedSourceSet_iff.mpr hc)

theorem card_sourceEndpointBad_le_discard_add_central
    (S : Set ℕ) (M : ℕ) (theta eta : ℝ) :
    (sourceEndpointBad S M).card ≤
      (centralDiscardedSourceSet M theta eta).card +
        (centralSourceEndpointBad S M theta eta).card := by
  calc
    (sourceEndpointBad S M).card ≤
        (centralDiscardedSourceSet M theta eta ∪
          centralSourceEndpointBad S M theta eta).card :=
      Finset.card_le_card
        (sourceEndpointBad_subset_central_union S M theta eta)
    _ ≤ (centralDiscardedSourceSet M theta eta).card +
          (centralSourceEndpointBad S M theta eta).card :=
      Finset.card_union_le _ _

/-- Exact retained-central shell estimate before choosing the overload
threshold. -/
theorem centralSourceEndpointBad_div_pow_le
    {S : Set ℕ} {C D : ℝ}
    (hS : QuantitativeDensity.IsCDDense S C D)
    (M : ℕ) (theta eta Q : ℝ)
    (hQ : 0 < Q) (htheta : 0 < theta) :
    ((centralSourceEndpointBad S M theta eta).card : ℝ) /
        (2 ^ M : ℝ) ≤
      C * Q * Real.exp (-D * Real.log 3) *
          ((1 + Real.exp (-D * Real.log 3)) / 2) ^ M +
        Q ^ (-theta) * centralEndpointInformation M theta eta := by
  classical
  rw [card_centralSourceEndpointBad_eq_sum]
  push_cast
  have hlevels :
      (∑ s ∈ Finset.range (M + 1),
          (centralLevelBadMass S M s theta eta : ℝ)) ≤
        ∑ s ∈ Finset.range (M + 1),
          (C * Q * (sourceOddLevel M s).card *
              (Real.exp (-D * Real.log 3)) ^ (s + 1) +
            Q ^ (-theta) *
              centralLevelRenyiInformation M s theta eta) := by
    apply Finset.sum_le_sum
    intro s hs
    exact centralLevelBadMass_cast_le hS M s theta eta Q hQ htheta
      (Nat.le_of_lt_succ (Finset.mem_range.mp hs))
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 ^ M)).2
  calc
    (∑ s ∈ Finset.range (M + 1),
        (centralLevelBadMass S M s theta eta : ℝ)) ≤
      ∑ s ∈ Finset.range (M + 1),
        (C * Q * (sourceOddLevel M s).card *
            (Real.exp (-D * Real.log 3)) ^ (s + 1) +
          Q ^ (-theta) *
            centralLevelRenyiInformation M s theta eta) := hlevels
    _ = C * Q * Real.exp (-D * Real.log 3) *
          (1 + Real.exp (-D * Real.log 3)) ^ M +
        Q ^ (-theta) *
          (∑ s ∈ Finset.range (M + 1),
            centralLevelRenyiInformation M s theta eta) := by
      rw [Finset.sum_add_distrib]
      have hchoose :
          (∑ s ∈ Finset.range (M + 1),
            (M.choose s : ℝ) *
              (Real.exp (-D * Real.log 3)) ^ s) =
            (1 + Real.exp (-D * Real.log 3)) ^ M := by
        calc
          (∑ s ∈ Finset.range (M + 1),
              (M.choose s : ℝ) *
                (Real.exp (-D * Real.log 3)) ^ s) =
              (Real.exp (-D * Real.log 3) + 1) ^ M := by
            rw [add_pow]
            apply Finset.sum_congr rfl
            intro s hs
            simp [mul_assoc, mul_left_comm, mul_comm]
          _ = (1 + Real.exp (-D * Real.log 3)) ^ M := by ring
      have hord :
          (∑ s ∈ Finset.range (M + 1),
            C * Q * ((sourceOddLevel M s).card : ℝ) *
              (Real.exp (-D * Real.log 3)) ^ (s + 1)) =
            C * Q * Real.exp (-D * Real.log 3) *
              (1 + Real.exp (-D * Real.log 3)) ^ M := by
        simp_rw [card_sourceOddLevel]
        rw [show
          (∑ s ∈ Finset.range (M + 1),
            C * Q * (M.choose s : ℝ) *
              (Real.exp (-D * Real.log 3)) ^ (s + 1)) =
            C * Q * Real.exp (-D * Real.log 3) *
              (∑ s ∈ Finset.range (M + 1),
                (M.choose s : ℝ) *
                  (Real.exp (-D * Real.log 3)) ^ s) by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro s hs
            ring]
        rw [hchoose]
      have hrenyi :
          (∑ s ∈ Finset.range (M + 1),
            Q ^ (-theta) *
              centralLevelRenyiInformation M s theta eta) =
            Q ^ (-theta) *
              (∑ s ∈ Finset.range (M + 1),
                centralLevelRenyiInformation M s theta eta) := by
        rw [Finset.mul_sum]
      rw [hord, hrenyi]
    _ = (C * Q * Real.exp (-D * Real.log 3) *
          ((1 + Real.exp (-D * Real.log 3)) / 2) ^ M +
        Q ^ (-theta) * centralEndpointInformation M theta eta) *
          (2 ^ M : ℝ) := by
      unfold centralEndpointInformation
      rw [div_pow]
      field_simp

/-- Balanced higher-Renyi shell rate. -/
def centralRenyiRate (theta D : ℝ) : ℝ :=
  theta / (1 + theta) * OptimizedLinearPullback.psi D

/-- Central higher-Renyi shell rate normalized by the dyadic shell size
and by the input density exponent. -/
def centralRenyiNormalizedRate (theta D : ℝ) : ℝ :=
  centralRenyiRate theta D / (Real.log 2 * D)

/-- Limiting linear transport slope supplied by the central
`(1 + theta)`-moment. -/
def centralRenyiAsymptoticRate (theta : ℝ) : ℝ :=
  theta / (1 + theta) *
    (Real.log 3 / (2 * Real.log 2))

/-- The balanced central shell rate is asymptotically linear in the target
density exponent. -/
theorem tendsto_centralRenyiNormalizedRate_zero_right (theta : ℝ) :
    Filter.Tendsto (centralRenyiNormalizedRate theta)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (centralRenyiAsymptoticRate theta)) := by
  have h :=
    (OptimizedLinearPullback.tendsto_psi_div_zero_right.const_mul
      (theta / (1 + theta))).div_const (Real.log 2)
  convert h using 1
  · funext D
    unfold centralRenyiNormalizedRate centralRenyiRate
    ring
  · unfold centralRenyiAsymptoticRate
    ring

theorem centralRenyiAsymptoticRate_pos
    {theta : ℝ} (htheta : 0 < theta) :
    0 < centralRenyiAsymptoticRate theta := by
  unfold centralRenyiAsymptoticRate
  exact mul_pos (div_pos htheta (by linarith))
    (div_pos (Real.log_pos (by norm_num))
      (mul_pos (by norm_num) (Real.log_pos (by norm_num))))

/-- Fixed exponential fraction retained when the polynomial moment cost is
absorbed. -/
def centralRenyiAbsorption (theta transport : ℝ) : ℝ :=
  (transport + centralRenyiAsymptoticRate theta) /
    (2 * centralRenyiAsymptoticRate theta)

/-- Absorbed central shell rate for a chosen transport coefficient. -/
def centralRenyiShellRate (theta transport D : ℝ) : ℝ :=
  centralRenyiAbsorption theta transport * centralRenyiRate theta D

/-- Dyadically normalized absorbed central shell rate. -/
def centralRenyiNormalizedShellRate
    (theta transport D : ℝ) : ℝ :=
  centralRenyiShellRate theta transport D / (Real.log 2 * D)

theorem centralRenyiAbsorption_pos
    {theta transport : ℝ}
    (htheta : 0 < theta) (htransport : 0 < transport) :
    0 < centralRenyiAbsorption theta transport := by
  unfold centralRenyiAbsorption
  exact div_pos
    (add_pos htransport (centralRenyiAsymptoticRate_pos htheta))
    (mul_pos (by norm_num) (centralRenyiAsymptoticRate_pos htheta))

theorem centralRenyiAbsorption_lt_one
    {theta transport : ℝ}
    (htheta : 0 < theta)
    (htransport : transport < centralRenyiAsymptoticRate theta) :
    centralRenyiAbsorption theta transport < 1 := by
  unfold centralRenyiAbsorption
  have hlimit := centralRenyiAsymptoticRate_pos htheta
  rw [div_lt_one (by positivity)]
  linarith

theorem transport_lt_absorption_mul_centralRenyiAsymptoticRate
    {theta transport : ℝ}
    (htheta : 0 < theta)
    (htransport : transport < centralRenyiAsymptoticRate theta) :
    transport < centralRenyiAbsorption theta transport *
      centralRenyiAsymptoticRate theta := by
  unfold centralRenyiAbsorption
  have hlimit := centralRenyiAsymptoticRate_pos htheta
  have heq :
      (transport + centralRenyiAsymptoticRate theta) /
            (2 * centralRenyiAsymptoticRate theta) *
          centralRenyiAsymptoticRate theta =
        (transport + centralRenyiAsymptoticRate theta) / 2 := by
    field_simp [hlimit.ne']
    ring
  rw [heq]
  linarith

theorem tendsto_centralRenyiNormalizedShellRate_zero_right
    (theta transport : ℝ) :
    Filter.Tendsto (centralRenyiNormalizedShellRate theta transport)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (centralRenyiAbsorption theta transport *
        centralRenyiAsymptoticRate theta)) := by
  have h :=
    (tendsto_centralRenyiNormalizedRate_zero_right theta).const_mul
      (centralRenyiAbsorption theta transport)
  exact h.congr' (Filter.Eventually.of_forall fun D => by
    simp only [centralRenyiNormalizedShellRate, centralRenyiShellRate,
      centralRenyiNormalizedRate, div_eq_mul_inv, mul_inv]
    ring)

theorem tendsto_centralRenyiShellRate_zero_right
    (theta transport : ℝ) :
    Filter.Tendsto (centralRenyiShellRate theta transport)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  have hpsi :
      Filter.Tendsto OptimizedLinearPullback.psi
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    have h :=
      (OptimizedLinearPullback.hasDerivAt_psi 0).continuousAt.tendsto
    simpa [OptimizedLinearPullback.psi_zero] using
      (h.mono_left inf_le_left)
  have h :=
    (hpsi.const_mul (theta / (1 + theta))).const_mul
      (centralRenyiAbsorption theta transport)
  simpa [centralRenyiShellRate, centralRenyiRate] using h

/-- The central higher-Renyi rate dominates every fixed transport
coefficient below its limiting slope on a punctured neighborhood of zero. -/
theorem exists_centralRenyi_linear_cutoff
    {theta transport : ℝ}
    (htheta : 0 < theta)
    (htransport0 : 0 < transport)
    (htransport : transport < centralRenyiAsymptoticRate theta) :
    ∃ Dcut : ℝ, 0 < Dcut ∧ Dcut ≤ 1 ∧
      ∀ D : ℝ, 0 < D → D ≤ Dcut →
        transport * D ≤
          centralRenyiShellRate theta transport D / Real.log 2 := by
  have htend :=
    tendsto_centralRenyiNormalizedShellRate_zero_right theta transport
  have hopen :
      Set.Ioi transport ∈
        nhds (centralRenyiAbsorption theta transport *
          centralRenyiAsymptoticRate theta) :=
    Ioi_mem_nhds
      (transport_lt_absorption_mul_centralRenyiAsymptoticRate
        htheta htransport)
  have hevent := htend.eventually hopen
  rw [eventually_nhdsWithin_iff] at hevent
  rcases Metric.eventually_nhds_iff.mp hevent with
    ⟨eps, heps, hball⟩
  let Dcut : ℝ := min (eps / 2) 1
  refine ⟨Dcut, ?_, min_le_right _ _, ?_⟩
  · dsimp [Dcut]
    positivity
  · intro D hD hDcut
    have hDeps : D < eps := by
      have hle : D ≤ eps / 2 := hDcut.trans (min_le_left _ _)
      linarith
    have hdist : dist D 0 < eps := by
      rw [Real.dist_eq]
      simpa [abs_of_pos hD] using hDeps
    have hnorm :
        transport < centralRenyiNormalizedShellRate theta transport D :=
      hball hdist hD
    have hscaled := mul_le_mul_of_nonneg_right hnorm.le hD.le
    calc
      transport * D ≤
          centralRenyiNormalizedShellRate theta transport D * D :=
        hscaled
      _ = centralRenyiShellRate theta transport D / Real.log 2 := by
        unfold centralRenyiNormalizedShellRate
        field_simp [hD.ne',
          (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne']
        ring

/-- Small-density cutoff that simultaneously preserves the desired linear
transport and leaves enough exponential room to absorb both discarded
cohort terms. -/
theorem exists_centralRenyi_full_cutoff
    {theta transport eta : ℝ}
    (htheta : 0 < theta) (heta : 0 < eta)
    (htransport0 : 0 < transport)
    (htransport : transport < centralRenyiAsymptoticRate theta) :
    ∃ Dcut : ℝ, 0 < Dcut ∧ Dcut ≤ 1 ∧
      ∀ D : ℝ, 0 < D → D ≤ Dcut →
        transport * D ≤
            centralRenyiShellRate theta transport D / Real.log 2 ∧
        centralRenyiShellRate theta transport D ≤
            eta * Real.log 2 / 16 ∧
        centralRenyiShellRate theta transport D ≤ eta ^ 2 / 8 := by
  obtain ⟨Dlinear, hDlinear0, hDlinear1, hlinear⟩ :=
    exists_centralRenyi_linear_cutoff htheta htransport0 htransport
  let cap := min (eta * Real.log 2 / 16) (eta ^ 2 / 8)
  have hcap : 0 < cap := by
    dsimp [cap]
    exact lt_min
      (div_pos (mul_pos heta (Real.log_pos (by norm_num))) (by norm_num))
      (div_pos (sq_pos_of_pos heta) (by norm_num))
  have htend := tendsto_centralRenyiShellRate_zero_right theta transport
  have hopen : Set.Iio cap ∈ nhds (0 : ℝ) := Iio_mem_nhds hcap
  have hevent := htend.eventually hopen
  rw [eventually_nhdsWithin_iff] at hevent
  rcases Metric.eventually_nhds_iff.mp hevent with ⟨eps, heps, hball⟩
  let Dcut := min Dlinear (eps / 2)
  refine ⟨Dcut, ?_, ?_, ?_⟩
  · dsimp [Dcut]
    exact lt_min hDlinear0 (half_pos heps)
  · exact (min_le_left _ _).trans hDlinear1
  · intro D hD hDcut
    have hlin := hlinear D hD (hDcut.trans (min_le_left _ _))
    have hDeps : D < eps := by
      have hle := hDcut.trans (min_le_right _ _)
      linarith
    have hdist : dist D 0 < eps := by
      rw [Real.dist_eq]
      simpa [abs_of_pos hD] using hDeps
    have hrateLt : centralRenyiShellRate theta transport D < cap :=
      hball hdist hD
    exact ⟨hlin,
      hrateLt.le.trans (min_le_left _ _),
      hrateLt.le.trans (min_le_right _ _)⟩

/-- Number of initial dyadic digits discarded before applying the central
fixed-total estimate. -/
def centralRenyiDiscardDepth (eta : ℝ) (M : ℕ) : ℕ :=
  ⌊eta * M / 8⌋₊

/-- One explicit scale above which every finite startup condition in the
central fixed-total theorem holds. -/
def centralRenyiStartupScale (theta eta : ℝ) : ℝ :=
  max 4 <| max (4 / eta) <|
    max (2 / (1 / 2 - eta)) <|
      max (4 + 4 * eta / centralRenyiGap theta eta)
        (1 / (Real.log 2 / Real.log 3 - (1 / 2 + eta)))

/-- The canonical discard depth discharges all finite startup hypotheses
once the shell is above `centralRenyiStartupScale`. -/
theorem centralRenyi_startup
    {theta eta : ℝ}
    (htheta0 : 0 < theta)
    (heta0 : 0 < eta)
    (heta1 : eta < centralRenyiAlpha theta - 1 / 2)
    {M : ℕ} (hM : centralRenyiStartupScale theta eta ≤ M) :
    let K := centralRenyiDiscardDepth eta M
    K ≤ M ∧
    (K : ℝ) ≤ eta * M / 8 ∧
    4 ≤ eta * M ∧
    ∀ N : ℕ, M - K ≤ N → N ≤ M →
      1 < N ∧
      (1 / 2 - eta) * N > 1 / 2 ∧
      2 * eta ≤ centralRenyiGap theta eta * ((N : ℝ) - 1) ∧
      (1 / 2 : ℝ) ≤
        (Real.log 2 / Real.log 3 - (1 / 2 + eta)) * N := by
  dsimp only
  have hetaHalf : eta < 1 / 2 := by
    have ha := centralRenyiAlpha_lt_log_ratio htheta0
    have hlog : Real.log 2 / Real.log 3 < 1 := by
      rw [div_lt_one (Real.log_pos (by norm_num))]
      exact Real.strictMonoOn_log (by norm_num) (by norm_num) (by norm_num)
    linarith
  let gap := centralRenyiGap theta eta
  have hgap : 0 < gap := centralRenyiGap_pos heta1
  let drift := Real.log 2 / Real.log 3 - (1 / 2 + eta)
  have hdrift : 0 < drift := by
    dsimp [drift]
    linarith [centralRenyiAlpha_lt_log_ratio htheta0]
  unfold centralRenyiStartupScale at hM
  rcases max_le_iff.mp hM with ⟨hM4, hM⟩
  rcases max_le_iff.mp hM with ⟨hetaScale, hM⟩
  rcases max_le_iff.mp hM with ⟨hhalfScale, hM⟩
  rcases max_le_iff.mp hM with ⟨hgapScale, hdriftScale⟩
  let K := centralRenyiDiscardDepth eta M
  have harg0 : 0 ≤ eta * (M : ℝ) / 8 := by positivity
  have hKcast : (K : ℝ) ≤ eta * M / 8 := by
    dsimp [K, centralRenyiDiscardDepth]
    exact Nat.floor_le harg0
  have hKhalfR : (K : ℝ) ≤ (M : ℝ) / 2 := by
    have hMr : 0 ≤ (M : ℝ) := by positivity
    nlinarith
  have h2K : 2 * K ≤ M := by
    exact_mod_cast (show 2 * (K : ℝ) ≤ M by linarith)
  have hKM : K ≤ M := by omega
  refine ⟨hKM, hKcast, ?_, ?_⟩
  · have hmul := mul_le_mul_of_nonneg_left hetaScale heta0.le
    field_simp [heta0.ne'] at hmul
    simpa [mul_comm] using hmul
  · intro N hNlower hNupper
    have hMNnat : M ≤ 2 * N := by omega
    have hMN : (M : ℝ) / 2 ≤ N := by
      have hcast : (M : ℝ) ≤ 2 * (N : ℝ) := by exact_mod_cast hMNnat
      linarith
    have hM4nat : 4 ≤ M := by exact_mod_cast hM4
    have hN2 : 2 ≤ N := by omega
    refine ⟨by omega, ?_, ?_, ?_⟩
    · have hhalf0 : 0 < 1 / 2 - eta := by linarith
      have hs := mul_le_mul_of_nonneg_left hhalfScale hhalf0.le
      have hbase : 2 ≤ (1 / 2 - eta) * M := by
        calc
          2 = (1 / 2 - eta) * (2 / (1 / 2 - eta)) := by
            rw [show
              (1 / 2 - eta) * (2 / (1 / 2 - eta)) =
                2 * ((1 / 2 - eta) / (1 / 2 - eta)) by ring]
            rw [div_self hhalf0.ne']
            norm_num
          _ ≤ (1 / 2 - eta) * M := hs
      nlinarith [mul_le_mul_of_nonneg_left hMN hhalf0.le]
    · change 2 * eta ≤ gap * ((N : ℝ) - 1)
      change 4 + 4 * eta / gap ≤ (M : ℝ) at hgapScale
      have hs := mul_le_mul_of_nonneg_left hgapScale hgap.le
      have hbase :
          gap * (4 + 4 * eta / gap) ≤ gap * M := hs
      have hNminus : (M : ℝ) / 2 - 1 ≤ N - 1 := by linarith
      have hmono := mul_le_mul_of_nonneg_left hNminus hgap.le
      have hid : gap * (4 + 4 * eta / gap) = 4 * gap + 4 * eta := by
        field_simp [hgap.ne']
      rw [hid] at hbase
      nlinarith
    · change (1 / 2 : ℝ) ≤ drift * N
      change 1 / drift ≤ (M : ℝ) at hdriftScale
      have hs := mul_le_mul_of_nonneg_left hdriftScale hdrift.le
      have hbase : 1 ≤ drift * M := by
        calc
          1 = drift * (1 / drift) := by
            rw [one_div, mul_inv_cancel₀ hdrift.ne']
          _ ≤ _ := hs
      have hhalf : (1 / 2 : ℝ) ≤ drift * ((M : ℝ) / 2) := by
        calc
          (1 : ℝ) / 2 ≤ (drift * M) / 2 :=
            div_le_div_of_nonneg_right hbase (by norm_num)
          _ = drift * ((M : ℝ) / 2) := by ring
      exact hhalf.trans (mul_le_mul_of_nonneg_left hMN hdrift.le)

/-- Exact real form of the late-first-odd discard ratio. -/
theorem centralRenyi_lateDiscardRatio_eq
    {M K : ℕ} (hKM : K ≤ M) :
    ((((M + 1) * 2 ^ (M - K) : ℕ) : ℝ) / (2 ^ M : ℝ)) =
      (M + 1 : ℝ) * Real.exp (-(Real.log 2) * K) := by
  push_cast
  rw [pow_sub₀ (2 : ℝ) (by norm_num) hKM]
  have hpow : (2 : ℝ) ^ K = Real.exp (Real.log 2 * K) := by
    rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by norm_num)]
  rw [hpow, show -Real.log 2 * (K : ℝ) =
      -(Real.log 2 * K) by ring, Real.exp_neg]
  field_simp
  ring

/-- Exponential estimate for the late-first-odd discard under the canonical
central cutoff. -/
theorem centralRenyi_lateDiscardRatio_le
    (eta : ℝ) (M : ℕ)
    (hKM : centralRenyiDiscardDepth eta M ≤ M) :
    (((((M + 1) *
        2 ^ (M - centralRenyiDiscardDepth eta M) : ℕ) : ℝ) /
        (2 ^ M : ℝ))) ≤
      2 * (M + 1 : ℝ) *
        Real.exp (-(eta * Real.log 2 / 8) * M) := by
  let K := centralRenyiDiscardDepth eta M
  rw [centralRenyi_lateDiscardRatio_eq hKM]
  have hfloor := Nat.lt_floor_add_one (eta * (M : ℝ) / 8)
  have hKlower : eta * (M : ℝ) / 8 - 1 < K := by
    dsimp [K, centralRenyiDiscardDepth]
    linarith
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hexp :
      Real.exp (-(Real.log 2) * K) ≤
        2 * Real.exp (-(eta * Real.log 2 / 8) * M) := by
    have hmono :
        -(Real.log 2) * K ≤
          -(Real.log 2) * (eta * (M : ℝ) / 8 - 1) := by
      nlinarith
    have hid :
        Real.exp (-(Real.log 2) * (eta * (M : ℝ) / 8 - 1)) =
          2 * Real.exp (-(eta * Real.log 2 / 8) * M) := by
      rw [show
        -(Real.log 2) * (eta * (M : ℝ) / 8 - 1) =
          Real.log 2 + (-(eta * Real.log 2 / 8) * M) by ring]
      rw [Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    rw [← hid]
    exact Real.exp_le_exp.mpr hmono
  calc
    (M + 1 : ℝ) * Real.exp (-(Real.log 2) * K) ≤
        (M + 1 : ℝ) *
          (2 * Real.exp (-(eta * Real.log 2 / 8) * M)) :=
      mul_le_mul_of_nonneg_left hexp (by positivity)
    _ = 2 * (M + 1 : ℝ) *
          Real.exp (-(eta * Real.log 2 / 8) * M) := by ring

/-- Sixth-degree polynomial absorption used for the central moment
prefactor. -/
theorem sixth_pow_succ_mul_exp_neg_le
    {r zeta x : ℝ}
    (hr : 0 < r) (hzeta0 : 0 < zeta) (hzeta1 : zeta < 1)
    (hx : 1 ≤ x) :
    (x + 1) ^ 6 * Real.exp (-r * x) ≤
      64 * ((((1 - zeta) * r / 6)⁻¹) ^ 6) *
        Real.exp (-(zeta * r) * x) := by
  let a := (1 - zeta) * r / 6
  have ha : 0 < a := by
    dsimp [a]
    exact div_pos (mul_pos (sub_pos.mpr hzeta1) hr) (by norm_num)
  have hax : a * x ≤ Real.exp (a * x) := by
    nlinarith [Real.add_one_le_exp (a * x)]
  have hxexp : x ≤ a⁻¹ * Real.exp (a * x) := by
    calc
      x = a⁻¹ * (a * x) := by field_simp [ha.ne']
      _ ≤ a⁻¹ * Real.exp (a * x) :=
        mul_le_mul_of_nonneg_left hax (inv_nonneg.mpr ha.le)
  have hsucc : x + 1 ≤ 2 * x := by linarith
  have hpow :
      (x + 1) ^ 6 ≤
        64 * (a⁻¹) ^ 6 * Real.exp (6 * (a * x)) := by
    calc
      (x + 1) ^ 6 ≤ (2 * x) ^ 6 := by
        exact pow_le_pow_left₀ (by positivity) hsucc 6
      _ = 64 * x ^ 6 := by ring
      _ ≤ 64 * (a⁻¹ * Real.exp (a * x)) ^ 6 := by
        gcongr
      _ = 64 * (a⁻¹) ^ 6 * Real.exp (6 * (a * x)) := by
        rw [mul_pow, ← Real.exp_nat_mul]
        ring
  calc
    (x + 1) ^ 6 * Real.exp (-r * x) ≤
        (64 * (a⁻¹) ^ 6 * Real.exp (6 * (a * x))) *
          Real.exp (-r * x) :=
      mul_le_mul_of_nonneg_right hpow (Real.exp_nonneg _)
    _ = 64 * (a⁻¹) ^ 6 * Real.exp (-(zeta * r) * x) := by
      rw [show
        64 * (a⁻¹) ^ 6 * Real.exp (6 * (a * x)) * Real.exp (-r * x) =
          64 * (a⁻¹) ^ 6 *
            (Real.exp (6 * (a * x)) * Real.exp (-r * x)) by ring]
      rw [← Real.exp_add]
      congr 2
      dsimp [a]
      ring
    _ = _ := by rfl

/-- First-degree polynomial absorption used for the late-first-odd
discard. -/
theorem succ_mul_exp_neg_le
    {r zeta x : ℝ}
    (hr : 0 < r) (hzeta0 : 0 < zeta) (hzeta1 : zeta < 1)
    (hx : 1 ≤ x) :
    (x + 1) * Real.exp (-r * x) ≤
      2 * (((1 - zeta) * r)⁻¹) *
        Real.exp (-(zeta * r) * x) := by
  let a := (1 - zeta) * r
  have ha : 0 < a := by
    dsimp [a]
    exact mul_pos (sub_pos.mpr hzeta1) hr
  have hax : a * x ≤ Real.exp (a * x) := by
    nlinarith [Real.add_one_le_exp (a * x)]
  have hxexp : x ≤ a⁻¹ * Real.exp (a * x) := by
    calc
      x = a⁻¹ * (a * x) := by field_simp [ha.ne']
      _ ≤ a⁻¹ * Real.exp (a * x) :=
        mul_le_mul_of_nonneg_left hax (inv_nonneg.mpr ha.le)
  have hsucc : x + 1 ≤ 2 * x := by linarith
  have hfront : x + 1 ≤ 2 * (a⁻¹ * Real.exp (a * x)) := by
    exact hsucc.trans
      (mul_le_mul_of_nonneg_left hxexp (by norm_num))
  calc
    (x + 1) * Real.exp (-r * x) ≤
        (2 * (a⁻¹ * Real.exp (a * x))) *
          Real.exp (-r * x) := by
      exact mul_le_mul_of_nonneg_right hfront (Real.exp_nonneg _)
    _ = 2 * a⁻¹ * Real.exp (-(zeta * r) * x) := by
      rw [show
        2 * (a⁻¹ * Real.exp (a * x)) * Real.exp (-r * x) =
          2 * a⁻¹ * (Real.exp (a * x) * Real.exp (-r * x)) by ring]
      rw [← Real.exp_add]
      congr 2
      dsimp [a]
      ring
    _ = _ := by rfl

/-- Optimal normalized overload threshold for the central split. -/
def centralRenyiThreshold (theta D : ℝ) (M : ℕ) : ℝ :=
  Real.exp
    ((OptimizedLinearPullback.psi D / (1 + theta)) * M)

theorem centralRenyiRate_pos
    {theta D : ℝ} (htheta : 0 < theta) (hD : 0 < D) :
    0 < centralRenyiRate theta D := by
  unfold centralRenyiRate
  exact mul_pos (div_pos htheta (by linarith))
    (OptimizedLinearPullback.psi_pos hD)

theorem centralRenyiThreshold_pos
    (theta D : ℝ) (M : ℕ) :
    0 < centralRenyiThreshold theta D M :=
  Real.exp_pos _

theorem centralRenyiThreshold_neg_rpow
    {theta D : ℝ} (M : ℕ) (htheta : 0 < theta) :
    (centralRenyiThreshold theta D M) ^ (-theta) =
      Real.exp (-centralRenyiRate theta D * M) := by
  unfold centralRenyiThreshold centralRenyiRate
  rw [← Real.exp_mul]
  congr 1
  have hden : 0 < 1 + theta := by linarith
  field_simp [hden.ne']
  ring

theorem centralRenyiThreshold_mul_oddRate
    {theta D : ℝ} (M : ℕ) (htheta : 0 < theta) :
    centralRenyiThreshold theta D M *
        ((1 + Real.exp (-D * Real.log 3)) / 2) ^ M =
      Real.exp (-centralRenyiRate theta D * M) := by
  rw [oddCountRate_pow_eq_exp]
  unfold centralRenyiThreshold centralRenyiRate
  rw [← Real.exp_add]
  congr 1
  have hden : 0 < 1 + theta := by linarith
  field_simp [hden.ne']
  ring

/-- Balanced retained-central shell estimate.  The polynomial factor is
explicit and does not alter the exponential rate. -/
theorem centralSourceEndpointBad_div_pow_le_balanced
    {S : Set ℕ} {C D theta eta : ℝ}
    (hS : QuantitativeDensity.IsCDDense S C D)
    (htheta0 : 0 < theta) (htheta1 : theta < 1)
    (heta0 : 0 < eta)
    (heta1 : eta < centralRenyiAlpha theta - 1 / 2)
    (M : ℕ) :
    ((centralSourceEndpointBad S M theta eta).card : ℝ) /
        (2 ^ M : ℝ) ≤
      (C * Real.exp (-D * Real.log 3) +
          (3 : ℝ) ^ theta * centralMomentConstant theta eta *
            (M + 1 : ℝ) ^ 6) *
        Real.exp (-centralRenyiRate theta D * M) := by
  have hbase := centralSourceEndpointBad_div_pow_le hS M theta eta
    (centralRenyiThreshold theta D M)
    (centralRenyiThreshold_pos theta D M) htheta0
  have hmoment := centralEndpointInformation_le
    htheta0 htheta1 heta0 heta1 (M := M)
  calc
    ((centralSourceEndpointBad S M theta eta).card : ℝ) /
          (2 ^ M : ℝ) ≤
      C * centralRenyiThreshold theta D M *
          Real.exp (-D * Real.log 3) *
          ((1 + Real.exp (-D * Real.log 3)) / 2) ^ M +
        (centralRenyiThreshold theta D M) ^ (-theta) *
          centralEndpointInformation M theta eta := hbase
    _ ≤ C * centralRenyiThreshold theta D M *
          Real.exp (-D * Real.log 3) *
          ((1 + Real.exp (-D * Real.log 3)) / 2) ^ M +
        (centralRenyiThreshold theta D M) ^ (-theta) *
          ((3 : ℝ) ^ theta * centralMomentConstant theta eta *
            (M + 1 : ℝ) ^ 6) := by
      exact add_le_add_left
        (mul_le_mul_of_nonneg_left hmoment
          (Real.rpow_nonneg (centralRenyiThreshold_pos theta D M).le _)) _
    _ = (C * Real.exp (-D * Real.log 3) +
          (3 : ℝ) ^ theta * centralMomentConstant theta eta *
            (M + 1 : ℝ) ^ 6) *
        Real.exp (-centralRenyiRate theta D * M) := by
      rw [centralRenyiThreshold_neg_rpow M htheta0]
      rw [show
        C * centralRenyiThreshold theta D M *
              Real.exp (-D * Real.log 3) *
              ((1 + Real.exp (-D * Real.log 3)) / 2) ^ M =
            C * Real.exp (-D * Real.log 3) *
              (centralRenyiThreshold theta D M *
                ((1 + Real.exp (-D * Real.log 3)) / 2) ^ M) by ring]
      rw [centralRenyiThreshold_mul_oddRate M htheta0]
      ring

/-- Full finite-shell theorem, including the explicit noncentral discard. -/
theorem sourceEndpointBad_div_pow_le_centralRenyi
    {S : Set ℕ} {C D theta eta : ℝ}
    (hS : QuantitativeDensity.IsCDDense S C D)
    (htheta0 : 0 < theta) (htheta1 : theta < 1)
    (heta0 : 0 < eta) (hetaHalf : eta ≤ 1 / 2)
    (heta1 : eta < centralRenyiAlpha theta - 1 / 2)
    (M K : ℕ) (hKM : K ≤ M)
    (hK : (K : ℝ) ≤ eta * M / 8)
    (hetaM : 4 ≤ eta * M)
    (hstartup : ∀ N : ℕ, M - K ≤ N → N ≤ M →
      1 < N ∧
      (1 / 2 - eta) * N > 1 / 2 ∧
      2 * eta ≤ centralRenyiGap theta eta * ((N : ℝ) - 1) ∧
      (1 / 2 : ℝ) ≤
        (Real.log 2 / Real.log 3 - (1 / 2 + eta)) * N) :
    ((sourceEndpointBad S M).card : ℝ) / (2 ^ M : ℝ) ≤
      (((M + 1) * 2 ^ (M - K) : ℕ) : ℝ) /
          (2 ^ M : ℝ) +
        2 * Real.exp (-2 * (eta / 4) ^ 2 * M) +
        (C * Real.exp (-D * Real.log 3) +
            (3 : ℝ) ^ theta * centralMomentConstant theta eta *
              (M + 1 : ℝ) ^ 6) *
          Real.exp (-centralRenyiRate theta D * M) := by
  have hsplit := card_sourceEndpointBad_le_discard_add_central
    S M theta eta
  have hdiscard := card_centralDiscardedSourceSet_cast_le
    hKM heta0 hetaHalf hK hetaM hstartup
  have hcentral := centralSourceEndpointBad_div_pow_le_balanced
    hS htheta0 htheta1 heta0 heta1 M
  have hpow : 0 < (2 : ℝ) ^ M := by positivity
  have hsplitR :
      ((sourceEndpointBad S M).card : ℝ) ≤
        (centralDiscardedSourceSet M theta eta).card +
          (centralSourceEndpointBad S M theta eta).card := by
    exact_mod_cast hsplit
  calc
    ((sourceEndpointBad S M).card : ℝ) / (2 ^ M : ℝ) ≤
        (((centralDiscardedSourceSet M theta eta).card : ℝ) +
          ((centralSourceEndpointBad S M theta eta).card : ℝ)) /
            (2 ^ M : ℝ) :=
      div_le_div_of_nonneg_right hsplitR hpow.le
    _ = ((centralDiscardedSourceSet M theta eta).card : ℝ) /
          (2 ^ M : ℝ) +
        ((centralSourceEndpointBad S M theta eta).card : ℝ) /
          (2 ^ M : ℝ) := by ring
    _ ≤ ((((M + 1) * 2 ^ (M - K) : ℕ) : ℝ) +
          (2 : ℝ) ^ M *
            (2 * Real.exp (-2 * (eta / 4) ^ 2 * M))) /
          (2 ^ M : ℝ) +
        (C * Real.exp (-D * Real.log 3) +
            (3 : ℝ) ^ theta * centralMomentConstant theta eta *
              (M + 1 : ℝ) ^ 6) *
          Real.exp (-centralRenyiRate theta D * M) := by
      gcongr
    _ = (((M + 1) * 2 ^ (M - K) : ℕ) : ℝ) /
          (2 ^ M : ℝ) +
        2 * Real.exp (-2 * (eta / 4) ^ 2 * M) +
        (C * Real.exp (-D * Real.log 3) +
            (3 : ℝ) ^ theta * centralMomentConstant theta eta *
              (M + 1 : ℝ) ^ 6) *
          Real.exp (-centralRenyiRate theta D * M) := by
      field_simp [hpow.ne']
      ring

/-- The full finite-shell theorem with all startup conditions discharged by
the explicit central startup scale. -/
theorem sourceEndpointBad_div_pow_le_centralRenyi_startup
    {S : Set ℕ} {C D theta eta : ℝ}
    (hS : QuantitativeDensity.IsCDDense S C D)
    (htheta0 : 0 < theta) (htheta1 : theta < 1)
    (heta0 : 0 < eta)
    (heta1 : eta < centralRenyiAlpha theta - 1 / 2)
    (M : ℕ) (hM : centralRenyiStartupScale theta eta ≤ M) :
    ((sourceEndpointBad S M).card : ℝ) / (2 ^ M : ℝ) ≤
      ((((M + 1) *
          2 ^ (M - centralRenyiDiscardDepth eta M) : ℕ) : ℝ) /
          (2 ^ M : ℝ)) +
        2 * Real.exp (-2 * (eta / 4) ^ 2 * M) +
        (C * Real.exp (-D * Real.log 3) +
            (3 : ℝ) ^ theta * centralMomentConstant theta eta *
              (M + 1 : ℝ) ^ 6) *
          Real.exp (-centralRenyiRate theta D * M) := by
  have hetaHalf : eta ≤ 1 / 2 := by
    have ha := centralRenyiAlpha_lt_log_ratio htheta0
    have hlog : Real.log 2 / Real.log 3 < 1 := by
      rw [div_lt_one (Real.log_pos (by norm_num))]
      exact Real.strictMonoOn_log (by norm_num) (by norm_num) (by norm_num)
    linarith
  obtain ⟨hKM, hK, hetaM, hstartup⟩ :=
    centralRenyi_startup htheta0 heta0 heta1 hM
  exact sourceEndpointBad_div_pow_le_centralRenyi
    hS htheta0 htheta1 heta0 hetaHalf heta1
    M (centralRenyiDiscardDepth eta M) hKM hK hetaM hstartup

/-- Explicit large-shell prefactor after absorbing all polynomial losses. -/
def centralRenyiLargeShellConstant
    (C theta eta transport D : ℝ) : ℝ :=
  C + 2 +
    4 * ((eta * Real.log 2 / 16)⁻¹) +
    (3 : ℝ) ^ theta * centralMomentConstant theta eta *
      (64 * ((((1 - centralRenyiAbsorption theta transport) *
        centralRenyiRate theta D / 6)⁻¹) ^ 6))

/-- Absorbed central-Renyi shell estimate above the explicit startup scale. -/
theorem sourceEndpointBad_div_pow_le_centralRenyi_absorbed_large
    {S : Set ℕ} {C D theta eta transport : ℝ}
    (hS : QuantitativeDensity.IsCDDense S C D)
    (htheta0 : 0 < theta) (htheta1 : theta < 1)
    (heta0 : 0 < eta)
    (heta1 : eta < centralRenyiAlpha theta - 1 / 2)
    (htransport0 : 0 < transport)
    (htransport : transport < centralRenyiAsymptoticRate theta)
    (hcutLate : centralRenyiShellRate theta transport D ≤
      eta * Real.log 2 / 16)
    (hcutParity : centralRenyiShellRate theta transport D ≤ eta ^ 2 / 8)
    (M : ℕ) (hM : centralRenyiStartupScale theta eta ≤ M) :
    ((sourceEndpointBad S M).card : ℝ) / (2 ^ M : ℝ) ≤
      centralRenyiLargeShellConstant C theta eta transport D *
        Real.exp (-centralRenyiShellRate theta transport D * M) := by
  let r := centralRenyiRate theta D
  let zeta := centralRenyiAbsorption theta transport
  let rs := centralRenyiShellRate theta transport D
  let rL := eta * Real.log 2 / 8
  let A := (3 : ℝ) ^ theta * centralMomentConstant theta eta
  have hr : 0 < r := centralRenyiRate_pos htheta0 hS.D_pos
  have hz0 : 0 < zeta := centralRenyiAbsorption_pos htheta0 htransport0
  have hz1 : zeta < 1 := centralRenyiAbsorption_lt_one htheta0 htransport
  have hrs : rs = zeta * r := rfl
  have hrL : 0 < rL := by dsimp [rL]; positivity
  have hA : 0 ≤ A := by
    dsimp [A]
    exact mul_nonneg (Real.rpow_nonneg (by norm_num) _)
      (centralMomentConstant_pos htheta0 htheta1 heta0 heta1).le
  have hM1 : (1 : ℝ) ≤ M := by
    have hscale : (4 : ℝ) ≤ centralRenyiStartupScale theta eta := by
      unfold centralRenyiStartupScale
      exact le_max_left _ _
    exact (show (1 : ℝ) ≤ 4 by norm_num).trans (hscale.trans hM)
  have hstart := sourceEndpointBad_div_pow_le_centralRenyi_startup
    hS htheta0 htheta1 heta0 heta1 M hM
  obtain ⟨hKM, _, _, _⟩ := centralRenyi_startup htheta0 heta0 heta1 hM
  have hlateRaw := centralRenyi_lateDiscardRatio_le eta M hKM
  have hlateAbs :
      (((((M + 1) * 2 ^ (M - centralRenyiDiscardDepth eta M) : ℕ) : ℝ) /
          (2 ^ M : ℝ))) ≤
        4 * ((eta * Real.log 2 / 16)⁻¹) *
          Real.exp (-rs * M) := by
    have hpoly := succ_mul_exp_neg_le hrL (by norm_num : (0 : ℝ) < 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1) hM1
    have hhalfRate : (1 / 2 : ℝ) * rL = eta * Real.log 2 / 16 := by
      dsimp [rL]
      ring
    have hrate : rs ≤ (1 / 2 : ℝ) * rL := by
      rw [hhalfRate]
      exact hcutLate
    have hexp : Real.exp (-((1 / 2 : ℝ) * rL) * M) ≤
        Real.exp (-rs * M) := by
      apply Real.exp_le_exp.mpr
      have hMr : 0 ≤ (M : ℝ) := by positivity
      nlinarith
    calc
      (((((M + 1) * 2 ^ (M - centralRenyiDiscardDepth eta M) : ℕ) : ℝ) /
          (2 ^ M : ℝ))) ≤
          2 * (M + 1 : ℝ) * Real.exp (-rL * M) := by
            simpa [rL] using hlateRaw
      _ ≤ 2 * (2 * (((1 - (1 / 2 : ℝ)) * rL)⁻¹) *
          Real.exp (-((1 / 2 : ℝ) * rL) * M)) := by
            rw [show 2 * (M + 1 : ℝ) * Real.exp (-rL * M) =
              2 * ((M + 1 : ℝ) * Real.exp (-rL * M)) by ring]
            exact mul_le_mul_of_nonneg_left hpoly (by norm_num)
      _ = 4 * ((eta * Real.log 2 / 16)⁻¹) *
          Real.exp (-((1 / 2 : ℝ) * rL) * M) := by
            rw [hhalfRate]
            ring
      _ ≤ 4 * ((eta * Real.log 2 / 16)⁻¹) *
          Real.exp (-rs * M) := by
            have hcoef : 0 ≤ 4 * ((eta * Real.log 2 / 16)⁻¹) := by
              positivity
            exact mul_le_mul_of_nonneg_left hexp hcoef
  have hparity :
      2 * Real.exp (-2 * (eta / 4) ^ 2 * M) ≤
        2 * Real.exp (-rs * M) := by
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    apply Real.exp_le_exp.mpr
    have hMr : 0 ≤ (M : ℝ) := by positivity
    have hmul := mul_le_mul_of_nonneg_right hcutParity hMr
    have hneg := neg_le_neg hmul
    simpa [rs, show 2 * (eta / 4) ^ 2 = eta ^ 2 / 8 by ring] using hneg
  have hcentralExp : Real.exp (-r * M) ≤ Real.exp (-rs * M) := by
    apply Real.exp_le_exp.mpr
    have hzr : zeta * r ≤ r := mul_le_of_le_one_left hr.le hz1.le
    have hMr : 0 ≤ (M : ℝ) := by positivity
    have hmul := mul_le_mul_of_nonneg_right hzr hMr
    have hneg := neg_le_neg hmul
    simpa [hrs, mul_assoc] using hneg
  have htarget :
      C * Real.exp (-D * Real.log 3) * Real.exp (-r * M) ≤
        C * Real.exp (-rs * M) := by
    have hq : Real.exp (-D * Real.log 3) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      rw [show -D * Real.log 3 = -(D * Real.log 3) by ring]
      exact neg_nonpos.mpr
        (mul_nonneg hS.D_pos.le
          (Real.log_pos (by norm_num : (1 : ℝ) < 3)).le)
    calc
      C * Real.exp (-D * Real.log 3) * Real.exp (-r * M) ≤
          C * 1 * Real.exp (-r * M) := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hq hS.C_pos.le)
              (Real.exp_nonneg _)
      _ = C * Real.exp (-r * M) := by ring
      _ ≤ C * Real.exp (-rs * M) :=
        mul_le_mul_of_nonneg_left hcentralExp hS.C_pos.le
  have hmoment :
      A * (M + 1 : ℝ) ^ 6 * Real.exp (-r * M) ≤
        (A * (64 * ((((1 - zeta) * r / 6)⁻¹) ^ 6))) *
          Real.exp (-rs * M) := by
    have hp := sixth_pow_succ_mul_exp_neg_le hr hz0 hz1 hM1
    rw [hrs]
    calc
      A * (M + 1 : ℝ) ^ 6 * Real.exp (-r * M) =
          A * ((M + 1 : ℝ) ^ 6 * Real.exp (-r * M)) := by ring
      _ ≤ A *
          (64 * ((((1 - zeta) * r / 6)⁻¹) ^ 6) *
            Real.exp (-(zeta * r) * M)) :=
        mul_le_mul_of_nonneg_left hp hA
      _ = (A * (64 * ((((1 - zeta) * r / 6)⁻¹) ^ 6))) *
          Real.exp (-(zeta * r) * M) := by ring
  have hcentral :
      (C * Real.exp (-D * Real.log 3) + A * (M + 1 : ℝ) ^ 6) *
          Real.exp (-r * M) ≤
        (C + A * (64 * ((((1 - zeta) * r / 6)⁻¹) ^ 6))) *
          Real.exp (-rs * M) := by
    rw [add_mul, add_mul]
    exact add_le_add htarget hmoment
  calc
    ((sourceEndpointBad S M).card : ℝ) / (2 ^ M : ℝ) ≤
        (((((M + 1) * 2 ^ (M - centralRenyiDiscardDepth eta M) : ℕ) : ℝ) /
            (2 ^ M : ℝ)) +
          2 * Real.exp (-2 * (eta / 4) ^ 2 * M) +
          (C * Real.exp (-D * Real.log 3) + A * (M + 1 : ℝ) ^ 6) *
            Real.exp (-r * M)) := by
      simpa [A, r] using hstart
    _ ≤
        (4 * ((eta * Real.log 2 / 16)⁻¹) + 2 + C +
          A * (64 * ((((1 - zeta) * r / 6)⁻¹) ^ 6))) *
          Real.exp (-rs * M) := by
      exact (add_le_add (add_le_add hlateAbs hparity) hcentral).trans_eq
        (by ring)
    _ = centralRenyiLargeShellConstant C theta eta transport D *
          Real.exp (-centralRenyiShellRate theta transport D * M) := by
      dsimp [centralRenyiLargeShellConstant, A, r, zeta, rs]
      ring

/-- First shell index beyond every finite startup condition in the central
higher-Renyi estimate. -/
def centralRenyiStartupIndex (theta eta : ℝ) : ℕ :=
  ⌈centralRenyiStartupScale theta eta⌉₊

/-- Uniform all-shell constant.  The second summand absorbs the finitely many
shells below `centralRenyiStartupIndex`. -/
def centralRenyiShellConstant
    (C theta eta transport D : ℝ) : ℝ :=
  centralRenyiLargeShellConstant C theta eta transport D +
    Real.exp (centralRenyiShellRate theta transport D *
      centralRenyiStartupIndex theta eta)

theorem centralRenyiShellRate_lt_log_two
    {theta transport D : ℝ}
    (htheta0 : 0 < theta) (htheta1 : theta < 1)
    (htransport0 : 0 < transport)
    (htransport : transport < centralRenyiAsymptoticRate theta)
    (hD : 0 < D) :
    centralRenyiShellRate theta transport D < Real.log 2 := by
  have hz1 := centralRenyiAbsorption_lt_one htheta0 htransport
  have hr0 := centralRenyiRate_pos htheta0 hD
  have hhalf : (0 : ℝ) < 1 / 2 := by norm_num
  have hinner := OptimizedLinearPullback.psi_inner_pos D
  have hlt :
      (1 / 2 : ℝ) <
        (1 + Real.exp (-D * Real.log 3)) / 2 := by
    have := Real.exp_pos (-D * Real.log 3)
    linarith
  have hlog := Real.strictMonoOn_log hhalf hinner hlt
  have hlogHalf : Real.log (1 / 2 : ℝ) = -Real.log 2 := by
    rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num,
      Real.log_inv]
  have hpsi : OptimizedLinearPullback.psi D < Real.log 2 := by
    unfold OptimizedLinearPullback.psi
    rw [hlogHalf] at hlog
    linarith
  have hthetaFrac : theta / (1 + theta) < 1 := by
    rw [div_lt_one (by linarith)]
    linarith
  have hratePsi :
      centralRenyiRate theta D < OptimizedLinearPullback.psi D := by
    unfold centralRenyiRate
    exact mul_lt_of_lt_one_left
      (OptimizedLinearPullback.psi_pos hD) hthetaFrac
  unfold centralRenyiShellRate
  exact (mul_lt_of_lt_one_left hr0 hz1).trans
    (hratePsi.trans hpsi)

theorem centralRenyiShellConstant_pos
    {C D theta eta transport : ℝ}
    (hC : 0 < C)
    (htheta0 : 0 < theta) (htheta1 : theta < 1)
    (heta0 : 0 < eta)
    (heta1 : eta < centralRenyiAlpha theta - 1 / 2) :
    0 < centralRenyiShellConstant C theta eta transport D := by
  unfold centralRenyiShellConstant centralRenyiLargeShellConstant
  have hmoment := centralMomentConstant_pos htheta0 htheta1 heta0 heta1
  have hterm1 : 0 ≤ 4 * ((eta * Real.log 2 / 16)⁻¹) := by positivity
  have hterm2 : 0 ≤ (3 : ℝ) ^ theta *
      centralMomentConstant theta eta *
        (64 * ((((1 - centralRenyiAbsorption theta transport) *
          centralRenyiRate theta D / 6)⁻¹) ^ 6)) := by positivity
  nlinarith [Real.exp_pos
    (centralRenyiShellRate theta transport D *
      centralRenyiStartupIndex theta eta)]

/-- Uniform absorbed central-Renyi shell estimate, including every finite
startup shell. -/
theorem sourceEndpointBad_div_pow_le_centralRenyi_absorbed
    {S : Set ℕ} {C D theta eta transport : ℝ}
    (hS : QuantitativeDensity.IsCDDense S C D)
    (htheta0 : 0 < theta) (htheta1 : theta < 1)
    (heta0 : 0 < eta)
    (heta1 : eta < centralRenyiAlpha theta - 1 / 2)
    (htransport0 : 0 < transport)
    (htransport : transport < centralRenyiAsymptoticRate theta)
    (hcutLate : centralRenyiShellRate theta transport D ≤
      eta * Real.log 2 / 16)
    (hcutParity : centralRenyiShellRate theta transport D ≤ eta ^ 2 / 8)
    (M : ℕ) :
    ((sourceEndpointBad S M).card : ℝ) / (2 ^ M : ℝ) ≤
      centralRenyiShellConstant C theta eta transport D *
        Real.exp (-centralRenyiShellRate theta transport D * M) := by
  let rate := centralRenyiShellRate theta transport D
  let N0 := centralRenyiStartupIndex theta eta
  have hrate0 : 0 < rate := by
    dsimp [rate, centralRenyiShellRate]
    exact mul_pos (centralRenyiAbsorption_pos htheta0 htransport0)
      (centralRenyiRate_pos htheta0 hS.D_pos)
  by_cases hlarge : centralRenyiStartupScale theta eta ≤ M
  · have h := sourceEndpointBad_div_pow_le_centralRenyi_absorbed_large
      hS htheta0 htheta1 heta0 heta1 htransport0 htransport
      hcutLate hcutParity M hlarge
    have hcoef : centralRenyiLargeShellConstant C theta eta transport D ≤
        centralRenyiShellConstant C theta eta transport D := by
      unfold centralRenyiShellConstant
      exact le_add_of_nonneg_right (Real.exp_nonneg _)
    exact h.trans
      (mul_le_mul_of_nonneg_right hcoef (Real.exp_nonneg _))
  · have hscaleCeil : centralRenyiStartupScale theta eta ≤ N0 := by
      dsimp [N0, centralRenyiStartupIndex]
      exact Nat.le_ceil _
    have hMN0 : (M : ℝ) ≤ N0 := by
      by_contra hnot
      have hN0M : (N0 : ℝ) < M := lt_of_not_ge hnot
      exact hlarge (hscaleCeil.trans hN0M.le)
    have hcard : ((sourceEndpointBad S M).card : ℝ) ≤ 2 ^ M := by
      have hnat :
          (sourceEndpointBad S M).card ≤ Fintype.card (SourceCode M) :=
        Finset.card_le_univ _
      have hcast : ((sourceEndpointBad S M).card : ℝ) ≤
          ((2 ^ M : ℕ) : ℝ) := by
        exact_mod_cast (by simpa [sourceCode_card] using hnat)
      simpa using hcast
    have hfrac :
        ((sourceEndpointBad S M).card : ℝ) / (2 ^ M : ℝ) ≤ 1 :=
      (div_le_one (by positivity)).2 hcard
    have hone :
        1 ≤ Real.exp (rate * N0) * Real.exp (-rate * M) := by
      rw [← Real.exp_add, ← Real.exp_zero]
      apply Real.exp_le_exp.mpr
      nlinarith
    have hlargeNonneg :
        0 ≤ centralRenyiLargeShellConstant C theta eta transport D := by
      unfold centralRenyiLargeShellConstant
      have hmoment := centralMomentConstant_pos htheta0 htheta1 heta0 heta1
      have hterm1 : 0 ≤ 4 * ((eta * Real.log 2 / 16)⁻¹) := by
        positivity
      have hterm2 : 0 ≤ (3 : ℝ) ^ theta *
          centralMomentConstant theta eta *
            (64 * ((((1 - centralRenyiAbsorption theta transport) *
              centralRenyiRate theta D / 6)⁻¹) ^ 6)) := by
        positivity
      nlinarith [hS.C_pos]
    calc
      ((sourceEndpointBad S M).card : ℝ) / (2 ^ M : ℝ) ≤ 1 := hfrac
      _ ≤ Real.exp (rate * N0) * Real.exp (-rate * M) := hone
      _ ≤ centralRenyiShellConstant C theta eta transport D *
          Real.exp (-rate * M) := by
        apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
        unfold centralRenyiShellConstant
        exact le_add_of_nonneg_left hlargeNonneg
      _ = _ := by rfl

/-- Prefix-density constant returned by exact dyadic shell summation. -/
def centralRenyiPullbackConstant
    (C theta eta transport D : ℝ) : ℝ :=
  2 * centralRenyiShellConstant C theta eta transport D /
    (2 * Real.exp (-centralRenyiShellRate theta transport D) - 1)

theorem shellBad_collatzPullback_le_centralRenyi
    {S : Set ℕ} {C D theta eta transport : ℝ}
    (hS : QuantitativeDensity.IsCDDense S C D)
    (htheta0 : 0 < theta) (htheta1 : theta < 1)
    (heta0 : 0 < eta)
    (heta1 : eta < centralRenyiAlpha theta - 1 / 2)
    (htransport0 : 0 < transport)
    (htransport : transport < centralRenyiAsymptoticRate theta)
    (hcutLate : centralRenyiShellRate theta transport D ≤
      eta * Real.log 2 / 16)
    (hcutParity : centralRenyiShellRate theta transport D ≤ eta ^ 2 / 8)
    (M : ℕ) :
    ((QuantitativeDensity.shellBad
        (QuantitativeDensity.collatzPullback S) M).card : ℝ) ≤
      centralRenyiShellConstant C theta eta transport D *
        Real.exp (-centralRenyiShellRate theta transport D * M) *
        (2 ^ M : ℝ) := by
  rw [card_shellBad_collatzPullback_eq_sourceEndpointBad]
  exact (div_le_iff₀ (by positivity : (0 : ℝ) < 2 ^ M)).mp
    (sourceEndpointBad_div_pow_le_centralRenyi_absorbed
      hS htheta0 htheta1 heta0 heta1 htransport0 htransport
      hcutLate hcutParity M)

/-- Concrete central higher-Renyi Collatz pullback in `(C,D)`-density form. -/
theorem collatzPullback_dense_centralRenyi
    {S : Set ℕ} {C D theta eta transport : ℝ}
    (hS : QuantitativeDensity.IsCDDense S C D)
    (htheta0 : 0 < theta) (htheta1 : theta < 1)
    (heta0 : 0 < eta)
    (heta1 : eta < centralRenyiAlpha theta - 1 / 2)
    (htransport0 : 0 < transport)
    (htransport : transport < centralRenyiAsymptoticRate theta)
    (hcutLate : centralRenyiShellRate theta transport D ≤
      eta * Real.log 2 / 16)
    (hcutParity : centralRenyiShellRate theta transport D ≤ eta ^ 2 / 8) :
    QuantitativeDensity.IsCDDense
      (QuantitativeDensity.collatzPullback S)
      (centralRenyiPullbackConstant C theta eta transport D)
      (centralRenyiShellRate theta transport D / Real.log 2) := by
  unfold centralRenyiPullbackConstant
  exact QuantitativeDensity.isCDDense_of_shell_bound
    (centralRenyiShellConstant_pos hS.C_pos htheta0 htheta1 heta0 heta1)
    (mul_pos (centralRenyiAbsorption_pos htheta0 htransport0)
      (centralRenyiRate_pos htheta0 hS.D_pos))
    (centralRenyiShellRate_lt_log_two
      htheta0 htheta1 htransport0 htransport hS.D_pos)
    (shellBad_collatzPullback_le_centralRenyi
      hS htheta0 htheta1 heta0 heta1 htransport0 htransport
      hcutLate hcutParity)

/-- Fixed coefficient that converts the nonlinear central rate into one
inverse power of the input density exponent. -/
def centralRenyiInverseRateFactor (theta transport : ℝ) : ℝ :=
  ((6 / (1 - centralRenyiAbsorption theta transport)) *
    (centralRenyiAbsorption theta transport /
      (transport * Real.log 2))) ^ 6

/-- Uniform shell prefactor used by one endpoint-density stage. -/
def centralRenyiStageShellConstant
    (theta eta transport : ℝ) : ℝ :=
  4 + 4 * ((eta * Real.log 2 / 16)⁻¹) +
    Real.exp ((eta ^ 2 / 8) * centralRenyiStartupIndex theta eta) +
    (3 : ℝ) ^ theta * centralMomentConstant theta eta *
      (64 * centralRenyiInverseRateFactor theta transport)

theorem centralRenyiRate_inv_le
    {theta transport D : ℝ}
    (htheta0 : 0 < theta)
    (htransport0 : 0 < transport)
    (hD0 : 0 < D)
    (hlinear : transport * D ≤
      centralRenyiShellRate theta transport D / Real.log 2) :
    (centralRenyiRate theta D)⁻¹ ≤
      (centralRenyiAbsorption theta transport /
        (transport * Real.log 2)) * D⁻¹ := by
  let zeta := centralRenyiAbsorption theta transport
  let r := centralRenyiRate theta D
  let lower := (transport * Real.log 2 / zeta) * D
  have hz0 : 0 < zeta := centralRenyiAbsorption_pos htheta0 htransport0
  have hr0 : 0 < r := centralRenyiRate_pos htheta0 hD0
  have hlower0 : 0 < lower := by dsimp [lower]; positivity
  have hlower : lower ≤ r := by
    have hlog2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
    have hmul : transport * D * Real.log 2 ≤ zeta * r := by
      apply (le_div_iff₀ hlog2).mp
      simpa [centralRenyiShellRate, zeta, r] using hlinear
    rw [show lower = (transport * D * Real.log 2) / zeta by
      dsimp [lower]
      ring]
    exact (div_le_iff₀ hz0).2 (by simpa [mul_comm] using hmul)
  have hinv : r⁻¹ ≤ lower⁻¹ :=
    (inv_le_inv₀ hr0 hlower0).2 hlower
  calc
    (centralRenyiRate theta D)⁻¹ = r⁻¹ := rfl
    _ ≤ lower⁻¹ := hinv
    _ = (centralRenyiAbsorption theta transport /
        (transport * Real.log 2)) * D⁻¹ := by
      dsimp [lower, zeta]
      field_simp [htransport0.ne', hD0.ne',
        (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne',
        (centralRenyiAbsorption_pos htheta0 htransport0).ne']

theorem centralRenyiMomentInverse_le
    {theta transport D : ℝ}
    (htheta0 : 0 < theta)
    (htransport0 : 0 < transport)
    (htransport : transport < centralRenyiAsymptoticRate theta)
    (hD0 : 0 < D)
    (hlinear : transport * D ≤
      centralRenyiShellRate theta transport D / Real.log 2) :
    ((((1 - centralRenyiAbsorption theta transport) *
      centralRenyiRate theta D / 6)⁻¹) ^ 6) ≤
      centralRenyiInverseRateFactor theta transport * (D⁻¹) ^ 6 := by
  let zeta := centralRenyiAbsorption theta transport
  let r := centralRenyiRate theta D
  have hz1 := centralRenyiAbsorption_lt_one htheta0 htransport
  have hr0 := centralRenyiRate_pos htheta0 hD0
  have hrInv := centralRenyiRate_inv_le htheta0 htransport0 hD0 hlinear
  have hcoef0 : 0 ≤ 6 / (1 - zeta) :=
    div_nonneg (by norm_num) (sub_nonneg.mpr hz1.le)
  have hcore :
      (((1 - zeta) * r / 6)⁻¹) ≤
        (6 / (1 - zeta)) *
          (zeta / (transport * Real.log 2)) * D⁻¹ := by
    rw [show (((1 - zeta) * r / 6)⁻¹) =
        (6 / (1 - zeta)) * r⁻¹ by
      field_simp [sub_ne_zero.mpr hz1.ne, hr0.ne']]
    have hmul := mul_le_mul_of_nonneg_left hrInv hcoef0
    simpa [zeta, r, mul_assoc] using hmul
  have hden0 : 0 ≤ (1 - zeta) * r / 6 :=
    div_nonneg (mul_nonneg (sub_nonneg.mpr hz1.le) hr0.le) (by norm_num)
  have hpow := pow_le_pow_left₀ (inv_nonneg.mpr hden0) hcore 6
  calc
    ((((1 - centralRenyiAbsorption theta transport) *
        centralRenyiRate theta D / 6)⁻¹) ^ 6) ≤
        ((6 / (1 - zeta)) *
          (zeta / (transport * Real.log 2)) * D⁻¹) ^ 6 := by
      simpa [zeta, r] using hpow
    _ = centralRenyiInverseRateFactor theta transport * (D⁻¹) ^ 6 := by
      unfold centralRenyiInverseRateFactor
      dsimp [zeta]
      rw [mul_pow]

theorem centralRenyiShellConstant_le_stage
    {C D theta eta transport : ℝ}
    (hC : 0 < C) (hD0 : 0 < D) (hD1 : D ≤ 1)
    (htheta0 : 0 < theta) (htheta1 : theta < 1)
    (heta0 : 0 < eta)
    (heta1 : eta < centralRenyiAlpha theta - 1 / 2)
    (htransport0 : 0 < transport)
    (htransport : transport < centralRenyiAsymptoticRate theta)
    (hlinear : transport * D ≤
      centralRenyiShellRate theta transport D / Real.log 2)
    (hcutParity : centralRenyiShellRate theta transport D ≤ eta ^ 2 / 8) :
    centralRenyiShellConstant C theta eta transport D ≤
      centralRenyiStageShellConstant theta eta transport *
        (C + 1) * (D⁻¹) ^ 6 := by
  let zeta := centralRenyiAbsorption theta transport
  let r := centralRenyiRate theta D
  let A := (3 : ℝ) ^ theta * centralMomentConstant theta eta
  let Z := (D⁻¹) ^ 6
  let B := 3 + 4 * ((eta * Real.log 2 / 16)⁻¹) +
    Real.exp ((eta ^ 2 / 8) * centralRenyiStartupIndex theta eta)
  let Q := A * (64 * centralRenyiInverseRateFactor theta transport)
  have hZ1 : 1 ≤ Z := by
    dsimp [Z]
    exact one_le_pow₀ ((one_le_inv₀ hD0).2 hD1)
  have hA0 : 0 ≤ A := by
    dsimp [A]
    exact mul_nonneg (Real.rpow_nonneg (by norm_num) _)
      (centralMomentConstant_pos htheta0 htheta1 heta0 heta1).le
  have hB0 : 0 ≤ B := by dsimp [B]; positivity
  have hfactor0 :
      0 ≤ centralRenyiInverseRateFactor theta transport := by
    unfold centralRenyiInverseRateFactor
    have hz0 := centralRenyiAbsorption_pos htheta0 htransport0
    have hz1 := centralRenyiAbsorption_lt_one htheta0 htransport
    have hleft :
        0 ≤ 6 / (1 - centralRenyiAbsorption theta transport) :=
      div_nonneg (by norm_num) (sub_nonneg.mpr hz1.le)
    have hright :
        0 ≤ centralRenyiAbsorption theta transport /
          (transport * Real.log 2) := by positivity
    exact pow_nonneg (mul_nonneg hleft hright) _
  have hQ0 : 0 ≤ Q := by
    dsimp [Q]
    exact mul_nonneg hA0 (mul_nonneg (by norm_num) hfactor0)
  have hmoment := centralRenyiMomentInverse_le
    htheta0 htransport0 htransport hD0 hlinear
  have hmoment' :
      A * (64 * ((((1 - zeta) * r / 6)⁻¹) ^ 6)) ≤ Q * Z := by
    calc
      A * (64 * ((((1 - zeta) * r / 6)⁻¹) ^ 6)) =
          (A * 64) * ((((1 - zeta) * r / 6)⁻¹) ^ 6) := by ring
      _ ≤ (A * 64) *
          (centralRenyiInverseRateFactor theta transport *
            (D⁻¹) ^ 6) := by
        apply mul_le_mul_of_nonneg_left _
          (mul_nonneg hA0 (by norm_num))
        simpa [zeta, r] using hmoment
      _ = Q * Z := by dsimp [Q, Z]; ring
  have hstartup :
      Real.exp (centralRenyiShellRate theta transport D *
          centralRenyiStartupIndex theta eta) ≤
        Real.exp ((eta ^ 2 / 8) *
          centralRenyiStartupIndex theta eta) := by
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_right hcutParity (by positivity)
  have hshell :
      centralRenyiShellConstant C theta eta transport D ≤
        C + B + Q * Z := by
    unfold centralRenyiShellConstant centralRenyiLargeShellConstant
    calc
      C + 2 + 4 * (eta * Real.log 2 / 16)⁻¹ +
              3 ^ theta * centralMomentConstant theta eta *
                (64 * (((1 - centralRenyiAbsorption theta transport) *
                  centralRenyiRate theta D / 6)⁻¹ ^ 6)) +
            Real.exp (centralRenyiShellRate theta transport D *
              centralRenyiStartupIndex theta eta)
          ≤ C + 2 + 4 * (eta * Real.log 2 / 16)⁻¹ + Q * Z +
            Real.exp ((eta ^ 2 / 8) *
              centralRenyiStartupIndex theta eta) := by
        gcongr
      _ ≤ C + B + Q * Z := by
        dsimp [B]
        linarith
  have hmajor :
      C + B + Q * Z ≤ (1 + B + Q) * (C + 1) * Z := by
    have hC1 : 0 ≤ C + 1 := by linarith
    have hZ0 : 0 ≤ Z := by linarith
    have hCB0 : 0 ≤ C + B := by linarith
    have hfirst : C + B + Q * Z ≤ (C + B + Q) * Z := by
      nlinarith [mul_nonneg hCB0 (sub_nonneg.mpr hZ1)]
    have hcoef : C + B + Q ≤ (1 + B + Q) * (C + 1) := by
      nlinarith [mul_nonneg hB0 hC.le, mul_nonneg hQ0 hC.le]
    exact hfirst.trans (mul_le_mul_of_nonneg_right hcoef hZ0)
  exact hshell.trans (by
    convert hmajor using 1 <;>
      dsimp [centralRenyiStageShellConstant, B, Q, A, Z] <;> ring)

/-- Uniform positive lower bound for the geometric-series denominator. -/
def centralRenyiDenominatorFloor (eta : ℝ) : ℝ :=
  2 * Real.exp (-(eta ^ 2 / 8)) - 1

/-- Fixed prefactor for one central higher-Renyi endpoint stage. -/
def centralRenyiStageConstant
    (theta eta transport : ℝ) : ℝ :=
  2 * centralRenyiStageShellConstant theta eta transport /
    centralRenyiDenominatorFloor eta

theorem centralRenyiDenominatorFloor_pos
    {theta eta : ℝ}
    (htheta0 : 0 < theta) (heta0 : 0 < eta)
    (heta1 : eta < centralRenyiAlpha theta - 1 / 2) :
    0 < centralRenyiDenominatorFloor eta := by
  have ha := centralRenyiAlpha_lt_log_ratio htheta0
  have hlogRatio : Real.log 2 / Real.log 3 < 1 := by
    rw [div_lt_one (Real.log_pos (by norm_num))]
    exact Real.strictMonoOn_log (by norm_num) (by norm_num) (by norm_num)
  have hetaHalf : eta < 1 / 2 := by linarith
  have hcap : eta ^ 2 / 8 < Real.log 2 := by
    have hlogHalf : (1 / 2 : ℝ) < Real.log 2 :=
      Real.log_two_gt_d9.trans' (by norm_num)
    nlinarith [sq_nonneg eta]
  have hexp : (1 / 2 : ℝ) < Real.exp (-(eta ^ 2 / 8)) := by
    have h := Real.exp_lt_exp.mpr
      (by linarith : -Real.log 2 < -(eta ^ 2 / 8))
    have heq : Real.exp (-Real.log 2) = (1 / 2 : ℝ) := by
      rw [Real.exp_neg, Real.exp_log (by norm_num)]
      norm_num
    simpa [heq] using h
  unfold centralRenyiDenominatorFloor
  linarith

theorem centralRenyiStageConstant_pos
    {theta eta transport : ℝ}
    (htheta0 : 0 < theta) (htheta1 : theta < 1)
    (heta0 : 0 < eta)
    (heta1 : eta < centralRenyiAlpha theta - 1 / 2)
    (htransport0 : 0 < transport)
    (htransport : transport < centralRenyiAsymptoticRate theta) :
    0 < centralRenyiStageConstant theta eta transport := by
  have hden := centralRenyiDenominatorFloor_pos htheta0 heta0 heta1
  have hmoment := centralMomentConstant_pos htheta0 htheta1 heta0 heta1
  have hfactor : 0 ≤ centralRenyiInverseRateFactor theta transport := by
    unfold centralRenyiInverseRateFactor
    have hz0 := centralRenyiAbsorption_pos htheta0 htransport0
    have hz1 := centralRenyiAbsorption_lt_one htheta0 htransport
    exact pow_nonneg (mul_nonneg
      (div_nonneg (by norm_num) (sub_nonneg.mpr hz1.le))
      (by positivity)) _
  unfold centralRenyiStageConstant centralRenyiStageShellConstant
  positivity

/-- Uniform inverse-sixth-power majorant for the exact central pullback
constant. -/
theorem centralRenyiPullbackConstant_le_stage
    {C D theta eta transport : ℝ}
    (hC : 0 < C) (hD0 : 0 < D) (hD1 : D ≤ 1)
    (htheta0 : 0 < theta) (htheta1 : theta < 1)
    (heta0 : 0 < eta)
    (heta1 : eta < centralRenyiAlpha theta - 1 / 2)
    (htransport0 : 0 < transport)
    (htransport : transport < centralRenyiAsymptoticRate theta)
    (hlinear : transport * D ≤
      centralRenyiShellRate theta transport D / Real.log 2)
    (hcutParity : centralRenyiShellRate theta transport D ≤ eta ^ 2 / 8) :
    centralRenyiPullbackConstant C theta eta transport D ≤
      centralRenyiStageConstant theta eta transport *
        (C + 1) * (D⁻¹) ^ 6 := by
  let rate := centralRenyiShellRate theta transport D
  let den := 2 * Real.exp (-rate) - 1
  let floor := centralRenyiDenominatorFloor eta
  have hfloor0 := centralRenyiDenominatorFloor_pos htheta0 heta0 heta1
  have hrate0 : 0 < rate := by
    dsimp [rate, centralRenyiShellRate]
    exact mul_pos (centralRenyiAbsorption_pos htheta0 htransport0)
      (centralRenyiRate_pos htheta0 hD0)
  have hrateLt := centralRenyiShellRate_lt_log_two
    htheta0 htheta1 htransport0 htransport hD0
  have hden0 : 0 < den := by
    dsimp [den]
    have h := Real.exp_lt_exp.mpr (by linarith : -Real.log 2 < -rate)
    have heq : Real.exp (-Real.log 2) = (1 / 2 : ℝ) := by
      rw [Real.exp_neg, Real.exp_log (by norm_num)]
      norm_num
    rw [heq] at h
    linarith
  have hfloorDen : floor ≤ den := by
    dsimp [floor, centralRenyiDenominatorFloor, den]
    have hexp : Real.exp (-(eta ^ 2 / 8)) ≤ Real.exp (-rate) :=
      Real.exp_le_exp.mpr (by linarith)
    linarith
  have hinv : den⁻¹ ≤ floor⁻¹ :=
    (inv_le_inv₀ hden0 hfloor0).2 hfloorDen
  have hshell := centralRenyiShellConstant_le_stage
    hC hD0 hD1 htheta0 htheta1 heta0 heta1 htransport0 htransport
      hlinear hcutParity
  have hstage0 :
      0 ≤ centralRenyiStageShellConstant theta eta transport := by
    unfold centralRenyiStageShellConstant
    have hmoment := centralMomentConstant_pos htheta0 htheta1 heta0 heta1
    have hfactor :
        0 ≤ centralRenyiInverseRateFactor theta transport := by
      unfold centralRenyiInverseRateFactor
      have hz0 := centralRenyiAbsorption_pos htheta0 htransport0
      have hz1 := centralRenyiAbsorption_lt_one htheta0 htransport
      exact pow_nonneg (mul_nonneg
        (div_nonneg (by norm_num) (sub_nonneg.mpr hz1.le))
        (by positivity)) _
    positivity
  unfold centralRenyiPullbackConstant centralRenyiStageConstant
  dsimp [den, floor] at hinv
  rw [div_eq_mul_inv, div_eq_mul_inv]
  calc
    2 * centralRenyiShellConstant C theta eta transport D *
          (2 * Real.exp (-centralRenyiShellRate theta transport D) - 1)⁻¹
        ≤ 2 *
            (centralRenyiStageShellConstant theta eta transport *
              (C + 1) * (D⁻¹) ^ 6) *
            (2 * Real.exp (-centralRenyiShellRate theta transport D) - 1)⁻¹ := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hshell (by norm_num))
        (inv_nonneg.mpr hden0.le)
    _ ≤ 2 *
            (centralRenyiStageShellConstant theta eta transport *
              (C + 1) * (D⁻¹) ^ 6) *
            (centralRenyiDenominatorFloor eta)⁻¹ := by
      have hinner : 0 ≤
          centralRenyiStageShellConstant theta eta transport *
            (C + 1) * (D⁻¹) ^ 6 :=
        mul_nonneg
          (mul_nonneg hstage0 (by linarith : 0 ≤ C + 1))
          (pow_nonneg (inv_nonneg.mpr hD0.le) _)
      exact mul_le_mul_of_nonneg_left hinv
        (mul_nonneg (by norm_num) hinner)
    _ = 2 * centralRenyiStageShellConstant theta eta transport *
          (centralRenyiDenominatorFloor eta)⁻¹ *
          (C + 1) * (D⁻¹) ^ 6 := by
      ring

end

end FixedTotal

end CollatzEndpointTransport
