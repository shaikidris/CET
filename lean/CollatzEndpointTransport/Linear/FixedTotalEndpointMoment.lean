/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik
-/
import CollatzEndpointTransport.Linear.FixedTotalEndpointBridge
import CollatzEndpointTransport.Linear.FixedTotalCriticalMoment

/-!
# Fixed Total Endpoint Moment

Critical endpoint moment for one fixed-total cohort.

Endpoint fibers refine numerator-residue fibers.  The proof is phrased as a
generic finite-fiber lemma:

  sum_x sqrt(card(endpoint fiber through x))
    <= sum_x sqrt(card(residue fiber through x)).

Writing the sum over source elements avoids choosing endpoint
representatives.  Re-indexing the residue side recovers the exact
`card * sqrt(card)` critical moment from `FixedTotalCriticalMoment`.
-/

namespace CollatzEndpointTransport

namespace FixedTotal

open Nat Finset

noncomputable section

local instance endpointCompositionDecidableEq (N : ℕ) :
    DecidableEq (Composition N) :=
  Classical.decEq _

/-- Fiber of a finite map inside a prescribed finite source set. -/
def mapFiber
    {α β : Type*} [DecidableEq β]
    (W : Finset α) (f : α → β) (b : β) : Finset α :=
  W.filter fun x => f x = b

/-- Cardinality of the fiber through a given source element. -/
def mapFiberCardAt
    {α β : Type*} [DecidableEq β]
    (W : Finset α) (f : α → β) (x : α) : ℕ :=
  (mapFiber W f (f x)).card

theorem sum_sqrt_mapFiberCardAt_eq
    {α β : Type*} [DecidableEq α] [DecidableEq β] [Fintype β]
    (W : Finset α) (f : α → β) :
    (∑ x ∈ W, Real.sqrt (mapFiberCardAt W f x)) =
      ∑ b : β,
        (mapFiber W f b).card * Real.sqrt (mapFiber W f b).card := by
  calc
    (∑ x ∈ W, Real.sqrt (mapFiberCardAt W f x)) =
        ∑ b : β, ∑ x ∈ mapFiber W f b,
          Real.sqrt (mapFiberCardAt W f x) := by
      symm
      exact Finset.sum_fiberwise W f
        (fun x => Real.sqrt (mapFiberCardAt W f x))
    _ = ∑ b : β,
        (mapFiber W f b).card * Real.sqrt (mapFiber W f b).card := by
      apply Finset.sum_congr rfl
      intro b hb
      calc
        (∑ x ∈ mapFiber W f b,
            Real.sqrt (mapFiberCardAt W f x)) =
            ∑ _x ∈ mapFiber W f b,
              Real.sqrt (mapFiber W f b).card := by
          apply Finset.sum_congr rfl
          intro x hx
          have hfx : f x = b := (Finset.mem_filter.mp hx).2
          simp [mapFiberCardAt, hfx]
        _ = (mapFiber W f b).card *
              Real.sqrt (mapFiber W f b).card := by
          simp

/-- Endpoint map for one first-odd cohort. -/
def cohortEndpoint
    {M : ℕ} (u : Fin M) (c : Composition (M - (u : ℕ))) : ℕ :=
  sourceEndpoint (Sum.inr ⟨u, c⟩ : SourceCode M)

/-- Numerator residue label at a prescribed odd-count level. -/
def cohortNumeratorResidue
    {N s : ℕ} (c : Composition N) : Fin (3 ^ s) :=
  ⟨syracuseNumerator c % 3 ^ s,
    Nat.mod_lt _ (pow_pos (by norm_num : 0 < (3 : ℕ)) s)⟩

/-- Within one first-odd and odd-count cohort, the endpoint fibers and the
normalized-correction residue fibers are exactly the same. -/
theorem cohortEndpoint_eq_iff_numeratorResidue
    {M s : ℕ} (u : Fin M)
    {c d : Composition (M - (u : ℕ))}
    (hc : c ∈ fixedSet (M - (u : ℕ)) s)
    (hd : d ∈ fixedSet (M - (u : ℕ)) s) :
    cohortEndpoint u c = cohortEndpoint u d ↔
      cohortNumeratorResidue (s := s) c =
        cohortNumeratorResidue (s := s) d := by
  have hcLen : c.length = s := (Finset.mem_filter.mp hc).2
  have hdLen : d.length = s := (Finset.mem_filter.mp hd).2
  constructor
  · intro hout
    apply Fin.ext
    exact sourceEndpoint_collision_modEq_numerator
      u c d hcLen hdLen hout
  · intro hres
    have hnum :
        Nat.ModEq (3 ^ s) (syracuseNumerator c)
          (syracuseNumerator d) := by
      rw [Nat.ModEq]
      exact congrArg Fin.val hres
    have hcorr :
        Nat.ModEq (3 ^ s)
          (2 ^ (u : ℕ) * syracuseNumerator c)
          (2 ^ (u : ℕ) * syracuseNumerator d) :=
      Nat.ModEq.mul_left _ hnum
    exact
      (sourceEndpoint_eq_iff_correction_modEq
        (M := M) (s := s)
        (x := (Sum.inr ⟨u, c⟩ : SourceCode M))
        (y := (Sum.inr ⟨u, d⟩ : SourceCode M))
        (by simpa [sourceCodeOddCount] using hcLen)
        (by simpa [sourceCodeOddCount] using hdLen)).2 <| by
          simpa [sourceCodeCorrection] using hcorr

/-- Exact equality of the endpoint fiber and normalized-correction fiber
through a source in one fixed cohort. -/
theorem cohortEndpoint_mapFiber_eq_numerator
    {M s : ℕ} (u : Fin M)
    {c : Composition (M - (u : ℕ))}
    (hc : c ∈ fixedSet (M - (u : ℕ)) s) :
    mapFiber (fixedSet (M - (u : ℕ)) s)
        (cohortEndpoint u) (cohortEndpoint u c) =
      mapFiber (fixedSet (M - (u : ℕ)) s)
        (cohortNumeratorResidue (s := s))
        (cohortNumeratorResidue (s := s) c) := by
  ext d
  simp only [mapFiber, Finset.mem_filter]
  constructor
  · rintro ⟨hd, hout⟩
    exact ⟨hd, (cohortEndpoint_eq_iff_numeratorResidue u hd hc).1 hout⟩
  · rintro ⟨hd, hres⟩
    exact ⟨hd, (cohortEndpoint_eq_iff_numeratorResidue u hd hc).2 hres⟩

theorem cohortEndpoint_mapFiberCardAt_eq_numerator
    {M s : ℕ} (u : Fin M)
    {c : Composition (M - (u : ℕ))}
    (hc : c ∈ fixedSet (M - (u : ℕ)) s) :
    mapFiberCardAt (fixedSet (M - (u : ℕ)) s)
        (cohortEndpoint u) c =
      mapFiberCardAt (fixedSet (M - (u : ℕ)) s)
        (cohortNumeratorResidue (s := s)) c := by
  exact congrArg Finset.card (cohortEndpoint_mapFiber_eq_numerator u hc)

/-- Critical endpoint moment of one `(M,u,s)` cohort. -/
def cohortCriticalNumerator
    (M : ℕ) (u : Fin M) (s : ℕ) : ℝ :=
  Real.sqrt (3 ^ s) *
    ∑ c ∈ fixedSet (M - (u : ℕ)) s,
      Real.sqrt
        (mapFiberCardAt
          (fixedSet (M - (u : ℕ)) s)
          (cohortEndpoint u) c)

theorem cohortNumerator_mapFiber_eq_residueFiber
    {N s : ℕ} (a : Fin (3 ^ s)) :
    mapFiber (fixedSet N s)
        (cohortNumeratorResidue (s := s)) a =
      residueFiber (fixedSet N s) syracuseNumerator (3 ^ s) a := by
  ext c
  simp [mapFiber, residueFiber, cohortNumeratorResidue, Fin.ext_iff]

/-- **Exact fixed-cohort endpoint-to-correction bridge.** -/
theorem cohortCriticalNumerator_eq_fixed
    (M : ℕ) (u : Fin M) (s : ℕ) :
    cohortCriticalNumerator M u s =
      fixedCriticalNumerator (M - (u : ℕ)) s := by
  let W := fixedSet (M - (u : ℕ)) s
  let f := cohortEndpoint u
  let g : Composition (M - (u : ℕ)) → Fin (3 ^ s) :=
    cohortNumeratorResidue
  have hsum :
      (∑ c ∈ W, Real.sqrt (mapFiberCardAt W f c)) =
        ∑ c ∈ W, Real.sqrt (mapFiberCardAt W g c) := by
    apply Finset.sum_congr rfl
    intro c hc
    rw [cohortEndpoint_mapFiberCardAt_eq_numerator u hc]
  have hreindex :
      (∑ c ∈ W, Real.sqrt (mapFiberCardAt W g c)) =
        ∑ a : Fin (3 ^ s),
          (fixedFiberCard (M - (u : ℕ)) s a : ℝ) *
            Real.sqrt (fixedFiberCard (M - (u : ℕ)) s a) := by
    rw [sum_sqrt_mapFiberCardAt_eq W g]
    apply Finset.sum_congr rfl
    intro a ha
    rw [cohortNumerator_mapFiber_eq_residueFiber]
    rfl
  calc
    cohortCriticalNumerator M u s =
        Real.sqrt (3 ^ s) *
          ∑ c ∈ W, Real.sqrt (mapFiberCardAt W f c) := by
      rfl
    _ = Real.sqrt (3 ^ s) *
          ∑ c ∈ W, Real.sqrt (mapFiberCardAt W g c) := by rw [hsum]
    _ = fixedCriticalNumerator (M - (u : ℕ)) s := by
      rw [hreindex]
      rfl

/-- Backward-compatible inequality form of the exact bridge. -/
theorem cohortCriticalNumerator_le
    (M : ℕ) (u : Fin M) (s : ℕ) :
    cohortCriticalNumerator M u s ≤
      fixedCriticalNumerator (M - (u : ℕ)) s :=
  (cohortCriticalNumerator_eq_fixed M u s).le

end

end FixedTotal

end CollatzEndpointTransport
