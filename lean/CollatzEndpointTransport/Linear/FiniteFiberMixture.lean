/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik
-/
import CollatzEndpointTransport.Linear.FixedTotalEndpointMoment
import Mathlib.Analysis.MeanInequalities

/-!
# Finite Fiber Mixture

Finite `L^(3/2)` mixture inequality for endpoint fibers.

For a family of finite source sets indexed by `U`, the combined endpoint
fiber is the sum of the component fibers.  Convexity of the `3/2` power
gives

  sum_y F(y) sqrt(F(y))
    <= sqrt(card U) * sum_u sum_y F_u(y) sqrt(F_u(y)).

This conservative square-root mixture loss is polynomial and therefore
does not affect the linear density exponent in the later pullback.
-/

namespace CollatzEndpointTransport

namespace FixedTotal

open Nat Finset

noncomputable section

theorem mul_sqrt_eq_rpow_three_halves
    (x : ℝ) (hx : 0 ≤ x) :
    x * Real.sqrt x = x ^ ((3 : ℝ) / 2) := by
  by_cases hx0 : x = 0
  · simp [hx0]
  have hxpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hx0)
  rw [Real.sqrt_eq_rpow]
  calc
    x * x ^ (1 / 2 : ℝ) =
        x ^ (1 : ℝ) * x ^ (1 / 2 : ℝ) := by rw [Real.rpow_one]
    _ = x ^ ((1 : ℝ) + 1 / 2) :=
      (Real.rpow_add hxpos 1 (1 / 2)).symm
    _ = x ^ ((3 : ℝ) / 2) := by norm_num

theorem sum_mul_sqrt_le
    {ι : Type*} (U : Finset ι) (a : ι → ℕ) :
    ((∑ i ∈ U, a i : ℕ) : ℝ) *
        Real.sqrt (∑ i ∈ U, a i : ℕ) ≤
      Real.sqrt U.card *
        ∑ i ∈ U, (a i : ℝ) * Real.sqrt (a i) := by
  have hpow :=
    Real.rpow_sum_le_const_mul_sum_rpow_of_nonneg
      (s := U) (f := fun i => (a i : ℝ))
      (p := (3 : ℝ) / 2) (by norm_num)
      (by intro i hi; positivity)
  have hsumNonneg :
      0 ≤ ∑ i ∈ U, (a i : ℝ) := by positivity
  have hcardNonneg : (0 : ℝ) ≤ U.card := by positivity
  calc
    ((∑ i ∈ U, a i : ℕ) : ℝ) *
          Real.sqrt (∑ i ∈ U, a i : ℕ) =
        (∑ i ∈ U, (a i : ℝ)) *
          Real.sqrt (∑ i ∈ U, (a i : ℝ)) := by
      norm_num
    _ = (∑ i ∈ U, (a i : ℝ)) ^ ((3 : ℝ) / 2) :=
      mul_sqrt_eq_rpow_three_halves _ hsumNonneg
    _ ≤ (U.card : ℝ) ^ ((3 : ℝ) / 2 - 1) *
          ∑ i ∈ U, (a i : ℝ) ^ ((3 : ℝ) / 2) := hpow
    _ = Real.sqrt U.card *
          ∑ i ∈ U, (a i : ℝ) * Real.sqrt (a i) := by
      have hhalf : (3 : ℝ) / 2 - 1 = 1 / 2 := by norm_num
      rw [hhalf, ← Real.sqrt_eq_rpow]
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      exact (mul_sqrt_eq_rpow_three_halves (a i) (by positivity)).symm

/-- Combined fiber cardinality of a finite family. -/
def mixedFiberCard
    {ι : Type*} {α : ι → Type*} {β : Type*}
    [∀ i, DecidableEq (α i)] [DecidableEq β]
    (U : Finset ι) (W : ∀ i, Finset (α i))
    (f : ∀ i, α i → β)
    (b : β) : ℕ :=
  ∑ i ∈ U, (mapFiber (W i) (f i) b).card

/-- A finite target set containing every endpoint of every component. -/
def mixedTargetSet
    {ι : Type*} {α : ι → Type*} {β : Type*}
    [DecidableEq β]
    (U : Finset ι) (W : ∀ i, Finset (α i))
    (f : ∀ i, α i → β) :
    Finset β :=
  U.biUnion fun i => (W i).image (f i)

theorem map_mem_mixedTargetSet
    {ι : Type*} {α : ι → Type*} {β : Type*}
    [DecidableEq β]
    (U : Finset ι) (W : ∀ i, Finset (α i))
    (f : ∀ i, α i → β)
    {i : ι} (hi : i ∈ U) {x : α i} (hx : x ∈ W i) :
    f i x ∈ mixedTargetSet U W f := by
  exact Finset.mem_biUnion.mpr
    ⟨i, hi, Finset.mem_image.mpr ⟨x, hx, rfl⟩⟩

theorem local_target_sum_eq_source_sum
    {ι : Type*} {α : ι → Type*} {β : Type*}
    [∀ i, DecidableEq (α i)] [DecidableEq β]
    (U : Finset ι) (W : ∀ i, Finset (α i))
    (f : ∀ i, α i → β)
    {i : ι} (hi : i ∈ U) :
    (∑ b ∈ mixedTargetSet U W f,
        (mapFiber (W i) (f i) b).card *
          Real.sqrt (mapFiber (W i) (f i) b).card) =
      ∑ x ∈ W i, Real.sqrt (mapFiberCardAt (W i) (f i) x) := by
  have hmaps :
      ∀ x ∈ W i, f i x ∈ mixedTargetSet U W f :=
    fun x hx => map_mem_mixedTargetSet U W f hi hx
  calc
    (∑ b ∈ mixedTargetSet U W f,
        (mapFiber (W i) (f i) b).card *
          Real.sqrt (mapFiber (W i) (f i) b).card) =
      ∑ b ∈ mixedTargetSet U W f,
        ∑ x ∈ mapFiber (W i) (f i) b,
          Real.sqrt (mapFiberCardAt (W i) (f i) x) := by
      apply Finset.sum_congr rfl
      intro b hb
      symm
      calc
        (∑ x ∈ mapFiber (W i) (f i) b,
            Real.sqrt (mapFiberCardAt (W i) (f i) x)) =
            ∑ _x ∈ mapFiber (W i) (f i) b,
              Real.sqrt (mapFiber (W i) (f i) b).card := by
          apply Finset.sum_congr rfl
          intro x hx
          have hfx : f i x = b := (Finset.mem_filter.mp hx).2
          simp [mapFiberCardAt, hfx]
        _ = (mapFiber (W i) (f i) b).card *
              Real.sqrt (mapFiber (W i) (f i) b).card := by
          simp
    _ = ∑ x ∈ W i,
        Real.sqrt (mapFiberCardAt (W i) (f i) x) := by
      exact Finset.sum_fiberwise_of_maps_to hmaps
        (fun x => Real.sqrt (mapFiberCardAt (W i) (f i) x))

/-- Critical `3/2` mixture bound. -/
theorem mixedFiberCritical_le
    {ι : Type*} {α : ι → Type*} {β : Type*}
    [∀ i, DecidableEq (α i)] [DecidableEq β]
    (U : Finset ι) (W : ∀ i, Finset (α i))
    (f : ∀ i, α i → β) :
    (∑ b ∈ mixedTargetSet U W f,
        (mixedFiberCard U W f b : ℝ) *
          Real.sqrt (mixedFiberCard U W f b)) ≤
      Real.sqrt U.card *
        ∑ i ∈ U, ∑ x ∈ W i,
          Real.sqrt (mapFiberCardAt (W i) (f i) x) := by
  calc
    (∑ b ∈ mixedTargetSet U W f,
        (mixedFiberCard U W f b : ℝ) *
          Real.sqrt (mixedFiberCard U W f b)) ≤
      ∑ b ∈ mixedTargetSet U W f,
        Real.sqrt U.card *
          ∑ i ∈ U,
            ((mapFiber (W i) (f i) b).card : ℝ) *
              Real.sqrt (mapFiber (W i) (f i) b).card := by
      apply Finset.sum_le_sum
      intro b hb
      simpa [mixedFiberCard] using
        sum_mul_sqrt_le U
          (fun i => (mapFiber (W i) (f i) b).card)
    _ = Real.sqrt U.card *
        ∑ i ∈ U, ∑ x ∈ W i,
          Real.sqrt (mapFiberCardAt (W i) (f i) x) := by
      rw [← Finset.mul_sum, Finset.sum_comm]
      apply congrArg (fun z : ℝ => Real.sqrt U.card * z)
      apply Finset.sum_congr rfl
      intro i hi
      exact local_target_sum_eq_source_sum U W f hi

end

end FixedTotal

end CollatzEndpointTransport
