/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik
-/
import CollatzEndpointTransport.Linear.CentralRenyiReverse
import CollatzEndpointTransport.Linear.FiniteFiberMixture
import CollatzEndpointTransport.Linear.FixedTotalActualEndpointMoment
import CollatzEndpointTransport.Common.TerrasPrefixEvents

/-!
# Central Renyi Shell

Finite `L^(1+theta)` mixture inequality for endpoint fibers.

For `theta > 0`, convexity gives

  (sum_i a_i)^(1+theta)
    <= card(U)^theta * sum_i a_i^(1+theta).

The resulting polynomial factor is harmless for every shell exponent.
-/

namespace CollatzEndpointTransport

namespace FixedTotal

open Nat Finset
open scoped Real

noncomputable section

theorem sum_rpow_one_add_le
    {ι : Type*} (U : Finset ι) (a : ι → ℕ)
    {theta : ℝ} (htheta : 0 < theta) :
    ((∑ i ∈ U, a i : ℕ) : ℝ) ^ (1 + theta) ≤
      (U.card : ℝ) ^ theta *
        ∑ i ∈ U, ((a i : ℝ) ^ (1 + theta)) := by
  have hpow :=
    Real.rpow_sum_le_const_mul_sum_rpow_of_nonneg
      (s := U) (f := fun i => (a i : ℝ))
      (p := 1 + theta) (by linarith)
      (by intro i hi; positivity)
  norm_num at hpow ⊢
  convert hpow using 1 <;> ring

theorem local_target_renyi_sum_eq_source_sum
    {ι : Type*} {α : ι → Type*} {β : Type*}
    [∀ i, DecidableEq (α i)] [DecidableEq β]
    (U : Finset ι) (W : ∀ i, Finset (α i))
    (f : ∀ i, α i → β)
    {i : ι} (hi : i ∈ U) {theta : ℝ} (htheta : 0 < theta) :
    (∑ b ∈ mixedTargetSet U W f,
        ((mapFiber (W i) (f i) b).card : ℝ) ^ (1 + theta)) =
      ∑ x ∈ W i,
        ((mapFiberCardAt (W i) (f i) x : ℕ) : ℝ) ^ theta := by
  have hmaps :
      ∀ x ∈ W i, f i x ∈ mixedTargetSet U W f :=
    fun x hx => map_mem_mixedTargetSet U W f hi hx
  calc
    (∑ b ∈ mixedTargetSet U W f,
        ((mapFiber (W i) (f i) b).card : ℝ) ^ (1 + theta)) =
      ∑ b ∈ mixedTargetSet U W f,
        ∑ x ∈ mapFiber (W i) (f i) b,
          ((mapFiberCardAt (W i) (f i) x : ℕ) : ℝ) ^ theta := by
      apply Finset.sum_congr rfl
      intro b hb
      by_cases hzero : (mapFiber (W i) (f i) b).card = 0
      · have hempty := Finset.card_eq_zero.mp hzero
        have hexponent : 1 + theta ≠ 0 := by linarith
        simp [hempty, hzero, Real.zero_rpow hexponent]
      · have hcardR : 0 < ((mapFiber (W i) (f i) b).card : ℝ) :=
          Nat.cast_pos.mpr (Nat.pos_of_ne_zero hzero)
        calc
          ((mapFiber (W i) (f i) b).card : ℝ) ^ (1 + theta) =
              ((mapFiber (W i) (f i) b).card : ℝ) *
                ((mapFiber (W i) (f i) b).card : ℝ) ^ theta := by
            rw [Real.rpow_add hcardR]
            simp
          _ = ∑ x ∈ mapFiber (W i) (f i) b,
              ((mapFiberCardAt (W i) (f i) x : ℕ) : ℝ) ^ theta := by
            calc
              ((mapFiber (W i) (f i) b).card : ℝ) *
                    ((mapFiber (W i) (f i) b).card : ℝ) ^ theta =
                  ∑ _x ∈ mapFiber (W i) (f i) b,
                    ((mapFiber (W i) (f i) b).card : ℝ) ^ theta := by simp
              _ = _ := by
                apply Finset.sum_congr rfl
                intro x hx
                have hfx : f i x = b := (Finset.mem_filter.mp hx).2
                simp [mapFiberCardAt, hfx]
    _ = ∑ x ∈ W i,
        ((mapFiberCardAt (W i) (f i) x : ℕ) : ℝ) ^ theta := by
      exact Finset.sum_fiberwise_of_maps_to hmaps
        (fun x => ((mapFiberCardAt (W i) (f i) x : ℕ) : ℝ) ^ theta)

/-- Combined `(1+theta)` endpoint-fiber moment of a finite family. -/
theorem mixedFiberRenyi_le
    {ι : Type*} {α : ι → Type*} {β : Type*}
    [∀ i, DecidableEq (α i)] [DecidableEq β]
    (U : Finset ι) (W : ∀ i, Finset (α i))
    (f : ∀ i, α i → β)
    {theta : ℝ} (htheta : 0 < theta) :
    (∑ b ∈ mixedTargetSet U W f,
        (mixedFiberCard U W f b : ℝ) ^ (1 + theta)) ≤
      (U.card : ℝ) ^ theta *
        ∑ i ∈ U, ∑ x ∈ W i,
          ((mapFiberCardAt (W i) (f i) x : ℕ) : ℝ) ^ theta := by
  calc
    (∑ b ∈ mixedTargetSet U W f,
        (mixedFiberCard U W f b : ℝ) ^ (1 + theta)) ≤
      ∑ b ∈ mixedTargetSet U W f,
        (U.card : ℝ) ^ theta *
          ∑ i ∈ U,
            ((mapFiber (W i) (f i) b).card : ℝ) ^ (1 + theta) := by
      apply Finset.sum_le_sum
      intro b hb
      simpa [mixedFiberCard] using
        sum_rpow_one_add_le U
          (fun i => (mapFiber (W i) (f i) b).card) htheta
    _ = (U.card : ℝ) ^ theta *
        ∑ i ∈ U, ∑ x ∈ W i,
          ((mapFiberCardAt (W i) (f i) x : ℕ) : ℝ) ^ theta := by
      rw [← Finset.mul_sum, Finset.sum_comm]
      apply congrArg (fun z : ℝ => (U.card : ℝ) ^ theta * z)
      apply Finset.sum_congr rfl
      intro i hi
      exact local_target_renyi_sum_eq_source_sum U W f hi htheta

end

end FixedTotal

end CollatzEndpointTransport
/-
Higher-Renyi endpoint-to-correction bridge for one fixed-total cohort.
-/

namespace CollatzEndpointTransport

namespace FixedTotal

open Nat Finset
open scoped Real

noncomputable section

local instance centralEndpointCompositionDecidableEq (N : ℕ) :
    DecidableEq (Composition N) :=
  Classical.decEq _

theorem sum_mapFiberCardAt_rpow_eq
    {α β : Type*} [DecidableEq α] [DecidableEq β] [Fintype β]
    (W : Finset α) (f : α → β) (theta : ℝ) :
    (∑ x ∈ W, ((mapFiberCardAt W f x : ℕ) : ℝ) ^ theta) =
      ∑ b : β, ((mapFiber W f b).card : ℝ) *
        ((mapFiber W f b).card : ℝ) ^ theta := by
  calc
    (∑ x ∈ W, ((mapFiberCardAt W f x : ℕ) : ℝ) ^ theta) =
        ∑ b : β, ∑ x ∈ mapFiber W f b,
          ((mapFiberCardAt W f x : ℕ) : ℝ) ^ theta := by
      symm
      exact Finset.sum_fiberwise W f
        (fun x => ((mapFiberCardAt W f x : ℕ) : ℝ) ^ theta)
    _ = ∑ b : β, ((mapFiber W f b).card : ℝ) *
        ((mapFiber W f b).card : ℝ) ^ theta := by
      apply Finset.sum_congr rfl
      intro b hb
      calc
        (∑ x ∈ mapFiber W f b,
            ((mapFiberCardAt W f x : ℕ) : ℝ) ^ theta) =
          ∑ _x ∈ mapFiber W f b,
            ((mapFiber W f b).card : ℝ) ^ theta := by
          apply Finset.sum_congr rfl
          intro x hx
          have hfx : f x = b := (Finset.mem_filter.mp hx).2
          simp [mapFiberCardAt, hfx]
        _ = ((mapFiber W f b).card : ℝ) *
            ((mapFiber W f b).card : ℝ) ^ theta := by simp

/-- Source-side endpoint fiber moment of one `(M,u,s)` cohort. -/
def cohortRenyiSourceMoment
    (M : ℕ) (u : Fin M) (s : ℕ) (theta : ℝ) : ℝ :=
  ((3 : ℝ) ^ s) ^ theta *
    ∑ c ∈ fixedSet (M - (u : ℕ)) s,
      ((mapFiberCardAt
        (fixedSet (M - (u : ℕ)) s)
        (cohortEndpoint u) c : ℕ) : ℝ) ^ theta

/-- Exact higher-Renyi endpoint-to-correction bridge.  No sign restriction
on the exponent is needed because the underlying fibers are equal. -/
theorem cohortRenyiSourceMoment_eq_fixed
    (M : ℕ) (u : Fin M) (s : ℕ) (theta : ℝ) :
    cohortRenyiSourceMoment M u s theta =
      fixedRenyiNumerator (M - (u : ℕ)) s theta := by
  let W := fixedSet (M - (u : ℕ)) s
  let f := cohortEndpoint u
  let g : Composition (M - (u : ℕ)) → Fin (3 ^ s) :=
    cohortNumeratorResidue
  have hsum :
      (∑ c ∈ W, ((mapFiberCardAt W f c : ℕ) : ℝ) ^ theta) =
        ∑ c ∈ W, ((mapFiberCardAt W g c : ℕ) : ℝ) ^ theta := by
    apply Finset.sum_congr rfl
    intro c hc
    rw [cohortEndpoint_mapFiberCardAt_eq_numerator u hc]
  have hreindex :
      (∑ c ∈ W, ((mapFiberCardAt W g c : ℕ) : ℝ) ^ theta) =
        ∑ a : Fin (3 ^ s),
          (fixedFiberCard (M - (u : ℕ)) s a : ℝ) *
            (fixedFiberCard (M - (u : ℕ)) s a : ℝ) ^ theta := by
    rw [sum_mapFiberCardAt_rpow_eq W g theta]
    apply Finset.sum_congr rfl
    intro a ha
    rw [cohortNumerator_mapFiber_eq_residueFiber]
    rfl
  calc
    cohortRenyiSourceMoment M u s theta =
        ((3 : ℝ) ^ s) ^ theta *
          ∑ c ∈ W, ((mapFiberCardAt W f c : ℕ) : ℝ) ^ theta := by rfl
    _ = ((3 : ℝ) ^ s) ^ theta *
          ∑ c ∈ W, ((mapFiberCardAt W g c : ℕ) : ℝ) ^ theta := by
      rw [hsum]
    _ = fixedRenyiNumerator (M - (u : ℕ)) s theta := by
      rw [hreindex]
      simp [fixedRenyiNumerator, Nat.cast_pow]

/-- Backward-compatible inequality form of the exact Renyi bridge. -/
theorem cohortRenyiSourceMoment_le_fixed
    (M : ℕ) (u : Fin M) (s : ℕ) {theta : ℝ}
    (_htheta : 0 ≤ theta) :
    cohortRenyiSourceMoment M u s theta ≤
      fixedRenyiNumerator (M - (u : ℕ)) s theta :=
  (cohortRenyiSourceMoment_eq_fixed M u s theta).le

end

end FixedTotal

end CollatzEndpointTransport
/-
Central higher-Renyi information for the actual dyadic shell endpoint law.

The formal polynomial bound is intentionally coarse.  Only its finiteness
and fixed degree enter the heavy-fiber absorption; the exact exponential
rate remains `theta/(1+theta) * psi(D)`.
-/

set_option maxHeartbeats 4000000

namespace CollatzEndpointTransport

namespace FixedTotal

open Nat Finset
open scoped Real

noncomputable section

local instance centralShellCompositionDecidableEq (N : ℕ) :
    DecidableEq (Composition N) :=
  Classical.decEq _

/-- All finite conditions needed to invoke the uniform central moment. -/
def CentralRenyiAdmissible
    (N s : ℕ) (theta eta : ℝ) : Prop :=
  1 < N ∧ 1 < s ∧ s < N ∧
  InCentralRenyiWindow N s eta ∧
  2 * eta ≤ centralRenyiGap theta eta * ((N : ℝ) - 1) ∧
  (1 / 2 : ℝ) ≤
    (Real.log 2 / Real.log 3 - (1 / 2 + eta)) * N

local instance centralRenyiAdmissibleDecidable
    (N s : ℕ) (theta eta : ℝ) :
    Decidable (CentralRenyiAdmissible N s theta eta) :=
  Classical.propDecidable _

/-- The allowed first-odd cohort at one shell odd-count level. -/
def centralLevelCohortSet
    (M s : ℕ) (theta eta : ℝ) (u : Fin M) :
    Finset (Composition (M - (u : ℕ))) := by
  classical
  exact if CentralRenyiAdmissible (M - (u : ℕ)) s theta eta then
    fixedSet (M - (u : ℕ)) s
  else ∅

def centralLevelEndpointSet
    (M s : ℕ) (theta eta : ℝ) : Finset ℕ :=
  mixedTargetSet (Finset.univ : Finset (Fin M))
    (centralLevelCohortSet M s theta eta) (fun u => cohortEndpoint u)

def centralLevelFiberCard
    (M s : ℕ) (theta eta : ℝ) (y : ℕ) : ℕ :=
  mixedFiberCard (Finset.univ : Finset (Fin M))
    (centralLevelCohortSet M s theta eta) (fun u => cohortEndpoint u) y

/-- One odd-count level of central endpoint information. -/
def centralLevelRenyiInformation
    (M s : ℕ) (theta eta : ℝ) : ℝ :=
  (((3 : ℝ) ^ (s + 1)) ^ theta /
      (((sourceOddLevel M s).card : ℝ) ^ theta)) *
    ∑ y ∈ centralLevelEndpointSet M s theta eta,
      (centralLevelFiberCard M s theta eta y : ℝ) ^ (1 + theta)

/-- Source-normalized central endpoint information. -/
def centralEndpointInformation
    (M : ℕ) (theta eta : ℝ) : ℝ :=
  (∑ s ∈ Finset.range (M + 1),
      centralLevelRenyiInformation M s theta eta) /
    (2 : ℝ) ^ M

theorem centralLevelCohortSet_eq_fixed
    {M s : ℕ} {theta eta : ℝ} (u : Fin M)
    (h : CentralRenyiAdmissible (M - (u : ℕ)) s theta eta) :
    centralLevelCohortSet M s theta eta u =
      fixedSet (M - (u : ℕ)) s := by
  simp [centralLevelCohortSet, h]

theorem centralLevelCohortSet_eq_empty
    {M s : ℕ} {theta eta : ℝ} (u : Fin M)
    (h : ¬ CentralRenyiAdmissible (M - (u : ℕ)) s theta eta) :
    centralLevelCohortSet M s theta eta u = ∅ := by
  simp [centralLevelCohortSet, h]

theorem fixedSet_card_le_sourceOddLevel
    {M s : ℕ} (u : Fin M) (hs : 0 < s) :
    (fixedSet (M - (u : ℕ)) s).card ≤
      (sourceOddLevel M s).card := by
  have hle :
      (levelCohortSet M s u).card ≤ levelSourceCard M s :=
    Finset.single_le_sum
      (fun i _ => Nat.zero_le (levelCohortSet M s i).card)
      (Finset.mem_univ u)
  simpa [levelCohortSet, levelSourceCard_eq_card_sourceOddLevel hs] using hle

theorem numerator_div_global_le_card_mul_moment
    {N s B : ℕ} {theta : ℝ}
    (htheta : 0 ≤ theta)
    (hcard : 0 < (fixedSet N s).card)
    (hB : (fixedSet N s).card ≤ B) :
    fixedRenyiNumerator N s theta / (B : ℝ) ^ theta ≤
      ((fixedSet N s).card : ℝ) * fixedRenyiMoment N s theta := by
  let L : ℝ := (fixedSet N s).card
  have hL : 0 < L := Nat.cast_pos.mpr hcard
  have hBR : 0 < (B : ℝ) := by
    exact lt_of_lt_of_le hL (by simpa [L] using (Nat.cast_le.mpr hB :
      ((fixedSet N s).card : ℝ) ≤ (B : ℝ)))
  have hpow : L ^ theta ≤ (B : ℝ) ^ theta :=
    Real.rpow_le_rpow hL.le
      (by simpa [L] using (Nat.cast_le.mpr hB :
        ((fixedSet N s).card : ℝ) ≤ (B : ℝ))) htheta
  have hnum : 0 ≤ fixedRenyiNumerator N s theta :=
    fixedRenyiNumerator_nonneg N s theta
  unfold fixedRenyiMoment
  have hdiv :
      fixedRenyiNumerator N s theta / (B : ℝ) ^ theta ≤
        fixedRenyiNumerator N s theta / L ^ theta :=
    div_le_div_of_nonneg_left hnum (Real.rpow_pos_of_pos hL _) hpow
  calc
    fixedRenyiNumerator N s theta / (B : ℝ) ^ theta ≤
        fixedRenyiNumerator N s theta / L ^ theta := hdiv
    _ = L *
        (fixedRenyiNumerator N s theta / L ^ (1 + theta)) := by
      rw [Real.rpow_add hL]
      simp only [Real.rpow_one]
      field_simp [hL.ne', (Real.rpow_pos_of_pos hL _).ne']
      ring

/-- One central cohort after normalization by the complete odd-count level. -/
theorem central_cohort_normalized_le
    {M s : ℕ} {theta eta : ℝ} (u : Fin M)
    (htheta0 : 0 < theta) (htheta1 : theta < 1) :
    (((3 : ℝ) ^ s) ^ theta /
        (((sourceOddLevel M s).card : ℝ) ^ theta)) *
      (∑ c ∈ centralLevelCohortSet M s theta eta u,
        ((mapFiberCardAt
          (centralLevelCohortSet M s theta eta u)
          (cohortEndpoint u) c : ℕ) : ℝ) ^ theta) ≤
    if CentralRenyiAdmissible (M - (u : ℕ)) s theta eta then
      ((fixedSet (M - (u : ℕ)) s).card : ℝ) *
        fixedRenyiMoment (M - (u : ℕ)) s theta
    else 0 := by
  classical
  by_cases hadm : CentralRenyiAdmissible (M - (u : ℕ)) s theta eta
  · rw [if_pos hadm]
    rw [centralLevelCohortSet_eq_fixed u hadm]
    have hs : 0 < s := by exact (hadm.2.1.trans' (by omega))
    have hcard : 0 < (fixedSet (M - (u : ℕ)) s).card := by
      have hN : 0 < M - (u : ℕ) := by omega
      rw [card_fixedSet _ _ hN hs]
      exact Nat.choose_pos
        (Nat.sub_le_sub_right (Nat.le_of_lt hadm.2.2.1) 1)
    have hB := fixedSet_card_le_sourceOddLevel u hs
    have hbridge := cohortRenyiSourceMoment_le_fixed M u s htheta0.le
    have hnorm := numerator_div_global_le_card_mul_moment
      htheta0.le hcard hB
    calc
      (((3 : ℝ) ^ s) ^ theta /
          (((sourceOddLevel M s).card : ℝ) ^ theta)) *
        (∑ c ∈ fixedSet (M - (u : ℕ)) s,
          ((mapFiberCardAt
            (fixedSet (M - (u : ℕ)) s)
            (cohortEndpoint u) c : ℕ) : ℝ) ^ theta) =
        cohortRenyiSourceMoment M u s theta /
          (((sourceOddLevel M s).card : ℝ) ^ theta) := by
        unfold cohortRenyiSourceMoment
        ring
      _ ≤ fixedRenyiNumerator (M - (u : ℕ)) s theta /
          (((sourceOddLevel M s).card : ℝ) ^ theta) := by
        exact div_le_div_of_nonneg_right hbridge (by positivity)
      _ ≤ ((fixedSet (M - (u : ℕ)) s).card : ℝ) *
          fixedRenyiMoment (M - (u : ℕ)) s theta := hnorm
  · rw [if_neg hadm]
    rw [centralLevelCohortSet_eq_empty u hadm]
    simp

/-- Polynomial central endpoint-information bound. -/
theorem centralEndpointInformation_le
    {M : ℕ} {theta eta : ℝ}
    (htheta0 : 0 < theta) (htheta1 : theta < 1)
    (heta0 : 0 < eta)
    (heta1 : eta < centralRenyiAlpha theta - 1 / 2) :
    centralEndpointInformation M theta eta ≤
      (3 : ℝ) ^ theta * centralMomentConstant theta eta *
        (M + 1 : ℝ) ^ 6 := by
  classical
  have hconst0 := (centralMomentConstant_pos
    htheta0 htheta1 heta0 heta1).le
  have hMpow : (M : ℝ) ^ theta ≤ (M + 1 : ℝ) := by
    by_cases hM0 : M = 0
    · subst M
      simp [htheta0.ne']
    · have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hM0
      calc
        (M : ℝ) ^ theta ≤ (M : ℝ) ^ 1 :=
          Real.rpow_le_rpow_of_exponent_le hM1 htheta1.le
        _ = (M : ℝ) := Real.rpow_one _
        _ ≤ (M + 1 : ℝ) := by push_cast; linarith
  unfold centralEndpointInformation
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < (2 : ℝ) ^ M)).2
  calc
    (∑ s ∈ Finset.range (M + 1),
        centralLevelRenyiInformation M s theta eta) ≤
      ∑ _s ∈ Finset.range (M + 1),
        (3 : ℝ) ^ theta * (M : ℝ) ^ theta *
          ((M : ℝ) *
            ((2 : ℝ) ^ M * centralMomentConstant theta eta * (M + 1))) := by
      apply Finset.sum_le_sum
      intro s hs
      have hsM : s ≤ M := Nat.le_of_lt_succ (Finset.mem_range.mp hs)
      have hmix := mixedFiberRenyi_le
        (Finset.univ : Finset (Fin M))
        (centralLevelCohortSet M s theta eta)
        (fun u => cohortEndpoint u) htheta0
      have hlevelCard : 0 < (sourceOddLevel M s).card := by
        rw [card_sourceOddLevel]
        exact Nat.choose_pos hsM
      unfold centralLevelRenyiInformation
      let scale := (((3 : ℝ) ^ (s + 1)) ^ theta /
        (((sourceOddLevel M s).card : ℝ) ^ theta))
      have hscale0 : 0 ≤ scale := by
        dsimp [scale]
        positivity
      have hscaled :
          scale *
              (∑ y ∈ centralLevelEndpointSet M s theta eta,
                (centralLevelFiberCard M s theta eta y : ℝ) ^ (1 + theta)) ≤
            scale *
              ((M : ℝ) ^ theta *
                ∑ u : Fin M,
                  ∑ c ∈ centralLevelCohortSet M s theta eta u,
                    ((mapFiberCardAt
                      (centralLevelCohortSet M s theta eta u)
                      (cohortEndpoint u) c : ℕ) : ℝ) ^ theta) := by
        simpa [scale, centralLevelEndpointSet, centralLevelFiberCard] using
          mul_le_mul_of_nonneg_left hmix hscale0
      calc
        ((((3 : ℝ) ^ (s + 1)) ^ theta /
              (((sourceOddLevel M s).card : ℝ) ^ theta)) *
            ∑ y ∈ centralLevelEndpointSet M s theta eta,
              (centralLevelFiberCard M s theta eta y : ℝ) ^ (1 + theta)) ≤
          (((3 : ℝ) ^ (s + 1)) ^ theta /
              (((sourceOddLevel M s).card : ℝ) ^ theta)) *
            ((M : ℝ) ^ theta *
              ∑ u : Fin M, ∑ c ∈ centralLevelCohortSet M s theta eta u,
                ((mapFiberCardAt
                  (centralLevelCohortSet M s theta eta u)
                  (cohortEndpoint u) c : ℕ) : ℝ) ^ theta) := by
          simpa [scale] using hscaled
        _ = (3 : ℝ) ^ theta * (M : ℝ) ^ theta *
            ∑ u : Fin M,
              ((((3 : ℝ) ^ s) ^ theta /
                  (((sourceOddLevel M s).card : ℝ) ^ theta)) *
                ∑ c ∈ centralLevelCohortSet M s theta eta u,
                  ((mapFiberCardAt
                    (centralLevelCohortSet M s theta eta u)
                    (cohortEndpoint u) c : ℕ) : ℝ) ^ theta) := by
          rw [pow_succ, Real.mul_rpow (by positivity) (by positivity)]
          rw [← Finset.mul_sum]
          ring
        _ ≤ (3 : ℝ) ^ theta * (M : ℝ) ^ theta *
            ∑ u : Fin M,
              (if CentralRenyiAdmissible (M - (u : ℕ)) s theta eta then
                ((fixedSet (M - (u : ℕ)) s).card : ℝ) *
                  fixedRenyiMoment (M - (u : ℕ)) s theta
               else 0) := by
          gcongr with u
          exact central_cohort_normalized_le u htheta0 htheta1
        _ ≤ (3 : ℝ) ^ theta * (M : ℝ) ^ theta *
            ((M : ℝ) *
              ((2 : ℝ) ^ M * centralMomentConstant theta eta * (M + 1))) := by
          apply mul_le_mul_of_nonneg_left _
            (mul_nonneg (Real.rpow_nonneg (by norm_num) _)
              (Real.rpow_nonneg (Nat.cast_nonneg M) _))
          calc
            (∑ u : Fin M,
                (if CentralRenyiAdmissible (M - (u : ℕ)) s theta eta then
                  ((fixedSet (M - (u : ℕ)) s).card : ℝ) *
                    fixedRenyiMoment (M - (u : ℕ)) s theta
                 else 0)) ≤
              ∑ _u : Fin M,
                ((2 : ℝ) ^ M * centralMomentConstant theta eta * (M + 1)) := by
              apply Finset.sum_le_sum
              intro u hu
              by_cases hadm : CentralRenyiAdmissible (M - (u : ℕ)) s theta eta
              · rw [if_pos hadm]
                have hpoint := fixedSourceWeight_mul_fixedRenyiMoment_le
                  htheta0 htheta1 heta0 heta1 hadm.1 hadm.2.1
                  hadm.2.2.1 hadm.2.2.2.1 hadm.2.2.2.2.1 hadm.2.2.2.2.2
                have hpowNM : (2 : ℝ) ^ (M - (u : ℕ)) ≤ (2 : ℝ) ^ M := by
                  exact_mod_cast pow_le_pow_right'
                    (by norm_num : (1 : ℕ) ≤ 2) (Nat.sub_le M (u : ℕ))
                have hrewrite :
                    ((fixedSet (M - (u : ℕ)) s).card : ℝ) *
                        fixedRenyiMoment (M - (u : ℕ)) s theta =
                      (2 : ℝ) ^ (M - (u : ℕ)) *
                        (fixedSourceWeight (M - (u : ℕ)) s *
                          fixedRenyiMoment (M - (u : ℕ)) s theta) := by
                  unfold fixedSourceWeight
                  have hp : 0 < (2 : ℝ) ^ (M - (u : ℕ)) := by positivity
                  field_simp [hp.ne']
                rw [hrewrite]
                have hNleM :
                    ((M - (u : ℕ) : ℕ) : ℝ) + 1 ≤ (M : ℝ) + 1 := by
                  exact add_le_add_right
                    (by exact_mod_cast Nat.sub_le M (u : ℕ)) 1
                have hpointM :
                    fixedSourceWeight (M - (u : ℕ)) s *
                        fixedRenyiMoment (M - (u : ℕ)) s theta ≤
                      centralMomentConstant theta eta * ((M : ℝ) + 1) := by
                  calc
                    fixedSourceWeight (M - (u : ℕ)) s *
                          fixedRenyiMoment (M - (u : ℕ)) s theta ≤
                        centralMomentConstant theta eta *
                          (((M - (u : ℕ) : ℕ) : ℝ) + 1) := hpoint
                    _ ≤ centralMomentConstant theta eta * ((M : ℝ) + 1) :=
                      mul_le_mul_of_nonneg_left hNleM hconst0
                have hweightMoment0 :
                    0 ≤ fixedSourceWeight (M - (u : ℕ)) s *
                      fixedRenyiMoment (M - (u : ℕ)) s theta :=
                  mul_nonneg (fixedSourceWeight_nonneg _ _)
                    (fixedRenyiMoment_nonneg _ _ _)
                calc
                  (2 : ℝ) ^ (M - (u : ℕ)) *
                        (fixedSourceWeight (M - (u : ℕ)) s *
                          fixedRenyiMoment (M - (u : ℕ)) s theta) ≤
                      (2 : ℝ) ^ M *
                        (fixedSourceWeight (M - (u : ℕ)) s *
                          fixedRenyiMoment (M - (u : ℕ)) s theta) :=
                    mul_le_mul_of_nonneg_right hpowNM hweightMoment0
                  _ ≤ (2 : ℝ) ^ M *
                        (centralMomentConstant theta eta * (M + 1 : ℝ)) :=
                    mul_le_mul_of_nonneg_left hpointM (by positivity)
                  _ = (2 : ℝ) ^ M * centralMomentConstant theta eta *
                        (M + 1 : ℝ) := by ring
              · rw [if_neg hadm]
                positivity
            _ = (M : ℝ) *
                ((2 : ℝ) ^ M * centralMomentConstant theta eta * (M + 1)) := by
              simp
    _ = (M + 1 : ℝ) *
        ((3 : ℝ) ^ theta * (M : ℝ) ^ theta * (M : ℝ) *
          ((2 : ℝ) ^ M * centralMomentConstant theta eta * (M + 1))) := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      push_cast
      ring
    _ ≤ ((3 : ℝ) ^ theta * centralMomentConstant theta eta *
          (M + 1 : ℝ) ^ 6) * (2 : ℝ) ^ M := by
      have hM0 : 0 ≤ (M : ℝ) := Nat.cast_nonneg M
      have hMle : (M : ℝ) ≤ (M + 1 : ℝ) := by push_cast; linarith
      have hbase1 : (1 : ℝ) ≤ (M + 1 : ℝ) := by
        exact_mod_cast Nat.succ_le_succ (Nat.zero_le M)
      have hpoly :
          (M : ℝ) ^ theta * (M : ℝ) * (M + 1 : ℝ) ^ 2 ≤
            (M + 1 : ℝ) ^ 6 := by
        calc
          (M : ℝ) ^ theta * (M : ℝ) * (M + 1 : ℝ) ^ 2 ≤
              (M + 1 : ℝ) * (M + 1 : ℝ) * (M + 1 : ℝ) ^ 2 := by
            gcongr
          _ = (M + 1 : ℝ) ^ 4 := by ring
          _ ≤ (M + 1 : ℝ) ^ 6 := by
            have hsq : (1 : ℝ) ≤ (M + 1 : ℝ) ^ 2 := by
              nlinarith [sq_nonneg (M : ℝ)]
            calc
              (M + 1 : ℝ) ^ 4 = (M + 1 : ℝ) ^ 4 * 1 := by ring
              _ ≤ (M + 1 : ℝ) ^ 4 * (M + 1 : ℝ) ^ 2 :=
                mul_le_mul_of_nonneg_left hsq (by positivity)
              _ = (M + 1 : ℝ) ^ 6 := by ring
      rw [show
        (M + 1 : ℝ) *
              ((3 : ℝ) ^ theta * (M : ℝ) ^ theta * (M : ℝ) *
                ((2 : ℝ) ^ M * centralMomentConstant theta eta *
                  (M + 1 : ℝ))) =
            ((3 : ℝ) ^ theta * centralMomentConstant theta eta *
              (2 : ℝ) ^ M) *
              ((M : ℝ) ^ theta * (M : ℝ) * (M + 1 : ℝ) ^ 2) by ring]
      rw [show
        ((3 : ℝ) ^ theta * centralMomentConstant theta eta *
              (M + 1 : ℝ) ^ 6) * (2 : ℝ) ^ M =
            ((3 : ℝ) ^ theta * centralMomentConstant theta eta *
              (2 : ℝ) ^ M) * (M + 1 : ℝ) ^ 6 by ring]
      have hfactor0 :
          0 ≤ (3 : ℝ) ^ theta * centralMomentConstant theta eta *
            (2 : ℝ) ^ M :=
        mul_nonneg
          (mul_nonneg (Real.rpow_nonneg (by norm_num) _) hconst0)
          (by positivity)
      exact mul_le_mul_of_nonneg_left hpoly hfactor0

end

end FixedTotal

end CollatzEndpointTransport
/-
Discarded source cohorts for the central higher-Renyi shell theorem.

The central moment controls only first-odd/composition cohorts satisfying
`CentralRenyiAdmissible`.  This file defines their literal source-code set
and isolates the finite complement.  The complement will be bounded by an
exact two-sided Terras parity tail together with the geometrically small
set of codes whose first odd letter occurs late.
-/

namespace CollatzEndpointTransport

namespace FixedTotal

open Nat Finset
open scoped Real

noncomputable section

/-- Source codes retained by the central higher-Renyi argument. -/
def centralSourceSet
    (M : ℕ) (theta eta : ℝ) : Finset (SourceCode M) := by
  classical
  exact Finset.univ.filter fun x =>
    match x with
    | Sum.inl _ => False
    | Sum.inr p =>
        CentralRenyiAdmissible (M - (p.1 : ℕ)) p.2.length theta eta

/-- The finite source complement not covered by the central moment. -/
def centralDiscardedSourceSet
    (M : ℕ) (theta eta : ℝ) : Finset (SourceCode M) :=
  Finset.univ \ centralSourceSet M theta eta

/-- Exact two-sided odd-count tail in source-code coordinates. -/
def sourceParityTail
    (M : ℕ) (t : ℝ) : Finset (SourceCode M) := by
  classical
  exact Finset.univ.filter fun x =>
    sourceCodeOddCount x ≤ Terras.parityLowerCutoff t M ∨
      M - Terras.parityLowerCutoff t M ≤ sourceCodeOddCount x

/-- The same terminal parity tail expressed by a real deviation from
`M/2`. -/
def sourceRealParityTail
    (M : ℕ) (t : ℝ) : Finset (SourceCode M) := by
  classical
  exact Finset.univ.filter fun x =>
    t * M < |(sourceCodeOddCount x : ℝ) - (M : ℝ) / 2|

/-- Codes whose first odd position is at least `K`, including the all-even
word. -/
def sourceLateFirstOdd
    (M K : ℕ) : Finset (SourceCode M) := by
  classical
  exact Finset.univ.filter fun x =>
    match x with
    | Sum.inl _ => True
    | Sum.inr p => K ≤ (p.1 : ℕ)

@[simp]
theorem mem_centralSourceSet_inr
    {M : ℕ} {theta eta : ℝ}
    (u : Fin M) (c : Composition (M - (u : ℕ))) :
    (Sum.inr ⟨u, c⟩ : SourceCode M) ∈ centralSourceSet M theta eta ↔
      CentralRenyiAdmissible (M - (u : ℕ)) c.length theta eta := by
  simp [centralSourceSet]

@[simp]
theorem mem_centralSourceSet_inl
    {M : ℕ} {theta eta : ℝ} (e : Unit) :
    (Sum.inl e : SourceCode M) ∉ centralSourceSet M theta eta := by
  simp [centralSourceSet]

theorem mem_centralDiscardedSourceSet_iff
    {M : ℕ} {theta eta : ℝ} {x : SourceCode M} :
    x ∈ centralDiscardedSourceSet M theta eta ↔
      x ∉ centralSourceSet M theta eta := by
  simp [centralDiscardedSourceSet]

@[simp]
theorem mem_sourceLateFirstOdd_inl
    {M K : ℕ} (e : Unit) :
    (Sum.inl e : SourceCode M) ∈ sourceLateFirstOdd M K := by
  simp [sourceLateFirstOdd]

@[simp]
theorem mem_sourceLateFirstOdd_inr
    {M K : ℕ} (u : Fin M) (c : Composition (M - (u : ℕ))) :
    (Sum.inr ⟨u, c⟩ : SourceCode M) ∈ sourceLateFirstOdd M K ↔
      K ≤ (u : ℕ) := by
  simp [sourceLateFirstOdd]

/-- The source-code parity tail has the same cardinality as the exact
residue tail supplied by the Terras bijection. -/
theorem card_sourceParityTail_eq
    (M : ℕ) (t : ℝ) :
    (sourceParityTail M t).card =
      (Terras.shellParityPrefixBadAt M M t).card := by
  classical
  apply Finset.card_bij (fun x _ => sourceShellStart x)
  · intro x hx
    rw [sourceParityTail, Finset.mem_filter] at hx
    rw [Terras.shellParityPrefixBadAt, Finset.mem_union]
    rcases hx.2 with hl | hu
    · left
      rw [Terras.shellLowerPrefixBad, Finset.mem_filter]
      exact ⟨by simpa [QuantitativeDensity.dyadicShell] using
        sourceShellStart_mem x, by simpa [oddCount_sourceShellStart] using hl⟩
    · right
      rw [Terras.shellUpperPrefixBad, Finset.mem_filter]
      exact ⟨by simpa [QuantitativeDensity.dyadicShell] using
        sourceShellStart_mem x, by simpa [oddCount_sourceShellStart] using hu⟩
  · intro x hx y hy hxy
    have heq :
        sourceCodeEquivDyadicShell M x = sourceCodeEquivDyadicShell M y := by
      apply Subtype.ext
      simpa [sourceCodeEquivDyadicShell_val] using hxy
    exact (sourceCodeEquivDyadicShell M).injective heq
  · intro n hn
    have hnShell : n ∈ QuantitativeDensity.dyadicShell M := by
      rw [Terras.shellParityPrefixBadAt, Finset.mem_union] at hn
      rcases hn with hn | hn
      · exact (Finset.mem_filter.mp hn).1
      · exact (Finset.mem_filter.mp hn).1
    let x : SourceCode M :=
      (sourceCodeEquivDyadicShell M).symm ⟨n, hnShell⟩
    have hxStart : sourceShellStart x = n := by
      have happly := (sourceCodeEquivDyadicShell M).apply_symm_apply
        ⟨n, hnShell⟩
      exact congrArg Subtype.val happly
    refine ⟨x, ?_, hxStart⟩
    rw [sourceParityTail, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [Terras.shellParityPrefixBadAt, Finset.mem_union] at hn
    rcases hn with hn | hn
    · left
      have hodd := (Finset.mem_filter.mp hn).2
      simpa [← oddCount_sourceShellStart x, hxStart] using hodd
    · right
      have hodd := (Finset.mem_filter.mp hn).2
      simpa [← oddCount_sourceShellStart x, hxStart] using hodd

/-- Exact source-code Hoeffding bound for the two-sided terminal parity
tail. -/
theorem card_sourceParityTail_le
    {M : ℕ} {t : ℝ} (ht0 : 0 ≤ t) (htHalf : t ≤ 1 / 2) :
    ((sourceParityTail M t).card : ℝ) ≤
      (2 : ℝ) ^ M * (2 * Real.exp (-2 * t ^ 2 * M)) := by
  rw [card_sourceParityTail_eq]
  exact Terras.card_shellParityPrefixBadAt_le (le_refl M) ht0 htHalf

/-- A real deviation by `t M` lies in the exact cutoff tail at tolerance
`t/2`; the loss absorbs the two integer cutoff boundaries. -/
theorem sourceRealParityTail_subset_sourceParityTail
    {M : ℕ} {t : ℝ}
    (ht0 : 0 < t) (htHalf : t ≤ 1 / 2)
    (htM : 2 ≤ t * M) :
    sourceRealParityTail M t ⊆ sourceParityTail M (t / 2) := by
  classical
  intro x hx
  rw [sourceRealParityTail, Finset.mem_filter] at hx
  rw [sourceParityTail, Finset.mem_filter]
  refine ⟨Finset.mem_univ _, ?_⟩
  have htHalf' : t / 2 ≤ 1 / 2 := by linarith
  let K := Terras.parityLowerCutoff (t / 2) M
  have hKcast : (K : ℝ) ≤ (1 / 2 - t / 2) * M := by
    exact Terras.parityLowerCutoff_cast_le htHalf' M
  have hKM : K ≤ M := by
    have hcoef : (1 / 2 - t / 2) * (M : ℝ) ≤ M := by
      have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg M
      nlinarith
    exact_mod_cast hKcast.trans hcoef
  have hdev :
      t * M < |(sourceCodeOddCount x : ℝ) - (M : ℝ) / 2| := hx.2
  rcases (lt_abs.mp hdev) with hhigh | hlow
  · right
    have hfloorlt :
        (1 / 2 - t / 2) * (M : ℝ) < (K : ℝ) + 1 := by
      exact Nat.lt_floor_add_one _
    have hcast : ((M - K : ℕ) : ℝ) ≤ sourceCodeOddCount x := by
      rw [Nat.cast_sub hKM]
      have hs0 : (0 : ℝ) ≤ sourceCodeOddCount x := Nat.cast_nonneg _
      nlinarith
    exact_mod_cast hcast
  · left
    have hcast :
        ((sourceCodeOddCount x : ℕ) : ℝ) ≤
          (1 / 2 - t / 2) * M := by
      nlinarith
    exact Nat.le_floor hcast

/-- Exact geometric count of the late-first-odd remainder. -/
theorem card_sourceLateFirstOdd_eq
    (M K : ℕ) :
    (sourceLateFirstOdd M K).card =
      1 + ∑ u : Fin M,
        if K ≤ (u : ℕ) then 2 ^ (M - (u : ℕ) - 1) else 0 := by
  classical
  rw [sourceLateFirstOdd, Finset.card_filter]
  unfold SourceCode
  rw [Fintype.sum_sum_type]
  simp only [Fintype.sum_unique, if_true]
  apply congrArg (fun z => 1 + z)
  rw [show
    (∑ u : Fin M,
        if K ≤ (u : ℕ) then 2 ^ (M - (u : ℕ) - 1) else 0) =
      ∑ u : Fin M, ∑ _c : Composition (M - (u : ℕ)),
        if K ≤ (u : ℕ) then 1 else 0 by
      apply Finset.sum_congr rfl
      intro u hu
      by_cases hKu : K ≤ (u : ℕ)
      · simp [hKu, composition_card]
      · simp [hKu]]
  convert (Finset.sum_sigma'
      (Finset.univ : Finset (Fin M))
      (fun u => (Finset.univ :
        Finset (Composition (M - (u : ℕ)))))
      (fun u (_c : Composition (M - (u : ℕ))) =>
        if K ≤ (u : ℕ) then 1 else 0)).symm using 1 <;>
    simp only [Finset.univ_sigma_univ]
  apply Finset.sum_congr rfl
  intro x hx
  by_cases h : K ≤ (x.1 : ℕ) <;> simp [h]

/-- A coarse polynomial-times-geometric bound for late first-odd
positions. -/
theorem card_sourceLateFirstOdd_le
    {M K : ℕ} (hKM : K ≤ M) :
    (sourceLateFirstOdd M K).card ≤
      (M + 1) * 2 ^ (M - K) := by
  rw [card_sourceLateFirstOdd_eq]
  calc
    1 + ∑ u : Fin M,
        (if K ≤ (u : ℕ) then 2 ^ (M - (u : ℕ) - 1) else 0) ≤
      1 + ∑ _u : Fin M, 2 ^ (M - K) := by
        gcongr with u
        by_cases hKu : K ≤ (u : ℕ)
        · rw [if_pos hKu]
          exact pow_le_pow_right' (by norm_num : (1 : ℕ) ≤ 2) (by omega)
        · rw [if_neg hKu]
          exact Nat.zero_le _
    _ = 1 + M * 2 ^ (M - K) := by simp
    _ ≤ (M + 1) * 2 ^ (M - K) := by
      have hp : 1 ≤ 2 ^ (M - K) := one_le_pow₀ (by norm_num : 0 < (2 : ℕ))
      nlinarith

/-- Centrality plus the explicit finite-size hypotheses implies all
conditions packaged by `CentralRenyiAdmissible`. -/
theorem centralRenyiAdmissible_of_window
    {N s : ℕ} {theta eta : ℝ}
    (heta0 : 0 < eta) (hetaHalf : eta < 1 / 2)
    (hN : 1 < N)
    (hinterior : (1 / 2 - eta) * N > 1 / 2)
    (hsizePi :
      2 * eta ≤ centralRenyiGap theta eta * ((N : ℝ) - 1))
    (hsizeDrift :
      (1 / 2 : ℝ) ≤
        (Real.log 2 / Real.log 3 - (1 / 2 + eta)) * N)
    (hcen : InCentralRenyiWindow N s eta) :
    CentralRenyiAdmissible N s theta eta := by
  have hlower := central_window_lower hcen
  have hupper := central_window_upper hcen
  have hs1 : 1 < s := by
    have : (1 : ℝ) < s := by linarith
    exact_mod_cast this
  have hsN : s < N := by
    have : (s : ℝ) < N := by linarith
    exact_mod_cast this
  exact ⟨hN, hs1, hsN, hcen, hsizePi, hsizeDrift⟩

/-- If the first odd letter occurs early, a noncentral fixed-total length
forces a proportional deviation of the whole shell odd count. -/
theorem noncentral_implies_global_parity_deviation
    {M s K : ℕ} {eta : ℝ}
    (u : Fin M) (huK : (u : ℕ) < K)
    (heta0 : 0 < eta) (hetaHalf : eta ≤ 1 / 2)
    (hK : (K : ℝ) ≤ eta * M / 8)
    (hetaM : 2 ≤ eta * M)
    (hnot : ¬ InCentralRenyiWindow (M - (u : ℕ)) s eta) :
    eta / 2 * M < |(s : ℝ) - (M : ℝ) / 2| := by
  unfold InCentralRenyiWindow at hnot
  have hcastSub :
      (((M - (u : ℕ) : ℕ) : ℝ)) = (M : ℝ) - (u : ℝ) := by
    rw [Nat.cast_sub (Nat.le_of_lt u.isLt)]
  have hfarNat :
      eta * (((M - (u : ℕ) : ℕ) : ℝ)) <
        |(s : ℝ) - (((M - (u : ℕ) : ℕ) : ℝ) + 1) / 2| :=
    lt_of_not_ge hnot
  have hfar :
      eta * ((M : ℝ) - (u : ℝ)) <
        |(s : ℝ) - (((M - (u : ℕ) : ℕ) : ℝ) + 1) / 2| := by
    simpa only [hcastSub] using hfarNat
  let a : ℝ :=
    (s : ℝ) - (((M - (u : ℕ) : ℕ) : ℝ) + 1) / 2
  let b : ℝ := (1 - (u : ℝ)) / 2
  let g : ℝ := (s : ℝ) - (M : ℝ) / 2
  have hga : g = a + b := by
    dsimp [g, a, b]
    rw [hcastSub]
    ring
  have hag : a = g - b := by linarith
  have hb : |b| ≤ ((u : ℝ) + 1) / 2 := by
    apply (abs_le).2
    dsimp [b]
    have hu0 : (0 : ℝ) ≤ u := Nat.cast_nonneg _
    constructor <;> nlinarith
  have htri : |a| ≤ |g| + |b| := by
    rw [hag]
    simpa only [sub_eq_add_neg, abs_neg] using abs_add g (-b)
  have huKR : (u : ℝ) < K := by exact_mod_cast huK
  have huBound : (u : ℝ) < eta * M / 8 := huKR.trans_le hK
  have hetaU : eta * (u : ℝ) ≤ (u : ℝ) / 2 := by
    have hu0 : (0 : ℝ) ≤ u := Nat.cast_nonneg _
    nlinarith
  have hfar' : eta * ((M : ℝ) - (u : ℝ)) < |a| := by
    simpa [a, hcastSub] using hfar
  dsimp [g] at htri ⊢
  nlinarith

/-- Under the explicit startup inequalities, every discarded source code
is either a late-first-odd code or lies in a whole-shell parity tail. -/
theorem centralDiscardedSourceSet_subset
    {M K : ℕ} {theta eta : ℝ}
    (hKM : K ≤ M)
    (heta0 : 0 < eta) (hetaHalf : eta ≤ 1 / 2)
    (hK : (K : ℝ) ≤ eta * M / 8)
    (hetaM : 4 ≤ eta * M)
    (hstartup : ∀ N : ℕ, M - K ≤ N → N ≤ M →
      1 < N ∧
      (1 / 2 - eta) * N > 1 / 2 ∧
      2 * eta ≤ centralRenyiGap theta eta * ((N : ℝ) - 1) ∧
      (1 / 2 : ℝ) ≤
        (Real.log 2 / Real.log 3 - (1 / 2 + eta)) * N) :
    centralDiscardedSourceSet M theta eta ⊆
      sourceLateFirstOdd M K ∪ sourceRealParityTail M (eta / 2) := by
  classical
  intro x hx
  have hxnot : x ∉ centralSourceSet M theta eta :=
    (mem_centralDiscardedSourceSet_iff.mp hx)
  cases x with
  | inl e =>
      exact Finset.mem_union_left _ (mem_sourceLateFirstOdd_inl e)
  | inr p =>
      rcases p with ⟨u, c⟩
      by_cases hlate : K ≤ (u : ℕ)
      · exact Finset.mem_union_left _
          (mem_sourceLateFirstOdd_inr u c |>.2 hlate)
      · refine Finset.mem_union_right _ ?_
        have huK : (u : ℕ) < K := Nat.lt_of_not_ge hlate
        have hNlow : M - K ≤ M - (u : ℕ) := by omega
        have hNhigh : M - (u : ℕ) ≤ M := Nat.sub_le _ _
        have hsizes := hstartup (M - (u : ℕ)) hNlow hNhigh
        have hnotWindow :
            ¬ InCentralRenyiWindow (M - (u : ℕ)) c.length eta := by
          intro hcen
          apply hxnot
          rw [mem_centralSourceSet_inr]
          exact centralRenyiAdmissible_of_window heta0
            (lt_of_le_of_ne hetaHalf (by
              intro h
              have hzero : eta = 1 / 2 := h
              rw [hzero] at hsizes
              linarith))
            hsizes.1 hsizes.2.1 hsizes.2.2.1 hsizes.2.2.2 hcen
        rw [sourceRealParityTail, Finset.mem_filter]
        refine ⟨Finset.mem_univ _, ?_⟩
        simpa [sourceCodeOddCount] using
          noncentral_implies_global_parity_deviation u huK heta0 hetaHalf hK
            (by linarith) hnotWindow

/-- The discarded central source is bounded by a geometric late-offset
remainder and one exact whole-shell parity tail. -/
theorem card_centralDiscardedSourceSet_le
    {M K : ℕ} {theta eta : ℝ}
    (hKM : K ≤ M)
    (heta0 : 0 < eta) (hetaHalf : eta ≤ 1 / 2)
    (hK : (K : ℝ) ≤ eta * M / 8)
    (hetaM : 4 ≤ eta * M)
    (hstartup : ∀ N : ℕ, M - K ≤ N → N ≤ M →
      1 < N ∧
      (1 / 2 - eta) * N > 1 / 2 ∧
      2 * eta ≤ centralRenyiGap theta eta * ((N : ℝ) - 1) ∧
      (1 / 2 : ℝ) ≤
        (Real.log 2 / Real.log 3 - (1 / 2 + eta)) * N) :
    (centralDiscardedSourceSet M theta eta).card ≤
      (sourceLateFirstOdd M K).card +
        (sourceParityTail M (eta / 4)).card := by
  have hcover := centralDiscardedSourceSet_subset
    hKM heta0 hetaHalf hK hetaM hstartup
  have hrealTail :
      sourceRealParityTail M (eta / 2) ⊆
        sourceParityTail M (eta / 4) := by
    convert sourceRealParityTail_subset_sourceParityTail
        (M := M) (t := eta / 2) (by positivity) (by linarith) (by linarith)
      using 1 <;> ring
  calc
    (centralDiscardedSourceSet M theta eta).card ≤
        (sourceLateFirstOdd M K ∪
          sourceRealParityTail M (eta / 2)).card :=
      Finset.card_le_card hcover
    _ ≤ (sourceLateFirstOdd M K).card +
          (sourceRealParityTail M (eta / 2)).card :=
      Finset.card_union_le _ _
    _ ≤ (sourceLateFirstOdd M K).card +
          (sourceParityTail M (eta / 4)).card :=
      Nat.add_le_add_left (Finset.card_le_card hrealTail) _

/-- Explicit polynomial-times-exponential cardinal bound for the discarded
central source. -/
theorem card_centralDiscardedSourceSet_cast_le
    {M K : ℕ} {theta eta : ℝ}
    (hKM : K ≤ M)
    (heta0 : 0 < eta) (hetaHalf : eta ≤ 1 / 2)
    (hK : (K : ℝ) ≤ eta * M / 8)
    (hetaM : 4 ≤ eta * M)
    (hstartup : ∀ N : ℕ, M - K ≤ N → N ≤ M →
      1 < N ∧
      (1 / 2 - eta) * N > 1 / 2 ∧
      2 * eta ≤ centralRenyiGap theta eta * ((N : ℝ) - 1) ∧
      (1 / 2 : ℝ) ≤
        (Real.log 2 / Real.log 3 - (1 / 2 + eta)) * N) :
    ((centralDiscardedSourceSet M theta eta).card : ℝ) ≤
      ((M + 1) * 2 ^ (M - K) : ℕ) +
        (2 : ℝ) ^ M *
          (2 * Real.exp (-2 * (eta / 4) ^ 2 * M)) := by
  have hcard := card_centralDiscardedSourceSet_le
    hKM heta0 hetaHalf hK hetaM hstartup
  have hlate := card_sourceLateFirstOdd_le hKM
  have htail := card_sourceParityTail_le
    (M := M) (t := eta / 4) (by positivity) (by linarith)
  have hcardR :
      ((centralDiscardedSourceSet M theta eta).card : ℝ) ≤
        (sourceLateFirstOdd M K).card +
          (sourceParityTail M (eta / 4)).card := by
    exact_mod_cast hcard
  calc
    ((centralDiscardedSourceSet M theta eta).card : ℝ) ≤
        (sourceLateFirstOdd M K).card +
          (sourceParityTail M (eta / 4)).card := hcardR
    _ ≤ ((M + 1) * 2 ^ (M - K) : ℕ) +
          ((sourceParityTail M (eta / 4)).card : ℝ) := by
      gcongr
    _ ≤ ((M + 1) * 2 ^ (M - K) : ℕ) +
        (2 : ℝ) ^ M *
          (2 * Real.exp (-2 * (eta / 4) ^ 2 * M)) := by
      gcongr

end

end FixedTotal

end CollatzEndpointTransport
/-
The higher-Renyi heavy/ordinary fiber split.

At normalized overload threshold `Q`, either a fiber has size at most
`Q * N / R`, or its mass is paid for by the `(1+theta)` moment with the
factor `Q^(-theta)`.  This is the finite algebraic source of the balanced
rate `theta / (1 + theta)`.
-/

namespace CollatzEndpointTransport

namespace FixedTotal

open scoped Real

noncomputable section

/-- Pointwise higher-Renyi split at reference range `R`, source mass `N`,
and normalized overload threshold `Q`. -/
theorem fiber_le_ordinary_add_renyi
    {Q N R f theta : ℝ}
    (hQ : 0 < Q) (hN : 0 < N) (hR : 0 < R)
    (hf : 0 ≤ f) (htheta : 0 < theta) :
    f ≤ Q * N / R +
      Q ^ (-theta) * (R / N) ^ theta * f ^ (1 + theta) := by
  by_cases hsmall : f ≤ Q * N / R
  · exact hsmall.trans (le_add_of_nonneg_right (by positivity))
  · have hlarge : Q * N / R < f := lt_of_not_ge hsmall
    have hfpos : 0 < f := lt_of_le_of_lt (by positivity) hlarge
    have hprod : Q * N < f * R := by
      exact (div_lt_iff₀ hR).mp (by simpa [mul_assoc] using hlarge)
    have hratio : 1 < (R / N) * f / Q := by
      rw [lt_div_iff₀ hQ]
      rw [show (R / N) * f = f * R / N by ring]
      exact (lt_div_iff₀ hN).2 (by nlinarith)
    have hratioPow : 1 ≤ (((R / N) * f / Q) ^ theta) :=
      Real.one_le_rpow hratio.le htheta.le
    have heq :
        f * (((R / N) * f / Q) ^ theta) =
          Q ^ (-theta) * (R / N) ^ theta * f ^ (1 + theta) := by
      rw [Real.div_rpow (mul_nonneg (by positivity) hf) hQ.le]
      rw [Real.mul_rpow (by positivity) hf]
      rw [Real.rpow_neg hQ.le]
      rw [Real.rpow_add hfpos]
      field_simp [(Real.rpow_pos_of_pos hQ theta).ne']
      ring
    have hheavy :
        f ≤ Q ^ (-theta) * (R / N) ^ theta * f ^ (1 + theta) := by
      calc
        f = f * 1 := by ring
        _ ≤ f * (((R / N) * f / Q) ^ theta) :=
          mul_le_mul_of_nonneg_left hratioPow hf
        _ = _ := heq
    exact hheavy.trans (le_add_of_nonneg_left (by positivity))

end

end FixedTotal

end CollatzEndpointTransport
