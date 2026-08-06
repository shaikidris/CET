/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik
-/
import CollatzEndpointTransport.Linear.EndpointOnlyBudget

/-!
# Endpoint Only Theorem

End-to-end endpoint-only logarithmic-block theorem.

This file removes the finitely many shells before the deterministic orbit
budget starts, assembles the remaining endpoint chains, and exports an
actual Collatz iterate below

  exp ((log n)^(1-delta)).

The parameter-selection theorem is deliberately kept separate.
-/

namespace CollatzEndpointTransport

namespace OptimizedLinearPullback

open scoped Real Topology

noncomputable section

open QuantitativeDensity

theorem asymptoticRateLimit_eq_a0_div_three :
    asymptoticRateLimit = a0 / 3 := by
  unfold asymptoticRateLimit a0 lg3 Real.logb
  ring

theorem asymptoticRateLimit_lt_a0 :
    asymptoticRateLimit < a0 := by
  rw [asymptoticRateLimit_eq_a0_div_three]
  nlinarith [a0_pos]

def endpointDescentShell
    (r omega delta : ℝ) (M : ℕ) : Set ℕ := by
  classical
  exact if endpointOrbitBudget r omega delta M ∧ 4 ≤ M then
    endpointChain (r - a0) (endpointStageCount omega M)
  else
    ∅

def endpointDescentSet
    (r omega delta : ℝ) : Set ℕ :=
  assembleDyadic (endpointDescentShell r omega delta)

def endpointTimeShellBudget
    (r omega timeConstant : ℝ) (M : ℕ) : Prop :=
  ∀ n : ℕ,
    Nat.log 2 n = M →
    0 < n →
    n ∈ endpointChain (r - a0) (endpointStageCount omega M) →
    (endpointTime (endpointStageCount omega M) n : ℝ) <
      timeConstant * Real.log n

def endpointTimedDescentShell
    (r omega delta timeConstant : ℝ) (M : ℕ) : Set ℕ := by
  classical
  exact if endpointOrbitBudget r omega delta M ∧
      endpointTimeShellBudget r omega timeConstant M ∧ 4 ≤ M then
    endpointChain (r - a0) (endpointStageCount omega M)
  else
    ∅

def endpointTimedDescentSet
    (r omega delta timeConstant : ℝ) : Set ℕ :=
  assembleDyadic
    (endpointTimedDescentShell r omega delta timeConstant)

def quantitativeEndpointTimedDescentSet
    (timeConstant delta C : ℝ) : Set ℕ :=
  {n | ∃ k : ℕ,
    (k : ℝ) < timeConstant * Real.log n ∧
      (((Terras.T^[k]) n : ℕ) : ℝ) ≤
        Real.exp (C * (Real.log n) ^ (1 - delta))}

theorem endpointDescentShell_ratio_eventually_eq
    {r omega delta : ℝ}
    (hbudget :
      ∀ᶠ M : ℕ in Filter.atTop,
        endpointOrbitBudget r omega delta M) :
    (fun M =>
      shellExceptionalRatio
        (endpointDescentShell r omega delta M) M)
      =ᶠ[Filter.atTop]
    (fun M =>
      shellExceptionalRatio
        (endpointChain (r - a0) (endpointStageCount omega M)) M) := by
  have hM4 :
      ∀ᶠ M : ℕ in Filter.atTop, 4 ≤ M :=
    Filter.eventually_atTop.2 ⟨4, fun _ h => h⟩
  filter_upwards [hbudget, hM4] with M hbudgetM hM4M
  simp [endpointDescentShell, hbudgetM, hM4M]

theorem endpointTimedDescentShell_ratio_eventually_eq
    {r omega delta timeConstant : ℝ}
    (hbudget :
      ∀ᶠ M : ℕ in Filter.atTop,
        endpointOrbitBudget r omega delta M)
    (htime :
      ∀ᶠ M : ℕ in Filter.atTop,
        endpointTimeShellBudget r omega timeConstant M) :
    (fun M =>
      shellExceptionalRatio
        (endpointTimedDescentShell r omega delta timeConstant M) M)
      =ᶠ[Filter.atTop]
    (fun M =>
      shellExceptionalRatio
        (endpointChain (r - a0) (endpointStageCount omega M)) M) := by
  have hM4 :
      ∀ᶠ M : ℕ in Filter.atTop, 4 ≤ M :=
    Filter.eventually_atTop.2 ⟨4, fun _ h => h⟩
  filter_upwards [hbudget, htime, hM4] with M hbudgetM htimeM hM4M
  simp [endpointTimedDescentShell, hbudgetM, htimeM, hM4M]

theorem endpointDescentSet_hasNaturalDensityOne
    {r transport eta D0 Dcut omega delta : ℝ}
    (hra : a0 < r) (hr1 : r < 1)
    (htransport0 : 0 < transport)
    (htransport1 : transport < 1)
    (heta0 : 0 < eta) (heta1 : eta < 1)
    (hD00 : 0 < D0) (hD01 : D0 ≤ 1)
    (hDcut0 : 0 < Dcut) (hD0cut : D0 ≤ Dcut)
    (hcut :
      ∀ D : ℝ, 0 < D → D ≤ Dcut →
        transport * D ≤ shellRate eta D / Real.log 2)
    (hwindow0 :
      transport * D0 ≤
        Terras.quadraticWindowDensityRate (r - a0))
    (homega : 0 < omega)
    (hdeltaU : delta < endpointOrbitPower r omega)
    (hdelta1 : delta < 1)
    (hw : endpointDensityPower transport omega < 1) :
    HasNaturalDensityOne
      (endpointDescentSet r omega delta) := by
  have ht0 : 0 < r - a0 := sub_pos.mpr hra
  have ht1 : r - a0 ≤ 1 := by
    linarith [a0_pos]
  have hbudget :=
    endpointOrbitBudget_eventually
      (a0_pos.trans hra) hr1 homega hdeltaU hdelta1
  have hratio :=
    endpointChainExceptionalRatio_tendsto_zero
      htransport0 htransport1 heta0 heta1 ht0 ht1
      hD00 hD01 hDcut0 hD0cut hcut hwindow0 homega hw
  have hratio' :=
    hratio.congr'
      (endpointDescentShell_ratio_eventually_eq hbudget).symm
  exact hasNaturalDensityOne_assembleDyadic _ hratio'

theorem mem_endpointDescentSet_data
    {r omega delta : ℝ} {n : ℕ}
    (hn : n ∈ endpointDescentSet r omega delta) :
    let M := Nat.log 2 n
    endpointOrbitBudget r omega delta M ∧
      4 ≤ M ∧
      n ∈ endpointChain (r - a0) (endpointStageCount omega M) := by
  classical
  let M := Nat.log 2 n
  have hshell :
      n ∈ endpointDescentShell r omega delta M := by
    simpa [endpointDescentSet, assembleDyadic, M] using hn
  by_cases hcond :
      endpointOrbitBudget r omega delta M ∧ 4 ≤ M
  · simpa [endpointDescentShell, hcond] using
      And.intro hcond hshell
  · simp [endpointDescentShell, hcond] at hshell

theorem mem_endpointTimedDescentSet_data
    {r omega delta timeConstant : ℝ} {n : ℕ}
    (hn : n ∈ endpointTimedDescentSet r omega delta timeConstant) :
    let M := Nat.log 2 n
    endpointOrbitBudget r omega delta M ∧
      endpointTimeShellBudget r omega timeConstant M ∧
      4 ≤ M ∧
      n ∈ endpointChain (r - a0) (endpointStageCount omega M) := by
  classical
  let M := Nat.log 2 n
  have hshell :
      n ∈ endpointTimedDescentShell r omega delta timeConstant M := by
    simpa [endpointTimedDescentSet, assembleDyadic, M] using hn
  by_cases hcond :
      endpointOrbitBudget r omega delta M ∧
        endpointTimeShellBudget r omega timeConstant M ∧ 4 ≤ M
  · simpa [endpointTimedDescentShell, hcond] using
      And.intro hcond hshell
  · simp [endpointTimedDescentShell, hcond] at hshell

theorem endpointDescentSet_subset_quantitativeLinearDescentSet
    {r omega delta : ℝ}
    (hra : a0 < r) (hr1 : r < 1)
    (homega : 0 < omega)
    (hdelta1 : delta < 1) :
    endpointDescentSet r omega delta ⊆
      quantitativeLinearDescentSet delta 1 := by
  intro n hn
  obtain ⟨hbudget, hM4, hchain⟩ :=
    mem_endpointDescentSet_data hn
  let M := Nat.log 2 n
  have hn0 : 0 < n := by
    by_contra hn
    have hnz : n = 0 := Nat.eq_zero_of_not_pos hn
    subst n
    simp [M] at hM4
  let R := endpointStageCount omega M
  let k := endpointTime R n
  refine ⟨k, ?_⟩
  have hvalue :=
    endpointIter_schedule_le_stretchedLog
      hn0 (M := M) rfl hM4 hra hr1 homega hdelta1
      hbudget hchain
  simpa [k, R, endpointIter_eq_iterate_endpointTime] using hvalue

theorem endpointTimedDescentSet_subset_quantitativeEndpointTimedDescentSet
    {r omega delta timeConstant : ℝ}
    (hra : a0 < r) (hr1 : r < 1)
    (homega : 0 < omega)
    (hdelta1 : delta < 1) :
    endpointTimedDescentSet r omega delta timeConstant ⊆
      quantitativeEndpointTimedDescentSet timeConstant delta 1 := by
  intro n hn
  obtain ⟨hbudget, htime, hM4, hchain⟩ :=
    mem_endpointTimedDescentSet_data hn
  let M := Nat.log 2 n
  have hn0 : 0 < n := by
    by_contra hn
    have hnz : n = 0 := Nat.eq_zero_of_not_pos hn
    subst n
    simp [M] at hM4
  let R := endpointStageCount omega M
  let k := endpointTime R n
  refine ⟨k, ?_, ?_⟩
  · exact htime n rfl hn0 hchain
  · have hvalue :=
      endpointIter_schedule_le_stretchedLog
        hn0 (M := M) rfl hM4 hra hr1 homega hdelta1
        hbudget hchain
    simpa [k, R, endpointIter_eq_iterate_endpointTime] using hvalue

/-- Fixed-parameter endpoint-only theorem.  This is the exact abstract
scalar statement: `delta` must lie below the orbit power, while the
retained density power must lie below one. -/
theorem endpointOnlyTheorem_parameterized
    {r transport eta D0 Dcut omega delta : ℝ}
    (hra : a0 < r) (hr1 : r < 1)
    (htransport0 : 0 < transport)
    (htransport1 : transport < 1)
    (heta0 : 0 < eta) (heta1 : eta < 1)
    (hD00 : 0 < D0) (hD01 : D0 ≤ 1)
    (hDcut0 : 0 < Dcut) (hD0cut : D0 ≤ Dcut)
    (hcut :
      ∀ D : ℝ, 0 < D → D ≤ Dcut →
        transport * D ≤ shellRate eta D / Real.log 2)
    (hwindow0 :
      transport * D0 ≤
        Terras.quadraticWindowDensityRate (r - a0))
    (homega : 0 < omega)
    (hdelta0 : 0 < delta)
    (hdeltaU : delta < endpointOrbitPower r omega)
    (htransportR : transport < r)
    (hw : endpointDensityPower transport omega < 1) :
    HasNaturalDensityOne
      (quantitativeLinearDescentSet delta 1) := by
  have hdelta1 : delta < 1 := by
    have hu0 :=
      endpointOrbitPower_pos
        (a0_pos.trans hra) hr1 homega
    have hw0 :=
      endpointDensityPower_pos
        htransport0 htransport1 homega
    have hlog :
        Real.log (1 / r) < Real.log (1 / transport) := by
      exact Real.strictMonoOn_log
        (Set.mem_Ioi.mpr (one_div_pos.mpr (a0_pos.trans hra)))
        (Set.mem_Ioi.mpr (one_div_pos.mpr htransport0))
        (one_div_lt_one_div_of_lt htransport0 htransportR)
    have huLt :
        endpointOrbitPower r omega <
          endpointDensityPower transport omega := by
      unfold endpointOrbitPower endpointDensityPower powerU
      exact mul_lt_mul_of_pos_left hlog homega
    linarith
  apply linearHasNaturalDensityOne_mono
    (endpointDescentSet_subset_quantitativeLinearDescentSet
      hra hr1 homega hdelta1)
  exact endpointDescentSet_hasNaturalDensityOne
    hra hr1 htransport0 htransport1 heta0 heta1
    hD00 hD01 hDcut0 hD0cut hcut hwindow0
    homega hdeltaU hdelta1 hw

/-- The concrete cutoffs required by the endpoint-only theorem exist for
every transport rate below the fixed-total asymptotic limit. -/
theorem endpointOnlyTheorem_of_transport
    {r transport omega delta : ℝ}
    (hra : a0 < r) (hr1 : r < 1)
    (htransport0 : 0 < transport)
    (htransportLimit : transport < asymptoticRateLimit)
    (homega : 0 < omega)
    (hdelta0 : 0 < delta)
    (hdeltaU : delta < endpointOrbitPower r omega)
    (hw : endpointDensityPower transport omega < 1) :
    HasNaturalDensityOne
      (quantitativeLinearDescentSet delta 1) := by
  obtain ⟨Dcut, hDcut0, hDcut1, hcut⟩ :=
    exists_linear_cutoff htransport0 htransportLimit
  let t := r - a0
  let W := Terras.quadraticWindowDensityRate t
  let D0 := min Dcut (W / transport)
  have ht0 : 0 < t := by
    dsimp [t]
    linarith
  have ht1 : t ≤ 1 := by
    dsimp [t]
    linarith [a0_pos]
  have hW0 : 0 < W := by
    unfold W Terras.quadraticWindowDensityRate
    exact div_pos
      (mul_pos Terras.maximalBarrierC0_pos (sq_pos_of_pos ht0))
      (Real.log_pos (by norm_num))
  have hD00 : 0 < D0 := by
    dsimp [D0]
    exact lt_min hDcut0 (div_pos hW0 htransport0)
  have hD01 : D0 ≤ 1 :=
    (min_le_left _ _).trans hDcut1
  have hD0cut : D0 ≤ Dcut :=
    min_le_left _ _
  have hwindow0 : transport * D0 ≤ W := by
    have h :=
      (le_div_iff₀ htransport0).mp (min_le_right Dcut (W / transport))
    simpa [D0, mul_comm] using h
  exact endpointOnlyTheorem_parameterized
    hra hr1 htransport0
    (htransportLimit.trans asymptoticRateLimit_lt_one)
    (asymptoticEta_pos htransport0)
    (asymptoticEta_lt_one htransportLimit)
    hD00 hD01 hDcut0 hD0cut hcut
    (by simpa [W, t] using hwindow0)
    homega hdelta0 hdeltaU
    (htransportLimit.trans asymptoticRateLimit_lt_a0 |>.trans hra)
    hw

end

end OptimizedLinearPullback

end CollatzEndpointTransport
