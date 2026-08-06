/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik
-/
import CollatzEndpointTransport.Linear.OptimizedLinearPowerBudget

/-!
# Optimized Linear Descent Assembly

End-to-end parameterized theorem for the optimized linear pullback.

This file packages one shell-dependent terminal envelope, removes the
finitely many shells where its deterministic endpoint budget has not yet
started, assembles the shell family into a natural-density-one set, and
exports the actual Collatz iterate bound

  T^k(n) <= exp ((log n)^(1-delta)).

The final parameter-selection theorem is kept separate.
-/

namespace CollatzEndpointTransport

namespace OptimizedLinearPullback

open scoped Real Topology

noncomputable section

open QuantitativeDensity

def powerDescentShell
    (q kappa s delta : ℝ) (M : ℕ) : Set ℕ := by
  classical
  exact if powerShellBudget q kappa s delta M ∧ 4 ≤ M then
    powerEnvelope q kappa s M
  else
    ∅

def powerDescentSet
    (q kappa s delta : ℝ) : Set ℕ :=
  assembleDyadic (powerDescentShell q kappa s delta)

def quantitativeLinearDescentSet
    (delta C : ℝ) : Set ℕ :=
  {n | ∃ k : ℕ,
    (((Terras.T^[k]) n : ℕ) : ℝ) ≤
      Real.exp (C * (Real.log n) ^ (1 - delta))}

def quantitativeTimedLinearDescentSet
    (delta C : ℝ) : Set ℕ :=
  {n | ∃ k : ℕ,
    (k : ℝ) ≤ Real.log n / (bConst * Real.log 2) ∧
      (k : ℝ) < (6953 / 1000 : ℝ) * Real.log n ∧
      (((Terras.T^[k]) n : ℕ) : ℝ) ≤
        Real.exp (C * (Real.log n) ^ (1 - delta))}

theorem linearHasNaturalDensityOne_mono
    {S U : Set ℕ} (hSU : S ⊆ U)
    (hS : HasNaturalDensityOne S) :
    HasNaturalDensityOne U := by
  have hbad :
      ∀ N,
        ((badPrefix U N).card : ℝ) / N ≤
          ((badPrefix S N).card : ℝ) / N := by
    intro N
    have hsub : badPrefix U N ⊆ badPrefix S N := by
      intro n hn
      simp only [badPrefix, Finset.mem_filter] at hn ⊢
      exact ⟨hn.1, fun hnS => hn.2 (hSU hnS)⟩
    exact div_le_div_of_nonneg_right
      (by exact_mod_cast Finset.card_le_card hsub)
      (Nat.cast_nonneg N)
  exact squeeze_zero
    (fun N => by positivity)
    hbad hS

theorem powerDescentShell_ratio_eventually_eq
    {q kappa s delta : ℝ}
    (hbudget :
      ∀ᶠ M : ℕ in Filter.atTop,
        powerShellBudget q kappa s delta M) :
    (fun M =>
      shellExceptionalRatio
        (powerDescentShell q kappa s delta M) M)
      =ᶠ[Filter.atTop]
    (fun M =>
      shellExceptionalRatio (powerEnvelope q kappa s M) M) := by
  have hM4 :
      ∀ᶠ M : ℕ in Filter.atTop, 4 ≤ M :=
    Filter.eventually_atTop.2 ⟨4, fun _ h => h⟩
  filter_upwards [hbudget, hM4] with M hbudgetM hM4M
  simp [powerDescentShell, hbudgetM, hM4M]

theorem powerDescentSet_hasNaturalDensityOne
    {q transport kappa s delta : ℝ}
    (hq0 : 0 < q) (hqa : a0 < q) (hq1 : q < 1)
    (htransport0 : 0 < transport)
    (htransportLimit : transport < asymptoticRateLimit)
    (hk : KappaAdmissible kappa)
    (hs : 0 < s)
    (huw : powerU q s + powerW q transport kappa s < 1)
    (hdeltaU : delta < powerU q s)
    (hdelta1 : delta < 1) :
    HasNaturalDensityOne
      (powerDescentSet q kappa s delta) := by
  have hbudget :=
    powerShellBudget_eventually hk hq0 hqa hq1
      hs hdeltaU hdelta1
  have hratio :=
    powerEnvelopeExceptionalRatio_tendsto_zero
      hq0 hqa hq1 htransport0 htransportLimit
      hk hs huw
  have hratio' :=
    hratio.congr'
      (powerDescentShell_ratio_eventually_eq hbudget).symm
  exact hasNaturalDensityOne_assembleDyadic _ hratio'

theorem mem_powerDescentSet_data
    {q kappa s delta : ℝ} {n : ℕ}
    (hn : n ∈ powerDescentSet q kappa s delta) :
    let M := Nat.log 2 n
    powerShellBudget q kappa s delta M ∧
      4 ≤ M ∧
      n ∈ powerEnvelope q kappa s M := by
  classical
  let M := Nat.log 2 n
  have hshell :
      n ∈ powerDescentShell q kappa s delta M := by
    simpa [powerDescentSet, assembleDyadic, M] using hn
  by_cases hcond :
      powerShellBudget q kappa s delta M ∧ 4 ≤ M
  · simpa [powerDescentShell, hcond] using
      And.intro hcond hshell
  · simp [powerDescentShell, hcond] at hshell

theorem log_le_powerShellScale
    {n M : ℕ}
    (hM : M = Nat.log 2 n) (hM4 : 4 ≤ M) :
    0 < Real.log n ∧
      Real.log n ≤ powerShellScale M := by
  have hn0 : 0 < n := by
    by_contra hn
    have hnz : n = 0 := Nat.eq_zero_of_not_pos hn
    subst n
    simp at hM
    omega
  have hnUpperNat : n < 2 ^ (M + 1) := by
    subst M
    exact Nat.lt_pow_succ_log_self (by norm_num) n
  have hnUpper : (n : ℝ) ≤ (2 : ℝ) ^ (M + 1) := by
    exact_mod_cast hnUpperNat.le
  have hnLowerNat : 2 ^ M ≤ n := by
    subst M
    exact Nat.pow_log_le_self 2 hn0.ne'
  have hnOne : 1 < n := by
    have hpowFour :
        2 ^ 4 ≤ n :=
      (Nat.pow_le_pow_right (by norm_num) hM4).trans hnLowerNat
    omega
  have hlogPos : 0 < Real.log n :=
    Real.log_pos (by exact_mod_cast hnOne)
  have hlogUpper :
      Real.log n ≤ ((M : ℝ) + 1) * Real.log 2 := by
    have hnR0 : 0 < (n : ℝ) := by exact_mod_cast hn0
    have h :=
      Real.strictMonoOn_log.monotoneOn
        (Set.mem_Ioi.mpr hnR0)
        (Set.mem_Ioi.mpr
          (by positivity : 0 < (2 : ℝ) ^ (M + 1)))
        hnUpper
    rw [Real.log_pow] at h
    push_cast at h
    simpa [mul_comm] using h
  have hlog2lt : Real.log 2 < 1 :=
    Real.log_two_lt_d9.trans (by norm_num)
  have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  refine ⟨hlogPos, ?_⟩
  unfold powerShellScale
  nlinarith

theorem rpow_shellExponent_le_stretched_log
    {delta : ℝ} {n M : ℕ}
    (hdelta0 : 0 ≤ delta)
    (hM : M = Nat.log 2 n) (hM4 : 4 ≤ M) :
    (n : ℝ) ^ powerShellExponent delta M ≤
      Real.exp ((Real.log n) ^ (1 - delta)) := by
  have hlog := log_le_powerShellScale hM hM4
  have hn0 : 0 < n := by
    by_contra hn
    have hnz : n = 0 := Nat.eq_zero_of_not_pos hn
    subst n
    simp at hM
    omega
  have heps :
      powerShellExponent delta M ≤
        (Real.log n) ^ (-delta) := by
    unfold powerShellExponent
    exact Real.rpow_le_rpow_of_nonpos
      hlog.1 hlog.2 (by linarith)
  have hprod :
      Real.log n * powerShellExponent delta M ≤
        Real.log n * (Real.log n) ^ (-delta) :=
    mul_le_mul_of_nonneg_left heps hlog.1.le
  rw [Real.rpow_def_of_pos (by exact_mod_cast hn0)]
  apply Real.exp_le_exp.2
  calc
    Real.log (n : ℝ) * powerShellExponent delta M
        ≤ Real.log n * (Real.log n) ^ (-delta) := hprod
    _ = (Real.log n) ^ (1 - delta) := by
      calc
        Real.log n * (Real.log n) ^ (-delta)
            =
          (Real.log n) ^ (1 : ℝ) *
            (Real.log n) ^ (-delta) := by
              rw [Real.rpow_one]
        _ = (Real.log n) ^ ((1 : ℝ) + (-delta)) := by
              rw [← Real.rpow_add hlog.1]
        _ = _ := by ring

theorem powerDescentSet_subset_quantitativeLinearDescentSet
    {q kappa s delta : ℝ}
    (hk : KappaAdmissible kappa)
    (hq0 : 0 < q) (hqa : a0 < q)
    (hdelta0 : 0 ≤ delta) :
    powerDescentSet q kappa s delta ⊆
      quantitativeLinearDescentSet delta 1 := by
  intro n hn
  obtain ⟨hbudget, hM4, hgood⟩ :=
    mem_powerDescentSet_data hn
  let M := Nat.log 2 n
  have hn0 : 0 < n := by
    by_contra hn
    have hnz : n = 0 := Nat.eq_zero_of_not_pos hn
    subst n
    simp [M] at hM4
  have ht0 :
      0 ≤ powerTR kappa q s M :=
    (powerTerminalTolerance_pos hk hq0 hqa _).le
  have heps0 := (powerShellExponent_pos delta M).le
  obtain ⟨k, hkvalue⟩ :=
    exists_iterate_le_rpow_of_mem_terminal_envelope
      hn0 rfl ht0 heps0 hbudget (by
        simpa [powerEnvelope, powerTR, powerR] using hgood)
  refine ⟨k, hkvalue.trans ?_⟩
  simpa using
    rpow_shellExponent_le_stretched_log
      hdelta0 (M := M) rfl hM4

theorem powerDescentSet_subset_quantitativeTimedLinearDescentSet
    {q kappa s delta : ℝ}
    (hk : KappaAdmissible kappa)
    (hq0 : 0 < q) (hqa : a0 < q) (hq1 : q < 1)
    (hdelta0 : 0 ≤ delta) :
    powerDescentSet q kappa s delta ⊆
      quantitativeTimedLinearDescentSet delta 1 := by
  intro n hn
  obtain ⟨hbudget, hM4, hgood⟩ :=
    mem_powerDescentSet_data hn
  let M := Nat.log 2 n
  have hn0 : 0 < n := by
    by_contra hn
    have hnz : n = 0 := Nat.eq_zero_of_not_pos hn
    subst n
    simp [M] at hM4
  have ht0 :
      0 ≤ powerTR kappa q s M :=
    (powerTerminalTolerance_pos hk hq0 hqa _).le
  have heps0 := (powerShellExponent_pos delta M).le
  let k := envelopeHorizon (linearLambda q (powerR s M)) n
  have hgood' :
      n ∈ EnvelopeGood
        (linearLambda q (powerR s M))
        (powerTR kappa q s M) := by
    simpa [powerEnvelope] using hgood
  have hvalue :
      (((Terras.T^[k]) n : ℕ) : ℝ) ≤
        (n : ℝ) ^ powerShellExponent delta M := by
    simpa [k] using
      iterate_at_horizon_le_rpow_of_mem_terminal_envelope
        hn0 rfl ht0 heps0 hbudget hgood'
  have hlambda0 :
      0 ≤ linearLambda q (powerR s M) :=
    (linearLambda_pos hq0 _).le
  have hlambda1 :
      linearLambda q (powerR s M) ≤ 1 :=
    (linearLambda_lt_one hq0 hq1 _).le
  have htime :
      (k : ℝ) ≤ Real.log n / (bConst * Real.log 2) := by
    simpa [k] using
      envelopeHorizon_le_natural_log_time
        hn0 hlambda0 hlambda1
  have hnOne : 1 < n := by
    have hpow := Nat.pow_log_le_self 2 hn0.ne'
    have hpowFour :
        2 ^ 4 ≤ n :=
      (Nat.pow_le_pow_right (by norm_num) hM4).trans hpow
    omega
  have htimeDecimal :
      (k : ℝ) < (6953 / 1000 : ℝ) * Real.log n := by
    simpa [k] using
      envelopeHorizon_lt_6953_log hnOne hlambda0 hlambda1
  refine ⟨k, htime, htimeDecimal, hvalue.trans ?_⟩
  simpa using
    rpow_shellExponent_le_stretched_log
      hdelta0 (M := M) rfl hM4

theorem quantitativeLinearTheorem_parameterized
    {q transport kappa s delta : ℝ}
    (hq0 : 0 < q) (hqa : a0 < q) (hq1 : q < 1)
    (htransport0 : 0 < transport)
    (htransportLimit : transport < asymptoticRateLimit)
    (hk : KappaAdmissible kappa)
    (hs : 0 < s)
    (hdelta0 : 0 < delta)
    (hdeltaU : delta < powerU q s)
    (huw : powerU q s + powerW q transport kappa s < 1) :
    HasNaturalDensityOne
      (quantitativeLinearDescentSet delta 1) := by
  have hw :=
    powerW_pos hq0 hq1 htransport0
      (htransportLimit.trans asymptoticRateLimit_lt_one)
      hk hs
  have hdelta1 : delta < 1 := by linarith
  apply linearHasNaturalDensityOne_mono
    (powerDescentSet_subset_quantitativeLinearDescentSet
      hk hq0 hqa hdelta0.le)
  exact powerDescentSet_hasNaturalDensityOne
    hq0 hqa hq1 htransport0 htransportLimit
    hk hs huw hdeltaU hdelta1

theorem quantitativeLinearTheorem_parameterized_timed
    {q transport kappa s delta : ℝ}
    (hq0 : 0 < q) (hqa : a0 < q) (hq1 : q < 1)
    (htransport0 : 0 < transport)
    (htransportLimit : transport < asymptoticRateLimit)
    (hk : KappaAdmissible kappa)
    (hs : 0 < s)
    (hdelta0 : 0 < delta)
    (hdeltaU : delta < powerU q s)
    (huw : powerU q s + powerW q transport kappa s < 1) :
    HasNaturalDensityOne
      (quantitativeTimedLinearDescentSet delta 1) := by
  have hw :=
    powerW_pos hq0 hq1 htransport0
      (htransportLimit.trans asymptoticRateLimit_lt_one)
      hk hs
  have hdelta1 : delta < 1 := by linarith
  apply linearHasNaturalDensityOne_mono
    (powerDescentSet_subset_quantitativeTimedLinearDescentSet
      hk hq0 hqa hq1 hdelta0.le)
  exact powerDescentSet_hasNaturalDensityOne
    hq0 hqa hq1 htransport0 htransportLimit
    hk hs huw hdeltaU hdelta1

end

end OptimizedLinearPullback

end CollatzEndpointTransport
