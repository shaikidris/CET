/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik
-/
import CollatzEndpointTransport.Linear.OptimizedLinearParameterChoice
import CollatzEndpointTransport.Common.StretchedExceptionalCount

/-!
# Optimized Linear Exceptional Count

Quantitative exceptional-count export for the optimized linear theorem.

The terminal shell estimate has power

  sigma = 1 - powerW q transport kappa s,

and the parameter inequalities give `delta < sigma`.  The generic dyadic
summation theorem preserves that power when passing from shells to prefixes.
-/

namespace CollatzEndpointTransport

namespace OptimizedLinearPullback

open scoped Real Topology

noncomputable section

open QuantitativeDensity

def powerExceptionalCountExponent
    (q transport kappa s : ℝ) : ℝ :=
  1 - powerW q transport kappa s

def powerExceptionalCountRate
    (q transport kappa : ℝ) : ℝ :=
  stretchedDyadicRate
      (Real.log 2 * powerDensityConstant q transport kappa / 4) / 2

theorem powerExceptionalCountRate_pos
    {q transport kappa : ℝ}
    (hq0 : 0 < q) (hqa : a0 < q)
    (htransport0 : 0 < transport)
    (hk : KappaAdmissible kappa) :
    0 < powerExceptionalCountRate q transport kappa := by
  unfold powerExceptionalCountRate
  apply div_pos
  apply stretchedDyadicRate_pos
  exact div_pos
    (mul_pos (Real.log_pos (by norm_num))
      (powerDensityConstant_pos hk hq0 hqa htransport0))
    (by norm_num)
  norm_num

/-- Parameterized shell-to-prefix exceptional-count theorem for the exact
power-schedule set. -/
theorem powerDescentSet_badPrefix_eventually_le_stretched_log
    {q transport kappa s delta : ℝ}
    (hq0 : 0 < q) (hqa : a0 < q) (hq1 : q < 1)
    (htransport0 : 0 < transport)
    (htransportLimit : transport < asymptoticRateLimit)
    (hk : KappaAdmissible kappa)
    (hs : 0 < s)
    (hdeltaU : delta < powerU q s)
    (huw : powerU q s + powerW q transport kappa s < 1) :
    ∀ᶠ N : ℕ in Filter.atTop,
      ((badPrefix (powerDescentSet q kappa s delta) N).card : ℝ) ≤
        5 * N *
          Real.exp
            (-(powerExceptionalCountRate q transport kappa) *
              (Real.log N) ^
                (powerExceptionalCountExponent q transport kappa s)) := by
  have htransport1 : transport < 1 :=
    htransportLimit.trans asymptoticRateLimit_lt_one
  have hW0 :
      0 < powerW q transport kappa s :=
    powerW_pos hq0 hq1 htransport0 htransport1 hk hs
  have halpha0 :
      0 < powerExceptionalCountExponent q transport kappa s := by
    unfold powerExceptionalCountExponent
    have hu := powerU_pos hq0 hq1 hs
    linarith
  have halpha1 :
      powerExceptionalCountExponent q transport kappa s ≤ 1 := by
    unfold powerExceptionalCountExponent
    linarith
  have hdelta1 : delta < 1 := by
    have hu := powerU_pos hq0 hq1 hs
    linarith
  have hbudget :=
    powerShellBudget_eventually hk hq0 hqa hq1
      hs hdeltaU hdelta1
  have heq :=
    powerDescentShell_ratio_eventually_eq hbudget
  have hmodel :=
    powerEnvelopeExceptionalRatio_eventually_le_model
      hq0 hqa hq1 htransport0 htransportLimit hk hs huw
  have hshellEvent :
      ∀ᶠ M : ℕ in Filter.atTop,
        shellExceptionalRatio
            (powerDescentShell q kappa s delta M) M ≤
          2 * Real.exp
            (-(Real.log 2 *
                powerDensityConstant q transport kappa / 4) *
              stretchedShellScale M ^
                (powerExceptionalCountExponent
                  q transport kappa s)) := by
    filter_upwards [heq, hmodel] with M heqM hmodelM
    rw [heqM]
    simpa [powerShellDecayModel, powerShellScale,
      stretchedShellScale, powerExceptionalCountExponent] using hmodelM
  obtain ⟨M₀, hM₀⟩ := Filter.eventually_atTop.1 hshellEvent
  let N₀ := 2 ^ (2 * M₀ + 2)
  filter_upwards [Filter.eventually_ge_atTop N₀] with N hN₀
  have hN0 : 0 < N := by
    have hpow0 : 0 < N₀ := by
      dsimp [N₀]
      positivity
    omega
  have hlogLower :
      2 * M₀ + 2 ≤ Nat.log 2 N := by
    apply Nat.le_log_of_pow_le (by norm_num)
    exact hN₀
  have hlogTwo : 2 ≤ Nat.log 2 N := by omega
  have hMhalf : M₀ ≤ Nat.log 2 N / 2 := by
    apply (Nat.le_div_iff_mul_le (by norm_num : 0 < 2)).2
    omega
  have hc :
      0 <
        Real.log 2 *
            powerDensityConstant q transport kappa / 4 := by
    exact div_pos
      (mul_pos (Real.log_pos (by norm_num))
        (powerDensityConstant_pos hk hq0 hqa htransport0))
      (by norm_num)
  have hcount :=
    card_badPrefix_assembleDyadic_le_stretched_log
      (powerDescentShell q kappa s delta) M₀ N 2
      (Real.log 2 * powerDensityConstant q transport kappa / 4)
      (powerExceptionalCountExponent q transport kappa s)
      (by norm_num) hc halpha0 halpha1
      (fun M hM => hM₀ M hM) hN0 hlogTwo hMhalf
  change
    ((badPrefix (assembleDyadic
      (powerDescentShell q kappa s delta)) N).card : ℝ) ≤ _
  simpa only [powerExceptionalCountRate] using
    (show
      ((badPrefix (assembleDyadic
        (powerDescentShell q kappa s delta)) N).card : ℝ) ≤
        5 * N *
          Real.exp
            (-(stretchedDyadicRate
                (Real.log 2 *
                  powerDensityConstant q transport kappa / 4) / 2) *
              (Real.log N) ^
                (powerExceptionalCountExponent q transport kappa s)) by
      convert hcount using 1 <;> norm_num)

/-- Exceptional-count theorem in the internal iterate formulation. The
stretched-exponential power `sigma` is strictly larger than the orbit
exponent `delta`. -/
theorem quantitativeLinearDescent_exceptional_count
    {delta : ℝ}
    (hdelta0 : 0 < delta)
    (hdelta : delta < linearHeadlineExponent) :
    ∃ sigma c : ℝ,
      delta < sigma ∧ sigma ≤ 1 ∧ 0 < c ∧
      ∀ᶠ N : ℕ in Filter.atTop,
        ((badPrefix (quantitativeLinearDescentSet delta 1) N).card : ℝ) ≤
          5 * N * Real.exp (-c * (Real.log N) ^ sigma) := by
  obtain ⟨q, transport, kappa, s,
      hq0, hqa, hq1, ht0, ht1, hk, hs, hdu, huw⟩ :=
    exists_optimized_linear_parameters hdelta0 hdelta
  let sigma := powerExceptionalCountExponent q transport kappa s
  let c := powerExceptionalCountRate q transport kappa
  have htransport1 : transport < 1 :=
    ht1.trans asymptoticRateLimit_lt_one
  have hW0 :
      0 < powerW q transport kappa s :=
    powerW_pos hq0 hq1 ht0 htransport1 hk hs
  have hsigmaDelta : delta < sigma := by
    dsimp [sigma, powerExceptionalCountExponent]
    linarith
  have hsigma1 : sigma ≤ 1 := by
    dsimp [sigma, powerExceptionalCountExponent]
    linarith
  have hc0 : 0 < c := by
    dsimp [c]
    exact powerExceptionalCountRate_pos hq0 hqa ht0 hk
  have hgenerated :=
    powerDescentSet_badPrefix_eventually_le_stretched_log
      hq0 hqa hq1 ht0 ht1 hk hs hdu huw
  refine ⟨sigma, c, hsigmaDelta, hsigma1, hc0, ?_⟩
  filter_upwards [hgenerated] with N hN
  have hsub :
      badPrefix (quantitativeLinearDescentSet delta 1) N ⊆
        badPrefix (powerDescentSet q kappa s delta) N := by
    intro n hn
    simp only [badPrefix, Finset.mem_filter] at hn ⊢
    exact ⟨hn.1, fun hgood =>
      hn.2 (powerDescentSet_subset_quantitativeLinearDescentSet
        hk hq0 hqa hdelta0.le hgood)⟩
  have hcard :
      ((badPrefix (quantitativeLinearDescentSet delta 1) N).card : ℝ) ≤
        ((badPrefix (powerDescentSet q kappa s delta) N).card : ℝ) := by
    exact_mod_cast Finset.card_le_card hsub
  exact hcard.trans hN

end

end OptimizedLinearPullback

end CollatzEndpointTransport
