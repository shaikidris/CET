/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik
-/
import CollatzEndpointTransport.Linear.OptimizedLinearDescentAssembly

/-!
# Optimized Linear Parameter Choice

Parameter selection at the optimized linear endpoint.

The admissible fixed-parameter exponent is

  log(1/q) / log(1/(transport*kappa^2*q^3)).

Letting

  q -> a0 from above,
  transport -> log(3)/(6 log(2)) from below,
  kappa -> sqrt(2)-1 from below

gives the published endpoint.  A concrete natural-number sequence realizes
the three one-sided limits, so the existence proof contains no appeal to an
informal boundary optimization.
-/

namespace CollatzEndpointTransport

namespace OptimizedLinearPullback

open scoped Real Topology

noncomputable section

open QuantitativeDensity

def linearKappaLimit : ℝ :=
  Real.sqrt 2 - 1

def linearParameterDelta
    (q transport kappa : ℝ) : ℝ :=
  Real.log (1 / q) /
    Real.log (1 / (transport * kappa ^ 2 * q ^ 3))

/-- The exact endpoint used by the optimized linear descent theorem. -/
def linearHeadlineExponent : ℝ :=
  linearParameterDelta
    a0 asymptoticRateLimit linearKappaLimit

def linearChoiceEps (n : ℕ) : ℝ :=
  1 / ((n : ℝ) + 2)

def linearChoiceQ (n : ℕ) : ℝ :=
  a0 + (1 - a0) * linearChoiceEps n

def linearChoiceTransport (n : ℕ) : ℝ :=
  asymptoticRateLimit * (1 - linearChoiceEps n)

def linearChoiceKappa (n : ℕ) : ℝ :=
  linearKappaLimit * (1 - linearChoiceEps n)

theorem linearKappaLimit_pos :
    0 < linearKappaLimit := by
  unfold linearKappaLimit
  have hsqrt : 1 < Real.sqrt 2 := by
    rw [Real.lt_sqrt (by norm_num)]
    norm_num
  linarith

theorem linearKappaLimit_lt_one :
    linearKappaLimit < 1 := by
  unfold linearKappaLimit
  have hsqrt : Real.sqrt 2 < 2 := by
    rw [Real.sqrt_lt' (by norm_num)]
    norm_num
  linarith

theorem linearKappaLimit_budget :
    2 * linearKappaLimit + linearKappaLimit ^ 2 = 1 := by
  have hsqrtSq : (Real.sqrt 2) ^ 2 = 2 :=
    Real.sq_sqrt (by norm_num)
  unfold linearKappaLimit
  nlinarith

theorem kappaAdmissible_of_lt_limit
    {kappa : ℝ}
    (hk0 : 0 < kappa)
    (hklt : kappa < linearKappaLimit) :
    KappaAdmissible kappa := by
  refine ⟨hk0, ?_⟩
  have hlimit0 := linearKappaLimit_pos
  have hdiff :
      0 <
        (linearKappaLimit - kappa) *
          (2 + linearKappaLimit + kappa) := by
    exact mul_pos (sub_pos.mpr hklt) (by positivity)
  rw [← linearKappaLimit_budget]
  nlinarith

theorem linearChoiceEps_pos (n : ℕ) :
    0 < linearChoiceEps n := by
  unfold linearChoiceEps
  positivity

theorem linearChoiceEps_le_half (n : ℕ) :
    linearChoiceEps n ≤ 1 / 2 := by
  unfold linearChoiceEps
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hden : (2 : ℝ) ≤ (n : ℝ) + 2 := by linarith
  exact one_div_le_one_div_of_le (by norm_num) hden

theorem linearChoiceEps_lt_one (n : ℕ) :
    linearChoiceEps n < 1 :=
  (linearChoiceEps_le_half n).trans_lt (by norm_num)

theorem linearChoiceQ_properties (n : ℕ) :
    0 < linearChoiceQ n ∧
      a0 < linearChoiceQ n ∧
      linearChoiceQ n < 1 := by
  have he0 := linearChoiceEps_pos n
  have he1 := linearChoiceEps_lt_one n
  have ha0 := a0_pos
  have ha1 := a0_lt_one
  unfold linearChoiceQ
  constructor
  · have hprod : 0 < (1 - a0) * linearChoiceEps n :=
      mul_pos (sub_pos.mpr ha1) he0
    linarith
  constructor <;> nlinarith

theorem linearChoiceTransport_properties (n : ℕ) :
    0 < linearChoiceTransport n ∧
      linearChoiceTransport n < asymptoticRateLimit := by
  have he0 := linearChoiceEps_pos n
  have he1 := linearChoiceEps_lt_one n
  have hc0 := asymptoticRateLimit_pos
  unfold linearChoiceTransport
  constructor <;> nlinarith

theorem linearChoiceKappa_properties (n : ℕ) :
    0 < linearChoiceKappa n ∧
      linearChoiceKappa n < linearKappaLimit ∧
      KappaAdmissible (linearChoiceKappa n) := by
  have he0 := linearChoiceEps_pos n
  have he1 := linearChoiceEps_lt_one n
  have hk0 := linearKappaLimit_pos
  have hkPos :
      0 < linearChoiceKappa n := by
    unfold linearChoiceKappa
    exact mul_pos hk0 (sub_pos.mpr he1)
  have hkLt :
      linearChoiceKappa n < linearKappaLimit := by
    unfold linearChoiceKappa
    nlinarith
  exact ⟨hkPos, hkLt, kappaAdmissible_of_lt_limit hkPos hkLt⟩

theorem linearChoiceEps_tendsto_zero :
    Filter.Tendsto linearChoiceEps Filter.atTop (nhds 0) := by
  have htop :
      Filter.Tendsto
        (fun n : ℕ => (n : ℝ) + 2)
        Filter.atTop Filter.atTop :=
    tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
  unfold linearChoiceEps
  simpa only [one_div] using htop.inv_tendsto_atTop

theorem linearChoiceQ_tendsto :
    Filter.Tendsto linearChoiceQ Filter.atTop (nhds a0) := by
  have h :=
    (linearChoiceEps_tendsto_zero.const_mul (1 - a0)).const_add a0
  simpa [linearChoiceQ] using h

theorem linearChoiceTransport_tendsto :
    Filter.Tendsto linearChoiceTransport Filter.atTop
      (nhds asymptoticRateLimit) := by
  have hone :=
    linearChoiceEps_tendsto_zero.neg.const_add 1
  have h := hone.mul_const asymptoticRateLimit
  simpa [linearChoiceTransport, sub_eq_add_neg, mul_comm] using h

theorem linearChoiceKappa_tendsto :
    Filter.Tendsto linearChoiceKappa Filter.atTop
      (nhds linearKappaLimit) := by
  have hone :=
    linearChoiceEps_tendsto_zero.neg.const_add 1
  have h := hone.mul_const linearKappaLimit
  simpa [linearChoiceKappa, sub_eq_add_neg, mul_comm] using h

theorem linearLimitBase_pos :
    0 <
      asymptoticRateLimit * linearKappaLimit ^ 2 * a0 ^ 3 := by
  exact mul_pos
    (mul_pos asymptoticRateLimit_pos
      (sq_pos_of_pos linearKappaLimit_pos))
    (pow_pos a0_pos 3)

theorem linearLimitBase_lt_one :
    asymptoticRateLimit * linearKappaLimit ^ 2 * a0 ^ 3 < 1 := by
  have hc1 := asymptoticRateLimit_lt_one
  have hk1 := linearKappaLimit_lt_one
  have ha1 := a0_lt_one
  have hkSq : linearKappaLimit ^ 2 < 1 := by
    nlinarith [linearKappaLimit_pos,
      mul_pos linearKappaLimit_pos (sub_pos.mpr hk1)]
  have haCube : a0 ^ 3 < 1 := by
    have haSq : a0 ^ 2 < 1 := by
      nlinarith [a0_pos, mul_pos a0_pos (sub_pos.mpr ha1)]
    calc
      a0 ^ 3 = a0 ^ 2 * a0 := by ring
      _ < 1 * a0 :=
        mul_lt_mul_of_pos_right haSq a0_pos
      _ < 1 := by simpa using ha1
  have hck :
      asymptoticRateLimit * linearKappaLimit ^ 2 < 1 := by
    calc
      asymptoticRateLimit * linearKappaLimit ^ 2
          < 1 * linearKappaLimit ^ 2 :=
        mul_lt_mul_of_pos_right hc1
          (sq_pos_of_pos linearKappaLimit_pos)
      _ < 1 := by simpa using hkSq
  calc
    asymptoticRateLimit * linearKappaLimit ^ 2 * a0 ^ 3
        < 1 * a0 ^ 3 :=
      mul_lt_mul_of_pos_right hck (pow_pos a0_pos 3)
    _ < 1 := by simpa using haCube

theorem linearHeadlineExponent_pos :
    0 < linearHeadlineExponent := by
  unfold linearHeadlineExponent linearParameterDelta
  exact div_pos
    (log_one_div_pos a0_pos a0_lt_one)
    (log_one_div_pos linearLimitBase_pos linearLimitBase_lt_one)

theorem linearParameterDelta_choice_tendsto :
    Filter.Tendsto
      (fun n =>
        linearParameterDelta
          (linearChoiceQ n)
          (linearChoiceTransport n)
          (linearChoiceKappa n))
      Filter.atTop (nhds linearHeadlineExponent) := by
  have hq := linearChoiceQ_tendsto
  have ht := linearChoiceTransport_tendsto
  have hk := linearChoiceKappa_tendsto
  have hprod :
      Filter.Tendsto
        (fun n =>
          linearChoiceTransport n *
            linearChoiceKappa n ^ 2 *
            linearChoiceQ n ^ 3)
        Filter.atTop
        (nhds
          (asymptoticRateLimit *
            linearKappaLimit ^ 2 * a0 ^ 3)) :=
    (ht.mul (hk.pow 2)).mul (hq.pow 3)
  have hnum :
      Filter.Tendsto
        (fun n => Real.log (1 / linearChoiceQ n))
        Filter.atTop (nhds (Real.log (1 / a0))) := by
    have hinv := hq.inv₀ a0_pos.ne'
    simpa [one_div] using hinv.log (inv_ne_zero a0_pos.ne')
  have hden :
      Filter.Tendsto
        (fun n =>
          Real.log
            (1 /
              (linearChoiceTransport n *
                linearChoiceKappa n ^ 2 *
                linearChoiceQ n ^ 3)))
        Filter.atTop
        (nhds
          (Real.log
            (1 /
              (asymptoticRateLimit *
                linearKappaLimit ^ 2 * a0 ^ 3)))) := by
    have hinv := hprod.inv₀ linearLimitBase_pos.ne'
    simpa [one_div] using
      hinv.log (inv_ne_zero linearLimitBase_pos.ne')
  have hden0 :
      Real.log
          (1 /
            (asymptoticRateLimit *
              linearKappaLimit ^ 2 * a0 ^ 3)) ≠ 0 :=
    ne_of_gt
      (log_one_div_pos linearLimitBase_pos linearLimitBase_lt_one)
  have hratio := hnum.div hden hden0
  simpa [linearParameterDelta, linearHeadlineExponent] using hratio

theorem combined_three_base_pos
    {q transport kappa : ℝ}
    (hq0 : 0 < q) (htransport0 : 0 < transport)
    (hk : KappaAdmissible kappa) :
    0 < transport * kappa ^ 2 * q ^ 3 := by
  exact mul_pos
    (mul_pos htransport0 (sq_pos_of_pos hk.1))
    (pow_pos hq0 3)

theorem combined_three_base_lt_one
    {q transport kappa : ℝ}
    (hq0 : 0 < q) (hq1 : q < 1)
    (htransport0 : 0 < transport) (htransport1 : transport < 1)
    (hk : KappaAdmissible kappa) :
    transport * kappa ^ 2 * q ^ 3 < 1 := by
  have hbase :=
    power_combined_base_lt_one hq0 hq1
      htransport0 htransport1 hk
  calc
    transport * kappa ^ 2 * q ^ 3 =
        (transport * kappa ^ 2 * q ^ 2) * q := by ring
    _ < 1 * q :=
      mul_lt_mul_of_pos_right hbase hq0
    _ < 1 := by simpa using hq1

theorem log_combined_three
    {q transport kappa : ℝ}
    (hq0 : 0 < q) (htransport0 : 0 < transport)
    (hk : KappaAdmissible kappa) :
    Real.log (1 / q) +
        Real.log (1 / (transport * kappa ^ 2 * q ^ 2)) =
      Real.log (1 / (transport * kappa ^ 2 * q ^ 3)) := by
  have hqne := hq0.ne'
  have htne := htransport0.ne'
  have hkne := hk.1.ne'
  have hbase2 :=
    power_combined_base_pos hq0 htransport0 hk
  have hfactor :
      1 / (transport * kappa ^ 2 * q ^ 3) =
        (1 / q) * (1 / (transport * kappa ^ 2 * q ^ 2)) := by
    field_simp [hqne, htne, hkne, hbase2.ne']
    ring
  rw [hfactor, Real.log_mul
    (one_div_ne_zero hqne) (one_div_ne_zero hbase2.ne')]

theorem exists_power_s_of_delta_lt_parameter
    {q transport kappa delta : ℝ}
    (hdelta0 : 0 < delta)
    (hq0 : 0 < q) (hq1 : q < 1)
    (htransport0 : 0 < transport) (htransport1 : transport < 1)
    (hk : KappaAdmissible kappa)
    (hdelta :
      delta < linearParameterDelta q transport kappa) :
    ∃ s : ℝ,
      0 < s ∧
      delta < powerU q s ∧
      powerU q s + powerW q transport kappa s < 1 := by
  let Lq := Real.log (1 / q)
  let L := Real.log (1 / (transport * kappa ^ 2 * q ^ 3))
  have hLq : 0 < Lq := by
    dsimp [Lq]
    exact log_one_div_pos hq0 hq1
  have hbase0 := combined_three_base_pos hq0 htransport0 hk
  have hbase1 :=
    combined_three_base_lt_one hq0 hq1
      htransport0 htransport1 hk
  have hL : 0 < L := by
    dsimp [L]
    exact log_one_div_pos hbase0 hbase1
  have hcross :
      delta / Lq < 1 / L := by
    unfold linearParameterDelta at hdelta
    dsimp [Lq, L]
    rw [div_lt_div_iff₀ hLq hL]
    have := (lt_div_iff₀ hL).mp hdelta
    nlinarith
  let s := (delta / Lq + 1 / L) / 2
  have hsLower : delta / Lq < s := by
    dsimp [s]
    linarith
  have hsUpper : s < 1 / L := by
    dsimp [s]
    linarith
  have hs0 : 0 < s := by
    have : 0 < delta / Lq := div_pos hdelta0 hLq
    linarith
  have hdeltaU : delta < powerU q s := by
    unfold powerU
    have hmul := mul_lt_mul_of_pos_right hsLower hLq
    dsimp [Lq] at hmul
    field_simp [hLq.ne'] at hmul
    simpa [mul_comm] using hmul
  have hsum :
      powerU q s + powerW q transport kappa s =
        s * L := by
    unfold powerU powerW
    rw [← mul_add,
      log_combined_three hq0 htransport0 hk]
  have huw : powerU q s + powerW q transport kappa s < 1 := by
    rw [hsum]
    have hmul := mul_lt_mul_of_pos_right hsUpper hL
    field_simp [hL.ne'] at hmul
    simpa using hmul
  exact ⟨s, hs0, hdeltaU, huw⟩

/-- Every exponent below the boundary value admits fixed interior proof
parameters and a valid power-schedule slope. -/
theorem exists_optimized_linear_parameters
    {delta : ℝ}
    (hdelta0 : 0 < delta)
    (hdelta : delta < linearHeadlineExponent) :
    ∃ q transport kappa s : ℝ,
      0 < q ∧ a0 < q ∧ q < 1 ∧
      0 < transport ∧ transport < asymptoticRateLimit ∧
      KappaAdmissible kappa ∧
      0 < s ∧
      delta < powerU q s ∧
      powerU q s + powerW q transport kappa s < 1 := by
  have hevent :
      ∀ᶠ n : ℕ in Filter.atTop,
        delta <
          linearParameterDelta
            (linearChoiceQ n)
            (linearChoiceTransport n)
            (linearChoiceKappa n) :=
    linearParameterDelta_choice_tendsto.eventually
      (Ioi_mem_nhds hdelta)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hevent
  let q := linearChoiceQ N
  let transport := linearChoiceTransport N
  let kappa := linearChoiceKappa N
  have hq := linearChoiceQ_properties N
  have ht := linearChoiceTransport_properties N
  have hk := linearChoiceKappa_properties N
  have hparam :
      delta < linearParameterDelta q transport kappa := by
    exact hN N le_rfl
  obtain ⟨s, hs0, hdeltaU, huw⟩ :=
    exists_power_s_of_delta_lt_parameter hdelta0
      hq.1 hq.2.2 ht.1
      (ht.2.trans asymptoticRateLimit_lt_one)
      hk.2.2 hparam
  exact ⟨q, transport, kappa, s,
    hq.1, hq.2.1, hq.2.2,
    ht.1, ht.2, hk.2.2,
    hs0, hdeltaU, huw⟩

theorem linearHeadlineExponent_eq_paper :
    linearHeadlineExponent =
      1 /
        (3 +
          Real.log
              (1 /
                (asymptoticRateLimit * linearKappaLimit ^ 2)) /
            Real.log (1 / a0)) := by
  let A := asymptoticRateLimit * linearKappaLimit ^ 2
  let L := Real.log (1 / a0)
  let LA := Real.log (1 / A)
  have hA0 : 0 < A := by
    dsimp [A]
    exact mul_pos asymptoticRateLimit_pos
      (sq_pos_of_pos linearKappaLimit_pos)
  have hAne := hA0.ne'
  have ha0ne := a0_pos.ne'
  have hL0 : 0 < L := by
    dsimp [L]
    exact log_one_div_pos a0_pos a0_lt_one
  have hfactor :
      1 /
          (asymptoticRateLimit * linearKappaLimit ^ 2 * a0 ^ 3) =
        (1 / A) * (1 / a0) ^ 3 := by
    dsimp [A]
    field_simp [hAne, ha0ne]
  have hden :
      Real.log
          (1 /
            (asymptoticRateLimit *
              linearKappaLimit ^ 2 * a0 ^ 3)) =
        LA + 3 * L := by
    rw [hfactor,
      Real.log_mul (one_div_ne_zero hAne)
        (pow_ne_zero 3 (one_div_ne_zero ha0ne)),
      Real.log_pow]
    rfl
  have hden0 :
      LA + 3 * L ≠ 0 := by
    rw [← hden]
    exact ne_of_gt
      (log_one_div_pos linearLimitBase_pos linearLimitBase_lt_one)
  unfold linearHeadlineExponent linearParameterDelta
  rw [hden]
  change L / (LA + 3 * L) = 1 / (3 + LA / L)
  calc
    L / (LA + 3 * L)
        = 1 / ((LA + 3 * L) / L) := by
          field_simp [hL0.ne', hden0]
    _ = 1 / (3 + LA / L) := by
          congr 2
          field_simp [hL0.ne']
          ring

/-- **Optimized linear descent, internal Collatz-iterate form.** -/
theorem quantitativeLinearDescent_one
    {delta : ℝ}
    (hdelta0 : 0 < delta)
    (hdelta : delta < linearHeadlineExponent) :
    HasNaturalDensityOne
      (quantitativeLinearDescentSet delta 1) := by
  obtain ⟨q, transport, kappa, s,
      hq0, hqa, hq1, ht0, ht1, hk, hs, hdu, huw⟩ :=
    exists_optimized_linear_parameters hdelta0 hdelta
  exact quantitativeLinearTheorem_parameterized
    hq0 hqa hq1 ht0 ht1 hk hs hdelta0 hdu huw

/-- The same theorem with the explicit logarithmic witness time. -/
theorem quantitativeLinearDescent_timed
    {delta : ℝ}
    (hdelta0 : 0 < delta)
    (hdelta : delta < linearHeadlineExponent) :
    HasNaturalDensityOne
      (quantitativeTimedLinearDescentSet delta 1) := by
  obtain ⟨q, transport, kappa, s,
      hq0, hqa, hq1, ht0, ht1, hk, hs, hdu, huw⟩ :=
    exists_optimized_linear_parameters hdelta0 hdelta
  exact quantitativeLinearTheorem_parameterized_timed
    hq0 hqa hq1 ht0 ht1 hk hs hdelta0 hdu huw

end

end OptimizedLinearPullback

end CollatzEndpointTransport
