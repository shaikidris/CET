/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik
-/
import CollatzEndpointTransport.Linear.CentralRenyiEndpointOnly

/-!
# Endpoint Only Fixed Power

Fixed-power consequences of the endpoint-only density recurrence.

The logarithmic-block proof is normally stopped after `O(log log n)` stages.
Stopping after the fixed number `ceil (log_r alpha)` instead gives descent
below `K * n^alpha`.  The terminal density exponent is bounded below by a
fixed multiple of `alpha^beta` for every beta above the reciprocal endpoint
exponent.
-/

namespace CollatzEndpointTransport

namespace OptimizedLinearPullback

open scoped Real Topology

noncomputable section

open QuantitativeDensity

/-- The fixed-power orbit-minimum event.  Including zero makes set inclusions
total; quantitative density only counts positive integers. -/
def endpointFixedPowerSet (alpha K : ℝ) : Set ℕ :=
  {n | n = 0 ∨ (Terras.Tmin n : ℝ) ≤ K * (n : ℝ) ^ alpha}

/-- Positivity of every endpoint in a supported chain. -/
theorem endpointIter_pos_of_mem :
    ∀ {R n : ℕ} {r : ℝ},
      0 < n →
      a0 < r → r < 1 →
      n ∈ endpointChain (r - a0) R →
      0 < endpointIter R n := by
  intro R
  induction R with
  | zero =>
      intro n r hn _ _ _
      simpa
  | succ R ih =>
      intro n r hn hra hr1 hchain
      rcases mem_endpointChain_succ.mp hchain with ⟨hwindow, hrest⟩
      rw [endpointIter_succ]
      exact ih (endpointBlock_pos_of_mem_initialWindow hn hwindow)
        hra hr1 hrest

/-- A fixed endpoint chain gives the paper's uniform fixed-power bound. -/
theorem endpointIter_le_fixed_power
    {n R : ℕ} {r alpha : ℝ}
    (hn : 0 < n)
    (hra : a0 < r) (hr1 : r < 1)
    (hchain : n ∈ endpointChain (r - a0) R)
    (hpower : r ^ R ≤ alpha) :
    (endpointIter R n : ℝ) ≤
      endpointK ^ ((1 - r)⁻¹) * (n : ℝ) ^ alpha := by
  have hr0 : 0 ≤ r := a0_pos.le.trans hra.le
  have hlogn0 : 0 ≤ Real.log n :=
    Real.log_nonneg (by exact_mod_cast hn)
  have hgeom := endpointGeom_le_inv_one_sub hr0 hr1 R
  have hlogK0 : 0 ≤ Real.log endpointK := by
    rw [log_endpointK]
    exact mul_nonneg bConst_pos.le
      (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le
  have hlog := log_endpointIter_le hn hra hr1 hchain
  have hlogBound :
      Real.log (endpointIter R n) ≤
        alpha * Real.log n + Real.log endpointK * (1 - r)⁻¹ := by
    calc
      Real.log (endpointIter R n)
          ≤ r ^ R * Real.log n +
              Real.log endpointK * endpointGeom r R := hlog
      _ ≤ alpha * Real.log n +
              Real.log endpointK * (1 - r)⁻¹ :=
        add_le_add
          (mul_le_mul_of_nonneg_right hpower hlogn0)
          (mul_le_mul_of_nonneg_left hgeom hlogK0)
  have hendpoint0 : 0 < (endpointIter R n : ℝ) := by
    exact_mod_cast endpointIter_pos_of_mem hn hra hr1 hchain
  have hexp := (Real.log_le_iff_le_exp hendpoint0).mp hlogBound
  rw [Real.exp_add] at hexp
  simpa [Real.rpow_def_of_pos (by exact_mod_cast hn : (0 : ℝ) < n),
    Real.rpow_def_of_pos endpointK_pos, mul_comm] using hexp

theorem endpointChain_subset_fixed_power
    {R : ℕ} {r alpha : ℝ}
    (hra : a0 < r) (hr1 : r < 1)
    (hpower : r ^ R ≤ alpha) :
    endpointChain (r - a0) R ⊆
      endpointFixedPowerSet alpha (endpointK ^ ((1 - r)⁻¹)) := by
  intro n hchain
  by_cases hn0 : n = 0
  · exact Or.inl hn0
  · right
    have hn : 0 < n := Nat.pos_of_ne_zero hn0
    have hmin : (Terras.Tmin n : ℝ) ≤ endpointIter R n := by
      exact_mod_cast Tmin_le_endpointIter n R
    exact hmin.trans (endpointIter_le_fixed_power hn hra hr1 hchain hpower)

/-- Number of endpoint blocks needed to reach the power `alpha`. -/
def fixedPowerStageCount (r alpha : ℝ) : ℕ :=
  ⌈Real.logb r alpha⌉₊

theorem fixedPowerStageCount_pos
    {r alpha : ℝ}
    (hr0 : 0 < r) (hr1 : r < 1)
    (ha0 : 0 < alpha) (ha1 : alpha < 1) :
    0 < fixedPowerStageCount r alpha := by
  have hlogr : Real.log r < 0 := Real.log_neg hr0 hr1
  have hloga : Real.log alpha < 0 := Real.log_neg ha0 ha1
  have hq : 0 < Real.logb r alpha := by
    unfold Real.logb
    exact div_pos_of_neg_of_neg hloga hlogr
  unfold fixedPowerStageCount
  exact Nat.ceil_pos.mpr hq

theorem fixedPowerStageCount_contracts
    {r alpha : ℝ}
    (hr0 : 0 < r) (hr1 : r < 1)
    (ha0 : 0 < alpha) :
    r ^ fixedPowerStageCount r alpha ≤ alpha := by
  have hceil :
      Real.logb r alpha ≤ (fixedPowerStageCount r alpha : ℝ) := by
    exact Nat.le_ceil _
  rw [← Real.rpow_natCast]
  calc
    r ^ (fixedPowerStageCount r alpha : ℝ)
        ≤ r ^ Real.logb r alpha :=
      Real.rpow_le_rpow_of_exponent_ge hr0 hr1.le hceil
    _ = alpha := Real.rpow_logb hr0 hr1.ne ha0

/-- Change-of-base symmetry used in the density-exponent calculation. -/
theorem rpow_logb_comm
    {r x y : ℝ}
    (hr0 : 0 < r) (hr1 : r ≠ 1)
    (hx0 : 0 < x) (hy0 : 0 < y) :
    x ^ Real.logb r y = y ^ Real.logb r x := by
  calc
    x ^ Real.logb r y
        = (r ^ Real.logb r x) ^ Real.logb r y := by
          rw [Real.rpow_logb hr0 hr1 hx0]
    _ = r ^ (Real.logb r x * Real.logb r y) := by
          rw [Real.rpow_mul hr0.le]
    _ = r ^ (Real.logb r y * Real.logb r x) := by rw [mul_comm]
    _ = (r ^ Real.logb r y) ^ Real.logb r x := by
          rw [Real.rpow_mul hr0.le]
    _ = y ^ Real.logb r x := by
          rw [Real.rpow_logb hr0 hr1 hy0]

/-- The terminal density after the fixed number of blocks retains a uniform
multiple of `alpha^beta`. -/
theorem fixedPower_density_lower
    {r transport alpha beta D0 : ℝ}
    (hr0 : 0 < r) (hr1 : r < 1)
    (ht0 : 0 < transport) (ht1 : transport < 1)
    (ha0 : 0 < alpha) (ha1 : alpha < 1)
    (hD0 : 0 < D0)
    (hbeta : Real.logb r transport < beta) :
    D0 * transport * alpha ^ beta ≤
      endpointD transport D0 (fixedPowerStageCount r alpha) := by
  let q := Real.logb r alpha
  let p := Real.logb r transport
  let R := fixedPowerStageCount r alpha
  have hq0 : 0 < q := by
    dsimp [q, Real.logb]
    exact div_pos_of_neg_of_neg (Real.log_neg ha0 ha1)
      (Real.log_neg hr0 hr1)
  have hRlt : (R : ℝ) < q + 1 := by
    dsimp [R, fixedPowerStageCount]
    exact Nat.ceil_lt_add_one hq0.le
  have htransportR :
      transport ^ (q + 1) ≤ transport ^ (R : ℝ) :=
    Real.rpow_le_rpow_of_exponent_ge ht0 ht1.le hRlt.le
  have hcomm : transport ^ q = alpha ^ p := by
    dsimp [q, p]
    exact rpow_logb_comm hr0 hr1.ne ht0 ha0
  have hbetaPow : alpha ^ beta ≤ alpha ^ p :=
    Real.rpow_le_rpow_of_exponent_ge ha0 ha1.le hbeta.le
  have hmain : transport * alpha ^ beta ≤ transport ^ (R : ℝ) := by
    calc
      transport * alpha ^ beta
          ≤ transport * alpha ^ p :=
        mul_le_mul_of_nonneg_left hbetaPow ht0.le
      _ = transport ^ (q + 1) := by
        rw [Real.rpow_add ht0, Real.rpow_one, hcomm]
        ring
      _ ≤ transport ^ (R : ℝ) := htransportR
  unfold endpointD
  rw [← Real.rpow_natCast]
  calc
    D0 * transport * alpha ^ beta
        = D0 * (transport * alpha ^ beta) := by ring
    _ ≤ D0 * transport ^ (R : ℝ) :=
      mul_le_mul_of_nonneg_left hmain hD0.le
    _ = transport ^ (R : ℝ) * D0 := by ring

/-- Fixed-parameter quantitative density theorem for every power target. -/
theorem endpointFixedPowerSet_dense_of_central_step
    {theta eta r transport D0 Dcut alpha beta : ℝ}
    (hra : a0 < r) (hr1 : r < 1)
    (ht0 : 0 < transport) (ht1 : transport < 1)
    (hstep : EndpointDensityStep (r - a0) transport
      (FixedTotal.centralRenyiStageConstant theta eta transport)
      Terras.quadraticWindowFixedGlobalConstant Dcut 6)
    (hD00 : 0 < D0) (hD01 : D0 ≤ 1) (hD0cut : D0 ≤ Dcut)
    (ha0 : 0 < alpha) (ha1 : alpha < 1)
    (hbeta : Real.logb r transport < beta) :
    IsCDDense
      (endpointFixedPowerSet alpha (endpointK ^ ((1 - r)⁻¹)))
      (endpointAbstractC
        (FixedTotal.centralRenyiStageConstant theta eta transport)
        Terras.quadraticWindowFixedGlobalConstant transport D0 6
        (fixedPowerStageCount r alpha))
      (D0 * transport * alpha ^ beta) := by
  let R := fixedPowerStageCount r alpha
  have hdense := endpointChain_dense_of_abstract_step hstep
    hD00 hD01 hD0cut R
  have hsubset := endpointChain_subset_fixed_power hra hr1
    (fixedPowerStageCount_contracts (a0_pos.trans hra) hr1 ha0)
  have hlarge := hdense.mono_set hsubset
  have hDlower := fixedPower_density_lower
    (a0_pos.trans hra) hr1 ht0 ht1 ha0 ha1 hD00 hbeta
  exact hlarge.degrade_exponent
    (mul_pos (mul_pos hD00 ht0) (Real.rpow_pos_of_pos ha0 beta))
    hDlower

/-- Reciprocal endpoint exponent governing fixed-power exceptional counts. -/
def fixedPowerDensityExponentLimit : ℝ :=
  Real.logb a0 (a0 / 2)

theorem fixedPowerDensityExponentLimit_eq :
    fixedPowerDensityExponentLimit =
      (centralRenyiEndpointHeadlineExponent)⁻¹ := by
  have ha0ne : a0 ≠ 0 := a0_pos.ne'
  have hlogne : Real.log a0 ≠ 0 :=
    (Real.log_neg a0_pos a0_lt_one).ne
  rw [centralRenyiEndpointHeadlineExponent_eq]
  unfold fixedPowerDensityExponentLimit Real.logb
  rw [Real.log_div ha0ne (by norm_num : (2 : ℝ) ≠ 0), one_div,
    Real.log_inv, Real.log_div (by norm_num : (2 : ℝ) ≠ 0) ha0ne]
  field_simp [hlogne]
  ring

theorem fixedPower_parameter_tendsto :
    Filter.Tendsto
      (fun n => Real.logb (linearChoiceQ n)
        (centralRenyiChoiceTransport n))
      Filter.atTop (nhds fixedPowerDensityExponentLimit) := by
  have hrlog := linearChoiceQ_tendsto.log a0_pos.ne'
  have htlog := centralRenyiChoiceTransport_tendsto.log
    (div_ne_zero a0_pos.ne' (by norm_num : (2 : ℝ) ≠ 0))
  have hlogne : Real.log a0 ≠ 0 :=
    (Real.log_neg a0_pos a0_lt_one).ne
  simpa [fixedPowerDensityExponentLimit, Real.logb] using
    htlog.div hrlog hlogne

/-- Every beta above the reciprocal headline endpoint admits one fixed set of
central-Renyi contraction and transport parameters. -/
theorem exists_fixedPower_parameters
    {beta : ℝ}
    (hbeta : fixedPowerDensityExponentLimit < beta) :
    ∃ theta r transport : ℝ,
      1 / 2 < theta ∧ theta < 1 ∧
      a0 < r ∧ r < 1 ∧
      0 < transport ∧
      transport < FixedTotal.centralRenyiAsymptoticRate theta ∧
      Real.logb r transport < beta := by
  have hevent := fixedPower_parameter_tendsto.eventually
    (Iio_mem_nhds hbeta)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hevent
  let theta := centralRenyiChoiceTheta N
  let r := linearChoiceQ N
  let transport := centralRenyiChoiceTransport N
  have htheta := centralRenyiChoiceTheta_properties N
  have hr := linearChoiceQ_properties N
  have ht := centralRenyiChoiceTransport_properties N
  exact ⟨theta, r, transport, htheta.1, htheta.2,
    hr.2.1, hr.2.2, ht.1, ht.2, hN N le_rfl⟩

/-- Formal version of the power-saving fixed-power corollary: the leading
power constant and density coefficient are uniform in `alpha`, while the
density prefactor may depend on `alpha`. -/
theorem centralRenyi_fixedPower_density
    {beta : ℝ}
    (hbeta : fixedPowerDensityExponentLimit < beta) :
    ∃ K c : ℝ,
      0 < K ∧ 0 < c ∧
      ∀ alpha : ℝ, 0 < alpha → alpha < 1 →
        ∃ C : ℝ, 0 < C ∧
          IsCDDense (endpointFixedPowerSet alpha K)
            C (c * alpha ^ beta) := by
  obtain ⟨theta, r, transport,
      hthetaHalf, htheta1, hra, hr1, ht0, htRate, hbetaParam⟩ :=
    exists_fixedPower_parameters hbeta
  obtain ⟨eta, Dcut, heta0, heta1, hDcut0, hDcut1, hstep⟩ :=
    exists_centralRenyiEndpointStep
      (by linarith [hthetaHalf]) htheta1 hra hr1 ht0 htRate
  let K := endpointK ^ ((1 - r)⁻¹)
  let c := Dcut * transport
  have hK0 : 0 < K := Real.rpow_pos_of_pos endpointK_pos _
  have hc0 : 0 < c := mul_pos hDcut0 ht0
  refine ⟨K, c, hK0, hc0, ?_⟩
  intro alpha ha0 ha1
  let C := endpointAbstractC
    (FixedTotal.centralRenyiStageConstant theta eta transport)
    Terras.quadraticWindowFixedGlobalConstant transport Dcut 6
    (fixedPowerStageCount r alpha)
  have ht1 : transport < 1 :=
    htRate.trans
      (centralRenyiAsymptoticRate_lt_a0
        (by linarith [hthetaHalf]) htheta1) |>.trans a0_lt_one
  have hdense := endpointFixedPowerSet_dense_of_central_step
    hra hr1 ht0 ht1 hstep hDcut0 hDcut1 le_rfl ha0 ha1 hbetaParam
  refine ⟨C, ?_, ?_⟩
  · exact endpointAbstractC_pos
      (FixedTotal.centralRenyiStageConstant_pos
        (by linarith [hthetaHalf]) htheta1 heta0 heta1 ht0 htRate)
      (Terras.initialWindowGood_dense_quadratic_fixed
        (sub_pos.mpr hra) (by linarith [a0_pos])).C_pos
      ht0 hDcut0 _
  · simpa [K, c, C] using hdense

end

end OptimizedLinearPullback

end CollatzEndpointTransport
