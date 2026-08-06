/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik
-/
import CollatzEndpointTransport.Linear.EndpointOnlyAsymptotic
import CollatzEndpointTransport.Linear.OptimizedLinearDescentAssembly

/-!
# Endpoint Only Budget

Endpoint budget for the logarithmic-block recursion.

The scheduled endpoint estimate has the form

  log (F^R(n)) <= (M + 4)^(-u) log n + log(K) / (1-r).

For `delta < u`, both terms fit eventually below

  ((M + 4) / 4)^(1-delta),

which in turn is at most `(log n)^(1-delta)` on the `M`-th dyadic
shell.  This is the deterministic bridge from endpoint contraction to the
coefficient-one stretched-logarithmic orbit bound.
-/

namespace CollatzEndpointTransport

namespace OptimizedLinearPullback

open scoped Real Topology

noncomputable section

open QuantitativeDensity

/-- Uniform contribution of the geometric one-block constants. -/
def endpointOrbitCost (r : ℝ) : ℝ :=
  Real.log endpointK * (1 - r)⁻¹

/-- Shellwise endpoint budget used by the endpoint-only assembly. -/
def endpointOrbitBudget
    (r omega delta : ℝ) (M : ℕ) : Prop :=
  powerShellScale M ^ (1 - endpointOrbitPower r omega) +
      endpointOrbitCost r ≤
    (powerShellScale M / 4) ^ (1 - delta)

theorem log_endpointK_eq :
    Real.log endpointK = bConst * Real.log 2 := by
  unfold endpointK
  rw [Real.log_rpow (by norm_num)]

theorem endpointOrbitCost_nonneg
    {r : ℝ} (hr1 : r < 1) :
    0 ≤ endpointOrbitCost r := by
  unfold endpointOrbitCost
  have hlogK : 0 < Real.log endpointK := by
    rw [log_endpointK_eq]
    exact mul_pos bConst_pos (Real.log_pos (by norm_num))
  exact mul_nonneg hlogK.le (inv_nonneg.mpr (sub_nonneg.mpr hr1.le))

/-- The endpoint budget becomes valid on all sufficiently large shells. -/
theorem endpointOrbitBudget_eventually
    {r omega delta : ℝ}
    (hr0 : 0 < r) (hr1 : r < 1)
    (homega : 0 < omega)
    (hdeltaU : delta < endpointOrbitPower r omega)
    (hdelta1 : delta < 1) :
    ∀ᶠ M : ℕ in Filter.atTop,
      endpointOrbitBudget r omega delta M := by
  let u := endpointOrbitPower r omega
  let e := 1 - delta
  let L := endpointOrbitCost r
  have hgap : 0 < u - delta := by
    dsimp [u]
    linarith
  have he0 : 0 < e := by
    dsimp [e]
    linarith
  have hfirst :
      Filter.Tendsto
        (fun M =>
          (4 : ℝ) ^ e *
            powerShellScale M ^ (-(u - delta)))
        Filter.atTop (nhds 0) := by
    simpa [Function.comp_apply] using
      ((tendsto_rpow_neg_atTop hgap).comp
        powerShellScale_tendsto_atTop).const_mul ((4 : ℝ) ^ e)
  have hsecond :
      Filter.Tendsto
        (fun M =>
          (L * (4 : ℝ) ^ e) *
            powerShellScale M ^ (-e))
        Filter.atTop (nhds 0) := by
    simpa [Function.comp_apply] using
      ((tendsto_rpow_neg_atTop he0).comp
        powerShellScale_tendsto_atTop).const_mul
          (L * (4 : ℝ) ^ e)
  have hsum := hfirst.add hsecond
  have hone :
      ∀ᶠ M : ℕ in Filter.atTop,
        (4 : ℝ) ^ e *
              powerShellScale M ^ (-(u - delta)) +
            (L * (4 : ℝ) ^ e) *
              powerShellScale M ^ (-e) < 1 := by
    have hdist :=
      (Metric.tendsto_atTop.1 hsum) 1 zero_lt_one
    filter_upwards [Filter.eventually_atTop.2 hdist] with M hM
    rw [Real.dist_eq] at hM
    exact lt_of_le_of_lt (le_abs_self _) (by simpa [sub_zero] using hM)
  filter_upwards [hone] with M hM
  have hX0 : 0 < powerShellScale M := powerShellScale_pos M
  have hfour0 : (0 : ℝ) < 4 := by norm_num
  have hden0 :
      0 < (powerShellScale M / 4) ^ e :=
    Real.rpow_pos_of_pos (div_pos hX0 hfour0) _
  unfold endpointOrbitBudget
  dsimp [u, e, L] at hM ⊢
  apply (div_le_one hden0).mp
  calc
    (powerShellScale M ^
          (1 - endpointOrbitPower r omega) +
        endpointOrbitCost r) /
        (powerShellScale M / 4) ^ (1 - delta)
        =
      (4 : ℝ) ^ (1 - delta) *
          powerShellScale M ^
            (-(endpointOrbitPower r omega - delta)) +
        (endpointOrbitCost r * (4 : ℝ) ^ (1 - delta)) *
          powerShellScale M ^ (-(1 - delta)) := by
      have hpow1 :
          powerShellScale M ^
                (delta - endpointOrbitPower r omega) *
              powerShellScale M ^ (1 - delta) =
            powerShellScale M ^
              (1 - endpointOrbitPower r omega) := by
        rw [← Real.rpow_add hX0]
        congr 1
        ring
      have hpow2 :
          powerShellScale M ^ (delta - 1) *
              powerShellScale M ^ (1 - delta) = 1 := by
        rw [← Real.rpow_add hX0]
        convert Real.rpow_zero (powerShellScale M) using 1 <;> ring
      rw [Real.div_rpow hX0.le (by norm_num : (0 : ℝ) ≤ 4)]
      field_simp
      calc
        (powerShellScale M ^ (1 - endpointOrbitPower r omega) +
              endpointOrbitCost r) *
              4 ^ (1 - delta)
            =
          4 ^ (1 - delta) *
              powerShellScale M ^
                (1 - endpointOrbitPower r omega) +
            endpointOrbitCost r * 4 ^ (1 - delta) := by ring
        _ =
          4 ^ (1 - delta) *
                (powerShellScale M ^
                    (delta - endpointOrbitPower r omega) *
                  powerShellScale M ^ (1 - delta)) +
            endpointOrbitCost r * 4 ^ (1 - delta) *
                (powerShellScale M ^ (delta - 1) *
                  powerShellScale M ^ (1 - delta)) := by
          rw [hpow1, hpow2]
          ring
        _ =
          (4 ^ (1 - delta) *
                powerShellScale M ^
                  (delta - endpointOrbitPower r omega) +
              endpointOrbitCost r * 4 ^ (1 - delta) *
                powerShellScale M ^ (delta - 1)) *
            powerShellScale M ^ (1 - delta) := by ring
    _ ≤ 1 := hM.le

/-- On a dyadic shell, one quarter of the shifted shell index is below the
natural logarithm of every shell element. -/
theorem quarter_powerShellScale_le_log
    {n M : ℕ}
    (hM : M = Nat.log 2 n) (hM4 : 4 ≤ M) :
    powerShellScale M / 4 ≤ Real.log n := by
  have hn0 : 0 < n := by
    by_contra hn
    have hnz : n = 0 := Nat.eq_zero_of_not_pos hn
    subst n
    simp at hM
    omega
  have hnLowerNat : 2 ^ M ≤ n := by
    subst M
    exact Nat.pow_log_le_self 2 hn0.ne'
  have hnLower : (2 : ℝ) ^ M ≤ n := by
    exact_mod_cast hnLowerNat
  have hlogLower :
      (M : ℝ) * Real.log 2 ≤ Real.log n := by
    have h :=
      Real.strictMonoOn_log.monotoneOn
        (Set.mem_Ioi.mpr (by positivity : (0 : ℝ) < (2 : ℝ) ^ M))
        (Set.mem_Ioi.mpr (by exact_mod_cast hn0 : (0 : ℝ) < n))
        hnLower
    simpa [Real.log_pow] using h
  have hlog2 : (1 / 2 : ℝ) < Real.log 2 :=
    Real.log_two_gt_d9.trans' (by norm_num)
  have hM4R : (4 : ℝ) ≤ M := by exact_mod_cast hM4
  have hshift :
      powerShellScale M / 4 ≤ (M : ℝ) * Real.log 2 := by
    unfold powerShellScale
    nlinarith
  exact hshift.trans hlogLower

/-- The scheduled endpoint itself satisfies the coefficient-one
stretched-logarithmic bound once the shell budget is active. -/
theorem endpointIter_schedule_le_stretchedLog
    {n M : ℕ} {r omega delta : ℝ}
    (hn : 0 < n)
    (hM : M = Nat.log 2 n) (hM4 : 4 ≤ M)
    (hra : a0 < r) (hr1 : r < 1)
    (homega : 0 < omega)
    (hdelta1 : delta < 1)
    (hbudget : endpointOrbitBudget r omega delta M)
    (hchain :
      n ∈ endpointChain (r - a0) (endpointStageCount omega M)) :
    (endpointIter (endpointStageCount omega M) n : ℝ) ≤
      Real.exp ((Real.log n) ^ (1 - delta)) := by
  have hlog :=
    log_endpointIter_schedule_le hn hM hra hr1 rfl homega hchain
  have hlogn :=
    log_le_powerShellScale hM hM4
  have hr0 : 0 ≤ r := (a0_pos.trans hra).le
  have hgeom :=
    endpointGeom_le_inv_one_sub hr0 hr1 (endpointStageCount omega M)
  have hlogK0 : 0 ≤ Real.log endpointK := by
    rw [log_endpointK_eq]
    exact mul_nonneg bConst_pos.le
      (Real.log_pos (by norm_num)).le
  have hcost :
      Real.log endpointK *
          endpointGeom r (endpointStageCount omega M) ≤
        endpointOrbitCost r := by
    unfold endpointOrbitCost
    exact mul_le_mul_of_nonneg_left hgeom hlogK0
  have hcontract :
      powerShellScale M ^ (-endpointOrbitPower r omega) *
          Real.log n ≤
        powerShellScale M ^ (1 - endpointOrbitPower r omega) := by
    have hmul :
        powerShellScale M ^ (-endpointOrbitPower r omega) *
              Real.log n ≤
            powerShellScale M ^ (-endpointOrbitPower r omega) *
              powerShellScale M :=
      mul_le_mul_of_nonneg_left hlogn.2
        (Real.rpow_nonneg (powerShellScale_pos M).le
          (-endpointOrbitPower r omega))
    calc
      powerShellScale M ^ (-endpointOrbitPower r omega) *
            Real.log n
          ≤
        powerShellScale M ^ (-endpointOrbitPower r omega) *
          powerShellScale M := hmul
      _ =
        powerShellScale M ^ (1 - endpointOrbitPower r omega) := by
        calc
          powerShellScale M ^ (-endpointOrbitPower r omega) *
                powerShellScale M
              =
            powerShellScale M ^ (-endpointOrbitPower r omega) *
              powerShellScale M ^ (1 : ℝ) := by rw [Real.rpow_one]
          _ =
            powerShellScale M ^
              (-endpointOrbitPower r omega + 1) :=
                (Real.rpow_add (powerShellScale_pos M) _ _).symm
          _ = _ := by congr 1 <;> ring
  have hbase :=
    quarter_powerShellScale_le_log hM hM4
  have hexp0 : 0 < 1 - delta := sub_pos.mpr hdelta1
  have hrpow :
      (powerShellScale M / 4) ^ (1 - delta) ≤
        (Real.log n) ^ (1 - delta) :=
    Real.rpow_le_rpow
      (div_pos (powerShellScale_pos M) (by norm_num)).le
      hbase hexp0.le
  have hlogFinal :
      Real.log (endpointIter (endpointStageCount omega M) n) ≤
        (Real.log n) ^ (1 - delta) := by
    exact hlog.trans
      ((add_le_add hcontract hcost).trans
        (hbudget.trans hrpow))
  have hiter0 :
      0 < endpointIter (endpointStageCount omega M) n := by
    have hchainPos :
        ∀ R n,
          0 < n →
          n ∈ endpointChain (r - a0) R →
          0 < endpointIter R n := by
      intro R
      induction R with
      | zero =>
          intro n hn hchain
          simpa using hn
      | succ R ih =>
          intro n hn hchain
          rcases (mem_endpointChain_succ.mp hchain) with
            ⟨hwindow, hrest⟩
          exact ih (endpointBlock n)
            (endpointBlock_pos_of_mem_initialWindow hn hwindow)
            hrest
    exact hchainPos _ n hn hchain
  rw [← Real.exp_log (by exact_mod_cast hiter0 : (0 : ℝ) <
    endpointIter (endpointStageCount omega M) n)]
  exact Real.exp_le_exp.2 hlogFinal

end

end OptimizedLinearPullback

end CollatzEndpointTransport
