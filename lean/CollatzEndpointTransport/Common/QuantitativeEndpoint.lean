/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik
-/
import CollatzEndpointTransport.Common.QuantitativeEnvelope

/-!
# Quantitative Endpoint

The deterministic endpoint shared by the quantitative bootstrap routes.

The paper writes the final floor loss as `O(1 / M)`.  Here it is exposed as
the exact scalar budget

  M * (lambda + t) + b + 1 + t <= M * epsilon.

Under this hypothesis, membership in the terminal envelope supplies the
explicit iterate `envelopeHorizon lambda n` below `n ^ epsilon`.
-/

namespace CollatzEndpointTransport

namespace QuantitativeDensity

open scoped Real

noncomputable section

/-- The exact floor-sensitive upper bound at the terminal envelope horizon. -/
theorem terminal_envelope_upper_pow_two
    {n M : ℕ} {lambda t : ℝ}
    (hn : 0 < n)
    (hM : M = Nat.log 2 n)
    (ht : 0 ≤ t)
    (hgood : n ∈ EnvelopeGood lambda t) :
    (((Terras.T^[envelopeHorizon lambda n]) n : ℕ) : ℝ) ≤
      (2 : ℝ) ^
        ((M : ℝ) * (lambda + t) + bConst + 1 + t) := by
  let ell := envelopeHorizon lambda n
  have hellGood :
      (((Terras.T^[ell]) n : ℕ) : ℝ) ≤
        Terras.centralOrbitScale ell * (n : ℝ) ^ (1 + t) :=
    (mem_EnvelopeGood.mp hgood ell le_rfl).2
  have hb := bConst_pos
  have hbne : bConst ≠ 0 := ne_of_gt hb
  have hfloor :
      (1 - lambda) * (M : ℝ) / bConst - 1 ≤ (ell : ℝ) := by
    subst M
    dsimp only [ell, envelopeHorizon]
    exact le_of_lt (by
      have hlt := Nat.lt_floor_add_one
        ((1 - lambda) * (Nat.log 2 n : ℝ) / bConst)
      linarith)
  have hscaleExp :
      -bConst * (ell : ℝ) ≤
        -(1 - lambda) * (M : ℝ) + bConst := by
    have hmul :=
      mul_le_mul_of_nonpos_left hfloor (by linarith : -bConst ≤ 0)
    calc
      -bConst * (ell : ℝ)
          ≤ -bConst *
              ((1 - lambda) * (M : ℝ) / bConst - 1) := hmul
      _ = -(1 - lambda) * (M : ℝ) + bConst := by
        field_simp [hbne]
        ring
  have hscale :
      Terras.centralOrbitScale ell ≤
        (2 : ℝ) ^ (-(1 - lambda) * (M : ℝ) + bConst) := by
    rw [Terras.centralOrbitScale_eq_two_rpow_neg_b]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hscaleExp
  have hnUpperNat : n < 2 ^ (M + 1) := by
    subst M
    exact Nat.lt_pow_succ_log_self (by norm_num) n
  have hnUpper : (n : ℝ) ≤ (2 : ℝ) ^ (M + 1) := by
    exact_mod_cast hnUpperNat.le
  have htExp : 0 ≤ 1 + t := by linarith
  have hnPow :
      (n : ℝ) ^ (1 + t) ≤
        ((2 : ℝ) ^ (M + 1)) ^ (1 + t) :=
    Real.rpow_le_rpow (by exact_mod_cast hn.le) hnUpper htExp
  have hbound :
      (((Terras.T^[ell]) n : ℕ) : ℝ) ≤
        (2 : ℝ) ^
          ((M : ℝ) * (lambda + t) + bConst + 1 + t) := by
    calc
      (((Terras.T^[ell]) n : ℕ) : ℝ)
          ≤ Terras.centralOrbitScale ell * (n : ℝ) ^ (1 + t) :=
        hellGood
      _ ≤ (2 : ℝ) ^ (-(1 - lambda) * (M : ℝ) + bConst) *
            ((2 : ℝ) ^ (M + 1)) ^ (1 + t) :=
        mul_le_mul hscale hnPow
          (Real.rpow_nonneg (Nat.cast_nonneg n) _)
          (Real.rpow_nonneg (by norm_num) _)
      _ = (2 : ℝ) ^
            ((M : ℝ) * (lambda + t) + bConst + 1 + t) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num),
          ← Real.rpow_add (by norm_num)]
        congr 1
        push_cast
        ring
  simpa only [ell] using hbound

/-- **Endpoint descent at the explicit terminal horizon.**

This form exposes the witness used by the bounded-time corollary. -/
theorem iterate_at_horizon_le_rpow_of_mem_terminal_envelope
    {n M : ℕ} {lambda t eps : ℝ}
    (hn : 0 < n)
    (hM : M = Nat.log 2 n)
    (ht : 0 ≤ t)
    (heps : 0 ≤ eps)
    (hbudget :
      (M : ℝ) * (lambda + t) + bConst + 1 + t ≤
        (M : ℝ) * eps)
    (hgood : n ∈ EnvelopeGood lambda t) :
    (((Terras.T^[envelopeHorizon lambda n]) n : ℕ) : ℝ) ≤
      (n : ℝ) ^ eps := by
  have hterminal :=
    terminal_envelope_upper_pow_two hn hM ht hgood
  have hnLowerNat : 2 ^ M ≤ n := by
    subst M
    exact Nat.pow_log_le_self 2 hn.ne'
  have hnLower : (2 : ℝ) ^ M ≤ (n : ℝ) := by
    exact_mod_cast hnLowerNat
  have hpowBudget :
      (2 : ℝ) ^
          ((M : ℝ) * (lambda + t) + bConst + 1 + t) ≤
        (2 : ℝ) ^ ((M : ℝ) * eps) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) hbudget
  have hnEps :
      (2 : ℝ) ^ ((M : ℝ) * eps) ≤ (n : ℝ) ^ eps := by
    calc
      (2 : ℝ) ^ ((M : ℝ) * eps)
          = ((2 : ℝ) ^ M) ^ eps := by
              rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
      _ ≤ (n : ℝ) ^ eps :=
        Real.rpow_le_rpow (by positivity) hnLower heps
  exact hterminal.trans (hpowBudget.trans hnEps)

/-- **Endpoint descent.**

The witness is the terminal envelope horizon itself. No orbit minimum needs
to be introduced as a separate object. -/
theorem exists_iterate_le_rpow_of_mem_terminal_envelope
    {n M : ℕ} {lambda t eps : ℝ}
    (hn : 0 < n)
    (hM : M = Nat.log 2 n)
    (ht : 0 ≤ t)
    (heps : 0 ≤ eps)
    (hbudget :
      (M : ℝ) * (lambda + t) + bConst + 1 + t ≤
        (M : ℝ) * eps)
    (hgood : n ∈ EnvelopeGood lambda t) :
    ∃ k : ℕ, (((Terras.T^[k]) n : ℕ) : ℝ) ≤ (n : ℝ) ^ eps :=
  ⟨envelopeHorizon lambda n,
    iterate_at_horizon_le_rpow_of_mem_terminal_envelope
      hn hM ht heps hbudget hgood⟩

/-- The terminal horizon never exceeds the full drift horizon `log₂(n) / b`
when `lambda` is a genuine remaining-window proportion. -/
theorem envelopeHorizon_le_log_div_b
    {n : ℕ} {lambda : ℝ}
    (hlambda0 : 0 ≤ lambda) (hlambda1 : lambda ≤ 1) :
    (envelopeHorizon lambda n : ℝ) ≤
      (Nat.log 2 n : ℝ) / bConst := by
  have hb := bConst_pos
  have harg0 :
      0 ≤
        (1 - lambda) * (Nat.log 2 n : ℝ) / bConst :=
    div_nonneg
      (mul_nonneg (sub_nonneg.mpr hlambda1) (Nat.cast_nonneg _))
      hb.le
  have hfloor :
      (envelopeHorizon lambda n : ℝ) ≤
        (1 - lambda) * (Nat.log 2 n : ℝ) / bConst := by
    unfold envelopeHorizon
    exact Nat.floor_le harg0
  calc
    (envelopeHorizon lambda n : ℝ)
        ≤ (1 - lambda) * (Nat.log 2 n : ℝ) / bConst := hfloor
    _ ≤ (Nat.log 2 n : ℝ) / bConst := by
      apply div_le_div_of_nonneg_right _ hb.le
      have hM0 : 0 ≤ (Nat.log 2 n : ℝ) := Nat.cast_nonneg _
      nlinarith

/-- In natural-log units, the explicit terminal witness occurs by
`log(n) / (b * log 2)`. -/
theorem envelopeHorizon_le_natural_log_time
    {n : ℕ} {lambda : ℝ}
    (hn : 0 < n)
    (hlambda0 : 0 ≤ lambda) (hlambda1 : lambda ≤ 1) :
    (envelopeHorizon lambda n : ℝ) ≤
      Real.log n / (bConst * Real.log 2) := by
  have hb := bConst_pos
  have hlog2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have hpowNat : 2 ^ Nat.log 2 n ≤ n :=
    Nat.pow_log_le_self 2 hn.ne'
  have hpow :
      (2 : ℝ) ^ Nat.log 2 n ≤ (n : ℝ) := by
    exact_mod_cast hpowNat
  have hnR0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hlog :
      (Nat.log 2 n : ℝ) * Real.log 2 ≤ Real.log n := by
    have h :=
      Real.strictMonoOn_log.monotoneOn
        (Set.mem_Ioi.mpr (by positivity : 0 < (2 : ℝ) ^ Nat.log 2 n))
        (Set.mem_Ioi.mpr hnR0)
        hpow
    rw [Real.log_pow] at h
    simpa [mul_comm] using h
  calc
    (envelopeHorizon lambda n : ℝ)
        ≤ (Nat.log 2 n : ℝ) / bConst :=
      envelopeHorizon_le_log_div_b hlambda0 hlambda1
    _ = ((Nat.log 2 n : ℝ) * Real.log 2) /
        (bConst * Real.log 2) := by
      field_simp [ne_of_gt hb, ne_of_gt hlog2]
      ring
    _ ≤ Real.log n / (bConst * Real.log 2) :=
      div_le_div_of_nonneg_right hlog
        (mul_nonneg hb.le hlog2.le)

/-- A certified rational upper bound for the natural-log horizon constant.

The proof is kernel-checked from a finite exponential-series majorant; no
floating-point evaluation enters the theorem. -/
theorem inv_bConst_mul_log_two_lt_6953 :
    1 / (bConst * Real.log 2) < (6953 / 1000 : ℝ) := by
  have hlog :
      (2000 / 6953 : ℝ) < Real.log (4 / 3) := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 4 / 3)]
    have h :=
      Real.exp_bound'
        (x := (2000 / 6953 : ℝ))
        (by norm_num) (by norm_num)
        (n := 8) (by norm_num)
    calc
      Real.exp (2000 / 6953 : ℝ)
          ≤ (∑ m ∈ Finset.range 8,
              (2000 / 6953 : ℝ) ^ m / m.factorial) +
            (2000 / 6953 : ℝ) ^ 8 * (8 + 1) /
              (Nat.factorial 8 * 8) := h
      _ < 4 / 3 := by
        norm_num [Finset.sum_range_succ, Nat.factorial]
  have hbIdentity :
      2 * (bConst * Real.log 2) = Real.log (4 / 3) := by
    have hlog2ne : Real.log 2 ≠ 0 :=
      ne_of_gt (Real.log_pos (by norm_num))
    unfold bConst a0 lg3 Real.logb
    rw [Real.log_div (by norm_num : (4 : ℝ) ≠ 0)
      (by norm_num : (3 : ℝ) ≠ 0)]
    have hlog4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
      calc
        Real.log (4 : ℝ) = Real.log ((2 : ℝ) ^ 2) := by norm_num
        _ = 2 * Real.log 2 := by rw [Real.log_pow]; norm_num
    rw [hlog4]
    field_simp [hlog2ne]
    ring
  have hbLower :
      (1000 / 6953 : ℝ) < bConst * Real.log 2 := by
    nlinarith
  have hbPos : 0 < bConst * Real.log 2 :=
    mul_pos bConst_pos (Real.log_pos (by norm_num))
  rw [div_lt_iff₀ hbPos]
  calc
    1 = (6953 / 1000 : ℝ) * (1000 / 6953 : ℝ) := by norm_num
    _ < (6953 / 1000 : ℝ) * (bConst * Real.log 2) :=
      mul_lt_mul_of_pos_left hbLower (by norm_num)

/-- The explicit terminal witness occurs strictly before `6.953 log n`
whenever `n > 1`. -/
theorem envelopeHorizon_lt_6953_log
    {n : ℕ} {lambda : ℝ}
    (hn : 1 < n)
    (hlambda0 : 0 ≤ lambda) (hlambda1 : lambda ≤ 1) :
    (envelopeHorizon lambda n : ℝ) <
      (6953 / 1000 : ℝ) * Real.log n := by
  have htime :=
    envelopeHorizon_le_natural_log_time
      (Nat.zero_lt_of_lt hn) hlambda0 hlambda1
  have hlogn : 0 < Real.log n :=
    Real.log_pos (by exact_mod_cast hn)
  calc
    (envelopeHorizon lambda n : ℝ)
        ≤ Real.log n / (bConst * Real.log 2) := htime
    _ = (1 / (bConst * Real.log 2)) * Real.log n := by ring
    _ < (6953 / 1000 : ℝ) * Real.log n :=
      mul_lt_mul_of_pos_right inv_bConst_mul_log_two_lt_6953 hlogn

end

end QuantitativeDensity

end CollatzEndpointTransport
