/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik
-/
import CollatzEndpointTransport.Linear.EndpointOnlyCore
import CollatzEndpointTransport.Common.TerrasOrbitMinimum

/-!
# Endpoint Only Orbit

Deterministic orbit consequences of the endpoint-only chain.

Membership in `endpointChain t R` supplies `R` consecutive logarithmic
blocks whose endpoints contract by one fixed exponent `r = a0 + t`.
-/

namespace CollatzEndpointTransport

namespace OptimizedLinearPullback

open scoped Real BigOperators

noncomputable section

open QuantitativeDensity

/-- The fixed multiplicative cost caused by the upper edge of one dyadic
shell. -/
def endpointK : ℝ :=
  (2 : ℝ) ^ bConst

theorem endpointK_pos :
    0 < endpointK := by
  unfold endpointK
  positivity

theorem endpointK_one_le :
    1 ≤ endpointK := by
  unfold endpointK
  exact Real.one_le_rpow (by norm_num) bConst_pos.le

/-- One-block contraction extracted from the upper initial-window envelope. -/
theorem endpointBlock_le_rpow_of_mem_initialWindow
    {n : ℕ} {r : ℝ}
    (hn : 0 < n)
    (hra : a0 < r) (hr1 : r < 1)
    (hgood : n ∈ Terras.initialWindowGood (r - a0)) :
    (endpointBlock n : ℝ) ≤ endpointK * (n : ℝ) ^ r := by
  let M := Nat.log 2 n
  have ht0 : 0 < r - a0 := sub_pos.mpr hra
  have ht1 : r - a0 ≤ 1 := by
    linarith [a0_pos]
  have hupper :
      (endpointBlock n : ℝ) ≤
        Terras.centralOrbitScale M *
          (n : ℝ) ^ (1 + (r - a0)) := by
    simpa [endpointBlock, M] using
      (hgood M (by simp [M])).2
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hnUpperNat : n < 2 ^ (M + 1) := by
    dsimp [M]
    exact Nat.lt_pow_succ_log_self (by norm_num) n
  have hnUpper :
      (n : ℝ) ≤ (2 : ℝ) ^ (M + 1) := by
    exact_mod_cast hnUpperNat.le
  have hb0 : 0 < bConst := bConst_pos
  have hpow :
      (n : ℝ) ^ bConst ≤
        ((2 : ℝ) ^ (M + 1)) ^ bConst :=
    Real.rpow_le_rpow hnR.le hnUpper hb0.le
  have hscale :
      Terras.centralOrbitScale M * (n : ℝ) ^ bConst ≤
        endpointK := by
    rw [Terras.centralOrbitScale_eq_two_rpow_neg_b]
    calc
      (2 : ℝ) ^ (-bConst * (M : ℝ)) * (n : ℝ) ^ bConst
          ≤ (2 : ℝ) ^ (-bConst * (M : ℝ)) *
              ((2 : ℝ) ^ (M + 1)) ^ bConst :=
        mul_le_mul_of_nonneg_left hpow (by positivity)
      _ = (2 : ℝ) ^ bConst := by
        rw [← Real.rpow_natCast,
          ← Real.rpow_mul (by norm_num),
          ← Real.rpow_add (by norm_num)]
        congr 1
        push_cast
        ring
      _ = endpointK := rfl
  have hexp :
      1 + (r - a0) = bConst + r := by
    unfold bConst
    ring
  calc
    (endpointBlock n : ℝ)
        ≤ Terras.centralOrbitScale M *
            (n : ℝ) ^ (1 + (r - a0)) := hupper
    _ = (Terras.centralOrbitScale M * (n : ℝ) ^ bConst) *
          (n : ℝ) ^ r := by
      rw [hexp, Real.rpow_add hnR]
      ring
    _ ≤ endpointK * (n : ℝ) ^ r :=
      mul_le_mul_of_nonneg_right hscale
        (Real.rpow_nonneg hnR.le r)

theorem endpointBlock_pos_of_mem_initialWindow
    {n : ℕ} {t : ℝ}
    (hn : 0 < n)
    (hgood : n ∈ Terras.initialWindowGood t) :
    0 < endpointBlock n := by
  let M := Nat.log 2 n
  have hlower :=
    (hgood M (by simp [M])).1
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hlower0 :
      0 <
        Terras.centralOrbitScale M *
          (n : ℝ) ^ (1 - t) :=
    mul_pos (Terras.centralOrbitScale_pos M)
      (Real.rpow_pos_of_pos hnR _)
  have hcast : (0 : ℝ) < endpointBlock n :=
    hlower0.trans_le (by simpa [endpointBlock, M] using hlower)
  exact_mod_cast hcast

/-- Logarithmic form of the fixed one-block contraction. -/
theorem log_endpointBlock_le
    {n : ℕ} {r : ℝ}
    (hn : 0 < n)
    (hra : a0 < r) (hr1 : r < 1)
    (hgood : n ∈ Terras.initialWindowGood (r - a0)) :
    Real.log (endpointBlock n) ≤
      r * Real.log n + Real.log endpointK := by
  have hbound :=
    endpointBlock_le_rpow_of_mem_initialWindow hn hra hr1 hgood
  have hblock0 :=
    endpointBlock_pos_of_mem_initialWindow hn hgood
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hpow0 : 0 < (n : ℝ) ^ r :=
    Real.rpow_pos_of_pos hnR _
  have hright0 : 0 < endpointK * (n : ℝ) ^ r :=
    mul_pos endpointK_pos hpow0
  have hlog :=
    Real.strictMonoOn_log.monotoneOn
      (Set.mem_Ioi.mpr (by exact_mod_cast hblock0 : (0 : ℝ) < endpointBlock n))
      (Set.mem_Ioi.mpr hright0)
      hbound
  rw [Real.log_mul endpointK_pos.ne' hpow0.ne',
    Real.log_rpow hnR] at hlog
  linarith

/-- Repeated endpoint map, oriented to match the recursive chain. -/
def endpointIter : ℕ → ℕ → ℕ
  | 0, n => n
  | R + 1, n => endpointIter R (endpointBlock n)

/-- Total number of half-Collatz steps consumed by `R` endpoint blocks. -/
def endpointTime : ℕ → ℕ → ℕ
  | 0, _ => 0
  | R + 1, n => Nat.log 2 n + endpointTime R (endpointBlock n)

@[simp]
theorem endpointIter_zero (n : ℕ) :
    endpointIter 0 n = n :=
  rfl

@[simp]
theorem endpointIter_succ (R n : ℕ) :
    endpointIter (R + 1) n =
      endpointIter R (endpointBlock n) :=
  rfl

@[simp]
theorem endpointTime_zero (n : ℕ) :
    endpointTime 0 n = 0 :=
  rfl

@[simp]
theorem endpointTime_succ (R n : ℕ) :
    endpointTime (R + 1) n =
      Nat.log 2 n + endpointTime R (endpointBlock n) :=
  rfl

/-- The repeated endpoint is an actual iterate of the original map. -/
theorem endpointIter_eq_iterate_endpointTime :
    ∀ R n,
      endpointIter R n =
        (Terras.T^[endpointTime R n]) n := by
  intro R
  induction R with
  | zero =>
      intro n
      simp
  | succ R ih =>
      intro n
      rw [endpointIter_succ, ih, endpointTime_succ]
      unfold endpointBlock
      rw [show
          Nat.log 2 n + endpointTime R ((Terras.T^[Nat.log 2 n]) n) =
            endpointTime R ((Terras.T^[Nat.log 2 n]) n) +
              Nat.log 2 n by omega,
        Function.iterate_add_apply]

/-- Geometric sum appearing in the logarithmic endpoint bound. -/
def endpointGeom (r : ℝ) (R : ℕ) : ℝ :=
  ∑ i ∈ Finset.range R, r ^ i

@[simp]
theorem endpointGeom_zero (r : ℝ) :
    endpointGeom r 0 = 0 := by
  simp [endpointGeom]

theorem endpointGeom_succ (r : ℝ) (R : ℕ) :
    endpointGeom r (R + 1) =
      endpointGeom r R + r ^ R := by
  simp [endpointGeom, Finset.sum_range_succ]

theorem endpointGeom_succ_head (r : ℝ) (R : ℕ) :
    endpointGeom r (R + 1) = 1 + r * endpointGeom r R := by
  induction R with
  | zero => simp [endpointGeom]
  | succ R ih =>
      calc
        endpointGeom r (R + 1 + 1) =
            endpointGeom r (R + 1) + r ^ (R + 1) :=
          endpointGeom_succ r (R + 1)
        _ = (1 + r * endpointGeom r R) + r ^ (R + 1) := by rw [ih]
        _ = 1 + r * endpointGeom r (R + 1) := by
          rw [endpointGeom_succ, pow_succ]
          ring

/-- Exact logarithmic contraction after every supported endpoint block. -/
theorem log_endpointIter_le
    {n R : ℕ} {r : ℝ}
    (hn : 0 < n)
    (hra : a0 < r) (hr1 : r < 1)
    (hchain : n ∈ endpointChain (r - a0) R) :
    Real.log (endpointIter R n) ≤
      r ^ R * Real.log n +
        Real.log endpointK * endpointGeom r R := by
  induction R generalizing n with
  | zero =>
      simp
  | succ R ih =>
      rcases (mem_endpointChain_succ.mp hchain) with
        ⟨hwindow, hrest⟩
      have hn1 :
          0 < endpointBlock n :=
        endpointBlock_pos_of_mem_initialWindow hn hwindow
      have hih := ih hn1 hrest
      have hone :=
        log_endpointBlock_le hn hra hr1 hwindow
      have hr0 : 0 ≤ r :=
        a0_pos.le.trans hra.le
      rw [endpointIter_succ]
      calc
        Real.log (endpointIter R (endpointBlock n))
            ≤ r ^ R * Real.log (endpointBlock n) +
                Real.log endpointK * endpointGeom r R := hih
        _ ≤ r ^ R *
                (r * Real.log n + Real.log endpointK) +
              Real.log endpointK * endpointGeom r R := by
          exact add_le_add_right
            (mul_le_mul_of_nonneg_left hone (pow_nonneg hr0 R)) _
        _ = r ^ (R + 1) * Real.log n +
              Real.log endpointK * endpointGeom r (R + 1) := by
          rw [pow_succ, endpointGeom_succ]
          ring

theorem endpointGeom_le_inv_one_sub
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    ∀ R, endpointGeom r R ≤ (1 - r)⁻¹ := by
  intro R
  have hsum :
      endpointGeom r R * (1 - r) = 1 - r ^ R := by
    induction R with
    | zero =>
        simp
    | succ R ih =>
        rw [endpointGeom_succ, add_mul, ih, pow_succ]
        ring
  have hden0 : 0 < 1 - r := sub_pos.mpr hr1
  have hpow0 : 0 ≤ r ^ R := pow_nonneg hr0 R
  have hquot : endpointGeom r R ≤ 1 / (1 - r) := by
    apply (le_div_iff₀ hden0).2
    rw [hsum]
    linarith
  simpa [one_div] using hquot

theorem log_endpointK :
    Real.log endpointK = bConst * Real.log 2 := by
  unfold endpointK
  rw [Real.log_rpow (by norm_num : (0 : ℝ) < 2)]

/-- Exact accounting for the total number of half-Collatz steps used by an
endpoint chain.  The first term is the geometric block-length sum; the
second is the accumulated fixed shell cost. -/
theorem endpointTime_mul_log_two_le
    {n R : ℕ} {r : ℝ}
    (hn : 0 < n)
    (hra : a0 < r) (hr1 : r < 1)
    (hchain : n ∈ endpointChain (r - a0) R) :
    (endpointTime R n : ℝ) * Real.log 2 ≤
      endpointGeom r R * Real.log n +
        (R : ℝ) * Real.log endpointK * (1 - r)⁻¹ := by
  induction R generalizing n with
  | zero =>
      simp
  | succ R ih =>
      rcases (mem_endpointChain_succ.mp hchain) with
        ⟨hwindow, hrest⟩
      have hn1 : 0 < endpointBlock n :=
        endpointBlock_pos_of_mem_initialWindow hn hwindow
      have hih := ih hn1 hrest
      have hone := log_endpointBlock_le hn hra hr1 hwindow
      have hlog2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
      have hpowNat : 2 ^ Nat.log 2 n ≤ n :=
        Nat.pow_log_le_self 2 hn.ne'
      have hpow :
          (2 : ℝ) ^ Nat.log 2 n ≤ (n : ℝ) := by
        exact_mod_cast hpowNat
      have hnR0 : (0 : ℝ) < n := by exact_mod_cast hn
      have hlogN :
          (Nat.log 2 n : ℝ) * Real.log 2 ≤ Real.log n := by
        have h :=
          Real.strictMonoOn_log.monotoneOn
            (Set.mem_Ioi.mpr
              (by positivity : 0 < (2 : ℝ) ^ Nat.log 2 n))
            (Set.mem_Ioi.mpr hnR0) hpow
        rw [Real.log_pow] at h
        simpa [mul_comm] using h
      have hr0 : 0 ≤ r := a0_pos.le.trans hra.le
      have hgeom0 : 0 ≤ endpointGeom r R := by
        unfold endpointGeom
        positivity
      have hgeom := endpointGeom_le_inv_one_sub hr0 hr1 R
      have hlogK0 : 0 ≤ Real.log endpointK := by
        rw [log_endpointK]
        exact mul_nonneg bConst_pos.le hlog2.le
      rw [endpointTime_succ]
      push_cast
      calc
        ((Nat.log 2 n : ℝ) + endpointTime R (endpointBlock n)) *
              Real.log 2
            = (Nat.log 2 n : ℝ) * Real.log 2 +
                (endpointTime R (endpointBlock n) : ℝ) * Real.log 2 := by
              ring
        _ ≤ Real.log n +
              (endpointGeom r R * Real.log (endpointBlock n) +
                (R : ℝ) * Real.log endpointK * (1 - r)⁻¹) :=
          add_le_add hlogN hih
        _ ≤ Real.log n +
              (endpointGeom r R *
                  (r * Real.log n + Real.log endpointK) +
                (R : ℝ) * Real.log endpointK * (1 - r)⁻¹) := by
          gcongr
        _ ≤ endpointGeom r (R + 1) * Real.log n +
              ((R : ℝ) + 1) * Real.log endpointK * (1 - r)⁻¹ := by
          have hden0 : 0 < 1 - r := sub_pos.mpr hr1
          have hgeomIdentity :
              1 + endpointGeom r R * r = endpointGeom r (R + 1) := by
            rw [endpointGeom_succ_head]
            ring
          calc
            Real.log n +
                  (endpointGeom r R *
                      (r * Real.log n + Real.log endpointK) +
                    (R : ℝ) * Real.log endpointK * (1 - r)⁻¹)
                = (1 + endpointGeom r R * r) * Real.log n +
                    endpointGeom r R * Real.log endpointK +
                    (R : ℝ) * Real.log endpointK * (1 - r)⁻¹ := by
                  ring
            _ ≤ endpointGeom r (R + 1) * Real.log n +
                    (1 - r)⁻¹ * Real.log endpointK +
                    (R : ℝ) * Real.log endpointK * (1 - r)⁻¹ := by
                  rw [hgeomIdentity]
                  gcongr
            _ = endpointGeom r (R + 1) * Real.log n +
                    ((R : ℝ) + 1) * Real.log endpointK * (1 - r)⁻¹ := by
                  field_simp [hden0.ne']
                  ring

/-- Convenient natural-log form of the endpoint-chain time bound. -/
theorem endpointTime_le
    {n R : ℕ} {r : ℝ}
    (hn : 0 < n)
    (hra : a0 < r) (hr1 : r < 1)
    (hchain : n ∈ endpointChain (r - a0) R) :
    (endpointTime R n : ℝ) ≤
      (1 - r)⁻¹ / Real.log 2 * Real.log n +
        (R : ℝ) * bConst * (1 - r)⁻¹ := by
  have hraw := endpointTime_mul_log_two_le hn hra hr1 hchain
  have hr0 : 0 ≤ r := a0_pos.le.trans hra.le
  have hgeom := endpointGeom_le_inv_one_sub hr0 hr1 R
  have hlogn0 : 0 ≤ Real.log n :=
    Real.log_nonneg (by exact_mod_cast hn)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hden : 0 < 1 - r := sub_pos.mpr hr1
  have hupper :
      (endpointTime R n : ℝ) * Real.log 2 ≤
        (1 - r)⁻¹ * Real.log n +
          (R : ℝ) * (bConst * Real.log 2) * (1 - r)⁻¹ := by
    rw [← log_endpointK]
    exact hraw.trans
      (add_le_add_right
        (mul_le_mul_of_nonneg_right hgeom hlogn0) _)
  rw [show
      (1 - r)⁻¹ / Real.log 2 * Real.log n +
            (R : ℝ) * bConst * (1 - r)⁻¹ =
        ((1 - r)⁻¹ * Real.log n +
            (R : ℝ) * (bConst * Real.log 2) * (1 - r)⁻¹) /
          Real.log 2 by
    field_simp [hlog2.ne', hden.ne']
    ring]
  exact (le_div_iff₀ hlog2).2 hupper

/-- Every iterate before the endpoint-chain witness stays below a fixed
power ceiling.  The deliberately coarse factor `endpointK ^ (2 * R)` is
polynomial in the shell index on the logarithmic schedule and is therefore
absorbed by any fixed exponent margin above `r - a0`. -/
theorem iterate_le_endpointChain_ceiling :
    ∀ {R n j : ℕ} {r : ℝ},
      0 < n →
      a0 < r → r < 1 →
      n ∈ endpointChain (r - a0) R →
      j ≤ endpointTime R n →
      (((Terras.T^[j]) n : ℕ) : ℝ) ≤
        endpointK ^ (2 * R) * (n : ℝ) ^ (1 + (r - a0)) := by
  intro R
  induction R with
  | zero =>
      intro n j r hn hra hr1 hchain hj
      have hj0 : j = 0 := by simpa using hj
      subst j
      change (n : ℝ) ≤ endpointK ^ (0 : ℕ) *
        (n : ℝ) ^ (1 + (r - a0))
      rw [pow_zero, one_mul]
      have hnOne : (1 : ℝ) ≤ n := by exact_mod_cast hn
      calc
        (n : ℝ) = (n : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
        _ ≤ (n : ℝ) ^ (1 + (r - a0)) :=
          Real.rpow_le_rpow_of_exponent_le hnOne (by linarith)
  | succ R ih =>
      intro n j r hn hra hr1 hchain hj
      rcases (mem_endpointChain_succ.mp hchain) with ⟨hwindow, hrest⟩
      let M := Nat.log 2 n
      let n₁ := endpointBlock n
      have ht0 : 0 < r - a0 := sub_pos.mpr hra
      have ht1 : r - a0 ≤ 1 := by linarith [a0_pos]
      have he0 : 0 ≤ 1 + (r - a0) := by linarith
      have he2 : 1 + (r - a0) ≤ 2 := by linarith
      have hnOne : (1 : ℝ) ≤ n := by exact_mod_cast hn
      have hKpow :
          (1 : ℝ) ≤ endpointK ^ (2 * (R + 1)) :=
        one_le_pow₀ endpointK_one_le
      by_cases hjM : j ≤ M
      · have hupper := (hwindow j (by simpa [M] using hjM)).2
        have hscale : Terras.centralOrbitScale j ≤ 1 := by
          rw [Terras.centralOrbitScale_eq]
          apply pow_le_one₀ (by positivity)
          have hsqrt : Real.sqrt 3 < 2 := by
            nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
          linarith
        calc
          (((Terras.T^[j]) n : ℕ) : ℝ)
              ≤ Terras.centralOrbitScale j *
                  (n : ℝ) ^ (1 + (r - a0)) := by
                simpa using hupper
          _ ≤ 1 * (n : ℝ) ^ (1 + (r - a0)) :=
            mul_le_mul_of_nonneg_right hscale
              (Real.rpow_nonneg (Nat.cast_nonneg n) _)
          _ ≤ endpointK ^ (2 * (R + 1)) *
                (n : ℝ) ^ (1 + (r - a0)) :=
            mul_le_mul_of_nonneg_right hKpow
              (Real.rpow_nonneg (Nat.cast_nonneg n) _)
      · have hMj : M < j := Nat.lt_of_not_ge hjM
        let j' := j - M
        have hjEq : j = j' + M := by
          dsimp [j']
          omega
        have hjTail : j' ≤ endpointTime R n₁ := by
          rw [endpointTime_succ] at hj
          dsimp [M, n₁]
          omega
        have hn₁ : 0 < n₁ :=
          endpointBlock_pos_of_mem_initialWindow hn hwindow
        have hih := ih hn₁ hra hr1 hrest hjTail
        have hblock :=
          endpointBlock_le_rpow_of_mem_initialWindow hn hra hr1 hwindow
        have hblockPow :
            (n₁ : ℝ) ^ (1 + (r - a0)) ≤
              (endpointK * (n : ℝ) ^ r) ^ (1 + (r - a0)) := by
          exact Real.rpow_le_rpow (Nat.cast_nonneg n₁) hblock he0
        have hKexp :
            endpointK ^ (1 + (r - a0)) ≤ endpointK ^ (2 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le endpointK_one_le he2
        have hnExp :
            (n : ℝ) ^ (r * (1 + (r - a0))) ≤
              (n : ℝ) ^ (1 + (r - a0)) := by
          apply Real.rpow_le_rpow_of_exponent_le hnOne
          nlinarith [a0_pos]
        have htail :
            (((Terras.T^[j']) n₁ : ℕ) : ℝ) ≤
              endpointK ^ (2 * (R + 1)) *
                (n : ℝ) ^ (1 + (r - a0)) := by
          calc
            (((Terras.T^[j']) n₁ : ℕ) : ℝ)
                ≤ endpointK ^ (2 * R) *
                    (n₁ : ℝ) ^ (1 + (r - a0)) := hih
            _ ≤ endpointK ^ (2 * R) *
                    (endpointK * (n : ℝ) ^ r) ^
                      (1 + (r - a0)) :=
              mul_le_mul_of_nonneg_left hblockPow
                (pow_nonneg endpointK_pos.le (2 * R))
            _ = endpointK ^ (2 * R) *
                    (endpointK ^ (1 + (r - a0)) *
                      (n : ℝ) ^ (r * (1 + (r - a0)))) := by
              rw [Real.mul_rpow endpointK_pos.le
                    (Real.rpow_nonneg (Nat.cast_nonneg n) r),
                Real.rpow_mul (Nat.cast_nonneg n)]
            _ ≤ endpointK ^ (2 * R) *
                    (endpointK ^ (2 : ℝ) *
                      (n : ℝ) ^ (1 + (r - a0))) := by
              apply mul_le_mul_of_nonneg_left
              · exact mul_le_mul hKexp hnExp
                  (Real.rpow_nonneg (Nat.cast_nonneg n) _)
                  (Real.rpow_nonneg endpointK_pos.le _)
              · exact pow_nonneg endpointK_pos.le _
            _ = endpointK ^ (2 * (R + 1)) *
                    (n : ℝ) ^ (1 + (r - a0)) := by
              rw [Real.rpow_two]
              calc
                endpointK ^ (2 * R) *
                      (endpointK ^ 2 *
                        (n : ℝ) ^ (1 + (r - a0))) =
                    (endpointK ^ (2 * R) * endpointK ^ 2) *
                      (n : ℝ) ^ (1 + (r - a0)) := by ring
                _ = endpointK ^ (2 * R + 2) *
                      (n : ℝ) ^ (1 + (r - a0)) := by rw [← pow_add]
                _ = endpointK ^ (2 * (R + 1)) *
                      (n : ℝ) ^ (1 + (r - a0)) := by
                  congr 2
        rw [hjEq, Function.iterate_add_apply]
        simpa [n₁, endpointBlock, M] using htail

/-- A chain endpoint is a witnessed value of the Collatz orbit minimum. -/
theorem Tmin_le_endpointIter (n R : ℕ) :
    Terras.Tmin n ≤ endpointIter R n := by
  rw [endpointIter_eq_iterate_endpointTime]
  exact Terras.Tmin_le_iterate n (endpointTime R n)

end

end OptimizedLinearPullback

end CollatzEndpointTransport
