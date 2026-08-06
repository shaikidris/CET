/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Data.Fintype.Card
import Mathlib.Logic.Equiv.Fin
import CollatzEndpointTransport.Common.TerrasAffineIterate

/-!
# Terras Maximal Barrier

Finite maximal-barrier counting for Boolean parity words.

The proof is a finite dynamic-programming version of the pruned-tree
cosh-potential argument. No probability space, martingale, or stopping-time
infrastructure is used.
-/

namespace CollatzEndpointTransport

namespace Terras

open scoped BigOperators

/-- A Boolean parity digit as a centered walk increment in `{-1,1}`. -/
def boolWalkStep (b : Bool) : ℤ :=
  if b then 1 else -1

@[simp]
theorem boolWalkStep_false : boolWalkStep false = -1 := rfl

@[simp]
theorem boolWalkStep_true : boolWalkStep true = 1 := rfl

/-- Whether a Boolean continuation hits the open absolute barrier `a`,
starting from the integer position `y`. The current position is included. -/
def hitsBarrierFrom (a : ℝ) :
    (r : ℕ) → ℤ → (Fin r → Bool) → Prop
  | 0, y, _ => a < |(y : ℝ)|
  | r + 1, y, v =>
      a < |(y : ℝ)| ∨
        hitsBarrierFrom a r (y + boolWalkStep (v 0)) (fun i => v i.succ)

/-- The exact number of `r`-bit continuations that hit the barrier. -/
noncomputable def barrierHitCount (a : ℝ) (r : ℕ) (y : ℤ) : ℕ := by
    classical
    exact (Finset.univ.filter (hitsBarrierFrom a r y)).card

theorem hitsBarrierFrom_of_bad
    {a : ℝ} {r : ℕ} {y : ℤ} (hy : a < |(y : ℝ)|)
    (v : Fin r → Bool) :
    hitsBarrierFrom a r y v := by
  cases r <;> simp [hitsBarrierFrom, hy]

theorem barrierHitCount_of_bad
    {a : ℝ} {r : ℕ} {y : ℤ} (hy : a < |(y : ℝ)|) :
    barrierHitCount a r y = 2 ^ r := by
  classical
  rw [barrierHitCount]
  have hfilter :
      Finset.univ.filter (hitsBarrierFrom a r y) = Finset.univ := by
    exact Finset.filter_eq_self.mpr (fun v _ => hitsBarrierFrom_of_bad hy v)
  rw [hfilter]
  simp

/-- On a safe current state, hitting over `r+1` steps is equivalent to
choosing the first bit and then hitting from the corresponding child. -/
noncomputable def safeHitSuccEquiv
    {a : ℝ} {r : ℕ} {y : ℤ} (hy : ¬a < |(y : ℝ)|) :
    {v : Fin (r + 1) → Bool // hitsBarrierFrom a (r + 1) y v} ≃
      Σ b : Bool,
        {w : Fin r → Bool //
          hitsBarrierFrom a r (y + boolWalkStep b) w} :=
  ((Equiv.piFinSucc r Bool).subtypeEquiv (fun v => by
      change
        hitsBarrierFrom a (r + 1) y v ↔
          hitsBarrierFrom a r (y + boolWalkStep (v 0))
            (fun i => v i.succ)
      simp [hitsBarrierFrom, hy])).trans
    (Equiv.subtypeProdEquivSigmaSubtype
      (fun b w => hitsBarrierFrom a r (y + boolWalkStep b) w))

theorem barrierHitCount_succ_of_safe
    {a : ℝ} {r : ℕ} {y : ℤ} (hy : ¬a < |(y : ℝ)|) :
    barrierHitCount a (r + 1) y =
      barrierHitCount a r (y - 1) + barrierHitCount a r (y + 1) := by
  classical
  have hc :
      Fintype.card
          {v : Fin (r + 1) → Bool // hitsBarrierFrom a (r + 1) y v} =
        Fintype.card
          (Σ b : Bool,
            {w : Fin r → Bool //
              hitsBarrierFrom a r (y + boolWalkStep b) w}) :=
    Fintype.card_congr (safeHitSuccEquiv (r := r) hy)
  simpa [barrierHitCount, Fintype.card_subtype, Fintype.card_sigma,
    Fintype.sum_bool, sub_eq_add_neg, add_comm] using hc

/-- The elementary hyperbolic identity used by the pruned-tree potential. -/
theorem cosh_int_children (θ : ℝ) (y : ℤ) :
    Real.cosh (θ * ((y - 1 : ℤ) : ℝ)) +
        Real.cosh (θ * ((y + 1 : ℤ) : ℝ)) =
      2 * Real.cosh (θ * (y : ℝ)) * Real.cosh θ := by
  rw [show θ * ((y - 1 : ℤ) : ℝ) = θ * (y : ℝ) - θ by push_cast; ring]
  rw [show θ * ((y + 1 : ℤ) : ℝ) = θ * (y : ℝ) + θ by push_cast; ring]
  rw [Real.cosh_sub, Real.cosh_add]
  ring

private theorem cosh_barrier_le_position
    {a θ : ℝ} {y : ℤ} (ha : 0 ≤ a) (hθ : 0 ≤ θ)
    (hy : a < |(y : ℝ)|) :
    Real.cosh (θ * a) ≤ Real.cosh (θ * (y : ℝ)) := by
  rw [Real.cosh_le_cosh]
  rw [abs_mul, abs_mul, abs_of_nonneg hθ, abs_of_nonneg ha]
  exact mul_le_mul_of_nonneg_left (le_of_lt hy) hθ

/-- Finite pruned-tree cosh potential. The left side counts exactly the
Boolean words that hit the barrier; no stopping-time probability space is
needed. -/
theorem barrierHitCount_mul_cosh_le
    (a θ : ℝ) (r : ℕ) (y : ℤ) (ha : 0 ≤ a) (hθ : 0 ≤ θ) :
    (barrierHitCount a r y : ℝ) * Real.cosh (θ * a) ≤
      (2 : ℝ) ^ r * Real.cosh (θ * (y : ℝ)) * Real.cosh θ ^ r := by
  induction r generalizing y with
  | zero =>
      by_cases hy : a < |(y : ℝ)|
      · rw [barrierHitCount_of_bad hy]
        simp only [pow_zero, Nat.cast_one, one_mul, mul_one]
        exact cosh_barrier_le_position ha hθ hy
      · simp [barrierHitCount, hitsBarrierFrom, hy, (Real.cosh_pos _).le]
  | succ r ihr =>
      by_cases hy : a < |(y : ℝ)|
      · rw [barrierHitCount_of_bad hy]
        have hcosh := cosh_barrier_le_position ha hθ hy
        have hpow : (1 : ℝ) ≤ Real.cosh θ ^ (r + 1) :=
          one_le_pow₀ (Real.one_le_cosh θ)
        have hcast :
            (((2 ^ (r + 1) : ℕ) : ℝ)) = (2 : ℝ) ^ (r + 1) := by
          norm_num
        calc
          ((2 ^ (r + 1) : ℕ) : ℝ) * Real.cosh (θ * a)
              ≤ (2 : ℝ) ^ (r + 1) * Real.cosh (θ * (y : ℝ)) := by
                rw [hcast]
                exact mul_le_mul_of_nonneg_left hcosh (by positivity)
          _ ≤ (2 : ℝ) ^ (r + 1) * Real.cosh (θ * (y : ℝ)) *
                Real.cosh θ ^ (r + 1) := by
              have hnonneg :
                  0 ≤ (2 : ℝ) ^ (r + 1) *
                    Real.cosh (θ * (y : ℝ)) := by positivity
              simpa only [mul_one] using
                mul_le_mul_of_nonneg_left hpow hnonneg
      · rw [barrierHitCount_succ_of_safe hy]
        push_cast
        have hminus := ihr (y := y - 1)
        have hplus := ihr (y := y + 1)
        calc
          ((barrierHitCount a r (y - 1) : ℝ) +
                (barrierHitCount a r (y + 1) : ℝ)) *
              Real.cosh (θ * a)
              =
              (barrierHitCount a r (y - 1) : ℝ) * Real.cosh (θ * a) +
                (barrierHitCount a r (y + 1) : ℝ) * Real.cosh (θ * a) := by
                  ring
          _ ≤
              (2 : ℝ) ^ r * Real.cosh (θ * ((y - 1 : ℤ) : ℝ)) *
                  Real.cosh θ ^ r +
                (2 : ℝ) ^ r * Real.cosh (θ * ((y + 1 : ℤ) : ℝ)) *
                  Real.cosh θ ^ r := add_le_add hminus hplus
          _ = (2 : ℝ) ^ (r + 1) * Real.cosh (θ * (y : ℝ)) *
                Real.cosh θ ^ (r + 1) := by
              calc
                _ = (2 : ℝ) ^ r *
                      (Real.cosh (θ * ((y - 1 : ℤ) : ℝ)) +
                        Real.cosh (θ * ((y + 1 : ℤ) : ℝ))) *
                      Real.cosh θ ^ r := by ring
                _ = (2 : ℝ) ^ r *
                      (2 * Real.cosh (θ * (y : ℝ)) * Real.cosh θ) *
                      Real.cosh θ ^ r := by rw [cosh_int_children]
                _ = _ := by rw [pow_succ, pow_succ]; ring

/-- Chernoff form of the maximal-barrier count. Optimizing with
`θ = a / r` gives the familiar `2^(r+1) exp (-a²/(2r))` estimate. -/
theorem barrierHitCount_le_chernoff
    (a θ : ℝ) (r : ℕ) (ha : 0 ≤ a) (hθ : 0 ≤ θ) :
    (barrierHitCount a r 0 : ℝ) ≤
      (2 : ℝ) ^ (r + 1) *
        Real.exp (((r : ℝ) * θ ^ 2 / 2) - θ * a) := by
  have hpot := barrierHitCount_mul_cosh_le a θ r 0 ha hθ
  have hlower :
      Real.exp (θ * a) / 2 ≤ Real.cosh (θ * a) := by
    rw [Real.cosh_eq]
    nlinarith [Real.exp_pos (-(θ * a))]
  have hleft :
      (barrierHitCount a r 0 : ℝ) * (Real.exp (θ * a) / 2) ≤
        (barrierHitCount a r 0 : ℝ) * Real.cosh (θ * a) :=
    mul_le_mul_of_nonneg_left hlower (by positivity)
  have hcoshpow :
      Real.cosh θ ^ r ≤ Real.exp ((r : ℝ) * (θ ^ 2 / 2)) := by
    calc
      Real.cosh θ ^ r ≤ Real.exp (θ ^ 2 / 2) ^ r :=
        pow_le_pow_left₀ (Real.cosh_pos θ).le
          (Real.cosh_le_exp_half_sq θ) r
      _ = Real.exp ((r : ℝ) * (θ ^ 2 / 2)) := by
        rw [← Real.exp_nat_mul]
  have hmain :
      (barrierHitCount a r 0 : ℝ) * (Real.exp (θ * a) / 2) ≤
        (2 : ℝ) ^ r * Real.exp ((r : ℝ) * (θ ^ 2 / 2)) := by
    calc
      _ ≤ (barrierHitCount a r 0 : ℝ) * Real.cosh (θ * a) := hleft
      _ ≤ (2 : ℝ) ^ r * Real.cosh (θ * (0 : ℝ)) *
          Real.cosh θ ^ r := by simpa only [Int.cast_zero] using hpot
      _ = (2 : ℝ) ^ r * Real.cosh θ ^ r := by norm_num
      _ ≤ (2 : ℝ) ^ r * Real.exp ((r : ℝ) * (θ ^ 2 / 2)) :=
        mul_le_mul_of_nonneg_left hcoshpow (by positivity)
  have hmul :
      (barrierHitCount a r 0 : ℝ) * Real.exp (θ * a) ≤
        2 * ((2 : ℝ) ^ r *
          Real.exp ((r : ℝ) * (θ ^ 2 / 2))) := by
    nlinarith
  have hdiv :
      (barrierHitCount a r 0 : ℝ) ≤
        (2 * ((2 : ℝ) ^ r *
          Real.exp ((r : ℝ) * (θ ^ 2 / 2)))) /
            Real.exp (θ * a) :=
    (le_div_iff₀ (Real.exp_pos (θ * a))).2 (by simpa [mul_comm] using hmul)
  calc
    (barrierHitCount a r 0 : ℝ)
        ≤ (2 * ((2 : ℝ) ^ r *
          Real.exp ((r : ℝ) * (θ ^ 2 / 2)))) /
            Real.exp (θ * a) := hdiv
    _ = (2 : ℝ) ^ (r + 1) *
          Real.exp (((r : ℝ) * θ ^ 2 / 2) - θ * a) := by
        rw [Real.exp_sub]
        ring

/-- The optimized two-sided maximal Boolean-walk estimate. -/
theorem barrierHitCount_le_exp
    (h : ℝ) (M : ℕ) (hh : 0 ≤ h) (hM : 0 < M) :
    (barrierHitCount (2 * h) M 0 : ℝ) ≤
      (2 : ℝ) ^ (M + 1) *
        Real.exp (-(2 * h ^ 2 / (M : ℝ))) := by
  have hMreal : 0 < (M : ℝ) := by exact_mod_cast hM
  have hchernoff :=
    barrierHitCount_le_chernoff (2 * h) (2 * h / (M : ℝ)) M
      (by positivity) (by positivity)
  convert hchernoff using 1 <;> field_simp <;> ring

theorem boolWalkStep_eq_indicator (b : Bool) :
    boolWalkStep b =
      2 * (if b then (1 : ℤ) else 0) - 1 := by
  cases b <;> norm_num

/-- Removing the first Collatz parity digit shifts the odd-count horizon. -/
theorem oddCount_succ_shift (H n : ℕ) :
    oddCount (H + 1) n =
      (if parityBit n then 1 else 0) + oddCount H (T n) := by
  calc
    oddCount (H + 1) n =
        ∑ i ∈ Finset.range (H + 1),
          if parityBit ((T^[i]) n) then 1 else 0 :=
      oddCount_eq_sum_range (H + 1) n
    _ = (if parityBit ((T^[0]) n) then 1 else 0) +
        ∑ i ∈ Finset.range H,
          if parityBit ((T^[i + 1]) n) then 1 else 0 := by
      rw [Finset.sum_range_succ']
      omega
    _ = (if parityBit n then 1 else 0) +
        ∑ i ∈ Finset.range H,
          if parityBit ((T^[i]) (T n)) then 1 else 0 := by
      simp only [Function.iterate_zero_apply, Function.iterate_succ_apply]
    _ = (if parityBit n then 1 else 0) + oddCount H (T n) := by
      rw [oddCount_eq_sum_range]

/-- The tail of the parity vector is the parity vector based at `T n`. -/
theorem parityVec_tail (r n : ℕ) :
    (fun i : Fin r => parityVec (r + 1) n i.succ) =
      parityVec r (T n) := by
  funext i
  change
    parityBit ((T^[((i : ℕ) + 1)]) n) =
      parityBit ((T^[(i : ℕ)]) (T n))
  rw [Function.iterate_succ_apply]

@[simp]
theorem oddCount_zero (n : ℕ) : oddCount 0 n = 0 := by
  simp [oddCount]

/-- A word that avoids the recursive barrier keeps every prefix position
inside it. For an actual Collatz parity word, the position is
`y + 2 * oddCount H n - H`. -/
theorem prefix_position_le_of_not_hitsBarrier :
    ∀ {r n : ℕ} {a : ℝ} {y : ℤ},
      ¬hitsBarrierFrom a r y (parityVec r n) →
      ∀ H : ℕ, H ≤ r →
        |(y : ℝ) + 2 * oddCount H n - H| ≤ a := by
  intro r
  induction r with
  | zero =>
      intro n a y hsafe H hHr
      have hy : ¬a < |(y : ℝ)| := by
        simpa [hitsBarrierFrom] using hsafe
      have hH : H = 0 := by omega
      subst H
      simpa using le_of_not_gt hy
  | succ r ihr =>
      intro n a y hsafe H hHr
      have hdecomp :
          ¬a < |(y : ℝ)| ∧
            ¬hitsBarrierFrom a r
              (y + boolWalkStep (parityBit n))
              (parityVec r (T n)) := by
        have hraw :
            ¬a < |(y : ℝ)| ∧
              ¬hitsBarrierFrom a r
                (y + boolWalkStep (parityVec (r + 1) n 0))
                (fun i => parityVec (r + 1) n i.succ) := by
          simpa [hitsBarrierFrom] using hsafe
        simpa [parityVec_tail, parityVec] using hraw
      rcases hdecomp with ⟨hy, htail⟩
      cases H with
      | zero =>
          simpa using le_of_not_gt hy
      | succ H =>
          have hHr' : H ≤ r := by omega
          have hchild := ihr htail H hHr'
          rw [oddCount_succ_shift]
          push_cast at hchild ⊢
          cases hb : parityBit n <;>
            simp [hb, boolWalkStep] at hchild ⊢ <;>
            convert hchild using 1 <;> ring

/-- Avoiding the walk barrier `2h` implies the two-sided odd-count barrier
`h` at every prefix. -/
theorem maximalParityRegular_of_not_hitsBarrier
    {M n : ℕ} {h : ℝ}
    (hgood : ¬hitsBarrierFrom (2 * h) M 0 (parityVec M n)) :
    ∀ H : ℕ, H ≤ M →
      |(oddCount H n : ℝ) - (H : ℝ) / 2| ≤ h := by
  intro H hHM
  have hp := prefix_position_le_of_not_hitsBarrier hgood H hHM
  have habs :
      |(2 : ℝ) * ((oddCount H n : ℝ) - (H : ℝ) / 2)| ≤ 2 * h := by
    convert hp using 1 <;> ring
  rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)] at habs
  nlinarith

end Terras

end CollatzEndpointTransport
