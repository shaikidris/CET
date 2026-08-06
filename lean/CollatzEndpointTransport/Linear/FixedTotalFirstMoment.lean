/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik
-/
import CollatzEndpointTransport.Linear.FixedTotalCompositionRecurrence

/-!
# Fixed Total First Moment

Exact first moment of the fixed-total Syracuse numerator.

The two-child composition recursion gives

  ∑_{c ⊧ N} 3 ^ length(c) = 3 * 4 ^ (N - 1)

and

  2 * ∑_{c ⊧ N} A(c) = (N + 1) * 4 ^ (N - 1).

Consequently the uniform fixed-total variable
`(3 ^ length(c) + A(c)) / 2 ^ N` has exact mean `(N + 7) / 4`.
-/

namespace CollatzEndpointTransport

namespace FixedTotal

open Nat Finset

noncomputable section

/-- Sum of `3 ^ length` over all positive compositions of `N`. -/
def lengthPowSum (N : ℕ) : ℕ :=
  ∑ c : Composition N, 3 ^ c.length

/-- Sum of the Syracuse numerator over all positive compositions of `N`. -/
def numeratorSum (N : ℕ) : ℕ :=
  ∑ c : Composition N, syracuseNumerator c

theorem composition_one_blocks (c : Composition 1) :
    c.blocks = [1] := by
  have hlenPos := c.length_pos_of_pos (by norm_num)
  have hlenLe := c.length_le
  have hlen : c.length = 1 := by omega
  cases hc : c.blocks with
  | nil =>
      have := c.blocks_sum
      simp [hc] at this
  | cons k ks =>
      have hks : ks = [] := by
        have : (k :: ks).length = 1 := by
          simpa [Composition.length, hc] using hlen
        simp only [List.length_cons] at this
        exact List.length_eq_zero.mp (Nat.succ.inj this)
      subst ks
      have hsum := c.blocks_sum
      simp [hc] at hsum
      subst k
      rfl

theorem lengthPowSum_one :
    lengthPowSum 1 = 3 := by
  rw [lengthPowSum]
  calc
    (∑ c : Composition 1, 3 ^ c.length) =
        ∑ _c : Composition 1, 3 := by
      apply Fintype.sum_congr
      intro c
      have hlenPos := c.length_pos_of_pos (by norm_num)
      have hlenLe := c.length_le
      have : c.length = 1 := by omega
      simp [this]
    _ = 3 := by simp [composition_card]

theorem numeratorSum_one :
    numeratorSum 1 = 1 := by
  rw [numeratorSum]
  calc
    (∑ c : Composition 1, syracuseNumerator c) =
        ∑ _c : Composition 1, 1 := by
      apply Fintype.sum_congr
      intro c
      simp [syracuseNumerator, composition_one_blocks c,
        syracuseNumeratorList]
    _ = 1 := by simp [composition_card]

theorem lengthPowSum_succ
    (N : ℕ) (hN : 0 < N) :
    lengthPowSum (N + 1) = 4 * lengthPowSum N := by
  let e := compositionSuccEquiv N hN
  have he :=
    (Equiv.sum_comp e (fun c : Composition (N + 1) => 3 ^ c.length)).symm
  rw [Fintype.sum_sum_type] at he
  dsimp [e, compositionSuccEquiv] at he
  change lengthPowSum (N + 1) = _ at he
  rw [he]
  simp only [increaseFirst_length, prependOne_length, pow_succ]
  rw [← Finset.sum_mul]
  change lengthPowSum N + lengthPowSum N * 3 = 4 * lengthPowSum N
  omega

theorem lengthPowSum_formula
    (N : ℕ) (hN : 0 < N) :
    lengthPowSum N = 3 * 4 ^ (N - 1) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hN)
  induction k with
  | zero =>
      simpa using lengthPowSum_one
  | succ k ih =>
      rw [lengthPowSum_succ (k + 1) (by omega), ih (by omega)]
      simp only [Nat.succ_eq_add_one, Nat.add_sub_cancel]
      rw [pow_succ]
      ring

theorem lowerLengthPowSum_formula
    (N : ℕ) (hN : 0 < N) :
    (∑ c : Composition N, 3 ^ (c.length - 1)) = 4 ^ (N - 1) := by
  have hpoint :
      ∀ c : Composition N,
        3 * 3 ^ (c.length - 1) = 3 ^ c.length := by
    intro c
    have hlen := c.length_pos_of_pos hN
    obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hlen)
    rw [hj]
    simp [pow_succ, mul_comm]
  have hsum :
      3 * (∑ c : Composition N, 3 ^ (c.length - 1)) =
        lengthPowSum N := by
    rw [Finset.mul_sum]
    apply Fintype.sum_congr
    exact hpoint
  rw [lengthPowSum_formula N hN] at hsum
  exact Nat.eq_of_mul_eq_mul_left (by norm_num) hsum

theorem child_numerator_sum
    {N : ℕ} (hN : 0 < N) (c : Composition N) :
    syracuseNumerator (increaseFirst hN c) +
        syracuseNumerator (prependOne c) =
      4 * syracuseNumerator c + 2 * 3 ^ (c.length - 1) := by
  have hinc := syracuseNumerator_increaseFirst hN c
  have hpre := syracuseNumerator_prependOne c
  have hlen := c.length_pos_of_pos hN
  have hpow : 3 ^ c.length = 3 * 3 ^ (c.length - 1) := by
    obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hlen)
    rw [hj]
    simp [pow_succ, mul_comm]
  omega

theorem numeratorSum_succ
    (N : ℕ) (hN : 0 < N) :
    numeratorSum (N + 1) =
      4 * numeratorSum N + 2 * 4 ^ (N - 1) := by
  let e := compositionSuccEquiv N hN
  have he :=
    (Equiv.sum_comp e
      (fun c : Composition (N + 1) => syracuseNumerator c)).symm
  rw [Fintype.sum_sum_type] at he
  dsimp [e, compositionSuccEquiv] at he
  change numeratorSum (N + 1) = _ at he
  rw [he]
  have hchildren :
      (∑ c : Composition N, syracuseNumerator (increaseFirst hN c)) +
          ∑ c : Composition N, syracuseNumerator (prependOne c) =
        ∑ c : Composition N,
          (4 * syracuseNumerator c + 2 * 3 ^ (c.length - 1)) := by
    rw [← Finset.sum_add_distrib]
    apply Fintype.sum_congr
    exact child_numerator_sum hN
  rw [hchildren, Finset.sum_add_distrib]
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  change
    4 * numeratorSum N +
        2 * (∑ c : Composition N, 3 ^ (c.length - 1)) =
      4 * numeratorSum N + 2 * 4 ^ (N - 1)
  rw [lowerLengthPowSum_formula N hN]

theorem numeratorSum_formula
    (N : ℕ) (hN : 0 < N) :
    2 * numeratorSum N = (N + 1) * 4 ^ (N - 1) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hN)
  induction k with
  | zero =>
      simp [numeratorSum_one]
  | succ k ih =>
      rw [numeratorSum_succ (k + 1) (by omega)]
      have ih' := ih (by omega)
      simp only [Nat.succ_eq_add_one, Nat.add_sub_cancel] at ih' ⊢
      rw [pow_succ]
      calc
        2 * (4 * numeratorSum (k + 1) + 2 * 4 ^ k) =
            4 * (2 * numeratorSum (k + 1)) + 4 * 4 ^ k := by ring
        _ = 4 * ((k + 2) * 4 ^ k) + 4 * 4 ^ k := by rw [ih']
        _ = (k + 3) * (4 ^ k * 4) := by ring

/-- Exact aggregate first-moment identity. -/
theorem fixedTotal_firstMoment_exact
    (N : ℕ) (hN : 0 < N) :
    2 * (∑ c : Composition N,
        (3 ^ c.length + syracuseNumerator c)) =
      (N + 7) * 4 ^ (N - 1) := by
  rw [Finset.sum_add_distrib, Nat.mul_add]
  have hlen := lengthPowSum_formula N hN
  have hnum := numeratorSum_formula N hN
  change
    2 * lengthPowSum N + 2 * numeratorSum N =
      (N + 7) * 4 ^ (N - 1)
  rw [hlen, hnum]
  ring

end

end FixedTotal

end CollatzEndpointTransport
