/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik
-/
import CollatzEndpointTransport.Linear.FixedTotalComposition

/-!
# Fixed Total Composition Recurrence

Two-child recursion for positive compositions.

For `0 < N`, every composition of `N + 1` is obtained uniquely either by
increasing the first part of a composition of `N`, or by prepending a part
equal to one.  The two branches give exact recurrences for the Syracuse
numerator and for `3 ^ length`.
-/

namespace CollatzEndpointTransport

namespace FixedTotal

open Nat Finset

noncomputable section

theorem composition_blocks_ne_nil
    {N : ℕ} (hN : 0 < N) (c : Composition N) :
    c.blocks ≠ [] := by
  intro hc
  have := c.blocks_sum
  simp [hc] at this
  omega

/-- Increase the first part of a positive composition. -/
def increaseFirst
    {N : ℕ} (hN : 0 < N) (c : Composition N) : Composition (N + 1) where
  blocks :=
    (c.blocks.head (composition_blocks_ne_nil hN c) + 1) :: c.blocks.tail
  blocks_pos := by
    intro i hi
    rcases List.mem_cons.mp hi with rfl | hi
    · omega
    · apply c.blocks_pos
      rw [← List.head_cons_tail c.blocks (composition_blocks_ne_nil hN c)]
      exact List.mem_cons_of_mem _ hi
  blocks_sum := by
    have hsplit :=
      congrArg List.sum
        (List.head_cons_tail c.blocks (composition_blocks_ne_nil hN c))
    simp only [List.sum_cons] at hsplit ⊢
    have hsum : c.blocks.sum = N := c.blocks_sum
    omega

/-- Prepend a part equal to one. -/
def prependOne
    {N : ℕ} (c : Composition N) : Composition (N + 1) where
  blocks := 1 :: c.blocks
  blocks_pos := by
    intro i hi
    rcases List.mem_cons.mp hi with rfl | hi
    · norm_num
    · exact c.blocks_pos hi
  blocks_sum := by
    simp only [List.sum_cons, c.blocks_sum]
    omega

/-- Remove a leading one from a composition of `N + 1`. -/
def removeLeadingOne
    {N : ℕ} (d : Composition (N + 1))
    (hd : d.blocks.head (composition_blocks_ne_nil (Nat.zero_lt_succ N) d) = 1) :
    Composition N where
  blocks := d.blocks.tail
  blocks_pos := by
    intro i hi
    apply d.blocks_pos
    rw [← List.head_cons_tail d.blocks
      (composition_blocks_ne_nil (Nat.zero_lt_succ N) d)]
    exact List.mem_cons_of_mem _ hi
  blocks_sum := by
    have hsplit :=
      congrArg List.sum
        (List.head_cons_tail d.blocks
          (composition_blocks_ne_nil (Nat.zero_lt_succ N) d))
    simp only [List.sum_cons] at hsplit
    rw [hd, d.blocks_sum] at hsplit
    omega

/-- Decrease a leading part greater than one. -/
def decreaseFirst
    {N : ℕ} (d : Composition (N + 1))
    (hd : d.blocks.head (composition_blocks_ne_nil (Nat.zero_lt_succ N) d) ≠ 1) :
    Composition N where
  blocks :=
    (d.blocks.head (composition_blocks_ne_nil (Nat.zero_lt_succ N) d) - 1) ::
      d.blocks.tail
  blocks_pos := by
    intro i hi
    rcases List.mem_cons.mp hi with rfl | hi
    · have hpos := d.blocks_pos
        (List.head_mem
          (composition_blocks_ne_nil (Nat.zero_lt_succ N) d))
      omega
    · apply d.blocks_pos
      rw [← List.head_cons_tail d.blocks
        (composition_blocks_ne_nil (Nat.zero_lt_succ N) d)]
      exact List.mem_cons_of_mem _ hi
  blocks_sum := by
    have hpos := d.blocks_pos
      (List.head_mem
        (composition_blocks_ne_nil (Nat.zero_lt_succ N) d))
    have hsplit :=
      congrArg List.sum
        (List.head_cons_tail d.blocks
          (composition_blocks_ne_nil (Nat.zero_lt_succ N) d))
    simp only [List.sum_cons] at hsplit ⊢
    have hsum : d.blocks.sum = N + 1 := d.blocks_sum
    omega

/-- The two canonical children enumerate every composition of `N + 1`. -/
def compositionSuccEquiv
    (N : ℕ) (hN : 0 < N) :
    Composition N ⊕ Composition N ≃ Composition (N + 1) where
  toFun
    | Sum.inl c => increaseFirst hN c
    | Sum.inr c => prependOne c
  invFun d :=
    if hd :
        d.blocks.head (composition_blocks_ne_nil (Nat.zero_lt_succ N) d) = 1
    then Sum.inr (removeLeadingOne d hd)
    else Sum.inl (decreaseFirst d hd)
  left_inv := by
    intro c
    cases c with
    | inl c =>
        have hcne := composition_blocks_ne_nil hN c
        have hheadpos : 0 <
            c.blocks.head (composition_blocks_ne_nil hN c) := by
          exact c.blocks_pos (List.head_mem hcne)
        simp only [increaseFirst, List.head_cons]
        split
        · rename_i hbad
          omega
        · rename_i hgood
          congr 1
          apply Composition.ext
          simp only [decreaseFirst, List.head_cons, List.tail_cons]
          rw [Nat.add_sub_cancel]
          exact List.head_cons_tail c.blocks hcne
    | inr c =>
        simp only [prependOne, List.head_cons]
        split
        · rename_i hgood
          congr 1
        · rename_i hbad
          simp at hbad
  right_inv := by
    intro d
    change
      (match
          (if hd :
              d.blocks.head
                  (composition_blocks_ne_nil (Nat.zero_lt_succ N) d) = 1
            then Sum.inr (removeLeadingOne d hd)
            else Sum.inl (decreaseFirst d hd)) with
        | Sum.inl c => increaseFirst hN c
        | Sum.inr c => prependOne c) = d
    by_cases hd :
        d.blocks.head
            (composition_blocks_ne_nil (Nat.zero_lt_succ N) d) = 1
    · simp only [hd, dite_true]
      change prependOne (removeLeadingOne d hd) = d
      apply Composition.ext
      change 1 :: d.blocks.tail = d.blocks
      calc
        1 :: d.blocks.tail =
            d.blocks.head
                (composition_blocks_ne_nil (Nat.zero_lt_succ N) d) ::
              d.blocks.tail := by
          congr 1
          exact hd.symm
        _ = d.blocks :=
          List.head_cons_tail d.blocks
            (composition_blocks_ne_nil (Nat.zero_lt_succ N) d)
    · simp only [hd, dite_false]
      change increaseFirst hN (decreaseFirst d hd) = d
      apply Composition.ext
      change
        (d.blocks.head
            (composition_blocks_ne_nil (Nat.zero_lt_succ N) d) - 1 + 1) ::
            d.blocks.tail = d.blocks
      have hpos := d.blocks_pos
        (List.head_mem
          (composition_blocks_ne_nil (Nat.zero_lt_succ N) d))
      rw [Nat.sub_add_cancel (by omega : 1 ≤
        d.blocks.head (composition_blocks_ne_nil (Nat.zero_lt_succ N) d))]
      exact List.head_cons_tail d.blocks
        (composition_blocks_ne_nil (Nat.zero_lt_succ N) d)

@[simp]
theorem increaseFirst_blocks
    {N : ℕ} (hN : 0 < N) (c : Composition N) :
    (increaseFirst hN c).blocks =
      (c.blocks.head (composition_blocks_ne_nil hN c) + 1) :: c.blocks.tail :=
  rfl

@[simp]
theorem prependOne_blocks
    {N : ℕ} (c : Composition N) :
    (prependOne c).blocks = 1 :: c.blocks :=
  rfl

theorem syracuseNumerator_increaseFirst
    {N : ℕ} (hN : 0 < N) (c : Composition N) :
    syracuseNumerator (increaseFirst hN c) + 3 ^ (c.length - 1) =
      2 * syracuseNumerator c := by
  have hcne := composition_blocks_ne_nil hN c
  cases hc : c.blocks with
  | nil => exact False.elim (hcne hc)
  | cons k ks =>
      have hlen : c.length - 1 = ks.length := by
        simp [Composition.length, hc]
      simp only [syracuseNumerator, increaseFirst, hc, List.head_cons,
        List.tail_cons, syracuseNumeratorList]
      rw [hlen]
      rw [pow_succ]
      ring

@[simp]
theorem syracuseNumerator_prependOne
    {N : ℕ} (c : Composition N) :
    syracuseNumerator (prependOne c) =
      3 ^ c.length + 2 * syracuseNumerator c := by
  simp [syracuseNumerator, prependOne, syracuseNumeratorList,
    Composition.length]

@[simp]
theorem increaseFirst_length
    {N : ℕ} (hN : 0 < N) (c : Composition N) :
    (increaseFirst hN c).length = c.length := by
  have hcne := composition_blocks_ne_nil hN c
  cases hc : c.blocks with
  | nil => exact False.elim (hcne hc)
  | cons k ks =>
      simp [Composition.length, increaseFirst, hc]

@[simp]
theorem prependOne_length
    {N : ℕ} (c : Composition N) :
    (prependOne c).length = c.length + 1 := by
  simp [Composition.length, prependOne]

end

end FixedTotal

end CollatzEndpointTransport
