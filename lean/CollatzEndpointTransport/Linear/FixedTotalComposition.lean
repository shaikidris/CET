/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik
-/
import Mathlib.Combinatorics.Enumerative.Composition
import Mathlib.NumberTheory.Padics.PadicVal.Basic

/-!
# Fixed Total Composition

Finite positive-composition layer for the optimized linear pullback.

For a positive composition `k = (k₁, ..., kₛ)`, the Syracuse numerator is

  A(k) = 3^(s-1) + 2^k₁ A(k₂, ..., kₛ).

This file proves the integer-lift injectivity used by the fixed-total argument.
The proof extracts the first
part from the exact 2-adic valuation of the recursive remainder; the final
part is recovered from the fixed total.
-/

namespace CollatzEndpointTransport

namespace FixedTotal

open Nat

/-- Recursive Syracuse numerator of a list of valuation parts. -/
def syracuseNumeratorList : List ℕ → ℕ
  | [] => 0
  | k :: ks =>
      3 ^ ks.length + 2 ^ k * syracuseNumeratorList ks

@[simp]
theorem syracuseNumeratorList_nil :
    syracuseNumeratorList [] = 0 := rfl

@[simp]
theorem syracuseNumeratorList_cons (k : ℕ) (ks : List ℕ) :
    syracuseNumeratorList (k :: ks) =
      3 ^ ks.length + 2 ^ k * syracuseNumeratorList ks := rfl

/-- The recursive numerator is positive on every nonempty list. -/
theorem syracuseNumeratorList_pos (k : ℕ) (ks : List ℕ) :
    0 < syracuseNumeratorList (k :: ks) := by
  simp only [syracuseNumeratorList_cons]
  positivity

/-- A nonempty positive valuation list has odd Syracuse numerator. -/
theorem syracuseNumeratorList_mod_two
    {k : ℕ} (hk : 0 < k) (ks : List ℕ) :
    syracuseNumeratorList (k :: ks) % 2 = 1 := by
  rw [syracuseNumeratorList_cons, Nat.add_mod, Nat.mul_mod]
  have hthree : ∀ n : ℕ, 3 ^ n % 2 = 1 := by
    intro n
    induction n with
    | zero => norm_num
    | succ n ih =>
        rw [pow_succ, Nat.mul_mod, ih]
  have hpow : 2 ^ k % 2 = 0 := by
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
    rw [pow_succ, Nat.mul_mod]
    norm_num
  rw [hthree, hpow]
  simp

/-- Equality of `2^a` times odd numbers determines the exponent. -/
theorem eq_exponent_of_pow_two_mul_eq
    {a b x y : ℕ}
    (hx : x % 2 = 1) (hy : y % 2 = 1)
    (h : 2 ^ a * x = 2 ^ b * y) :
    a = b := by
  have hx0 : x ≠ 0 := by
    intro hzero
    simp [hzero] at hx
  have hy0 : y ≠ 0 := by
    intro hzero
    simp [hzero] at hy
  have hxdvd : ¬2 ∣ x := by
    rw [Nat.dvd_iff_mod_eq_zero]
    omega
  have hydvd : ¬2 ∣ y := by
    rw [Nat.dvd_iff_mod_eq_zero]
    omega
  have hvx : padicValNat 2 x = 0 :=
    padicValNat.eq_zero_of_not_dvd hxdvd
  have hvy : padicValNat 2 y = 0 :=
    padicValNat.eq_zero_of_not_dvd hydvd
  have hv := congrArg (padicValNat 2) h
  rw [padicValNat.mul (pow_ne_zero _ (by norm_num)) hx0,
    padicValNat.mul (pow_ne_zero _ (by norm_num)) hy0,
    padicValNat.prime_pow, padicValNat.prime_pow, hvx, hvy,
    add_zero, add_zero] at hv
  exact hv

/-- Integer-lift injectivity for positive lists of fixed length and total. -/
theorem syracuseNumeratorList_injective_of_length_sum
    (s : ℕ) :
    ∀ {ks ls : List ℕ},
      ks.length = s →
      ls.length = s →
      (∀ k ∈ ks, 0 < k) →
      (∀ l ∈ ls, 0 < l) →
      ks.sum = ls.sum →
      syracuseNumeratorList ks = syracuseNumeratorList ls →
      ks = ls := by
  induction s with
  | zero =>
      intro ks ls hks hls _ _ _ _
      have hksNil : ks = [] := List.length_eq_zero.mp hks
      have hlsNil : ls = [] := List.length_eq_zero.mp hls
      simpa [hksNil, hlsNil]
  | succ s ih =>
      intro ks ls hks hls hksPos hlsPos hsum hnum
      obtain ⟨k, kt, rfl⟩ := List.exists_cons_of_length_pos (by omega : 0 < ks.length)
      obtain ⟨l, lt, rfl⟩ := List.exists_cons_of_length_pos (by omega : 0 < ls.length)
      have hktLen : kt.length = s := by simpa using hks
      have hltLen : lt.length = s := by simpa using hls
      have hkPos : 0 < k := hksPos k (by simp)
      have hlPos : 0 < l := hlsPos l (by simp)
      have hktPos : ∀ x ∈ kt, 0 < x := by
        intro x hx
        exact hksPos x (by simp [hx])
      have hltPos : ∀ x ∈ lt, 0 < x := by
        intro x hx
        exact hlsPos x (by simp [hx])
      by_cases hs0 : s = 0
      · have hktZero : kt.length = 0 := hktLen.trans hs0
        have hltZero : lt.length = 0 := hltLen.trans hs0
        have hktNil : kt = [] := List.length_eq_zero.mp hktZero
        have hltNil : lt = [] := List.length_eq_zero.mp hltZero
        subst kt
        subst lt
        simp only [List.sum_cons, List.sum_nil, add_zero] at hsum
        subst l
        rfl
      · have hktNonempty : kt ≠ [] := by
          intro h
          rw [h, List.length_nil] at hktLen
          exact hs0 hktLen.symm
        have hltNonempty : lt ≠ [] := by
          intro h
          rw [h, List.length_nil] at hltLen
          exact hs0 hltLen.symm
        obtain ⟨k', ktt, hkt⟩ := List.exists_cons_of_ne_nil hktNonempty
        obtain ⟨l', ltt, hlt⟩ := List.exists_cons_of_ne_nil hltNonempty
        have hk'Pos : 0 < k' := by
          exact hktPos k' (hkt ▸ by simp)
        have hl'Pos : 0 < l' := by
          exact hltPos l' (hlt ▸ by simp)
        have htailMul :
            2 ^ k * syracuseNumeratorList kt =
              2 ^ l * syracuseNumeratorList lt := by
          rw [syracuseNumeratorList_cons, syracuseNumeratorList_cons] at hnum
          have hpowLen : 3 ^ kt.length = 3 ^ lt.length := by
            rw [hktLen, hltLen]
          omega
        have hfirst : k = l := by
          apply eq_exponent_of_pow_two_mul_eq
          · exact hkt ▸ syracuseNumeratorList_mod_two hk'Pos ktt
          · exact hlt ▸ syracuseNumeratorList_mod_two hl'Pos ltt
          · exact htailMul
        have htailNum :
            syracuseNumeratorList kt = syracuseNumeratorList lt := by
          subst l
          exact Nat.eq_of_mul_eq_mul_left
            (pow_pos (by norm_num : 0 < (2 : ℕ)) k) htailMul
        have htailSum : kt.sum = lt.sum := by
          subst l
          simpa using hsum
        have htailEq :
            kt = lt :=
          ih hktLen hltLen hktPos hltPos htailSum htailNum
        simpa [hfirst, htailEq]

/-- Syracuse numerator of a Mathlib positive composition. -/
def syracuseNumerator {N : ℕ} (c : Composition N) : ℕ :=
  syracuseNumeratorList c.blocks

/-- **Integer-lift injectivity.**

At fixed total `N` and fixed number of parts `s`, distinct positive
compositions have distinct integer Syracuse numerators. -/
theorem syracuseNumerator_injective_on_length
    {N s : ℕ} {c d : Composition N}
    (hc : c.length = s) (hd : d.length = s)
    (hnum : syracuseNumerator c = syracuseNumerator d) :
    c = d := by
  apply Composition.ext
  apply syracuseNumeratorList_injective_of_length_sum s
  · exact hc
  · exact hd
  · intro k hk
    exact c.blocks_pos hk
  · intro k hk
    exact d.blocks_pos hk
  · rw [c.blocks_sum, d.blocks_sum]
  · exact hnum

/-- Positive compositions with fixed total `N` and fixed number of parts
`s`. -/
def FixedComposition (N s : ℕ) :=
  {c : Composition N // c.length = s}

noncomputable instance fixedCompositionFintype (N s : ℕ) :
    Fintype (FixedComposition N s) :=
  Fintype.ofFinset
    ((Finset.univ : Finset (Composition N)).filter
      (fun c => c.length = s))
    (by
      intro c
      constructor
      · intro h
        exact (Finset.mem_filter.mp h).2
      · intro h
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)

noncomputable instance fixedCompositionDecidableEq (N s : ℕ) :
    DecidableEq (FixedComposition N s) :=
  Classical.decEq _

/-- Numerator in the fixed-total, fixed-length model. -/
def fixedNumerator
    {N s : ℕ} (c : FixedComposition N s) : ℕ :=
  syracuseNumerator c.1

/-- Numerator residue modulo `3^s`.  Multiplication by `2^{-N}` is a
permutation modulo `3^s`, so this label has exactly the same fiber
multiplicities as the normalized offset in the paper. -/
def fixedNumeratorResidue
    {N s : ℕ} (c : FixedComposition N s) : Fin (3 ^ s) :=
  ⟨fixedNumerator c % 3 ^ s,
    Nat.mod_lt _ (pow_pos (by norm_num : 0 < (3 : ℕ)) s)⟩

/-- Integer-lift injectivity in the fixed-total model. -/
theorem fixedNumerator_injective
    {N s : ℕ} :
    Function.Injective (fixedNumerator : FixedComposition N s → ℕ) := by
  intro c d hnum
  apply Subtype.ext
  exact
    syracuseNumerator_injective_on_length
      c.2
      d.2
      hnum

end FixedTotal

end CollatzEndpointTransport
