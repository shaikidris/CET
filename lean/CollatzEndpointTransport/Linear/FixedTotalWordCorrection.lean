/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik
-/
import CollatzEndpointTransport.Common.TerrasIntegerAffine
import CollatzEndpointTransport.Linear.FixedTotalComposition
import Mathlib.Data.List.OfFn

/-!
# Fixed Total Word Correction

Boolean-word correction and the fixed-total composition dictionary.

A positive block `k` is encoded as one odd letter followed by `k-1` even
letters.  For a positive composition `ks`, this encoding has total length
`ks.sum`, and its integer affine correction, when preceded by `u` even
letters, is exactly

  2^u * syracuseNumeratorList ks.
-/

namespace CollatzEndpointTransport

namespace FixedTotal

open Nat Finset

/-- Advance an integer affine correction through a Boolean word, starting at
absolute time `i`. -/
def wordCorrectionFrom : ℕ → ℕ → List Bool → ℕ
  | _, c, [] => c
  | i, c, b :: bs =>
      wordCorrectionFrom (i + 1)
        (if b then 3 * c + 2 ^ i else c) bs

@[simp]
theorem wordCorrectionFrom_nil (i c : ℕ) :
    wordCorrectionFrom i c [] = c := rfl

theorem wordCorrectionFrom_cons (i c : ℕ) (b : Bool) (bs : List Bool) :
    wordCorrectionFrom i c (b :: bs) =
      wordCorrectionFrom (i + 1)
        (if b then 3 * c + 2 ^ i else c) bs := rfl

theorem wordCorrectionFrom_append
    (i c : ℕ) (xs ys : List Bool) :
    wordCorrectionFrom i c (xs ++ ys) =
      wordCorrectionFrom (i + xs.length)
        (wordCorrectionFrom i c xs) ys := by
  induction xs generalizing i c with
  | nil => simp
  | cons b bs ih =>
      rw [List.cons_append, wordCorrectionFrom_cons, ih]
      simp [wordCorrectionFrom_cons, Nat.add_assoc, Nat.add_left_comm,
        Nat.add_comm]

theorem wordCorrectionFrom_replicate_false_append
    (i c r : ℕ) (ys : List Bool) :
    wordCorrectionFrom i c (List.replicate r false ++ ys) =
      wordCorrectionFrom (i + r) c ys := by
  induction r generalizing i with
  | zero => simp
  | succ r ih =>
      rw [List.replicate_succ, List.cons_append, wordCorrectionFrom_cons]
      simp only [Bool.false_eq_true, ↓reduceIte]
      rw [ih]
      simp [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

/-- Encode one positive part as an odd letter followed by its remaining even
letters. -/
def encodePart (k : ℕ) : List Bool :=
  true :: List.replicate (k - 1) false

/-- Encode a positive composition as its odd/even word beginning at the first
odd letter. -/
def encodeBlocks : List ℕ → List Bool
  | [] => []
  | k :: ks => encodePart k ++ encodeBlocks ks

@[simp]
theorem encodeBlocks_nil : encodeBlocks [] = [] := rfl

@[simp]
theorem encodeBlocks_cons (k : ℕ) (ks : List ℕ) :
    encodeBlocks (k :: ks) = encodePart k ++ encodeBlocks ks := rfl

theorem encodePart_length {k : ℕ} (hk : 0 < k) :
    (encodePart k).length = k := by
  simp [encodePart]
  omega

theorem encodeBlocks_length
    {ks : List ℕ} (hpos : ∀ k ∈ ks, 0 < k) :
    (encodeBlocks ks).length = ks.sum := by
  induction ks with
  | nil => simp
  | cons k ks ih =>
      have hk : 0 < k := hpos k (by simp)
      have htail : ∀ l ∈ ks, 0 < l :=
        fun l hl => hpos l (by simp [hl])
      simp only [encodeBlocks_cons, List.length_append, List.sum_cons]
      rw [encodePart_length hk, ih htail]

theorem wordCorrectionFrom_encodeBlocks
    (u c : ℕ) (ks : List ℕ)
    (hpos : ∀ k ∈ ks, 0 < k) :
    wordCorrectionFrom u c (encodeBlocks ks) =
      3 ^ ks.length * c + 2 ^ u * syracuseNumeratorList ks := by
  induction ks generalizing u c with
  | nil => simp
  | cons k ks ih =>
      have hk : 0 < k := hpos k (by simp)
      have htail : ∀ l ∈ ks, 0 < l :=
        fun l hl => hpos l (by simp [hl])
      rw [encodeBlocks_cons, encodePart]
      simp only [List.cons_append, wordCorrectionFrom_cons, if_true]
      rw [wordCorrectionFrom_replicate_false_append]
      have htime : u + 1 + (k - 1) = u + k := by omega
      rw [htime, ih (u := u + k) (c := 3 * c + 2 ^ u) htail]
      simp only [syracuseNumeratorList_cons, List.length_cons, pow_succ]
      rw [pow_add]
      ring

theorem wordCorrectionFrom_zero_encodeBlocks
    (u : ℕ) (ks : List ℕ)
    (hpos : ∀ k ∈ ks, 0 < k) :
    wordCorrectionFrom u 0 (encodeBlocks ks) =
      2 ^ u * syracuseNumeratorList ks := by
  simpa using wordCorrectionFrom_encodeBlocks u 0 ks hpos

theorem wordCorrectionFrom_prefix_encodeComposition
    {N : ℕ} (u : ℕ) (c : Composition N) :
    wordCorrectionFrom 0 0
        (List.replicate u false ++ encodeBlocks c.blocks) =
      2 ^ u * syracuseNumerator c := by
  rw [wordCorrectionFrom_replicate_false_append]
  simpa [syracuseNumerator] using
    wordCorrectionFrom_zero_encodeBlocks u c.blocks
      (fun k hk => c.blocks_pos hk)

theorem wordCorrectionFrom_concat
    (i c : ℕ) (xs : List Bool) (b : Bool) :
    wordCorrectionFrom i c (xs.concat b) =
      if b then
        3 * wordCorrectionFrom i c xs + 2 ^ (i + xs.length)
      else
        wordCorrectionFrom i c xs := by
  rw [List.concat_eq_append, wordCorrectionFrom_append]
  simp [wordCorrectionFrom_cons]

theorem parityVec_castSucc
    (M n : ℕ) :
    (fun i : Fin M => Terras.parityVec (M + 1) n i.castSucc) =
      Terras.parityVec M n := by
  rfl

/-- The recursively defined orbit correction is exactly the correction of
the corresponding Terras parity word. -/
theorem wordCorrection_parityVec
    (M n : ℕ) :
    wordCorrectionFrom 0 0 (List.ofFn (Terras.parityVec M n)) =
      Terras.integerCorrection M n := by
  induction M with
  | zero => simp [wordCorrectionFrom, Terras.integerCorrection]
  | succ M ih =>
      rw [List.ofFn_succ']
      have hprefix :
          List.ofFn
              (fun i : Fin M =>
                Terras.parityVec (M + 1) n i.castSucc) =
            List.ofFn (Terras.parityVec M n) := by
        rw [parityVec_castSucc]
      rw [hprefix, wordCorrectionFrom_concat, ih,
        Terras.integerCorrection_succ]
      simp [Terras.parityVec]

end FixedTotal

end CollatzEndpointTransport
