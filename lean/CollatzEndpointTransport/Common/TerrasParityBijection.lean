/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik
-/
import Mathlib

/-!
# Terras Parity Bijection

The Terras parity-word bijection.

For the accelerated Collatz map

  T n = n / 2        if n is even,
  T n = (3n + 1) / 2 if n is odd,

the parity vector of the first `H` steps starting from `n` depends only on
`n % 2 ^ H`, and the induced map

  Fin (2 ^ H)  ->  (Fin H -> Bool)

is a BIJECTION. This is the classical observation of Terras and Everett.

Consequence used downstream: under the uniform distribution on residues mod
`2 ^ H`, the number of odd steps in the first `H` steps is *exactly*
`Binomial (H, 1/2)`. No independence hypothesis is introduced anywhere; the
statement is pure counting, which is what makes it usable against a
deterministic map.

This file is independent of the endpoint-transport bootstrap and can be reused
wherever exact parity-word counting is needed.
-/

namespace CollatzEndpointTransport

namespace Terras

/-- The accelerated Collatz map. -/
def T (n : ℕ) : ℕ := if n % 2 = 0 then n / 2 else (3 * n + 1) / 2

theorem two_mul_T_of_even {n : ℕ} (h : n % 2 = 0) : 2 * T n = n := by
  unfold T
  rw [if_pos h]
  omega

theorem two_mul_T_of_odd {n : ℕ} (h : n % 2 = 1) : 2 * T n = 3 * n + 1 := by
  unfold T
  rw [if_neg (by omega)]
  omega

/-- Halving a congruence: `2a ≡ 2b [MOD 2^(H+1)]` gives `a ≡ b [MOD 2^H]`. -/
theorem modEq_of_two_mul {H a b : ℕ}
    (h : 2 * a ≡ 2 * b [MOD 2 ^ (H + 1)]) : a ≡ b [MOD 2 ^ H] := by
  rw [Nat.modEq_iff_dvd] at h ⊢
  push_cast at h ⊢
  obtain ⟨k, hk⟩ := h
  refine ⟨k, ?_⟩
  have hp : ((2 : ℤ)) ^ (H + 1) = 2 * 2 ^ H := by ring
  rw [hp] at hk
  linarith

/-- One step of `T` consumes exactly one bit of modular information. -/
theorem T_modEq {H n n' : ℕ} (h : n ≡ n' [MOD 2 ^ (H + 1)]) :
    T n ≡ T n' [MOD 2 ^ H] := by
  have hdvd : (2 : ℕ) ∣ 2 ^ (H + 1) := dvd_pow_self 2 (Nat.succ_ne_zero H)
  have h2 : n % 2 = n' % 2 := h.of_dvd hdvd
  apply modEq_of_two_mul
  rcases Nat.even_or_odd n with he | ho
  · have hn : n % 2 = 0 := Nat.even_iff.mp he
    have hn' : n' % 2 = 0 := by omega
    rw [two_mul_T_of_even hn, two_mul_T_of_even hn']
    exact h
  · have hn : n % 2 = 1 := Nat.odd_iff.mp ho
    have hn' : n' % 2 = 1 := by omega
    rw [two_mul_T_of_odd hn, two_mul_T_of_odd hn']
    exact Nat.ModEq.add_right 1 (Nat.ModEq.mul_left 3 h)

/-- `i` steps of `T` consume exactly `i` bits. -/
theorem iterate_T_modEq :
    ∀ (i j n n' : ℕ), n ≡ n' [MOD 2 ^ (i + j)] →
      T^[i] n ≡ T^[i] n' [MOD 2 ^ j] := by
  intro i
  induction i with
  | zero => intro j n n' h; simpa using h
  | succ i ih =>
      intro j n n' h
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
      apply ih
      apply T_modEq (H := i + j)
      rwa [show i + 1 + j = i + j + 1 by ring] at h

/-- The parity of a natural number, as a `Bool`. -/
def parityBit (n : ℕ) : Bool := decide (n % 2 = 1)

/-- The parity vector of the first `H` steps of `T` starting from `n`. -/
def parityVec (H n : ℕ) : Fin H → Bool := fun i => parityBit (T^[(i : ℕ)] n)

/-- **Terras, well-definedness.** The parity vector depends only on
`n % 2 ^ H`. -/
theorem parityVec_congr {H n n' : ℕ} (h : n ≡ n' [MOD 2 ^ H]) :
    parityVec H n = parityVec H n' := by
  funext i
  obtain ⟨j, hj⟩ := Nat.exists_eq_add_of_lt i.isLt
  have hstep : T^[(i : ℕ)] n ≡ T^[(i : ℕ)] n' [MOD 2 ^ (j + 1)] := by
    apply iterate_T_modEq
    rwa [show (i : ℕ) + (j + 1) = H by omega]
  have hdvd : (2 : ℕ) ∣ 2 ^ (j + 1) := dvd_pow_self 2 (Nat.succ_ne_zero j)
  have h2 : T^[(i : ℕ)] n % 2 = T^[(i : ℕ)] n' % 2 := hstep.of_dvd hdvd
  simp only [parityVec, parityBit, h2]

/-- **Terras, injectivity.** Equal parity vectors force equal residues. -/
theorem modEq_of_parityVec_eq :
    ∀ (H n n' : ℕ), parityVec H n = parityVec H n' → n ≡ n' [MOD 2 ^ H] := by
  intro H
  induction H with
  | zero => intro n n' _; simp [Nat.ModEq, Nat.mod_one]
  | succ H ih =>
      intro n n' h
      have h0 : parityBit n = parityBit n' := by
        have hc := congrFun h ⟨0, Nat.succ_pos H⟩
        simpa [parityVec] using hc
      have hpar : n % 2 = n' % 2 := by
        simp only [parityBit, decide_eq_decide] at h0
        omega
      have htail : parityVec H (T n) = parityVec H (T n') := by
        funext i
        have hc := congrFun h ⟨(i : ℕ) + 1, by omega⟩
        simpa [parityVec, Function.iterate_succ_apply] using hc
      have hT : T n ≡ T n' [MOD 2 ^ H] := ih (T n) (T n') htail
      have hTT : 2 * T n ≡ 2 * T n' [MOD 2 * 2 ^ H] :=
        Nat.ModEq.mul_left' 2 hT
      have hpow : 2 * 2 ^ H = 2 ^ (H + 1) := by ring
      rw [hpow] at hTT
      rcases Nat.even_or_odd n with he | ho
      · have hn : n % 2 = 0 := Nat.even_iff.mp he
        have hn' : n' % 2 = 0 := by omega
        rwa [two_mul_T_of_even hn, two_mul_T_of_even hn'] at hTT
      · have hn : n % 2 = 1 := Nat.odd_iff.mp ho
        have hn' : n' % 2 = 1 := by omega
        rw [two_mul_T_of_odd hn, two_mul_T_of_odd hn'] at hTT
        have h3 : 3 * n ≡ 3 * n' [MOD 2 ^ (H + 1)] :=
          Nat.ModEq.add_right_cancel' 1 hTT
        have hcop : Nat.gcd (2 ^ (H + 1)) 3 = 1 :=
          Nat.Coprime.pow_left (H + 1) (by norm_num)
        exact Nat.ModEq.cancel_left_of_coprime hcop h3

/-- The Terras map on residues: `Fin (2 ^ H) → (Fin H → Bool)`. -/
def terrasMap (H : ℕ) : Fin (2 ^ H) → (Fin H → Bool) :=
  fun x => parityVec H (x : ℕ)

theorem terrasMap_injective (H : ℕ) : Function.Injective (terrasMap H) := by
  intro a b hab
  have h := modEq_of_parityVec_eq H (a : ℕ) (b : ℕ) hab
  have ha : (a : ℕ) < 2 ^ H := a.isLt
  have hb : (b : ℕ) < 2 ^ H := b.isLt
  have : (a : ℕ) = (b : ℕ) := by
    have := h
    rwa [Nat.ModEq, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at this
  exact Fin.ext this

/-- **The Terras parity-word bijection.** Residues mod `2 ^ H` correspond
bijectively to parity words of length `H`. -/
theorem terrasMap_bijective (H : ℕ) : Function.Bijective (terrasMap H) := by
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨terrasMap_injective H, ?_⟩
  simp

/-- The bijection as an `Equiv`. -/
noncomputable def terrasEquiv (H : ℕ) : Fin (2 ^ H) ≃ (Fin H → Bool) :=
  Equiv.ofBijective (terrasMap H) (terrasMap_bijective H)

/-- The number of odd steps in the first `H` steps starting from `n`. -/
def oddCount (H n : ℕ) : ℕ :=
  (Finset.univ.filter (fun i : Fin H => parityVec H n i = true)).card

/-- The number of `true` entries of a parity word. -/
def wordWeight {H : ℕ} (v : Fin H → Bool) : ℕ :=
  (Finset.univ.filter (fun i : Fin H => v i = true)).card

theorem oddCount_eq_wordWeight (H n : ℕ) :
    oddCount H n = wordWeight (parityVec H n) := rfl

/-- **Exact binomial count.** The residues mod `2 ^ H` whose first `H` steps
contain exactly `k` odd steps number exactly `H.choose k`.

This is the precise sense in which the odd count is `Binomial (H, 1/2)` under
uniform residues: it is a counting identity, with no probabilistic hypothesis
and no independence assumption. -/
theorem card_wordWeight_eq_choose (H k : ℕ) :
    (Finset.univ.filter (fun v : Fin H → Bool => wordWeight v = k)).card
      = H.choose k := by
  classical
  have hbij :
      (Finset.univ.filter (fun v : Fin H → Bool => wordWeight v = k)).card
        = (Finset.powersetCard k (Finset.univ : Finset (Fin H))).card := by
    apply Finset.card_bij
      (fun v _ => Finset.univ.filter (fun i : Fin H => v i = true))
    · intro v hv
      have hw : wordWeight v = k := (Finset.mem_filter.mp hv).2
      simp only [Finset.mem_powersetCard, Finset.subset_univ, true_and]
      exact hw
    · intro v _ w _ hvw
      funext i
      have hi := Finset.ext_iff.mp hvw i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
      cases hv : v i <;> cases hw : w i <;> simp [hv, hw] at hi ⊢
    · intro s hs
      have hcard : s.card = k := (Finset.mem_powersetCard.mp hs).2
      refine ⟨fun i => decide (i ∈ s), ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and, wordWeight,
          decide_eq_true_eq]
        rwa [Finset.filter_mem_eq_inter, Finset.univ_inter]
      · simp only [decide_eq_true_eq]
        rw [Finset.filter_mem_eq_inter, Finset.univ_inter]
  rw [hbij, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]

theorem card_residues_with_oddCount (H k : ℕ) :
    (Finset.univ.filter
      (fun x : Fin (2 ^ H) => oddCount H (x : ℕ) = k)).card = H.choose k := by
  classical
  have hcard :
      (Finset.univ.filter
        (fun x : Fin (2 ^ H) => oddCount H (x : ℕ) = k)).card =
      (Finset.univ.filter
        (fun v : Fin H → Bool => wordWeight v = k)).card := by
    apply Finset.card_bij (fun x _ => terrasMap H x)
    · intro x hx
      simpa [wordWeight, terrasMap, oddCount] using
        (Finset.mem_filter.mp hx).2
    · intro x _ y _ hxy
      exact terrasMap_injective H hxy
    · intro v hv
      obtain ⟨x, hx⟩ := (terrasMap_bijective H).2 v
      refine ⟨x, ?_, hx⟩
      have hw : wordWeight v = k := (Finset.mem_filter.mp hv).2
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [oddCount_eq_wordWeight, show parityVec H (x : ℕ) = v from hx]
      exact hw
  rw [hcard, card_wordWeight_eq_choose]

end Terras

end CollatzEndpointTransport
