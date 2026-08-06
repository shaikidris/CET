/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik
-/
import Mathlib.Data.Nat.Periodic
import Mathlib.Logic.Equiv.Fin
import CollatzEndpointTransport.Common.TerrasBinomialTail

/-!
# Terras Shell Repetition

Exact periodic counting on dyadic shells.

For `H <= M`, the shell `[2^M, 2^(M+1))` has length `2^M`, starts at a
multiple of `2^H`, and therefore contains every residue modulo `2^H`
exactly `2^(M-H)` times.  This is the deterministic bridge from residue
counts to shell counts.

The hypothesis `H <= M` is load-bearing.  The longer window
`K = floor (M / b)` used later in the endpoint bootstrap has `K > M`;
this file deliberately makes no repetition claim in that regime.
-/

namespace CollatzEndpointTransport

namespace Terras

/-- In `Fin (blocks * q)`, every residue modulo a positive `q` occurs
exactly `blocks` times. -/
theorem card_fin_filter_mod_mem
    {blocks q : ℕ} (hq : 0 < q) (S : Finset (Fin q)) :
    (Finset.univ.filter
      (fun x : Fin (blocks * q) =>
        (⟨(x : ℕ) % q, Nat.mod_lt _ hq⟩ : Fin q) ∈ S)).card =
      blocks * S.card := by
  classical
  let e : Fin blocks × Fin q ≃ Fin (blocks * q) :=
    finProdFinEquiv
  have hres (x : Fin (blocks * q)) :
      (⟨(x : ℕ) % q, Nat.mod_lt _ hq⟩ : Fin q) = (e.symm x).2 := by
    apply Fin.ext
    simp [e, finProdFinEquiv]
  calc
    (Finset.univ.filter
      (fun x : Fin (blocks * q) =>
        (⟨(x : ℕ) % q, Nat.mod_lt _ hq⟩ : Fin q) ∈ S)).card =
        ((Finset.univ : Finset (Fin blocks)) ×ˢ S).card := by
          apply Finset.card_bij (fun x _ => e.symm x)
          · intro x hx
            have hxS := (Finset.mem_filter.mp hx).2
            simp only [Finset.mem_product, Finset.mem_univ, true_and]
            rw [← hres x]
            exact hxS
          · intro x _ y _ hxy
            exact e.symm.injective hxy
          · intro y hy
            refine ⟨e y, ?_, e.symm_apply_apply y⟩
            have hyS : y.2 ∈ S := (Finset.mem_product.mp hy).2
            simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            rw [hres (e y), e.symm_apply_apply]
            exact hyS
    _ = blocks * S.card := by simp

/-- A periodic predicate has its exact expected count on an interval made
of complete periods, provided the interval starts at a period boundary. -/
theorem card_Ico_filter_mod_mem_of_dvd
    {base blocks q : ℕ} (hq : 0 < q) (hbase : q ∣ base)
    (S : Finset (Fin q)) :
    ((Finset.Ico base (base + blocks * q)).filter
      (fun n =>
        (⟨n % q, Nat.mod_lt _ hq⟩ : Fin q) ∈ S)).card =
      blocks * S.card := by
  classical
  have hbase_mod : base % q = 0 := Nat.mod_eq_zero_of_dvd hbase
  have hcard :
      ((Finset.Ico base (base + blocks * q)).filter
        (fun n =>
          (⟨n % q, Nat.mod_lt _ hq⟩ : Fin q) ∈ S)).card =
        (Finset.univ.filter
          (fun x : Fin (blocks * q) =>
            (⟨(x : ℕ) % q, Nat.mod_lt _ hq⟩ : Fin q) ∈ S)).card := by
    apply Finset.card_bij
      (fun n hn =>
        ⟨n - base, by
          have hnIco := (Finset.mem_filter.mp hn).1
          have hnle := (Finset.mem_Ico.mp hnIco).1
          have hnlt := (Finset.mem_Ico.mp hnIco).2
          omega⟩)
    · intro n hn
      have hnIco := (Finset.mem_filter.mp hn).1
      have hnS := (Finset.mem_filter.mp hn).2
      have hnle := (Finset.mem_Ico.mp hnIco).1
      have hn_eq : base + (n - base) = n := Nat.add_sub_of_le hnle
      have hmod : n % q = (n - base) % q := by
        calc
          n % q = (base + (n - base)) % q := by rw [hn_eq]
          _ = (n - base) % q := by simp [Nat.add_mod, hbase_mod]
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      simpa [hmod] using hnS
    · intro n hn m hm hnm
      have hnIco := (Finset.mem_filter.mp hn).1
      have hmIco := (Finset.mem_filter.mp hm).1
      have hnle := (Finset.mem_Ico.mp hnIco).1
      have hmle := (Finset.mem_Ico.mp hmIco).1
      have hval : n - base = m - base := congrArg Fin.val hnm
      omega
    · intro x hx
      refine ⟨base + (x : ℕ), ?_, ?_⟩
      · have hxS := (Finset.mem_filter.mp hx).2
        simp only [Finset.mem_filter, Finset.mem_Ico]
        constructor
        · constructor
          · omega
          · exact Nat.add_lt_add_left x.isLt base
        · simpa [Nat.add_mod, hbase_mod] using hxS
      · apply Fin.ext
        simp
  rw [hcard, card_fin_filter_mod_mem hq S]

/-- A periodic residue family occupies at most one extra incomplete period
in an arbitrary interval.  This is the division-free form of
`density + one-period boundary error`. -/
theorem card_Ico_filter_mod_mem_le
    {base length q : ℕ} (hq : 0 < q) (S : Finset (Fin q)) :
    ((Finset.Ico base (base + length)).filter
      (fun n =>
        (⟨n % q, Nat.mod_lt _ hq⟩ : Fin q) ∈ S)).card ≤
      (length / q + 1) * S.card := by
  classical
  let blocks := length / q + 1
  let p : ℕ → Prop := fun n =>
    (⟨n % q, Nat.mod_lt _ hq⟩ : Fin q) ∈ S
  have hp : Function.Periodic p q := by
    intro n
    simp [p, Nat.add_mod]
  have hlength : length ≤ blocks * q := by
    calc
      length = length % q + q * (length / q) :=
        (Nat.mod_add_div length q).symm
      _ ≤ q + q * (length / q) := by
        exact Nat.add_le_add_right (Nat.mod_lt length hq).le _
      _ = blocks * q := by
        simp [blocks]
        ring
  have hsubset :
      (Finset.Ico base (base + length)).filter p ⊆
        (Finset.Ico base (base + blocks * q)).filter p := by
    intro n hn
    rw [Finset.mem_filter, Finset.mem_Ico] at hn ⊢
    exact ⟨⟨hn.1.1,
      hn.1.2.trans_le (Nat.add_le_add_left hlength base)⟩, hn.2⟩
  have hpblocks : Function.Periodic p (blocks * q) := by
    simpa [nsmul_eq_mul] using hp.nsmul blocks
  have hperiod :=
    Nat.filter_Ico_card_eq_of_periodic base (blocks * q) p hpblocks
  have hzero := card_Ico_filter_mod_mem_of_dvd
    (base := 0) (blocks := blocks) (q := q) hq (dvd_zero q) S
  have hcount : (blocks * q).count p = blocks * S.card := by
    rw [Nat.count_eq_card_filter_range, ← Nat.Ico_zero_eq_range]
    simpa [p] using hzero
  calc
    ((Finset.Ico base (base + length)).filter
      (fun n =>
        (⟨n % q, Nat.mod_lt _ hq⟩ : Fin q) ∈ S)).card =
        ((Finset.Ico base (base + length)).filter p).card := by rfl
    _ ≤ ((Finset.Ico base (base + blocks * q)).filter p).card :=
      Finset.card_le_card hsubset
    _ = (blocks * q).count p := hperiod
    _ = blocks * S.card := hcount
    _ = (length / q + 1) * S.card := by rfl

/-- **Exact dyadic-shell repetition.** If `H <= M`, every selected residue
modulo `2^H` occurs exactly `2^(M-H)` times in
`[2^M, 2^(M+1))`. -/
theorem card_dyadic_shell_filter_mod_mem
    {H M : ℕ} (hHM : H ≤ M) (S : Finset (Fin (2 ^ H))) :
    ((Finset.Ico (2 ^ M) (2 ^ (M + 1))).filter
      (fun n =>
        (⟨n % (2 ^ H), Nat.mod_lt _ (pow_pos (by omega) _)⟩ :
          Fin (2 ^ H)) ∈ S)).card =
      2 ^ (M - H) * S.card := by
  have hq : 0 < 2 ^ H := pow_pos (by omega) _
  have hbase : 2 ^ H ∣ 2 ^ M := pow_dvd_pow 2 hHM
  have hlength : 2 ^ (M - H) * 2 ^ H = 2 ^ M :=
    pow_sub_mul_pow 2 hHM
  have hupper : 2 ^ M + 2 ^ (M - H) * 2 ^ H = 2 ^ (M + 1) := by
    rw [hlength, pow_succ]
    omega
  have h := card_Ico_filter_mod_mem_of_dvd
    (base := 2 ^ M) (blocks := 2 ^ (M - H)) (q := 2 ^ H)
    hq hbase S
  simpa only [hupper] using h

/-- The first `H` parity bits, and hence their odd count, are unchanged when
the starting value is reduced modulo `2^H`. -/
theorem oddCount_mod_pow_two (H n : ℕ) :
    oddCount H (n % (2 ^ H)) = oddCount H n := by
  unfold oddCount
  rw [parityVec_congr]
  show n % 2 ^ H % 2 ^ H = n % 2 ^ H
  exact Nat.mod_mod _ _

/-- Exact shell count for a lower odd-count tail. -/
theorem card_dyadic_shell_oddCount_le
    {H M K : ℕ} (hHM : H ≤ M) :
    ((Finset.Ico (2 ^ M) (2 ^ (M + 1))).filter
      (fun n => oddCount H n ≤ K)).card =
      2 ^ (M - H) * lowerBinomialSum H K := by
  classical
  let S : Finset (Fin (2 ^ H)) :=
    Finset.univ.filter (fun x => oddCount H (x : ℕ) ≤ K)
  have hset :
      (Finset.Ico (2 ^ M) (2 ^ (M + 1))).filter
          (fun n => oddCount H n ≤ K) =
        (Finset.Ico (2 ^ M) (2 ^ (M + 1))).filter
          (fun n =>
            (⟨n % (2 ^ H), Nat.mod_lt _ (pow_pos (by omega) _)⟩ :
              Fin (2 ^ H)) ∈ S) := by
    ext n
    simp only [S, Finset.mem_filter, Finset.mem_Ico, Finset.mem_univ,
      true_and]
    rw [oddCount_mod_pow_two]
  rw [hset, card_dyadic_shell_filter_mod_mem hHM S]
  congr 1
  exact card_residues_with_oddCount_le H K

/-- **Shell Hoeffding bound.** In the exact-repetition regime `H <= M`,
the lower parity tail occupies at most an `exp (-2 t^2 H)` fraction of the
dyadic shell.  There is no shell-transfer error term. -/
theorem card_dyadic_shell_oddCount_le_hoeffding
    {H M K : ℕ} {t : ℝ} (hHM : H ≤ M) (ht : 0 ≤ t)
    (hcut : (K : ℝ) ≤ (1 / 2 - t) * H) :
    (((Finset.Ico (2 ^ M) (2 ^ (M + 1))).filter
      (fun n => oddCount H n ≤ K)).card : ℝ) ≤
      (2 : ℝ) ^ M * Real.exp (-2 * t ^ 2 * H) := by
  rw [card_dyadic_shell_oddCount_le hHM, Nat.cast_mul, Nat.cast_pow]
  have htail := lowerBinomialSum_le_hoeffding ht hcut
  calc
    (2 : ℝ) ^ (M - H) * (lowerBinomialSum H K : ℝ) ≤
        (2 : ℝ) ^ (M - H) *
          ((2 : ℝ) ^ H * Real.exp (-2 * t ^ 2 * H)) :=
      mul_le_mul_of_nonneg_left htail (by positivity)
    _ = (2 : ℝ) ^ M * Real.exp (-2 * t ^ 2 * H) := by
      rw [← mul_assoc, ← pow_add]
      congr 2
      omega

/-- Exact shell count for the symmetric upper odd-count tail. -/
theorem card_dyadic_shell_oddCount_ge_sub
    {H M K : ℕ} (hHM : H ≤ M) (hKH : K ≤ H) :
    ((Finset.Ico (2 ^ M) (2 ^ (M + 1))).filter
      (fun n => H - K ≤ oddCount H n)).card =
      2 ^ (M - H) * lowerBinomialSum H K := by
  classical
  let S : Finset (Fin (2 ^ H)) :=
    Finset.univ.filter (fun x => H - K ≤ oddCount H (x : ℕ))
  have hset :
      (Finset.Ico (2 ^ M) (2 ^ (M + 1))).filter
          (fun n => H - K ≤ oddCount H n) =
        (Finset.Ico (2 ^ M) (2 ^ (M + 1))).filter
          (fun n =>
            (⟨n % (2 ^ H), Nat.mod_lt _ (pow_pos (by omega) _)⟩ :
              Fin (2 ^ H)) ∈ S) := by
    ext n
    simp only [S, Finset.mem_filter, Finset.mem_Ico, Finset.mem_univ,
      true_and]
    rw [oddCount_mod_pow_two]
  rw [hset, card_dyadic_shell_filter_mod_mem hHM S]
  congr 1
  exact card_residues_with_oddCount_ge_sub H K hKH

/-- The symmetric upper parity tail has the same shell Hoeffding bound. -/
theorem card_dyadic_shell_oddCount_ge_sub_le_hoeffding
    {H M K : ℕ} {t : ℝ} (hHM : H ≤ M) (ht : 0 ≤ t)
    (hcut : (K : ℝ) ≤ (1 / 2 - t) * H) :
    (((Finset.Ico (2 ^ M) (2 ^ (M + 1))).filter
      (fun n => H - K ≤ oddCount H n)).card : ℝ) ≤
      (2 : ℝ) ^ M * Real.exp (-2 * t ^ 2 * H) := by
  have hKHreal : (K : ℝ) ≤ H := by
    calc
      (K : ℝ) ≤ (1 / 2 - t) * H := hcut
      _ ≤ H := by
        have hH : (0 : ℝ) ≤ H := Nat.cast_nonneg H
        nlinarith
  have hKH : K ≤ H := by exact_mod_cast hKHreal
  rw [card_dyadic_shell_oddCount_ge_sub hHM hKH, Nat.cast_mul, Nat.cast_pow]
  have htail := lowerBinomialSum_le_hoeffding ht hcut
  calc
    (2 : ℝ) ^ (M - H) * (lowerBinomialSum H K : ℝ) ≤
        (2 : ℝ) ^ (M - H) *
          ((2 : ℝ) ^ H * Real.exp (-2 * t ^ 2 * H)) :=
      mul_le_mul_of_nonneg_left htail (by positivity)
    _ = (2 : ℝ) ^ M * Real.exp (-2 * t ^ 2 * H) := by
      rw [← mul_assoc, ← pow_add]
      congr 2
      omega

end Terras

end CollatzEndpointTransport
