/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik
-/
import CollatzEndpointTransport.Common.TerrasAffineMaximalBarrier
import CollatzEndpointTransport.Common.TerrasShellRepetition
import CollatzEndpointTransport.Common.ShellToGlobalDensity
import CollatzEndpointTransport.Common.QuantitativeDensityConstants

/-!
# Terras Maximal Barrier Density

Transfer of the finite maximal Boolean-walk estimate to Collatz parity words
and dyadic shells.
-/

namespace CollatzEndpointTransport

namespace Terras

open Nat Finset

noncomputable section

/-- Residues modulo `2^M` whose parity word hits the barrier. -/
noncomputable def barrierResidues (M : ℕ) (h : ℝ) :
    Finset (Fin (2 ^ M)) := by
  classical
  exact Finset.univ.filter
    (fun x => hitsBarrierFrom (2 * h) M 0 (parityVec M (x : ℕ)))

noncomputable def barrierResidueEquiv (M : ℕ) (h : ℝ) :
    {x : Fin (2 ^ M) //
      hitsBarrierFrom (2 * h) M 0 (parityVec M (x : ℕ))} ≃
      {v : Fin M → Bool // hitsBarrierFrom (2 * h) M 0 v} :=
  (terrasEquiv M).subtypeEquiv (fun _ => Iff.rfl)

theorem card_barrierResidues (M : ℕ) (h : ℝ) :
    (barrierResidues M h).card = barrierHitCount (2 * h) M 0 := by
  classical
  have hc := Fintype.card_congr (barrierResidueEquiv M h)
  simpa [barrierResidues, barrierHitCount, Fintype.card_subtype] using hc

/-- Shell points whose actual Collatz parity word hits the barrier. -/
noncomputable def shellBarrierHit (M : ℕ) (h : ℝ) : Finset ℕ := by
  classical
  exact (Finset.Ico (2 ^ M) (2 ^ (M + 1))).filter
    (fun n => hitsBarrierFrom (2 * h) M 0 (parityVec M n))

theorem card_shellBarrierHit (M : ℕ) (h : ℝ) :
    (shellBarrierHit M h).card = barrierHitCount (2 * h) M 0 := by
  classical
  have hparity (n : ℕ) :
      parityVec M (n % (2 ^ M)) = parityVec M n := by
    apply parityVec_congr
    show n % 2 ^ M % 2 ^ M = n % 2 ^ M
    exact Nat.mod_mod _ _
  have heq :
      shellBarrierHit M h =
        (Finset.Ico (2 ^ M) (2 ^ (M + 1))).filter
          (fun n =>
            (⟨n % (2 ^ M), Nat.mod_lt _ (pow_pos (by omega) _)⟩ :
              Fin (2 ^ M)) ∈ barrierResidues M h) := by
    ext n
    simp only [shellBarrierHit, Finset.mem_filter,
      barrierResidues, Finset.mem_univ, true_and]
    exact and_congr_right (fun _ => by rw [hparity])
  rw [heq, card_dyadic_shell_filter_mod_mem (le_refl M),
    Nat.sub_self, pow_zero, one_mul, card_barrierResidues]

/-- Shell points where the concrete two-sided parity barrier fails. -/
noncomputable def shellMaximalParityBad (M : ℕ) (h : ℝ) : Finset ℕ := by
  classical
  exact (Finset.Ico (2 ^ M) (2 ^ (M + 1))).filter
    (fun n => ¬MaximalParityRegular n M h)

theorem shellMaximalParityBad_subset_hit (M : ℕ) (h : ℝ) :
    shellMaximalParityBad M h ⊆ shellBarrierHit M h := by
  classical
  intro n hn
  rw [shellMaximalParityBad, Finset.mem_filter] at hn
  rw [shellBarrierHit, Finset.mem_filter]
  refine ⟨hn.1, ?_⟩
  by_contra hnot
  apply hn.2
  intro H hHM
  exact maximalParityRegular_of_not_hitsBarrier hnot H hHM

theorem card_shellMaximalParityBad_le
    {M : ℕ} {h : ℝ} (hh : 0 ≤ h) (hM : 0 < M) :
    ((shellMaximalParityBad M h).card : ℝ) ≤
      (2 : ℝ) ^ (M + 1) *
        Real.exp (-(2 * h ^ 2 / (M : ℝ))) := by
  have hcard :
      (shellMaximalParityBad M h).card ≤ (shellBarrierHit M h).card :=
    Finset.card_le_card (shellMaximalParityBad_subset_hit M h)
  have hcardR :
      ((shellMaximalParityBad M h).card : ℝ) ≤
        ((shellBarrierHit M h).card : ℝ) := by exact_mod_cast hcard
  rw [card_shellBarrierHit] at hcardR
  exact hcardR.trans (barrierHitCount_le_exp h M hh hM)

def maximalBarrierC0 : ℝ :=
  1 / (2 * QuantitativeDensity.lg3 ^ 2)

theorem maximalBarrierC0_pos : 0 < maximalBarrierC0 := by
  unfold maximalBarrierC0
  exact one_div_pos.mpr
    (mul_pos (by norm_num)
      (sq_pos_of_pos QuantitativeDensity.lg3_pos))

/-- The barrier height used by the strengthened initial window. -/
def maximalBarrierHeight (t : ℝ) (M : ℕ) : ℝ :=
  t * M / (2 * QuantitativeDensity.lg3)

theorem maximalBarrierHeight_nonneg
    {t : ℝ} {M : ℕ} (ht : 0 ≤ t) :
    0 ≤ maximalBarrierHeight t M := by
  unfold maximalBarrierHeight
  exact div_nonneg
    (mul_nonneg ht (Nat.cast_nonneg M))
    (mul_nonneg (by norm_num) QuantitativeDensity.lg3_pos.le)

/-- Concrete quadratic shell tail for the simultaneous parity-prefix
barrier. -/
theorem card_shellMaximalParityBad_le_concrete
    {M : ℕ} {t : ℝ} (ht : 0 ≤ t) :
    ((shellMaximalParityBad M (maximalBarrierHeight t M)).card : ℝ) ≤
      2 * Real.exp (-(maximalBarrierC0 * t ^ 2 * M)) *
        (2 : ℝ) ^ M := by
  classical
  cases M with
  | zero =>
      have hcard :
          (shellMaximalParityBad 0 (maximalBarrierHeight t 0)).card ≤ 1 := by
        calc
          (shellMaximalParityBad 0
              (maximalBarrierHeight t 0)).card
              ≤ (Finset.Ico (2 ^ 0) (2 ^ (0 + 1))).card := by
                apply Finset.card_le_card
                intro n hn
                rw [shellMaximalParityBad, Finset.mem_filter] at hn
                exact hn.1
          _ = 1 := by norm_num
      have hcardR :
          ((shellMaximalParityBad 0
            (maximalBarrierHeight t 0)).card : ℝ) ≤ 1 := by
        exact_mod_cast hcard
      norm_num at hcardR ⊢
      linarith
  | succ M =>
      have hraw := card_shellMaximalParityBad_le
        (M := M + 1) (h := maximalBarrierHeight t (M + 1))
        (maximalBarrierHeight_nonneg ht) (Nat.succ_pos M)
      have hlg3 :
          QuantitativeDensity.lg3 ≠ 0 :=
        ne_of_gt QuantitativeDensity.lg3_pos
      have hexp :
          -(2 * maximalBarrierHeight t (M + 1) ^ 2 /
              ((M + 1 : ℕ) : ℝ)) =
            -(maximalBarrierC0 * t ^ 2 * ((M + 1 : ℕ) : ℝ)) := by
        unfold maximalBarrierHeight maximalBarrierC0
        have hM : (0 : ℝ) < M + 1 := by positivity
        field_simp [hlg3]
        ring
      calc
        ((shellMaximalParityBad (M + 1)
          (maximalBarrierHeight t (M + 1))).card : ℝ)
            ≤ (2 : ℝ) ^ (M + 1 + 1) *
              Real.exp
                (-(2 * maximalBarrierHeight t (M + 1) ^ 2 /
                  ((M + 1 : ℕ) : ℝ))) := by simpa [Nat.succ_eq_add_one] using hraw
        _ = 2 * Real.exp
              (-(maximalBarrierC0 * t ^ 2 * ((M + 1 : ℕ) : ℝ))) *
              (2 : ℝ) ^ (M + 1) := by
          rw [hexp, pow_succ, pow_succ]
          ring

end

end Terras

end CollatzEndpointTransport
