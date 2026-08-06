/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik
-/
import CollatzEndpointTransport.Common.QuantitativePullbackDefs
import CollatzEndpointTransport.Common.TerrasMaximalInitialWindowDensity

/-!
# Quantitative Envelope

The concrete orbit-envelope sets and the one-step concatenation used in
The one-step envelope concatenation used by the quantitative natural-density proof.

This file deliberately keeps the dyadic logarithm and both nested floors in
the definitions. The main theorem is the one-step envelope concatenation:

  Pull (G lambda delta) ∩ W zeta ∩ startup(mu)
    ⊆ G (q * lambda) t.

The paper statement needs `zeta <= 1` in the lower-shell comparison
`n^(1-zeta) >= (2^M)^(1-zeta)`.  The live bootstrap has this hypothesis
automatically (`zeta = t_j <= 1`), and it is explicit below.
-/

namespace CollatzEndpointTransport

namespace QuantitativeDensity

open scoped Real

noncomputable section

/-- The logarithmic horizon
`floor ((1-lambda) floor(log_2 n) / b)`. -/
def envelopeHorizon (lambda : ℝ) (n : ℕ) : ℕ :=
  ⌊(1 - lambda) * (Nat.log 2 n : ℝ) / bConst⌋₊

/-- The paper's set `G(lambda,t)`. -/
def EnvelopeGood (lambda t : ℝ) : Set ℕ :=
  {n | ∀ k : ℕ, k ≤ envelopeHorizon lambda n →
    Terras.centralOrbitScale k * (n : ℝ) ^ (1 - t) ≤
        ((Terras.T^[k]) n : ℝ) ∧
      ((Terras.T^[k]) n : ℝ) ≤
        Terras.centralOrbitScale k * (n : ℝ) ^ (1 + t)}

/-- Integers beyond the finite startup required by the horizon comparison. -/
def EnvelopeStartup (mu : ℝ) : Set ℕ :=
  {n | (1 + bConst) / mu ≤ (Nat.log 2 n : ℝ)}

@[simp]
theorem mem_EnvelopeGood {lambda t : ℝ} {n : ℕ} :
    n ∈ EnvelopeGood lambda t ↔
      ∀ k : ℕ, k ≤ envelopeHorizon lambda n →
        Terras.centralOrbitScale k * (n : ℝ) ^ (1 - t) ≤
            ((Terras.T^[k]) n : ℝ) ∧
          ((Terras.T^[k]) n : ℝ) ≤
            Terras.centralOrbitScale k * (n : ℝ) ^ (1 + t) :=
  Iff.rfl

@[simp]
theorem mem_EnvelopeStartup {mu : ℝ} {n : ℕ} :
    n ∈ EnvelopeStartup mu ↔
      (1 + bConst) / mu ≤ (Nat.log 2 n : ℝ) :=
  Iff.rfl

theorem envelopeHorizon_a0 (n : ℕ) :
    envelopeHorizon a0 n = Nat.log 2 n := by
  have hbne : bConst ≠ 0 := ne_of_gt bConst_pos
  unfold envelopeHorizon bConst
  have harg :
      (1 - a0) * (Nat.log 2 n : ℝ) / (1 - a0) =
        (Nat.log 2 n : ℝ) := by
    field_simp [show 1 - a0 ≠ 0 by simpa [bConst] using hbne]
  rw [harg, Nat.floor_natCast]

/-- The initial maximal window is exactly the first envelope set. -/
theorem EnvelopeGood_a0 (t : ℝ) :
    EnvelopeGood a0 t = Terras.initialWindowGood t := by
  ext n
  simp only [EnvelopeGood, Terras.initialWindowGood, Set.mem_setOf_eq,
    envelopeHorizon_a0]

theorem centralOrbitScale_add (a b : ℕ) :
    Terras.centralOrbitScale (a + b) =
      Terras.centralOrbitScale a * Terras.centralOrbitScale b := by
  simp only [Terras.centralOrbitScale_eq, pow_add]

theorem centralOrbitScale_le_one (k : ℕ) :
    Terras.centralOrbitScale k ≤ 1 := by
  rw [Terras.centralOrbitScale_eq]
  apply pow_le_one₀ (by positivity)
  have hsqrt : Real.sqrt 3 < 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  linarith

/-- The real lower estimate for the dyadic logarithm used in the horizon
comparison. -/
theorem log_two_iterate_lower
    {n M : ℕ} {zeta : ℝ}
    (hn : 0 < n) (hzeta0 : 0 ≤ zeta) (hzeta1 : zeta ≤ 1)
    (hM : M = Nat.log 2 n)
    (hwindow :
      Terras.centralOrbitScale M * (n : ℝ) ^ (1 - zeta) ≤
        ((Terras.T^[M]) n : ℝ)) :
    (a0 - zeta) * M - 1 ≤
      (Nat.log 2 ((Terras.T^[M]) n) : ℝ) := by
  subst M
  let M := Nat.log 2 n
  let m := (Terras.T^[M]) n
  have hnPowNat : 2 ^ M ≤ n := Nat.pow_log_le_self 2 (ne_of_gt hn)
  have hnPow : (2 : ℝ) ^ M ≤ (n : ℝ) := by exact_mod_cast hnPowNat
  have honeMinus : 0 ≤ 1 - zeta := by linarith
  have hnRpow :
      ((2 : ℝ) ^ M) ^ (1 - zeta) ≤ (n : ℝ) ^ (1 - zeta) :=
    Real.rpow_le_rpow (by positivity) hnPow honeMinus
  have hscale :
      Terras.centralOrbitScale M =
        (2 : ℝ) ^ (-bConst * M) :=
    Terras.centralOrbitScale_eq_two_rpow_neg_b M
  have hbase :
      (2 : ℝ) ^ ((a0 - zeta) * M) ≤ (m : ℝ) := by
    calc
      (2 : ℝ) ^ ((a0 - zeta) * M)
          = (2 : ℝ) ^ (-bConst * M) *
              ((2 : ℝ) ^ M) ^ (1 - zeta) := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num),
              ← Real.rpow_add (by norm_num)]
            congr 1
            unfold bConst
            ring
      _ ≤ Terras.centralOrbitScale M * (n : ℝ) ^ (1 - zeta) := by
            rw [← hscale]
            exact mul_le_mul_of_nonneg_left hnRpow
              (Terras.centralOrbitScale_pos M).le
      _ ≤ (m : ℝ) := hwindow
  by_cases hzetaA : zeta ≤ a0
  ·
    let K : ℕ := ⌊(a0 - zeta) * M⌋₊
    have hKexp :
        (2 : ℝ) ^ K ≤ (2 : ℝ) ^ ((a0 - zeta) * M) := by
      rw [← Real.rpow_natCast]
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      exact Nat.floor_le
        (mul_nonneg (sub_nonneg.mpr hzetaA) (Nat.cast_nonneg M))
    have hKpowR : ((2 ^ K : ℕ) : ℝ) ≤ (m : ℝ) := by
      simpa only [Nat.cast_pow, Nat.cast_ofNat] using hKexp.trans hbase
    have hKpow : 2 ^ K ≤ m := by exact_mod_cast hKpowR
    have hKlog : K ≤ Nat.log 2 m :=
      Nat.le_log_of_pow_le (by norm_num) hKpow
    have hfloor :
        (a0 - zeta) * M - 1 ≤ (K : ℝ) := by
      have hlt := Nat.lt_floor_add_one ((a0 - zeta) * (M : ℝ))
      dsimp only [K] at hlt ⊢
      linarith
    exact hfloor.trans (by exact_mod_cast hKlog)
  ·
    have hcoef : a0 - zeta < 0 := by linarith
    have hM0 : 0 ≤ (M : ℝ) := Nat.cast_nonneg M
    have hlog0 : 0 ≤ (Nat.log 2 m : ℝ) := Nat.cast_nonneg _
    nlinarith

/-- The floor-sensitive horizon calculation used by envelope concatenation. -/
theorem envelopeHorizon_le_add
    {n m M : ℕ} {lambda q zeta mu : ℝ}
    (hM : M = Nat.log 2 n)
    (hlambda0 : 0 < lambda) (hlambda1 : lambda < 1)
    (hmu :
      mu = lambda * (q - a0) - zeta * (1 - lambda))
    (hmu0 : 0 < mu)
    (hstartup : (1 + bConst) / mu ≤ (M : ℝ))
    (hlog :
      (a0 - zeta) * M - 1 ≤ (Nat.log 2 m : ℝ)) :
    envelopeHorizon (q * lambda) n ≤
      M + envelopeHorizon lambda m := by
  have hb := bConst_pos
  have hbne : bConst ≠ 0 := ne_of_gt hb
  have hfloor :
      (1 - lambda) * (Nat.log 2 m : ℝ) / bConst - 1 ≤
        (envelopeHorizon lambda m : ℝ) := by
    unfold envelopeHorizon
    have hlt := Nat.lt_floor_add_one
      ((1 - lambda) * (Nat.log 2 m : ℝ) / bConst)
    exact le_of_lt (by linarith)
  have hstartupMul :
      1 + bConst ≤ mu * (M : ℝ) := by
    have := (div_le_iff₀ hmu0).mp hstartup
    simpa [mul_comm] using this
  have hreal :
      (1 - q * lambda) * (M : ℝ) / bConst ≤
        (M + envelopeHorizon lambda m : ℕ) := by
    have hlogMul :
        (1 - lambda) * ((a0 - zeta) * (M : ℝ) - 1) / bConst ≤
          (1 - lambda) * (Nat.log 2 m : ℝ) / bConst := by
      have hfac : 0 ≤ (1 - lambda) / bConst :=
        div_nonneg (by linarith) hb.le
      have := mul_le_mul_of_nonneg_left hlog hfac
      convert this using 1 <;> ring
    have hcombined :
        (1 - q * lambda) * (M : ℝ) / bConst ≤
          (M : ℝ) +
            ((1 - lambda) * (Nat.log 2 m : ℝ) / bConst - 1) := by
      have hlogScaled :
          (1 - lambda) * ((a0 - zeta) * (M : ℝ) - 1) ≤
            (1 - lambda) * (Nat.log 2 m : ℝ) :=
        mul_le_mul_of_nonneg_left hlog (by linarith)
      have hnum :
          (1 - q * lambda) * (M : ℝ) ≤
            (M : ℝ) * bConst +
              (1 - lambda) * (Nat.log 2 m : ℝ) - bConst := by
        rw [hmu] at hstartupMul
        unfold bConst at hstartupMul ⊢
        nlinarith
      have hrhs :
          (M : ℝ) +
              ((1 - lambda) * (Nat.log 2 m : ℝ) / bConst - 1) =
            ((M : ℝ) * bConst +
              (1 - lambda) * (Nat.log 2 m : ℝ) - bConst) / bConst := by
        field_simp [hbne]
        <;> ring
      rw [hrhs]
      exact (div_le_div_iff_of_pos_right hb).2 hnum
    calc
      (1 - q * lambda) * (M : ℝ) / bConst
          ≤ (M : ℝ) +
              ((1 - lambda) * (Nat.log 2 m : ℝ) / bConst - 1) := hcombined
      _ ≤ (M : ℝ) +
          (envelopeHorizon lambda m : ℝ) := by linarith [hfloor]
      _ = (M + envelopeHorizon lambda m : ℕ) := by norm_num
  unfold envelopeHorizon
  rw [← hM]
  exact Nat.floor_le_of_le hreal

/-- The scalar lower-envelope concatenation used after the first dyadic
block.  The deliberately loose loss `delta + zeta + delta*zeta` controls
both signs at once. -/
theorem concatenate_lower_envelope
    {scale₀ scale₁ n m z delta zeta t : ℝ}
    (hscale₀ : 0 < scale₀) (hscale₀_one : scale₀ ≤ 1)
    (hscale₁ : 0 ≤ scale₁) (hn : 1 ≤ n)
    (hdelta0 : 0 ≤ delta) (hdelta1 : delta ≤ 1)
    (hzeta0 : 0 ≤ zeta)
    (ht : delta + zeta + delta * zeta ≤ t)
    (hm : scale₀ * n ^ (1 - zeta) ≤ m)
    (hz : scale₁ * m ^ (1 - delta) ≤ z) :
    scale₀ * scale₁ * n ^ (1 - t) ≤ z := by
  have hpowScale :
      scale₀ ≤ scale₀ ^ (1 - delta) := by
    calc
      scale₀ = scale₀ ^ (1 : ℝ) := (Real.rpow_one scale₀).symm
      _ ≤ scale₀ ^ (1 - delta) :=
        Real.rpow_le_rpow_of_exponent_ge hscale₀ hscale₀_one (by linarith)
  have hpowN :
      n ^ (1 - t) ≤ n ^ ((1 - zeta) * (1 - delta)) := by
    apply Real.rpow_le_rpow_of_exponent_le hn
    nlinarith [mul_nonneg hdelta0 hzeta0]
  have hm0 : 0 ≤ m := le_trans
    (mul_nonneg hscale₀.le (Real.rpow_nonneg (by linarith) _)) hm
  have hmono :
      (scale₀ * n ^ (1 - zeta)) ^ (1 - delta) ≤
        m ^ (1 - delta) :=
    Real.rpow_le_rpow
      (mul_nonneg hscale₀.le (Real.rpow_nonneg (by linarith) _))
      hm (by linarith)
  calc
    scale₀ * scale₁ * n ^ (1 - t)
        ≤ scale₁ *
            (scale₀ ^ (1 - delta) *
              n ^ ((1 - zeta) * (1 - delta))) := by
          have := mul_le_mul hpowScale hpowN
            (Real.rpow_nonneg (by linarith) _)
            (Real.rpow_nonneg hscale₀.le _)
          nlinarith
    _ = scale₁ * (scale₀ * n ^ (1 - zeta)) ^ (1 - delta) := by
          rw [Real.mul_rpow hscale₀.le (Real.rpow_nonneg (by linarith) _),
            Real.rpow_mul (by linarith)]
    _ ≤ scale₁ * m ^ (1 - delta) :=
          mul_le_mul_of_nonneg_left hmono hscale₁
    _ ≤ z := hz

/-- The scalar upper-envelope concatenation. -/
theorem concatenate_upper_envelope
    {scale₀ scale₁ n m z delta zeta t : ℝ}
    (hscale₀ : 0 < scale₀) (hscale₀_one : scale₀ ≤ 1)
    (hscale₁ : 0 ≤ scale₁) (hn : 1 ≤ n)
    (hdelta0 : 0 ≤ delta) (hzeta0 : 0 ≤ zeta)
    (ht : delta + zeta + delta * zeta ≤ t)
    (hm0 : 0 ≤ m)
    (hm : m ≤ scale₀ * n ^ (1 + zeta))
    (hz : z ≤ scale₁ * m ^ (1 + delta)) :
    z ≤ scale₀ * scale₁ * n ^ (1 + t) := by
  have hmono :
      m ^ (1 + delta) ≤
        (scale₀ * n ^ (1 + zeta)) ^ (1 + delta) :=
    Real.rpow_le_rpow hm0 hm (by linarith)
  have hpowScale :
      scale₀ ^ (1 + delta) ≤ scale₀ := by
    calc
      scale₀ ^ (1 + delta) ≤ scale₀ ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_ge hscale₀ hscale₀_one (by linarith)
      _ = scale₀ := Real.rpow_one scale₀
  have hpowN :
      n ^ ((1 + zeta) * (1 + delta)) ≤ n ^ (1 + t) := by
    apply Real.rpow_le_rpow_of_exponent_le hn
    nlinarith
  calc
    z ≤ scale₁ * m ^ (1 + delta) := hz
    _ ≤ scale₁ * (scale₀ * n ^ (1 + zeta)) ^ (1 + delta) :=
      mul_le_mul_of_nonneg_left hmono hscale₁
    _ = scale₁ *
        (scale₀ ^ (1 + delta) *
          n ^ ((1 + zeta) * (1 + delta))) := by
      rw [Real.mul_rpow hscale₀.le (Real.rpow_nonneg (by linarith) _),
        Real.rpow_mul (by linarith)]
    _ ≤ scale₁ * (scale₀ * n ^ (1 + t)) := by
      gcongr
    _ = scale₀ * scale₁ * n ^ (1 + t) := by ring

/-- **One-step envelope concatenation.**

The startup set is kept explicit so the subsequent density theorem must pay
for the finite initial range instead of hiding it in an asymptotic phrase. -/
theorem one_step_envelope_concatenation
    {lambda q delta zeta t mu : ℝ}
    (hlambda0 : 0 < lambda) (hlambda1 : lambda < 1)
    (hdelta0 : 0 ≤ delta) (hdelta1 : delta ≤ 1)
    (hzeta0 : 0 ≤ zeta) (hzeta1 : zeta ≤ 1)
    (ht : delta + zeta + delta * zeta ≤ t)
    (hmu :
      mu = lambda * (q - a0) - zeta * (1 - lambda))
    (hmu0 : 0 < mu) :
    collatzPullback (EnvelopeGood lambda delta) ∩
          Terras.initialWindowGood zeta ∩ EnvelopeStartup mu ⊆
      EnvelopeGood (q * lambda) t := by
  intro n hn
  rcases hn with ⟨⟨hpull, hwindow⟩, hstartup⟩
  let M := Nat.log 2 n
  let m := (Terras.T^[M]) n
  have hstartup' :
      (1 + bConst) / mu ≤ (M : ℝ) := by
    simpa [EnvelopeStartup, M] using hstartup
  have hthresholdPos : 0 < (1 + bConst) / mu :=
    div_pos (by linarith [bConst_pos]) hmu0
  have hMposR : 0 < (M : ℝ) := lt_of_lt_of_le hthresholdPos hstartup'
  have hMpos : 0 < M := by exact_mod_cast hMposR
  have hnPos : 0 < n := by
    by_contra h
    have hn0 : n = 0 := Nat.eq_zero_of_not_pos h
    simp [M, hn0] at hMpos
  have hnOne : (1 : ℝ) ≤ n := by exact_mod_cast hnPos
  have hwindow' :
      ∀ k : ℕ, k ≤ M →
        Terras.centralOrbitScale k * (n : ℝ) ^ (1 - zeta) ≤
            ((Terras.T^[k]) n : ℝ) ∧
          ((Terras.T^[k]) n : ℝ) ≤
            Terras.centralOrbitScale k * (n : ℝ) ^ (1 + zeta) := by
    simpa [Terras.initialWindowGood, M] using hwindow
  have hmBounds := hwindow' M le_rfl
  have hlogm :
      (a0 - zeta) * M - 1 ≤ (Nat.log 2 m : ℝ) :=
    log_two_iterate_lower hnPos hzeta0 hzeta1 rfl hmBounds.1
  have hhorizon :
      envelopeHorizon (q * lambda) n ≤
        M + envelopeHorizon lambda m :=
    envelopeHorizon_le_add rfl hlambda0 hlambda1 hmu hmu0
      hstartup' hlogm
  have hpull' : m ∈ EnvelopeGood lambda delta := by
    simpa [collatzPullback, M, m] using hpull
  intro k hk
  by_cases hkM : k ≤ M
  ·
    have hkBounds := hwindow' k hkM
    have hzetaT : zeta ≤ t := by
      nlinarith [mul_nonneg hdelta0 hzeta0]
    have hloPow :
        (n : ℝ) ^ (1 - t) ≤ (n : ℝ) ^ (1 - zeta) :=
      Real.rpow_le_rpow_of_exponent_le hnOne (by linarith)
    have hhiPow :
        (n : ℝ) ^ (1 + zeta) ≤ (n : ℝ) ^ (1 + t) :=
      Real.rpow_le_rpow_of_exponent_le hnOne (by linarith)
    exact ⟨
      (mul_le_mul_of_nonneg_left hloPow
        (Terras.centralOrbitScale_pos k).le).trans hkBounds.1,
      hkBounds.2.trans
        (mul_le_mul_of_nonneg_left hhiPow
          (Terras.centralOrbitScale_pos k).le)⟩
  ·
    let i := k - M
    have hki : k = i + M := by
      dsimp [i]
      omega
    have hi :
        i ≤ envelopeHorizon lambda m := by
      omega
    have hiBounds := (mem_EnvelopeGood.mp hpull') i hi
    have hiter :
        (Terras.T^[k]) n = (Terras.T^[i]) m := by
      rw [hki, Function.iterate_add_apply]
    have hlo := concatenate_lower_envelope
      (hscale₀ := Terras.centralOrbitScale_pos M)
      (hscale₀_one := centralOrbitScale_le_one M)
      (hscale₁ := (Terras.centralOrbitScale_pos i).le)
      (hn := hnOne) hdelta0 hdelta1 hzeta0 ht hmBounds.1 hiBounds.1
    have hhi := concatenate_upper_envelope
      (hscale₀ := Terras.centralOrbitScale_pos M)
      (hscale₀_one := centralOrbitScale_le_one M)
      (hscale₁ := (Terras.centralOrbitScale_pos i).le)
      (hn := hnOne) hdelta0 hzeta0 ht
      (hm0 := Nat.cast_nonneg m) hmBounds.2 hiBounds.2
    constructor
    ·
      rw [hiter]
      simpa [hki, add_comm, centralOrbitScale_add] using hlo
    ·
      rw [hiter]
      simpa [hki, add_comm, centralOrbitScale_add] using hhi

end

end QuantitativeDensity

end CollatzEndpointTransport
