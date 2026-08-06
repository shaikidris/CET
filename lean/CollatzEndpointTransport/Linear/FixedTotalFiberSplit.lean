/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik
-/
import CollatzEndpointTransport.Linear.FixedTotalEndpointTarget

/-!
# Fixed Total Fiber Split

The elementary heavy/ordinary fiber split used by the fixed-total linear
pullback.

The estimate is deliberately stated over nonnegative reals.  It is the
pointwise form of the threshold argument: either a fiber is no larger than
`E^2` times its reference average, or its source mass is paid for by the
critical `3/2`-moment with the factor `E⁻¹`.
-/

namespace CollatzEndpointTransport

namespace FixedTotal

noncomputable section

/-- Pointwise heavy/ordinary split at reference size `R` and total mass
`N`. -/
theorem fiber_le_ordinary_add_critical
    {E N R f : ℝ}
    (hE : 0 < E) (hN : 0 < N) (hR : 0 < R) (hf : 0 ≤ f) :
    f ≤
      E ^ 2 * N / R +
        E⁻¹ * Real.sqrt (R / N) * f * Real.sqrt f := by
  have hRN : 0 ≤ R / N := by positivity
  have hsqrtRN : 0 ≤ Real.sqrt (R / N) := Real.sqrt_nonneg _
  have hsqrtf : 0 ≤ Real.sqrt f := Real.sqrt_nonneg _
  by_cases hsmall : f ≤ E ^ 2 * N / R
  · exact hsmall.trans (le_add_of_nonneg_right (by positivity))
  · have hlarge : E ^ 2 * N / R < f := lt_of_not_ge hsmall
    have hcross : E ^ 2 * N < f * R := by
      exact (div_lt_iff₀ hR).mp (by simpa [mul_assoc] using hlarge)
    have hsq :
        E ^ 2 ≤
          (Real.sqrt (R / N) * Real.sqrt f) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hRN, Real.sq_sqrt hf]
      apply le_of_lt
      rw [div_mul_eq_mul_div]
      apply (lt_div_iff₀ hN).2
      nlinarith
    have hroot :
        E ≤ Real.sqrt (R / N) * Real.sqrt f :=
      (sq_le_sq₀ hE.le (mul_nonneg hsqrtRN hsqrtf)).mp hsq
    have hcritical :
        f ≤
          E⁻¹ * Real.sqrt (R / N) * f * Real.sqrt f := by
      calc
        f = E⁻¹ * E * f := by
          field_simp [ne_of_gt hE]
        _ ≤ E⁻¹ *
            (Real.sqrt (R / N) * Real.sqrt f) * f := by
          gcongr
        _ = E⁻¹ * Real.sqrt (R / N) * f * Real.sqrt f := by
          ring
    exact hcritical.trans (le_add_of_nonneg_left (by positivity))

end

end FixedTotal

end CollatzEndpointTransport
