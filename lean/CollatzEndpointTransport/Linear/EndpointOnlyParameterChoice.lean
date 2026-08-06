/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik
-/
import CollatzEndpointTransport.Linear.EndpointOnlyTheorem
import CollatzEndpointTransport.Linear.OptimizedLinearParameterChoice

/-!
# Endpoint Only Parameter Choice

Boundary parameter selection for the endpoint-only theorem.

For fixed contraction `r` and transport `transport`, the admissible
endpoint exponent is

  log(1/r) / log(1/transport).

Letting `r` decrease to `a0` and `transport` increase to the proved
fixed-total limit gives the exact endpoint-only headline exponent.
-/

namespace CollatzEndpointTransport

namespace OptimizedLinearPullback

open scoped Real Topology

noncomputable section

open QuantitativeDensity

def endpointParameterDelta (r transport : ℝ) : ℝ :=
  Real.log (1 / r) / Real.log (1 / transport)

/-- Scalar transport slope associated with a hypothetical
`(1 + theta)` endpoint moment.  This definition records only the parameter
calculation; it does not assert the corresponding moment estimate. -/
def momentTransportSlope (theta : ℝ) : ℝ :=
  a0 * theta / (1 + theta)

/-- Endpoint-only ceiling associated with `momentTransportSlope theta`. -/
def momentEndpointCeiling (theta : ℝ) : ℝ :=
  endpointParameterDelta a0 (momentTransportSlope theta)

/-- Exact endpoint-only exponent supported by the critical
fixed-total moment. -/
def endpointHeadlineExponent : ℝ :=
  endpointParameterDelta a0 asymptoticRateLimit

theorem endpointHeadlineExponent_eq :
    endpointHeadlineExponent =
      Real.log (1 / a0) / Real.log (3 / a0) := by
  unfold endpointHeadlineExponent endpointParameterDelta
  rw [asymptoticRateLimit_eq_a0_div_three]
  congr 1
  field_simp [ne_of_gt a0_pos]

/-- At the proved critical moment `theta = 1/2`, the generic scalar slope is
exactly the unconditional fixed-total transport limit. -/
theorem momentTransportSlope_one_half :
    momentTransportSlope (1 / 2 : ℝ) = asymptoticRateLimit := by
  rw [asymptoticRateLimit_eq_a0_div_three]
  unfold momentTransportSlope
  ring

/-- The phase-transition scalar formula specializes to the unconditional
endpoint headline at `theta = 1/2`. -/
theorem momentEndpointCeiling_one_half :
    momentEndpointCeiling (1 / 2 : ℝ) = endpointHeadlineExponent := by
  unfold momentEndpointCeiling endpointHeadlineExponent
  rw [momentTransportSlope_one_half]

theorem endpointHeadlineExponent_pos :
    0 < endpointHeadlineExponent := by
  unfold endpointHeadlineExponent endpointParameterDelta
  exact div_pos
    (log_one_div_pos a0_pos a0_lt_one)
    (log_one_div_pos asymptoticRateLimit_pos
      asymptoticRateLimit_lt_one)

theorem endpointParameterDelta_choice_tendsto :
    Filter.Tendsto
      (fun n =>
        endpointParameterDelta
          (linearChoiceQ n)
          (linearChoiceTransport n))
      Filter.atTop (nhds endpointHeadlineExponent) := by
  have hr := linearChoiceQ_tendsto
  have ht := linearChoiceTransport_tendsto
  have hnum :
      Filter.Tendsto
        (fun n => Real.log (1 / linearChoiceQ n))
        Filter.atTop (nhds (Real.log (1 / a0))) := by
    have hinv := hr.inv₀ a0_pos.ne'
    simpa [one_div] using
      hinv.log (inv_ne_zero a0_pos.ne')
  have hden :
      Filter.Tendsto
        (fun n => Real.log (1 / linearChoiceTransport n))
        Filter.atTop
          (nhds (Real.log (1 / asymptoticRateLimit))) := by
    have hinv := ht.inv₀ asymptoticRateLimit_pos.ne'
    simpa [one_div] using
      hinv.log (inv_ne_zero asymptoticRateLimit_pos.ne')
  have hden0 :
      Real.log (1 / asymptoticRateLimit) ≠ 0 :=
    ne_of_gt
      (log_one_div_pos asymptoticRateLimit_pos
        asymptoticRateLimit_lt_one)
  have hratio := hnum.div hden hden0
  change Filter.Tendsto
    (fun n =>
      Real.log (1 / linearChoiceQ n) /
        Real.log (1 / linearChoiceTransport n))
    Filter.atTop
    (nhds
      (Real.log (1 / a0) /
        Real.log (1 / asymptoticRateLimit)))
  exact hratio

theorem exists_endpoint_omega_of_delta_lt_parameter
    {r transport delta : ℝ}
    (hdelta0 : 0 < delta)
    (hr0 : 0 < r) (hr1 : r < 1)
    (htransport0 : 0 < transport)
    (htransport1 : transport < 1)
    (hdelta : delta < endpointParameterDelta r transport) :
    ∃ omega : ℝ,
      0 < omega ∧
      delta < endpointOrbitPower r omega ∧
      endpointDensityPower transport omega < 1 := by
  let Lr := Real.log (1 / r)
  let Lt := Real.log (1 / transport)
  have hLr : 0 < Lr := by
    dsimp [Lr]
    exact log_one_div_pos hr0 hr1
  have hLt : 0 < Lt := by
    dsimp [Lt]
    exact log_one_div_pos htransport0 htransport1
  have hcross :
      delta / Lr < 1 / Lt := by
    unfold endpointParameterDelta at hdelta
    dsimp [Lr, Lt]
    rw [div_lt_div_iff₀ hLr hLt]
    have := (lt_div_iff₀ hLt).mp hdelta
    nlinarith
  let omega := (delta / Lr + 1 / Lt) / 2
  have homegaLower : delta / Lr < omega := by
    dsimp [omega]
    linarith
  have homegaUpper : omega < 1 / Lt := by
    dsimp [omega]
    linarith
  have homega0 : 0 < omega := by
    have hquot : 0 < delta / Lr :=
      div_pos hdelta0 hLr
    linarith
  have hdeltaU :
      delta < endpointOrbitPower r omega := by
    unfold endpointOrbitPower powerU
    have hmul := mul_lt_mul_of_pos_right homegaLower hLr
    dsimp [Lr] at hmul
    field_simp [hLr.ne'] at hmul
    simpa [mul_comm] using hmul
  have hw :
      endpointDensityPower transport omega < 1 := by
    unfold endpointDensityPower powerU
    have hmul := mul_lt_mul_of_pos_right homegaUpper hLt
    dsimp [Lt] at hmul
    field_simp [hLt.ne'] at hmul
    simpa [mul_comm] using hmul
  exact ⟨omega, homega0, hdeltaU, hw⟩

/-- Every exponent below the endpoint boundary admits fixed interior
contraction and transport parameters. -/
theorem exists_endpoint_only_parameters
    {delta : ℝ}
    (hdelta0 : 0 < delta)
    (hdelta : delta < endpointHeadlineExponent) :
    ∃ r transport omega : ℝ,
      a0 < r ∧ r < 1 ∧
      0 < transport ∧ transport < asymptoticRateLimit ∧
      0 < omega ∧
      delta < endpointOrbitPower r omega ∧
      endpointDensityPower transport omega < 1 := by
  have hevent :
      ∀ᶠ n : ℕ in Filter.atTop,
        delta <
          endpointParameterDelta
            (linearChoiceQ n)
            (linearChoiceTransport n) :=
    endpointParameterDelta_choice_tendsto.eventually
      (Ioi_mem_nhds hdelta)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hevent
  let r := linearChoiceQ N
  let transport := linearChoiceTransport N
  have hr := linearChoiceQ_properties N
  have ht := linearChoiceTransport_properties N
  have hparam :
      delta < endpointParameterDelta r transport :=
    hN N le_rfl
  obtain ⟨omega, homega0, hdeltaU, hw⟩ :=
    exists_endpoint_omega_of_delta_lt_parameter
      hdelta0 hr.1 hr.2.2 ht.1
      (ht.2.trans asymptoticRateLimit_lt_one) hparam
  exact ⟨r, transport, omega,
    hr.2.1, hr.2.2, ht.1, ht.2,
    homega0, hdeltaU, hw⟩

/-- **Endpoint-only stretched-logarithmic theorem.** -/
theorem endpointOnlyTheorem_one
    {delta : ℝ}
    (hdelta0 : 0 < delta)
    (hdelta : delta < endpointHeadlineExponent) :
    HasNaturalDensityOne
      (quantitativeLinearDescentSet delta 1) := by
  obtain ⟨r, transport, omega,
      hra, hr1, ht0, ht1, homega, hdu, hw⟩ :=
    exists_endpoint_only_parameters hdelta0 hdelta
  exact endpointOnlyTheorem_of_transport
    hra hr1 ht0 ht1 homega hdelta0 hdu hw

end

end OptimizedLinearPullback

end CollatzEndpointTransport
