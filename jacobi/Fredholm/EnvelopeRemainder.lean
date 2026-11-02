import jacobi.Fredholm.EnvelopeTransport

/-!
Article: jacobi, Appendix D.4 (envelope identities and global parameter uniqueness).
The two original compact-core envelope remainders are evaluated by exact
integration by parts. Their boundary values cancel the literal derivatives
of log((1-chi*tau)/(1-chi)). No proposed optimizer family, ODE solution
certificate or numerical approximation is an assumption of these identities.
Source: the proved rational transport identities and endpoint integration theorem.
Use: discharges every continuity premise of shape-envelope integration by parts.
-/
namespace jacobi.Fredholm
noncomputable section
open Real Set MeasureTheory jacobi.Elliptic
set_option backward.isDefEq.respectTransparency false

/-- Both rational shape transport functions are continuous on the entire actual integration interval.
Use: discharges every continuity premise of shape-envelope integration by parts.
Article: jacobi, Appendix D.4 (envelope identities and global parameter uniqueness).
Proof: the original affine denominator is uniformly positive; the true
ordinary derivative gives continuity of the transport, and its explicit
rational slope is continuous at every closed-interval point. -/
theorem shapeTransport_continuous {t c : ℝ} (ht : t∈Icc (0:ℝ) 1) (hc : c∈Ico (0:ℝ) 1) :
    ContinuousOn (shapeTransport t c) (Icc (0:ℝ) 1) ∧
      ContinuousOn (shapeTransportSlope t c) (Icc (0:ℝ) 1) := by
  -- All divisions use the positive original Green normalization, including at v=0.
  have hp (v : ℝ) (hv : v∈Icc (0:ℝ) 1) : 0<nu t c v := by
    have hh := nu_bounds ht hc hv
    exact hh.1.trans_le hh.2.1
  constructor
  · intro v hv
    exact (shapeTransport_hasDerivAt t c v (hp v hv).ne').continuousAt.continuousWithinAt
  · intro v hv
    have hNp := hp v hv
    change 0<1-c*t*(1-v) at hNp
    apply ContinuousAt.continuousWithinAt
    unfold shapeTransportSlope nu
    fun_prop (disch := positivity)

/-- Both rational chi transport functions are continuous on the entire actual integration interval.
Use: discharges the genuine compact-core chi integration-by-parts hypotheses.
Article: jacobi, Appendix D.4 (envelope identities and global parameter uniqueness).
Proof: positivity of N_chi excludes every nonconstant denominator zero;
the original transport derivative and its explicit rational formula give continuity. -/
theorem parameterTransport_continuous {t c : ℝ} (ht : t∈Icc (0:ℝ) 1) (hc : c∈Ico (0:ℝ) 1) :
    ContinuousOn (parameterTransport t c) (Icc (0:ℝ) 1) ∧
      ContinuousOn (parameterTransportSlope t c) (Icc (0:ℝ) 1) := by
  -- The common denominator estimate is uniform over the closed spatial interval.
  have hp (v : ℝ) (hv : v∈Icc (0:ℝ) 1) : 0<nu t c v := by
    have hh := nu_bounds ht hc hv
    exact hh.1.trans_le hh.2.1
  constructor
  · intro v hv
    exact (parameterTransport_hasDerivAt t c v (hp v hv).ne').continuousAt.continuousWithinAt
  · intro v hv
    have hNp := hp v hv
    change 0<1-c*t*(1-v) at hNp
    apply ContinuousAt.continuousWithinAt
    unfold parameterTransportSlope nu
    fun_prop (disch := positivity)

/-- The original compact-core shape remainder is exactly the opposite of the logarithmic exterior derivative.
Use: cancels the shape remainder when assembling the determinant, energy and mass one-form.
Article: jacobi, Appendix D.4 (envelope identities and global parameter uniqueness).
Proof: the original rational remainder equals its proved weighted
divergence on (0,1). Apply the genuine endpoint integral theorem. Its
actual value at zero simplifies to c/(1-c*t), with all denominators positive. -/
theorem shape_remainder_integral {t c : ℝ} (ht : t∈Ioo (0:ℝ) 1) (hc : c∈Ioo (0:ℝ) 1) :
    (∫ v in (0:ℝ)..1,shapeDifference t c v/sqrt (P t c v))=c/(1-c*t) := by
  -- The original singular integrals are identified only off their two null endpoint representatives.
  have hcont := shapeTransport_continuous ⟨ht.1.le,ht.2.le⟩ ⟨hc.1.le,hc.2⟩
  have heq : (∫ v in (0:ℝ)..1,shapeDifference t c v/sqrt (P t c v))=
      ∫ v in (0:ℝ)..1,weightedDivergence t c v (shapeTransport t c v) (shapeTransportSlope t c v)/sqrt (P t c v) := by
    rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1),
      intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1),
      integral_Ioc_eq_integral_Ioo,integral_Ioc_eq_integral_Ioo]
    exact setIntegral_congr_fun measurableSet_Ioo fun v hv => by
      rw [shape_difference_divergence ⟨ht.1,ht.2.le⟩ hc hv]
  rw [heq,divergence_integral ht ⟨hc.1.le,hc.2.le⟩ _ _ hcont.1 hcont.2
    (fun v hv => shapeTransport_hasDerivAt t c v (by
      have hh := nu_bounds ⟨ht.1.le,ht.2.le⟩ ⟨hc.1.le,hc.2⟩ ⟨hv.1.le,hv.2.le⟩
      exact (hh.1.trans_le hh.2.1).ne'))]
  have hct : c*t<1 := (mul_le_mul_of_nonneg_left ht.2.le hc.1.le).trans_lt (by simpa only [mul_one] using hc.2)
  norm_num only [shapeTransport,nu,sub_zero,zero_pow (by decide : 3≠0),mul_zero,zero_div,sub_zero]
  field_simp [(sub_pos.mpr ht.2).ne',(sub_pos.mpr hct).ne']
  ring

/-- The original compact-core chi remainder is exactly the negative logarithmic exterior derivative.
Use: cancels the second remainder in the actual Fredholm envelope one-form.
Article: jacobi, Appendix D.4 (envelope identities and global parameter uniqueness).
Proof: substitute the verified rational divergence and use the genuine
convergent endpoint integral. Its zero-endpoint value is the literal
derivative of log((1-c*t)/(1-c)), with the opposite sign after integration. -/
theorem parameter_remainder_integral {t c : ℝ} (ht : t∈Ioo (0:ℝ) 1) (hc : c∈Ioo (0:ℝ) 1) :
    (∫ v in (0:ℝ)..1,parameterDifference t c v/sqrt (P t c v))=
      -(1-t)/((1-c)*(1-c*t)) := by
  -- Every endpoint and denominator condition is discharged from the original physical parameter range.
  have hcont := parameterTransport_continuous ⟨ht.1.le,ht.2.le⟩ ⟨hc.1.le,hc.2⟩
  have heq : (∫ v in (0:ℝ)..1,parameterDifference t c v/sqrt (P t c v))=
      ∫ v in (0:ℝ)..1,weightedDivergence t c v (parameterTransport t c v) (parameterTransportSlope t c v)/sqrt (P t c v) := by
    rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1),
      intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1),
      integral_Ioc_eq_integral_Ioo,integral_Ioc_eq_integral_Ioo]
    exact setIntegral_congr_fun measurableSet_Ioo fun v hv => by
      rw [parameter_difference_divergence ⟨ht.1,ht.2.le⟩ hc hv]
  rw [heq,divergence_integral ht ⟨hc.1.le,hc.2.le⟩ _ _ hcont.1 hcont.2
    (fun v hv => parameterTransport_hasDerivAt t c v (by
      have hh := nu_bounds ⟨ht.1.le,ht.2.le⟩ ⟨hc.1.le,hc.2⟩ ⟨hv.1.le,hv.2.le⟩
      exact (hh.1.trans_le hh.2.1).ne'))]
  have hct : c*t<1 := (mul_le_mul_of_nonneg_left ht.2.le hc.1.le).trans_lt (by simpa only [mul_one] using hc.2)
  norm_num only [parameterTransport,nu,sub_zero,zero_pow (by decide : 3≠0),zero_pow (by decide : 2≠0),
    mul_zero,zero_div,zero_add,add_zero]
  field_simp [(sub_pos.mpr ht.2).ne',(sub_pos.mpr hct).ne',(sub_pos.mpr hc.2).ne']
  field_simp [show 1-t*c≠0 by nlinarith [hct]]
  ring

end
end jacobi.Fredholm
