import jacobi.Fredholm.FreeCoreCalculus

/-!
Article: jacobi, Appendix D.4 (envelope identities and global parameter uniqueness).
The literal full-support determinant has a strictly positive derivative.
Its printed envelope identity gives uniqueness of its defining root.
Source: the regularized actual quadratures and their proved endpoint primitive.
Use: proves the free determinant envelope after subtraction of the mass trace.
-/
namespace jacobi.Fredholm
noncomputable section
open Real Set MeasureTheory jacobi.Elliptic
set_option backward.isDefEq.respectTransparency false

/-- The actual full-support core derivative has exactly the original mass and energy decomposition.
Use: proves the free determinant envelope after subtraction of the mass trace.
Article: jacobi, Appendix D.4 (envelope identities and global parameter uniqueness).
Proof: use the proved integrability of the original core derivative.
Expand its literal rational remainder and integrate the original moments;
the regularized endpoint primitive has zero boundary contribution. -/
theorem free_core_envelope {c : ℝ} (hc : c∈Ioo (0:ℝ) 1) :
    (∫ v in (0:ℝ)..1,coreParameterSlope 1 c v/sqrt (P 1 c v))=
      -(1-1)/((1-c)*(1-c*1))+
        2*edge 1 c*((3/2:ℝ)*(i2 1 c-c*1/2*response2 1 c))+
        envelopeCoefficient 1 c*((3/(2*c))*i3 1 c-(1/2)*response3 1 c) := by
  -- The exact linear combination uses the same original common weight in every term.
  have ht' : 1∈Icc (0:ℝ) 1 := by norm_num
  have hc' : c∈Icc (0:ℝ) 1 := ⟨hc.1.le,hc.2.le⟩
  have hR := response_integrable ht' hc'
  have hI2 := quadratureWeight_integrable ht' hc'
  have hI3 : IntervalIntegrable (fun v => v*quadratureWeight 1 c v) volume 0 1 := by
    simpa only [id_eq] using hI2.continuousOn_mul continuous_id.continuousOn
  have hK := (free_core_hasDerivAt hc).1
  have heq : (fun v => parameterDifference 1 c v/sqrt (P 1 c v))=
      fun v => coreParameterSlope 1 c v/sqrt (P 1 c v)-
        (2*edge 1 c*(3/2:ℝ))*(quadratureWeight 1 c v-
          (c*1/2)*((v^3/r 1 c v)*quadratureWeight 1 c v))-
        envelopeCoefficient 1 c*((3/(2*c))*(v*quadratureWeight 1 c v)-
          (1/2)*(v*((v^3/r 1 c v)*quadratureWeight 1 c v))) := by
    funext v
    unfold parameterDifference quadratureWeight
    ring
  have h : (∫ v in (0:ℝ)..1,parameterDifference 1 c v/sqrt (P 1 c v))=
      -(1-(1:ℝ))/((1-c)*(1-c*1)) := by simpa using free_remainder_integral hc
  rw [heq,intervalIntegral.integral_sub (hK.sub ((hI2.sub (hR.1.const_mul _)).const_mul _))
      (((hI3.const_mul _).sub (hR.2.const_mul _)).const_mul _),
    intervalIntegral.integral_sub hK ((hI2.sub (hR.1.const_mul _)).const_mul _),
    intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul,
    intervalIntegral.integral_sub hI2 (hR.1.const_mul _),
    intervalIntegral.integral_sub (hI3.const_mul _) (hR.2.const_mul _),
    intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul] at h
  change (∫ v in (0:ℝ)..1,coreParameterSlope 1 c v/sqrt (P 1 c v))-
    (2*edge 1 c*(3/2:ℝ))*(i2 1 c-(c*1/2)*response2 1 c)-
    envelopeCoefficient 1 c*((3/(2*c))*i3 1 c-(1/2)*response3 1 c)=
      -(1-1)/((1-c)*(1-c*1)) at h
  linear_combination h

/-- The full-support switching level is exactly one half.
Use: the mass term vanishes identically in the free envelope.
Article: jacobi, Appendix D.4 (envelope identities and global parameter uniqueness).
Proof: cancel the original nonzero normalization factor 1-chi. -/
theorem free_edge {c : ℝ} (hc : c<1) : edge 1 c=(1/2:ℝ) := by
  unfold edge
  field_simp [(sub_pos.mpr hc).ne']

/-- The actual full-support determinant has its exact chi-envelope derivative.
Use: the free branch can be ordered and its scalar defining equation has at most one solution.
Article: jacobi, Appendix D.4 (envelope identities and global parameter uniqueness).
Proof: differentiate the literal exterior, regularized core and mass.
The actual zero boundary remainder cancels the exterior derivative.
The mass contribution disappears because the switching level is one half. -/
theorem free_determinant_hasDerivAt {c : ℝ} (hc : c∈Ioo (0:ℝ) 1) :
    HasDerivAt (determinant 1)
      (envelopeCoefficient 1 c*((3/(2*c))*i3 1 c-(1/2:ℝ)*response3 1 c)) c := by
  -- The regularized calculation differentiates the original free determinant function.
  have ht : (1:ℝ)∈Icc 0 1 := by norm_num
  have h := ((exterior_parameter_hasDerivAt ht hc).add
    (by simpa only [one_mul] using (free_core_hasDerivAt hc).2)).sub
      (mass_parameter_hasDerivAt ht hc)
  convert h using 1
  · funext u
    simp only [determinant,one_mul,Pi.sub_apply,Pi.add_apply]
  · rw [free_core_envelope hc,free_edge hc.2]
    ring

/-- The printed envelope identity holds for the actual free branch, including its endpoint singularity.
Use: completes the free branch of the Fredholm envelope calculation.
Article: jacobi, Appendix D.4 (envelope identities and global parameter uniqueness).
Proof: substitute both genuine derivatives and use the exact verified
amplitude normalization; the mass term has already vanished identically. -/
theorem free_envelope {c : ℝ} (hc : c∈Ioo (0:ℝ) 1) :
    deriv (energy 1) c=(3/2:ℝ)*amplitude 1 c*deriv (determinant 1) c := by
  -- Both sides concern the original source quadratures.
  rw [(energy_parameter_hasDerivAt (by norm_num : (1:ℝ)∈Ioc 0 1) hc).deriv,
    (free_determinant_hasDerivAt hc).deriv,← mul_assoc,
    amplitude_envelope_coefficient (by norm_num : (0:ℝ)<1) hc]

/-- The true third chi-response moment is bounded by the original third state moment.
Use: proves a strictly positive actual free-energy and determinant derivative.
Article: jacobi, Appendix D.4 (envelope identities and global parameter uniqueness).
Proof: h=v^3/r lies between zero and one. Compare the original
integrable positive third-moment weights before taking the integral. -/
theorem response3_le {t c : ℝ} (ht : t∈Icc (0:ℝ) 1) (hc : c∈Icc (0:ℝ) 1) :
    response3 t c≤ i3 t c := by
  -- This estimate is valid at full support without a uniform positive lower bound for r.
  have hi : IntervalIntegrable (fun v => v*quadratureWeight t c v) volume 0 1 := by
    simpa only [id_eq] using (quadratureWeight_integrable ht hc).continuousOn_mul continuous_id.continuousOn
  apply intervalIntegral.integral_mono_on_of_le_Ioo (by norm_num : (0:ℝ)≤1)
    (response_integrable ht hc).2 hi
  intro v hv
  have hh := (h_bounds ht hc hv).2.trans hv.2.le
  nlinarith [mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right hh (quadratureWeight_bound ht hc hv).1) hv.1.le]

/-- The original free determinant has a strictly positive derivative at every nonzero physical chi.
Use: gives global uniqueness of its defining root by the mean-value theorem.
Article: jacobi, Appendix D.4 (envelope identities and global parameter uniqueness).
Proof: the response moment is at most I3, while 3/(2*chi)>1 and
I3>0. The rational envelope coefficient is positive. Multiply these
proved strict inequalities and use the actual determinant derivative. -/
theorem free_determinant_deriv_pos {c : ℝ} (hc : c∈Ioo (0:ℝ) 1) :
    0<deriv (determinant 1) c := by
  -- The sign follows from actual convergent moments, rather than an assumed energy slope.
  rw [(free_determinant_hasDerivAt hc).deriv]
  have hi := (state_mean_bounds (by norm_num : (1:ℝ)∈Icc 0 1) ⟨hc.1.le,hc.2.le⟩).1
  have hR := response3_le (by norm_num : (1:ℝ)∈Icc 0 1) ⟨hc.1.le,hc.2.le⟩
  have hratio : (1:ℝ)<3/(2*c) := (one_lt_div₀ (by linarith [hc.1])).mpr (by linarith [hc.2])
  have hprod : i3 1 c<(3/(2*c))*i3 1 c := by nlinarith [mul_pos (sub_pos.mpr hratio) hi]
  have hcoef : 0<envelopeCoefficient 1 c := by
    unfold envelopeCoefficient
    exact div_pos (by nlinarith [sq_pos_of_pos hc.1]) (sub_pos.mpr hc.2)
  exact mul_pos hcoef (by nlinarith)

/-- The actual free-branch determinant is strictly increasing on its full physical open interval.
Use: closes uniqueness for every right-hand side in the printed free-branch scalar equation.
Article: jacobi, Appendix D.4 (envelope identities and global parameter uniqueness).
Proof: every ordinary derivative exists and is strictly positive;
apply the mean-value strict monotonicity theorem on the convex interval. -/
theorem free_determinant_strictMono : StrictMonoOn (determinant 1) (Ioo (0:ℝ) 1) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioo 0 1)
  · intro c hc
    exact (free_determinant_hasDerivAt hc).continuousAt.continuousWithinAt
  · intro c hc
    exact free_determinant_deriv_pos (interior_subset hc)

/-- The defining determinant equation of the free Fredholm branch has at most one physical root.
Use: the unqualified uniqueness assertion in the source Fredholm theorem (b).
Article: jacobi, Appendix D.4 (envelope identities and global parameter uniqueness).
Proof: the actual printed determinant is strictly increasing, hence injective on (0,1). -/
theorem free_root_unique {c k d : ℝ} (hc : c∈Ioo (0:ℝ) 1) (hk : k∈Ioo (0:ℝ) 1)
    (hcD : determinant 1 c=d) (hkD : determinant 1 k=d) : c=k :=
  free_determinant_strictMono.injOn hc hk (hcD.trans hkD.symm)

end
end jacobi.Fredholm
