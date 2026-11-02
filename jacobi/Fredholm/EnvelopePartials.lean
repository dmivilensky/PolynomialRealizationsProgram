import jacobi.Fredholm.CoreCalculus
import jacobi.Fredholm.EnvelopeRemainder
import jacobi.Fredholm.NormalizedEnergy

/-!
Article: jacobi, Appendix D.4 (envelope identities and global parameter uniqueness).
The two parameter derivatives below concern the original mass, energy and
regularized determinant quadratures. Exact integration by parts cancels
the logarithmic exterior term; no hypothetical density family is assumed.
Source: dominated differentiation and the verified rational primitives.
Use: the shape component of the Fredholm envelope one-form.
-/
namespace jacobi.Fredholm
noncomputable section
open Real Set MeasureTheory jacobi.Elliptic
set_option backward.isDefEq.respectTransparency false

/-- The literal normalized energy has its ordinary interior shape derivative.
Use: the shape component of the Fredholm envelope one-form.
Article: jacobi, Appendix D.4 (envelope identities and global parameter uniqueness).
Proof: differentiate the positive square-root denominator and the true
third moment, then simplify with the square of the same positive root. -/
theorem energy_shape_hasDerivAt {t c : ℝ} (ht : t∈Ioo (0:ℝ) 1)
    (hc : c∈Icc (0:ℝ) 1) :
    HasDerivAt (fun u => energy u c)
      ((3*c)^(3/2:ℝ)/sqrt t*(shape3 t c-i3 t c/(2*t))) t := by
  -- Every differentiated moment is the actual convergent integral.
  have h := ((((hasDerivAt_id t).sqrt ht.1.ne').inv (sqrt_pos.mpr ht.1).ne').const_mul
    ((3*c)^(3/2:ℝ))).mul (shape_calculus ht hc).2
  convert h using 1
  · funext u
    dsimp [energy]
    ring
  · simp only [id_eq,Pi.inv_apply]
    field_simp [(sqrt_pos.mpr ht.1).ne',ht.1.ne']
    rw [sq_sqrt ht.1.le]
    ring

/-- The literal normalized energy has its ordinary chi derivative, also at full support.
Use: the second envelope component and strict free-branch determinant monotonicity.
Article: jacobi, Appendix D.4 (envelope identities and global parameter uniqueness).
Proof: use the power rule at positive chi and the genuine third-moment
response derivative. The identity x^(p-1)=x^p/x gives the printed coefficient. -/
theorem energy_parameter_hasDerivAt {t c : ℝ} (ht : t∈Ioc (0:ℝ) 1)
    (hc : c∈Ioo (0:ℝ) 1) :
    HasDerivAt (energy t)
      ((3*c)^(3/2:ℝ)/sqrt t*((3/(2*c))*i3 t c-(t/2)*response3 t c)) c := by
  -- Positive chi fixes the real-power branch without extending outside its domain.
  have hc0 := hc.1
  have h := ((((hasDerivAt_id c).const_mul 3).rpow_const
    (p := (3/2:ℝ)) (Or.inl (by positivity : 3*c≠0))).div_const (sqrt t)).mul
    (parameter_calculus ⟨ht.1.le,ht.2⟩ hc).2
  convert h using 1
  · rfl
  · simp only [id_eq]
    rw [rpow_sub_one (by positivity : 3*c≠0)]
    field_simp
    ring

/-- The source amplitude and the rational envelope coefficient have the exact energy normalization.
Use: converts the rational quadrature envelope into the printed coefficient (3/2)*tilde_a.
Article: jacobi, Appendix D.4 (envelope identities and global parameter uniqueness).
Proof: factor the positive square root of 3*chi/tau, rewrite the
three-halves power as a square-root cube and cancel nonzero parameters. -/
theorem amplitude_envelope_coefficient {t c : ℝ} (ht : 0<t) (hc : c∈Ioo (0:ℝ) 1) :
    (3/2:ℝ)*amplitude t c*envelopeCoefficient t c=(3*c)^(3/2:ℝ)/sqrt t := by
  -- All cancellations use the original positive parameters and their square roots.
  have hc0 := hc.1
  rw [amplitude,envelopeCoefficient,delta,sqrt_div (by positivity : 0≤3*c),
    rpow_div_two_eq_sqrt 3 (by positivity : 0≤3*c),rpow_ofNat]
  have hs := sq_sqrt (show 0≤3*c by positivity)
  field_simp [ht.ne',hc.1.ne',(sub_pos.mpr hc.2).ne',(sqrt_pos.mpr ht).ne']
  nlinarith [hs]

/-- The logarithmic exterior term has its exact ordinary shape derivative.
Use: cancels the evaluated interior shape remainder in the actual determinant derivative.
Article: jacobi, Appendix D.4 (envelope identities and global parameter uniqueness).
Proof: the affine numerator and the fixed positive denominator have a
nonzero positive quotient. Differentiate its logarithm and simplify. -/
theorem exterior_shape_hasDerivAt {t c : ℝ} (ht : t∈Icc (0:ℝ) 1)
    (hc : c∈Ioo (0:ℝ) 1) :
    HasDerivAt (fun u => log ((1-c*u)/(1-c))) (-c/(1-c*t)) t := by
  -- Positivity of the actual Green normalization rules out the logarithmic pole.
  have hp : 0<1-c*t := by nlinarith [hc.2,mul_le_mul_of_nonneg_left ht.2 hc.1.le]
  convert ((((hasDerivAt_id t).const_mul c).const_sub 1).div_const (1-c)).log
    (div_pos hp (sub_pos.mpr hc.2)).ne' using 1
  simp only [id_eq]
  field_simp [(sub_pos.mpr hc.2).ne',hp.ne']
  dsimp only [id_eq]

/-- The logarithmic exterior term has its exact ordinary chi derivative.
Use: cancels the second exact integration-by-parts remainder.
Article: jacobi, Appendix D.4 (envelope identities and global parameter uniqueness).
Proof: apply the quotient and logarithm rules to the original positive
ratio, retaining both actual nonzero affine denominators. -/
theorem exterior_parameter_hasDerivAt {t c : ℝ} (ht : t∈Icc (0:ℝ) 1)
    (hc : c∈Ioo (0:ℝ) 1) :
    HasDerivAt (fun u => log ((1-u*t)/(1-u))) ((1-t)/((1-c)*(1-c*t))) c := by
  -- The same positivity estimate includes the free shape tau=1.
  have hp : 0<1-c*t := by nlinarith [hc.2,mul_le_mul_of_nonneg_left ht.2 hc.1.le]
  convert ((((hasDerivAt_id c).mul_const t).const_sub 1).div
    ((hasDerivAt_id c).const_sub 1) (sub_pos.mpr hc.2).ne').log
      (div_pos hp (sub_pos.mpr hc.2)).ne' using 1
  · funext u
    congr 1
  · simp only [id_eq,Pi.div_apply]
    field_simp
    ring

/-- The genuine shape core derivative splits into the mass and energy moments plus its exact exterior cancellation.
Use: proves the shape envelope derivative of the original determinant.
Article: jacobi, Appendix D.4 (envelope identities and global parameter uniqueness).
Proof: all three derivative integrands are integrable. Expand the
literal remainder, integrate its linear combination, and use its already
proved boundary value. The remaining integrals are exactly I3 and the
actual shape response moments. -/
theorem core_shape_envelope {t c : ℝ} (ht : t∈Ioo (0:ℝ) 1)
    (hc : c∈Ioo (0:ℝ) 1) :
    (∫ v in (0:ℝ)..1,coreShapeSlope t c v/sqrt (P t c v))=
      c/(1-c*t)+2*edge t c*((3/2:ℝ)*c*shape2 t c)+
        envelopeCoefficient t c*(shape3 t c-i3 t c/(2*t)) := by
  -- Normalize the pointwise rational remainder before using integral linearity.
  have ht' : t∈Icc (0:ℝ) 1 := ⟨ht.1.le,ht.2.le⟩
  have hc' : c∈Icc (0:ℝ) 1 := ⟨hc.1.le,hc.2.le⟩
  have hS := shape_integrable ht' hc'
  have hI : IntervalIntegrable (fun v => v*quadratureWeight t c v) volume 0 1 := by
    simpa only [id_eq] using (quadratureWeight_integrable ht' hc').continuousOn_mul continuous_id.continuousOn
  have hK := (core_shape_hasDerivAt ht hc).1
  have heq : (fun v => shapeDifference t c v/sqrt (P t c v))=
      fun v => coreShapeSlope t c v/sqrt (P t c v)-
        (2*edge t c*((3/2:ℝ)*c))*(psi t c v*quadratureWeight t c v)-
        envelopeCoefficient t c*(v*(psi t c v*quadratureWeight t c v)-
          (1/(2*t))*(v*quadratureWeight t c v)) := by
    funext v
    unfold shapeDifference quadratureWeight
    ring
  have h := shape_remainder_integral ht hc
  rw [heq,intervalIntegral.integral_sub (hK.sub (hS.1.const_mul _))
      ((hS.2.sub (hI.const_mul _)).const_mul _),
    intervalIntegral.integral_sub hK (hS.1.const_mul _),
    intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul,
    intervalIntegral.integral_sub hS.2 (hI.const_mul _),
    intervalIntegral.integral_const_mul] at h
  change (∫ v in (0:ℝ)..1,coreShapeSlope t c v/sqrt (P t c v))-
    (2*edge t c*((3/2:ℝ)*c))*shape2 t c-
    envelopeCoefficient t c*(shape3 t c-(1/(2*t))*i3 t c)=c/(1-c*t) at h
  linear_combination h

/-- The original determinant satisfies the shape component of the full envelope identity.
Use: differentiates the determinant on constant-mass curves without an assumed family of candidate operators.
Article: jacobi, Appendix D.4 (envelope identities and global parameter uniqueness).
Proof: differentiate the actual logarithmic exterior, core and mass.
The exact integrated rational primitive cancels the exterior derivative;
the remaining terms are the stated energy and mass components. -/
theorem determinant_shape_envelope {t c : ℝ} (ht : t∈Ioo (0:ℝ) 1)
    (hc : c∈Ioo (0:ℝ) 1) :
    HasDerivAt (fun u => determinant u c)
      (envelopeCoefficient t c*(shape3 t c-i3 t c/(2*t))+
        (2*edge t c-1)*((3/2:ℝ)*c*shape2 t c)) t := by
  -- The exterior term is differentiated as printed, including its dependence on tau.
  have h := ((exterior_shape_hasDerivAt ⟨ht.1.le,ht.2.le⟩ hc).add
    (core_shape_hasDerivAt ht hc).2).sub
      (mass_shape_hasDerivAt_pos ht ⟨hc.1,hc.2.le⟩).1
  convert h using 1
  · rfl
  · rw [core_shape_envelope ht hc]
    ring

/-- The actual mass has its explicitly normalized chi derivative.
Use: identifies the mass component in the second envelope identity.
Article: jacobi, Appendix D.4 (envelope identities and global parameter uniqueness).
Proof: differentiate chi times the original second moment, using its
proved ordinary parameter derivative, and collect the scalar factors. -/
theorem mass_parameter_hasDerivAt {t c : ℝ} (ht : t∈Icc (0:ℝ) 1)
    (hc : c∈Ioo (0:ℝ) 1) :
    HasDerivAt (mass t) ((3/2:ℝ)*(i2 t c-c*t/2*response2 t c)) c := by
  convert (((hasDerivAt_id c).const_mul (3/2:ℝ)).mul (parameter_calculus ht hc).1) using 1
  · rfl
  · dsimp only [id_eq]
    ring

/-- The original chi core derivative splits into its actual energy and mass moments with the exact boundary remainder.
Use: proves the second component of the genuine Fredholm envelope one-form.
Article: jacobi, Appendix D.4 (envelope identities and global parameter uniqueness).
Proof: expand the rational remainder only after all original derivative
moments have been shown integrable. Integral linearity and the verified
boundary evaluation give exactly the displayed actual moments. -/
theorem core_parameter_envelope {t c : ℝ} (ht : t∈Ioo (0:ℝ) 1)
    (hc : c∈Ioo (0:ℝ) 1) :
    (∫ v in (0:ℝ)..1,coreParameterSlope t c v/sqrt (P t c v))=
      -(1-t)/((1-c)*(1-c*t))+
        2*edge t c*((3/2:ℝ)*(i2 t c-c*t/2*response2 t c))+
        envelopeCoefficient t c*((3/(2*c))*i3 t c-(t/2)*response3 t c) := by
  -- The exact linear combination uses the same original common weight in every term.
  have ht' : t∈Icc (0:ℝ) 1 := ⟨ht.1.le,ht.2.le⟩
  have hc' : c∈Icc (0:ℝ) 1 := ⟨hc.1.le,hc.2.le⟩
  have hR := response_integrable ht' hc'
  have hI2 := quadratureWeight_integrable ht' hc'
  have hI3 : IntervalIntegrable (fun v => v*quadratureWeight t c v) volume 0 1 := by
    simpa only [id_eq] using hI2.continuousOn_mul continuous_id.continuousOn
  have hK := (core_parameter_hasDerivAt ht hc).1
  have heq : (fun v => parameterDifference t c v/sqrt (P t c v))=
      fun v => coreParameterSlope t c v/sqrt (P t c v)-
        (2*edge t c*(3/2:ℝ))*(quadratureWeight t c v-
          (c*t/2)*((v^3/r t c v)*quadratureWeight t c v))-
        envelopeCoefficient t c*((3/(2*c))*(v*quadratureWeight t c v)-
          (t/2)*(v*((v^3/r t c v)*quadratureWeight t c v))) := by
    funext v
    unfold parameterDifference quadratureWeight
    ring
  have h := parameter_remainder_integral ht hc
  rw [heq,intervalIntegral.integral_sub (hK.sub ((hI2.sub (hR.1.const_mul _)).const_mul _))
      (((hI3.const_mul _).sub (hR.2.const_mul _)).const_mul _),
    intervalIntegral.integral_sub hK ((hI2.sub (hR.1.const_mul _)).const_mul _),
    intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul,
    intervalIntegral.integral_sub hI2 (hR.1.const_mul _),
    intervalIntegral.integral_sub (hI3.const_mul _) (hR.2.const_mul _),
    intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul] at h
  change (∫ v in (0:ℝ)..1,coreParameterSlope t c v/sqrt (P t c v))-
    (2*edge t c*(3/2:ℝ))*(i2 t c-(c*t/2)*response2 t c)-
    envelopeCoefficient t c*((3/(2*c))*i3 t c-(t/2)*response3 t c)=
      -(1-t)/((1-c)*(1-c*t)) at h
  linear_combination h

/-- The actual determinant has the asserted ordinary chi envelope derivative on the interior branch.
Use: together with the shape component gives the complete interior one-form.
Article: jacobi, Appendix D.4 (envelope identities and global parameter uniqueness).
Proof: differentiate the literal determinant. Its logarithmic derivative
cancels the true integrated boundary remainder, leaving precisely the
actual mass and energy terms. -/
theorem determinant_parameter_envelope {t c : ℝ} (ht : t∈Ioo (0:ℝ) 1)
    (hc : c∈Ioo (0:ℝ) 1) :
    HasDerivAt (determinant t)
      (envelopeCoefficient t c*((3/(2*c))*i3 t c-(t/2)*response3 t c)+
        (2*edge t c-1)*((3/2:ℝ)*(i2 t c-c*t/2*response2 t c))) c := by
  -- Every term comes from a proved derivative of the original convergent quadratures.
  have h := ((exterior_parameter_hasDerivAt ⟨ht.1.le,ht.2.le⟩ hc).add
    (core_parameter_hasDerivAt ht hc).2).sub
      (mass_parameter_hasDerivAt ⟨ht.1.le,ht.2.le⟩ hc)
  convert h using 1
  · rfl
  · rw [core_parameter_envelope ht hc]
    ring

/-- Both actual parameter derivatives satisfy the printed Fredholm envelope one-form.
Use: restriction to a differentiable constant-mass curve gives Ehat'=(3/2)*tilde_a*Dhat'.
Article: jacobi, Appendix D.4 (envelope identities and global parameter uniqueness).
Proof: substitute the genuine mass, energy and determinant derivatives
in each parameter direction and use the exact positive amplitude
normalization. All remainder and endpoint terms have been evaluated. -/
theorem interior_envelope {t c : ℝ} (ht : t∈Ioo (0:ℝ) 1)
    (hc : c∈Ioo (0:ℝ) 1) :
    deriv (fun u => energy u c) t=(3/2:ℝ)*amplitude t c*
      (deriv (fun u => determinant u c) t-(2*edge t c-1)*deriv (fun u => mass u c) t) ∧
    deriv (energy t) c=(3/2:ℝ)*amplitude t c*
      (deriv (determinant t) c-(2*edge t c-1)*deriv (mass t) c) := by
  -- The common rational coefficient is identified with the source amplitude in both directions.
  have ha := amplitude_envelope_coefficient ht.1 hc
  constructor
  · rw [(energy_shape_hasDerivAt ht ⟨hc.1.le,hc.2.le⟩).deriv,
      (determinant_shape_envelope ht hc).deriv,
      (mass_shape_hasDerivAt_pos ht ⟨hc.1,hc.2.le⟩).1.deriv]
    rw [add_sub_cancel_right,← mul_assoc,ha]
  · rw [(energy_parameter_hasDerivAt ⟨ht.1,ht.2.le⟩ hc).deriv,
      (determinant_parameter_envelope ht hc).deriv,
      (mass_parameter_hasDerivAt ⟨ht.1.le,ht.2.le⟩ hc).deriv]
    rw [add_sub_cancel_right,← mul_assoc,ha]

end
end jacobi.Fredholm
