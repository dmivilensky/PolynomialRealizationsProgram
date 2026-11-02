import jacobi.Fredholm.EnvelopeCurves

/-!
Article: jacobi, Appendix D.4 (envelope identities and global parameter uniqueness).
The actual mass/determinant Jacobian has a strict sign throughout the
physical interior. Consequently every genuine constant-mass curve with
increasing shape has strictly decreasing determinant, including the exact
derivative sign needed for the scalar-root uniqueness argument.
Source: the proved covariance, response-mean and actual envelope identities.
Use: qualifies the actual mass constraint and fixes the orientation of its implicit curve.
-/
namespace jacobi.Fredholm
noncomputable section
open Real Set MeasureTheory jacobi.Elliptic
set_option backward.isDefEq.respectTransparency false

/-- Both components of the actual normalized mass gradient are strictly positive.
Use: qualifies the actual mass constraint and fixes the orientation of its implicit curve.
Article: jacobi, Appendix D.4 (envelope identities and global parameter uniqueness).
Proof: the shape component is the proved positive derivative.
The ordinary chi derivative is unique, so its previously proved positive
value equals the explicit gradient component. -/
theorem massGradient_pos {t c : ℝ} (ht : t∈Ioo (0:ℝ) 1) (hc : c∈Ioo (0:ℝ) 1) :
    0<(massGradient t c).1 ∧ 0<(massGradient t c).2 := by
  -- Constraint qualification is established for the literal original mass.
  refine ⟨(mass_shape_hasDerivAt_pos ht ⟨hc.1,hc.2.le⟩).2,?_⟩
  obtain ⟨D,hD,hpos⟩ := mass_parameter_hasDerivAt_pos ⟨ht.1.le,ht.2.le⟩ hc
  have he := hD.unique (mass_parameter_hasDerivAt ⟨ht.1.le,ht.2.le⟩ hc)
  change 0<(3/2:ℝ)*(i2 t c-c*t/2*response2 t c)
  rwa [← he]

/-- The true determinant strictly decreases in the oriented constant-mass tangent direction everywhere in the interior.
Use: the full actual Jacobian sign for the source's uniqueness proof, rather than an assumed monotonicity of a proposed graph.
Article: jacobi, Appendix D.4 (envelope identities and global parameter uniqueness).
Proof: subtract the common mass-logarithmic derivative from each energy
component. The shape covariance leaves a strictly negative term
-I3/(2*tau), while the response-mean inequality makes the chi component
nonnegative. Positive mass partials and the exact envelope cancellation
give the strict determinant Jacobian sign. -/
theorem determinant_mass_jacobian_neg {t c : ℝ} (ht : t∈Ioo (0:ℝ) 1) (hc : c∈Ioo (0:ℝ) 1) :
    (determinantGradient t c).1*(massGradient t c).2-
      (determinantGradient t c).2*(massGradient t c).1<0 := by
  -- Both corrected energy components use the same true moment ratio.
  have ht' : t∈Icc (0:ℝ) 1 := ⟨ht.1.le,ht.2.le⟩
  have hc' : c∈Icc (0:ℝ) 1 := ⟨hc.1.le,hc.2.le⟩
  have hI2 := i2_pos ht' hc'
  have hI3 := (state_mean_bounds ht' hc').1
  have hM := massGradient_pos ht hc
  have hS : 0<shape2 t c := (mul_pos_iff_of_pos_left
    (mul_pos (by norm_num : (0:ℝ)<3/2) hc.1)).mp hM.1
  let Q := i3 t c/(c*i2 t c)
  let U := shape3 t c-i3 t c/(2*t)
  let V := (3/(2*c))*i3 t c-(t/2)*response3 t c
  have hU : U-Q*(massGradient t c).1<0 := by
    have hid : U-Q*(massGradient t c).1=
        (shape3 t c*i2 t c-(3/2:ℝ)*shape2 t c*i3 t c)/i2 t c-i3 t c/(2*t) := by
      dsimp only [U,Q,massGradient,Prod.fst]
      field_simp [hI2.ne',hc.1.ne']
      ring
    rw [hid]
    have hcov := shape_covariance ⟨ht.1,ht.2.le⟩ hc'
    have hneg : shape3 t c*i2 t c-(3/2:ℝ)*shape2 t c*i3 t c≤0 := by
      nlinarith [mul_pos hS hI3]
    exact sub_neg.mpr ((div_nonpos_of_nonpos_of_nonneg hneg hI2.le).trans_lt
      (div_pos hI3 (mul_pos (by norm_num) ht.1)))
  have hV : 0≤V-Q*(massGradient t c).2 := by
    have hid : V-Q*(massGradient t c).2=
        t/(2*i2 t c)*((3/2:ℝ)*response2 t c*i3 t c-response3 t c*i2 t c) := by
      dsimp only [V,Q,massGradient,Prod.snd]
      field_simp [hI2.ne',hc.1.ne']
      ring
    rw [hid]
    exact mul_nonneg (div_nonneg ht.1.le (by positivity))
      (sub_nonneg.mpr (response_mean_bound ht' hc'))
  have hJ : (U-Q*(massGradient t c).1)*(massGradient t c).2-
      (V-Q*(massGradient t c).2)*(massGradient t c).1<0 := by
    have hn := mul_neg_of_neg_of_pos hU hM.2
    have hp := mul_nonneg hV hM.1.le
    linarith
  have hK : 0<envelopeCoefficient t c :=
    div_pos (mul_pos ht.1 (sq_pos_of_pos hc.1)) (sub_pos.mpr hc.2)
  have heq : (determinantGradient t c).1*(massGradient t c).2-
      (determinantGradient t c).2*(massGradient t c).1=
      envelopeCoefficient t c*((U-Q*(massGradient t c).1)*(massGradient t c).2-
        (V-Q*(massGradient t c).2)*(massGradient t c).1) := by
    dsimp only [determinantGradient,U,V,Prod.fst,Prod.snd]
    ring
  rw [heq]
  exact mul_neg_of_pos_of_neg hK hJ

/-- Every actual differentiable constant-mass graph has a strictly negative determinant derivative.
Use: orders the defining determinant along any genuine local implicit mass graph.
Article: jacobi, Appendix D.4 (envelope identities and global parameter uniqueness).
Proof: the actual chain rule gives m_tau+m_chi*k'=0 and the true
determinant derivative. Multiply that derivative by positive m_chi;
the mass relation reduces it to the already negative actual Jacobian. -/
theorem mass_graph_determinant_deriv_neg {k : ℝ → ℝ} {t b : ℝ}
    (ht : t∈Ioo (0:ℝ) 1) (hc : k t∈Ioo (0:ℝ) 1)
    (hk : HasDerivAt k b t) (hm : HasDerivAt (fun u => mass u (k u)) 0 t) :
    deriv (fun u => determinant u (k u)) t<0 := by
  -- This theorem concerns an arbitrary actual graph, with no asserted derivative formula left unchecked.
  have hM := curve_hasDerivAt_of_partials mass massGradient
    (fun u hu v hv => (mass_shape_hasDerivAt_pos hu ⟨hv.1,hv.2.le⟩).1)
    (fun u hu v hv => mass_parameter_hasDerivAt ⟨hu.1.le,hu.2.le⟩ hv)
    (hasDerivAt_id t) hk ht hc (gradients_continuousAt ht hc).1
  have hD := curve_hasDerivAt_of_partials determinant determinantGradient
    (fun u hu v hv => determinant_shape_envelope hu hv)
    (fun u hu v hv => determinant_parameter_envelope hu hv)
    (hasDerivAt_id t) hk ht hc (gradients_continuousAt ht hc).2.2
  have hzero := hM.unique hm
  simp only [id_eq] at hD hzero
  rw [hD.deriv]
  have hneg := determinant_mass_jacobian_neg ht hc
  have hpos := (massGradient_pos ht hc).2
  have heq : ((determinantGradient t (k t)).1*1+(determinantGradient t (k t)).2*b)*
      (massGradient t (k t)).2=
      (determinantGradient t (k t)).1*(massGradient t (k t)).2-
        (determinantGradient t (k t)).2*(massGradient t (k t)).1 := by
    linear_combination (determinantGradient t (k t)).2*hzero
  have hh := heq.trans_lt hneg
  nlinarith

end
end jacobi.Fredholm
