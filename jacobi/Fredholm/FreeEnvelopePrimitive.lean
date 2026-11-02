import jacobi.Fredholm.EnvelopePartials

/-!
Article: jacobi, Appendix D.4 (envelope identities and global parameter uniqueness).
At tau=1 the apparent zero-coordinate singularity is removable. The
transport primitive is explicitly regularized before applying the
fundamental theorem of calculus, so its two endpoint values are genuine.
Source: exact factorization r(1,chi,v)=v^2*(1+chi*v).
Use: writes the true chi-envelope primitive continuously at zero.
-/
namespace jacobi.Fredholm
noncomputable section
open Real Set MeasureTheory jacobi.Elliptic
set_option backward.isDefEq.respectTransparency false

/-- The regularized free-branch transport numerator.
Use: writes the true chi-envelope primitive continuously at zero.
Article: jacobi, Appendix D.4 (envelope identities and global parameter uniqueness).
-/
def freeTransportNumerator (c v : ℝ) : ℝ :=
  v*(2+(3*c-c^2)*v+c^2*v^2)

/-- The actual spatial slope of the regularized transport numerator.
Use: differentiates the free-branch primitive by an ordinary quotient rule.
Article: jacobi, Appendix D.4 (envelope identities and global parameter uniqueness).
-/
def freeTransportNumeratorSlope (c v : ℝ) : ℝ :=
  2+2*(3*c-c^2)*v+3*c^2*v^2

/-- The continuous regularized transport coefficient at full support.
Use: its product with sqrt(1-v)/sqrt(1+chi*v) is the genuine endpoint primitive.
Article: jacobi, Appendix D.4 (envelope identities and global parameter uniqueness).
-/
def freeTransport (c v : ℝ) : ℝ :=
  freeTransportNumerator c v/(2*(1-c)*nu 1 c v)

/-- The explicit spatial derivative of the regularized free transport.
Use: proves the integrable derivative and both endpoint cancellations.
Article: jacobi, Appendix D.4 (envelope identities and global parameter uniqueness).
-/
def freeTransportSlope (c v : ℝ) : ℝ :=
  (freeTransportNumeratorSlope c v*nu 1 c v-freeTransportNumerator c v*c)/
    (2*(1-c)*(nu 1 c v)^2)

/-- The free transport has its asserted genuine spatial derivative.
Use: ordinary differentiation of the regularized free-envelope primitive.
Article: jacobi, Appendix D.4 (envelope identities and global parameter uniqueness).
Proof: differentiate the cubic numerator and affine denominator and
collect the fixed nonzero normalization factors by real field algebra. -/
theorem freeTransport_hasDerivAt {c v : ℝ} (hc : c≠1) (hn : nu 1 c v≠0) :
    HasDerivAt (freeTransport c) (freeTransportSlope c v) v := by
  -- The endpoint regularization is explicit; no derivative is inferred from a limit of singular formulas.
  have hN : HasDerivAt (freeTransportNumerator c) (freeTransportNumeratorSlope c v) v := by
    convert (hasDerivAt_id v).mul (((((hasDerivAt_id v).const_mul (3*c-c^2)).const_add 2).add
      (((hasDerivAt_id v).pow 2).const_mul (c^2)))) using 1
    · rfl
    · dsimp [freeTransportNumeratorSlope]
      ring
  have h := hN.div ((nu_spatial_hasDerivAt 1 c v).const_mul (2*(1-c)))
    (mul_ne_zero (mul_ne_zero (by norm_num) (sub_ne_zero.mpr (Ne.symm hc))) hn)
  convert h using 1
  · rfl
  · dsimp [freeTransportSlope]
    field_simp

/-- The free-branch rational transport divergence has its exact removable zero factor.
Use: identifies the regularized primitive derivative with the actual original chi-envelope remainder.
Article: jacobi, Appendix D.4 (envelope identities and global parameter uniqueness).
Proof: use r=v^2*(1+chi*v), clear the physical nonzero denominators
and verify the resulting polynomial identity. -/
theorem free_difference_identity {c v : ℝ} (hc : c∈Ioo (0:ℝ) 1)
    (hv : v∈Ioo (0:ℝ) 1) :
    parameterDifference 1 c v=v*((1-v)*freeTransportSlope c v-freeTransport c v/2-
      (1-v)*freeTransport c v*c/(2*(1+c*v))) := by
  -- Cancellation concerns the literal original remainder, not a redefined integral.
  have hn := nu_bounds (by norm_num : (1:ℝ)∈Icc 0 1) ⟨hc.1.le,hc.2⟩ ⟨hv.1.le,hv.2.le⟩
  have hn0 := (hn.1.trans_le hn.2.1).ne'
  have hR : 0<1+c*v := by nlinarith [mul_pos hc.1 hv.1]
  have hr := (r_pos (by norm_num : (1:ℝ)∈Icc 0 1)
    ⟨hc.1.le,hc.2.le⟩ ⟨hv.1,hv.2.le⟩).ne'
  unfold parameterDifference coreParameterSlope envelopeCoefficient edge
    freeTransportSlope freeTransport freeTransportNumerator freeTransportNumeratorSlope
  field_simp [hc.1.ne',(sub_pos.mpr hc.2).ne',hn0,hR.ne',hr]
  unfold L nu r q
  ring

/-- The free-branch square-root denominator has its actual removable endpoint factorization.
Use: restores the printed singular integrand from a continuous coefficient times the common endpoint weight.
Article: jacobi, Appendix D.4 (envelope identities and global parameter uniqueness).
Proof: factor the literal polynomial, then use positive v and the
nonnegative factors in the square-root product identity. -/
theorem free_sqrt {c v : ℝ} (hv : v∈Ioo (0:ℝ) 1) :
    sqrt (P 1 c v)=v*sqrt (1-v)*sqrt (1+c*v) := by
  -- The positive coordinate selects v, rather than |v|, when taking sqrt(v^2).
  have hr : r 1 c v=v^2*(1+c*v) := by unfold r q; ring
  rw [P,hr,sqrt_mul (sub_pos.mpr hv.2).le,sqrt_mul (sq_nonneg v),sqrt_sq hv.1.le]
  ring

/-- The actual free-branch chi-envelope remainder has zero integral with no additional endpoint premise.
Use: closes the boundary case needed for uniqueness of the printed free determinant root.
Article: jacobi, Appendix D.4 (envelope identities and global parameter uniqueness).
Proof: the regularized primitive is continuous at both endpoints and
vanishes at each. Its true derivative is a continuous coefficient times
the integrable square-root endpoint weight. Apply the fundamental theorem
of calculus and restore the original remainder off the null endpoints. -/
theorem free_remainder_integral {c : ℝ} (hc : c∈Ioo (0:ℝ) 1) :
    (∫ v in (0:ℝ)..1,parameterDifference 1 c v/sqrt (P 1 c v))=0 := by
  -- Regularize before applying the endpoint theorem; r(1,c,0)=0 cannot be inverted continuously.
  have hn (v : ℝ) (hv : v∈Icc (0:ℝ) 1) : 0<nu 1 c v := by
    have h := nu_bounds (by norm_num : (1:ℝ)∈Icc 0 1) ⟨hc.1.le,hc.2⟩ hv
    exact h.1.trans_le h.2.1
  have hr (v : ℝ) (hv : v∈Icc (0:ℝ) 1) : 0<1+c*v := by
    nlinarith [mul_nonneg hc.1.le hv.1]
  have hU : ContinuousOn (freeTransport c) (Icc (0:ℝ) 1) := fun v hv =>
    (freeTransport_hasDerivAt (ne_of_lt hc.2) (hn v hv).ne').continuousAt.continuousWithinAt
  have hD : ContinuousOn (freeTransportSlope c) (Icc (0:ℝ) 1) := by
    intro v hv
    have hn0 : 0<1-c*1*(1-v) := hn v hv
    have hc1 := sub_pos.mpr hc.2
    apply ContinuousAt.continuousWithinAt
    unfold freeTransportSlope freeTransportNumeratorSlope freeTransportNumerator nu
    fun_prop (disch := positivity)
  let B := fun v => (1-v)*freeTransportSlope c v-freeTransport c v/2-
    (1-v)*freeTransport c v*c/(2*(1+c*v))
  have he : ContinuousOn (fun v : ℝ => 1-v) (Icc 0 1) := continuousOn_const.sub continuousOn_id
  have hR : ContinuousOn (fun v : ℝ => 1+c*v) (Icc 0 1) := by fun_prop
  have hB : ContinuousOn B (Icc (0:ℝ) 1) :=
    ((he.mul hD).sub (hU.div_const 2)).sub
      (((he.mul hU).mul continuousOn_const).div (continuousOn_const.mul hR)
        (fun v hv => mul_ne_zero (by norm_num) (hr v hv).ne'))
  have hi : IntervalIntegrable (fun v => B v/sqrt (1+c*v)*endpointWeight v) volume 0 1 :=
    endpointWeight_integrable.continuousOn_mul (by
      simpa only [uIcc_of_le (by norm_num : (0:ℝ)≤1),Pi.div_apply] using
        (show ContinuousOn (fun v => B v/sqrt (1+c*v)) (Icc (0:ℝ) 1) from
          fun v hv => (hB v hv).div (hR.sqrt v hv) (sqrt_pos.mpr (hr v hv)).ne'))
  have hprim : ContinuousOn (fun v => freeTransport c v*sqrt (1-v)/sqrt (1+c*v)) (Icc (0:ℝ) 1) :=
    (hU.mul he.sqrt).div hR.sqrt (fun v hv => (sqrt_pos.mpr (hr v hv)).ne')
  have hd (v : ℝ) (hv : v∈Ioo (0:ℝ) 1) :
      HasDerivAt (fun x => freeTransport c x*sqrt (1-x)/sqrt (1+c*x))
        (B v/sqrt (1+c*v)*endpointWeight v) v := by
    have h := ((freeTransport_hasDerivAt (ne_of_lt hc.2) (hn v ⟨hv.1.le,hv.2.le⟩).ne').mul
      (((hasDerivAt_id v).const_sub 1).sqrt (sub_pos.mpr hv.2).ne')).div
        ((((hasDerivAt_id v).const_mul c).const_add 1).sqrt (hr v ⟨hv.1.le,hv.2.le⟩).ne')
        (sqrt_pos.mpr (hr v ⟨hv.1.le,hv.2.le⟩)).ne'
    convert h using 1
    · rfl
    · have hr' : 0<1+v*c := by simpa only [mul_comm c v] using hr v ⟨hv.1.le,hv.2.le⟩
      simp only [B,id_eq,Pi.mul_apply,mul_comm c v]
      unfold endpointWeight
      field_simp [(sqrt_pos.mpr (sub_pos.mpr hv.2)).ne',
        (sqrt_pos.mpr hr').ne',hr'.ne']
      ring_nf
      simp only [sq_sqrt (sub_pos.mpr hv.2).le,sq_sqrt hr'.le]
      ring
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    (by norm_num : (0:ℝ)≤1) hprim hd hi
  have heq : (∫ v in (0:ℝ)..1,parameterDifference 1 c v/sqrt (P 1 c v))=
      ∫ v in (0:ℝ)..1,B v/sqrt (1+c*v)*endpointWeight v := by
    apply intervalIntegral.integral_congr_uIoo
    intro v hv
    have hv' : v∈Ioo (0:ℝ) 1 := by simpa only [uIoo_of_le (by norm_num : (0:ℝ)≤1)] using hv
    dsimp only
    rw [free_difference_identity hc hv',free_sqrt hv']
    dsimp only [B]
    unfold endpointWeight
    field_simp [hv'.1.ne']
  rw [heq,hFTC]
  simp [freeTransport,freeTransportNumerator]

end
end jacobi.Fredholm
