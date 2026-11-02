import jacobi.Fredholm.EndpointIntegration

/-!
Article: jacobi, Appendix D.4 (envelope identities and global parameter uniqueness).
Two explicit rational transport functions give exact primitives for the
difference between the determinant, energy and mass parameter derivatives.
All identities are rational algebra checked by Lean. The integration by
parts theorem proves their original singular integrals and boundary values.
Source: direct differentiation of the printed Fredholm quadratures.
Use: cancels the interior shape remainder in the Fredholm envelope identity.
-/
namespace jacobi.Fredholm
noncomputable section
open Real Set MeasureTheory jacobi.Elliptic
set_option backward.isDefEq.respectTransparency false

/-- The shape transport coefficient of the genuine endpoint primitive.
Use: cancels the interior shape remainder in the Fredholm envelope identity.
Article: jacobi, Appendix D.4 (envelope identities and global parameter uniqueness).
-/
def shapeTransport (t c v : ℝ) : ℝ := (1-c)/nu t c v-1-c^2*v^3/(2*(1-c))

/-- The exact spatial derivative of the shape transport coefficient.
Use: the weighted divergence integrates to its proved endpoint values.
Article: jacobi, Appendix D.4 (envelope identities and global parameter uniqueness).
-/
def shapeTransportSlope (t c v : ℝ) : ℝ :=
  -(1-c)*c*t/(nu t c v)^2-3*c^2*v^2/(2*(1-c))

/-- The determinant-parameter transport coefficient of the genuine endpoint primitive.
Use: cancels the chi remainder, with the compact and full-support boundary treated separately.
Article: jacobi, Appendix D.4 (envelope identities and global parameter uniqueness).
-/
def parameterTransport (t c v : ℝ) : ℝ :=
  (c*t*v^3/2+v^2+v+1+t*(c-2+t*(1-v))/nu t c v)/(1-c)

/-- The exact spatial derivative of the determinant transport coefficient.
Use: gives the actual chi weighted-divergence primitive.
Article: jacobi, Appendix D.4 (envelope identities and global parameter uniqueness).
-/
def parameterTransportSlope (t c v : ℝ) : ℝ :=
  (3*c*t*v^2/2+2*v+1+t*(-t*nu t c v-(c-2+t*(1-v))*c*t)/(nu t c v)^2)/(1-c)

/-- The normalized energy coefficient after division by three halves of the printed amplitude.
Use: removes square roots from the two exact envelope remainder identities.
Article: jacobi, Appendix D.4 (envelope identities and global parameter uniqueness).
-/
def envelopeCoefficient (t c : ℝ) : ℝ := t*c^2/(1-c)

/-- The numerator of the genuine shape derivative of the core Green integral.
Use: determines the actual determinant shape derivative after restoring the logarithmic exterior and mass trace.
Article: jacobi, Appendix D.4 (envelope identities and global parameter uniqueness).
-/
def coreShapeSlope (t c v : ℝ) : ℝ := c*L t v/nu t c v+
  t*c*(-(1-c)*(1-v)/(nu t c v)^2+L t v/nu t c v*psi t c v)

/-- The numerator of the genuine chi derivative of the core Green integral.
Use: determines the actual determinant chi derivative, including the free branch.
Article: jacobi, Appendix D.4 (envelope identities and global parameter uniqueness).
-/
def coreParameterSlope (t c v : ℝ) : ℝ := t*L t v/nu t c v+
  t*c*(t*L t v*(1-v)/(nu t c v)^2-(t/2)*(L t v/nu t c v)*(v^3/r t c v))

/-- The actual shape envelope remainder numerator before its exact derivative cancellation.
Use: integration by parts proves the shape one-form relation among the three original quadratures.
Article: jacobi, Appendix D.4 (envelope identities and global parameter uniqueness).
-/
def shapeDifference (t c v : ℝ) : ℝ := coreShapeSlope t c v-
  2*edge t c*(3/2:ℝ)*c*v^2*psi t c v-
  envelopeCoefficient t c*(v^3*psi t c v-v^3/(2*t))

/-- The actual chi envelope remainder numerator before its exact derivative cancellation.
Use: proves the second one-form relation directly from the source integrals.
Article: jacobi, Appendix D.4 (envelope identities and global parameter uniqueness).
-/
def parameterDifference (t c v : ℝ) : ℝ := coreParameterSlope t c v-
  2*edge t c*(3/2:ℝ)*(v^2-c*t/2*v^2*(v^3/r t c v))-
  envelopeCoefficient t c*((3/(2*c))*v^3-(t/2)*v^3*(v^3/r t c v))

/-- The affine Green denominator has its literal ordinary spatial derivative.
Use: both rational transport derivatives use the actual same denominator.
Article: jacobi, Appendix D.4 (envelope identities and global parameter uniqueness).
Proof: differentiate the affine polynomial and expand its normalization. -/
theorem nu_spatial_hasDerivAt (t c v : ℝ) : HasDerivAt (nu t c) (c*t) v := by
  convert ((hasDerivAt_id v).const_mul (c*t)).const_add (1-c*t) using 1
  · funext x
    unfold nu
    dsimp only [id_eq]
    ring
  · ring

/-- The shape transport slope is the genuine derivative of its original rational coefficient.
Use: discharges the ordinary derivative premise of the actual endpoint integration theorem.
Article: jacobi, Appendix D.4 (envelope identities and global parameter uniqueness).
Proof: differentiate the reciprocal affine denominator and the cubic polynomial. -/
theorem shapeTransport_hasDerivAt (t c v : ℝ) (hN : nu t c v≠0) :
    HasDerivAt (shapeTransport t c) (shapeTransportSlope t c v) v := by
  convert (((hasDerivAt_const v (1-c)).div (nu_spatial_hasDerivAt t c v) hN).sub_const 1).sub
    ((((hasDerivAt_id v).pow 3).const_mul (c^2)).div_const (2*(1-c))) using 1
  · rfl
  · dsimp [shapeTransportSlope]
    ring

/-- The chi transport slope is the genuine derivative of its original rational coefficient.
Use: both parameter envelopes are proved using ordinary spatial derivatives of explicit functions.
Article: jacobi, Appendix D.4 (envelope identities and global parameter uniqueness).
Proof: use the original cubic polynomial and quotient rule with the
actual affine Green denominator, then collect the constant coefficients. -/
theorem parameterTransport_hasDerivAt (t c v : ℝ) (hN : nu t c v≠0) :
    HasDerivAt (parameterTransport t c) (parameterTransportSlope t c v) v := by
  -- The rational derivative retains the same nonzero physical Green denominator.
  have hnum := (((hasDerivAt_id v).const_sub 1).const_mul t |>.const_add (c-2)).const_mul t
  have hpoly := (((((hasDerivAt_id v).pow 3).const_mul (c*t)).div_const 2).add
    ((hasDerivAt_id v).pow 2)).add (hasDerivAt_id v) |>.add_const 1
  convert (hpoly.add (hnum.div (nu_spatial_hasDerivAt t c v) hN)).div_const (1-c) using 1
  · rfl
  · dsimp [parameterTransportSlope]
    ring

/-- The shape envelope remainder is exactly the weighted divergence of its explicit transport.
Use: replaces an operator-family regularity argument by an independently checked exact integral primitive.
Article: jacobi, Appendix D.4 (envelope identities and global parameter uniqueness).
Proof: clear the proved nonzero physical denominators and expand the common polynomial identities. -/
theorem shape_difference_divergence {t c v : ℝ} (ht : t∈Ioc (0:ℝ) 1)
    (hc : c∈Ioo (0:ℝ) 1) (hv : v∈Ioo (0:ℝ) 1) :
    shapeDifference t c v=weightedDivergence t c v (shapeTransport t c v) (shapeTransportSlope t c v) := by
  -- This is a literal polynomial certificate; all positive denominator claims are proved separately.
  have hN := (nu_bounds ⟨ht.1.le,ht.2⟩ ⟨hc.1.le,hc.2⟩ ⟨hv.1.le,hv.2.le⟩)
  have hNp : nu t c v≠0 := (hN.1.trans_le hN.2.1).ne'
  have hR := (r_pos ⟨ht.1.le,ht.2⟩ ⟨hc.1.le,hc.2.le⟩ ⟨hv.1,hv.2.le⟩).ne'
  unfold shapeDifference coreShapeSlope envelopeCoefficient weightedDivergence shapeTransport shapeTransportSlope edge psi spatialSlope
  field_simp [ht.1.ne',hNp,hR,sub_ne_zero.mpr hc.2.ne']
  unfold N L nu r q
  ring

/-- The chi envelope remainder is exactly the weighted divergence of its explicit transport.
Use: gives the original determinant-parameter integration-by-parts cancellation, including tau=1 pointwise.
Article: jacobi, Appendix D.4 (envelope identities and global parameter uniqueness).
Proof: expand the literal rational integrands after clearing all proved nonzero physical denominators. -/
theorem parameter_difference_divergence {t c v : ℝ} (ht : t∈Ioc (0:ℝ) 1)
    (hc : c∈Ioo (0:ℝ) 1) (hv : v∈Ioo (0:ℝ) 1) :
    parameterDifference t c v=weightedDivergence t c v (parameterTransport t c v) (parameterTransportSlope t c v) := by
  -- The polynomial certificate proves equality of the actual original weighted numerators.
  have hN := (nu_bounds ⟨ht.1.le,ht.2⟩ ⟨hc.1.le,hc.2⟩ ⟨hv.1.le,hv.2.le⟩)
  have hNp : nu t c v≠0 := (hN.1.trans_le hN.2.1).ne'
  have hR := (r_pos ⟨ht.1.le,ht.2⟩ ⟨hc.1.le,hc.2.le⟩ ⟨hv.1,hv.2.le⟩).ne'
  unfold parameterDifference coreParameterSlope envelopeCoefficient weightedDivergence parameterTransport parameterTransportSlope edge spatialSlope
  field_simp [hc.1.ne',hNp,hR,sub_ne_zero.mpr hc.2.ne']
  unfold L nu r q
  ring

end
end jacobi.Fredholm
