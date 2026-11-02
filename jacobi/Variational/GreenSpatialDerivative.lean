import jacobi.Variational.GreenSpatialTrace

/-!
Article: jacobi, Appendix D.4 (green diagonal and determinant identities).
The unrestricted parameter kernel is used only to take ordinary derivatives
at actual nonnegative subcritical couplings. The regularized spatial
integrand is 1-1/(2g)-t*m. Its genuine derivative is the actual Green-ratio
source integral minus the original mass density. The zero-coupling
integrand is identically zero before integration.
Source: the proved actual inverse derivative and elementary quotient calculus.
Use: its proved derivatives and integrable majorant identify the spectral determinant with the spatial formula.
-/
namespace jacobi.Variational
noncomputable section
open MeasureTheory Real Filter Set chebyshev2.Continuum
open scoped Topology InnerProductSpace
set_option backward.isDefEq.respectTransparency false

/-- The actual regularized spatial determinant integrand in a free scalar parameter.
Use: its proved derivatives and integrable majorant identify the spectral determinant with the spatial formula.
Article: jacobi, Appendix D.4 (green diagonal and determinant identities).
-/
def L1Source.greenSpatialIntegrand (m : L1Source) (t x : ℝ) : ℝ :=
  1-(2*m.greenParameter t x x)⁻¹-t*m.value x

/-- The actual spatial parameter derivative written without proof-dependent coupling arguments.
Use: a single measurable function family supplies the dominated parameter integration theorem.
Article: jacobi, Appendix D.4 (green diagonal and determinant identities).
-/
def L1Source.greenSpatialDerivative (m : L1Source) (t x : ℝ) : ℝ :=
  (∫ y,m.value y*(m.greenParameter t x y/m.greenParameter t x x)^2)-m.value x

/-- The true zero-coupling inverse kernel is exactly the free exponential Green kernel.
Use: proves that the actual spatial determinant integrand has zero initial value.
Article: jacobi, Appendix D.4 (green diagonal and determinant identities).
Proof: at zero the actual pencil is the identity, whose ring inverse is itself. -/
theorem L1Source.greenParameter_zero (m : L1Source) (x y : ℝ) :
    m.greenParameter 0 x y=(1/2:ℝ)*exp (-|x-y|) := by
  have hzero : m.fredholmPencil 0=(1 : FeatureSpace →L[ℝ] FeatureSpace) := by
    apply ContinuousLinearMap.ext
    intro u
    change u-(0:ℝ) • densityOperator m.value u=u
    rw [zero_smul,sub_zero]
  unfold L1Source.greenParameter
  rw [hzero,Ring.inverse_one,one_apply_eq_self,feature_inner]

/-- The actual spatial regularized determinant integrand is identically zero at zero coupling.
Use: fixes the constant in the equality between the spatial integral and the actual spectral determinant.
Article: jacobi, Appendix D.4 (green diagonal and determinant identities).
Proof: substitute the exact free diagonal one half and the zero mass regularization. -/
theorem L1Source.greenSpatialIntegrand_zero (m : L1Source) (x : ℝ) : m.greenSpatialIntegrand 0 x=0 := by
  unfold L1Source.greenSpatialIntegrand
  rw [m.greenParameter_zero]
  norm_num

/-- The actual spatial determinant integrand has its genuine Green-ratio derivative at every below-pole nonnegative coupling.
Use: discharges the pointwise calculus premise before dominated integration in the spatial determinant formula.
Article: jacobi, Appendix D.4 (green diagonal and determinant identities).
Proof: differentiate the actual inverse diagonal and its reciprocal using
its proved positive value. The scalar quotient cancels the factor four;
constant-denominator integration gives the literal Green-ratio source term. -/
theorem L1Source.greenSpatialIntegrand_hasDerivAt (m : L1Source) {s : ℝ} (hs : 0≤s)
    (hp : s*observe m .top<1) (x : ℝ) :
    HasDerivAt (fun t => m.greenSpatialIntegrand t x) (m.greenSpatialDerivative s x) s := by
  -- The actual diagonal's strict positivity licenses the reciprocal derivative.
  have hker : HasDerivAt (fun t => m.greenParameter t x x)
      (2*(∫ y,m.value y*(m.fredholmGreen s hs hp x y)^2)) s := by
    convert m.greenParameter_hasDerivAt hs hp x x using 1
    congr 1
    apply integral_congr_ae
    exact Eventually.of_forall fun y => by ring
  have hpos : 0<m.greenParameter s x x := by rw [m.greenParameter_eq hs hp]; exact m.fredholmGreen_pos hs hp x x
  have h := ((hasDerivAt_const s (1:ℝ)).sub ((hker.const_mul 2).inv (by positivity))).sub
    ((hasDerivAt_id s).mul_const (m.value x))
  have hquot : (∫ y,m.value y*(m.fredholmGreen s hs hp x y/m.fredholmGreen s hs hp x x)^2)=
      (∫ y,m.value y*(m.fredholmGreen s hs hp x y)^2)/(m.fredholmGreen s hs hp x x)^2 := by
    simp_rw [div_pow,← mul_div_assoc]
    exact integral_div _ _
  convert h using 1
  · rfl
  · unfold L1Source.greenSpatialDerivative
    simp_rw [m.greenParameter_eq hs hp]
    rw [hquot]
    field_simp [(m.fredholmGreen_pos hs hp x x).ne']
    ring

/-- The actual spatial derivative is the integrable Green-ratio source trace already computed on the product line.
Use: makes its measurability and integrated value available to the final determinant identity.
Article: jacobi, Appendix D.4 (green diagonal and determinant identities).
Proof: identify the unrestricted parameter kernel at the stated actual coupling and apply the proved genuine Fubini trace. -/
theorem L1Source.greenSpatialDerivative_trace (m : L1Source) (hc : Continuous m.value) {s : ℝ}
    (hs : 0≤s) (hp : s*observe m .top<1) :
    Integrable (m.greenSpatialDerivative s) ∧
      (∫ x,m.greenSpatialDerivative s x)=∫ x,m.value x*(2*m.fredholmGreen s hs hp x x-1) := by
  have he : m.greenSpatialDerivative s=fun x => (∫ y,m.greenRatioSource s hs hp (x,y))-m.value x := by
    funext x
    unfold L1Source.greenSpatialDerivative L1Source.greenRatioSource L1Source.greenDiagonal
    simp_rw [m.greenParameter_eq hs hp]
  rw [he]
  exact m.greenSpatialSlope_trace hc hs hp

end
end jacobi.Variational
