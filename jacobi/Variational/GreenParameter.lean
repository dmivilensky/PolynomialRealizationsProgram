import jacobi.Variational.GreenWard
import chebyshev2.LocalObstruction.InverseVariation

/-!
Article: jacobi, Appendix D.4 (green diagonal and determinant identities).
The existing Banach-algebra inverse derivative is applied to the genuine
Schrodinger pencil I-t*K_m. Below its proved pole it agrees with the actual
Green inverse. Its derivative is the actual R*K_m*R operator, which becomes
the literal positive Green-kernel product integral in physical coordinates.
Source: reuse of the inverse differentiation proved in chebyshev2.
Use: permits ordinary two-sided scalar derivatives while all operator identifications retain their pole hypotheses.
-/
namespace jacobi.Variational
noncomputable section
open MeasureTheory Real Set Filter
open chebyshev2.Continuum chebyshev2.Sobolev
open scoped Topology InnerProductSpace
set_option backward.isDefEq.respectTransparency false

/-- The unrestricted real-parameter kernel used only to differentiate at a proved subcritical point.
Use: permits ordinary two-sided scalar derivatives while all operator identifications retain their pole hypotheses.
Article: jacobi, Appendix D.4 (green diagonal and determinant identities).
-/
def L1Source.greenParameter (m : L1Source) (t x y : ℝ) : ℝ :=
  (1/2:ℝ)*inner ℝ (Ring.inverse (m.fredholmPencil t) (feature x)) (feature y)

/-- The differentiable parameter kernel agrees with the actual Green kernel at every proved subcritical nonnegative parameter.
Use: all parameter derivatives refer to the genuine inverse and its already proved Green identities.
Article: jacobi, Appendix D.4 (green diagonal and determinant identities).
Proof: the actual pencil is a unit and ring inverse is exactly its constructed inverse. -/
theorem L1Source.greenParameter_eq (m : L1Source) {s : ℝ} (hs : 0≤s)
    (hp : s*observe m .top<1) (x y : ℝ) :
    m.greenParameter s x y=m.fredholmGreen s hs hp x y := by
  unfold L1Source.greenParameter L1Source.fredholmGreen L1Source.fredholmResolvent
  rw [Ring.inverse_of_isUnit (m.fredholmPencil_isUnit hs hp)]
  rfl

/-- The actual pencil inverse has its genuine coupling derivative on every H1 vector.
Use: derives the true Green parameter derivative before taking scalar physical kernel values.
Article: jacobi, Appendix D.4 (green diagonal and determinant identities).
Proof: apply the existing affine inverse derivative to direction -K_m,
translate the increment to the parameter point, and identify the proved unit inverse. -/
theorem L1Source.resolvent_parameter_derivative (m : L1Source) {s : ℝ} (hs : 0≤s)
    (hp : s*observe m .top<1) (u : FeatureSpace) :
    HasDerivAt (fun t => Ring.inverse (m.fredholmPencil t) u)
      (m.fredholmResolvent s hs hp (densityOperator m.value (m.fredholmResolvent s hs hp u))) s := by
  -- The only inverse differentiation premise is the already proved actual spectral pole condition.
  let hu := m.fredholmPencil_isUnit hs hp
  have hpencil : HasDerivAt (m.fredholmPencil) (-densityOperator m.value) s := by
    change HasDerivAt (fun t => ContinuousLinearMap.id ℝ FeatureSpace-t • densityOperator m.value)
      (-densityOperator m.value) s
    simpa only [id_eq,one_smul] using
      ((hasDerivAt_id s).smul_const (densityOperator m.value)).const_sub (ContinuousLinearMap.id ℝ FeatureSpace)
  have hi := hasFDerivAt_ringInverse (𝕜 := ℝ) (R := FeatureSpace →L[ℝ] FeatureSpace) hu.unit
  rw [IsUnit.unit_spec] at hi
  have hR := hi.comp_hasDerivAt s hpencil
  have happly := (ContinuousLinearMap.apply ℝ FeatureSpace u).hasFDerivAt.comp_hasDerivAt s hR
  convert! happly using 1
  simp only [ContinuousLinearMap.mulLeftRight_apply,neg_apply,map_neg,neg_neg]
  rfl

/-- The actual Green parameter derivative is the literal nonnegative kernel-product integral.
Use: proves monotonicity in coupling and differentiates the spatial reciprocal-diagonal functional.
Article: jacobi, Appendix D.4 (green diagonal and determinant identities).
Proof: evaluate the actual inverse derivative on the two feature vectors,
move one inverse by symmetry, and use the actual density-operator form.
The feature inner values are precisely twice the true physical Green kernel. -/
theorem L1Source.greenParameter_hasDerivAt (m : L1Source) {s : ℝ} (hs : 0≤s)
    (hp : s*observe m .top<1) (x y : ℝ) :
    HasDerivAt (fun t => m.greenParameter t x y)
      (2*(∫ z,m.value z*m.fredholmGreen s hs hp x z*m.fredholmGreen s hs hp y z)) s := by
  -- Every factor in the derivative comes from the actual inverse rather than a formal resolvent symbol.
  have h := ((innerSL ℝ (feature y)).hasFDerivAt.comp_hasDerivAt s
    (m.resolvent_parameter_derivative hs hp (feature x))).const_mul (1/2:ℝ)
  have hsym := (m.fredholmResolvent_symmetric hs hp) (feature y)
    (densityOperator m.value (m.fredholmResolvent s hs hp (feature x)))
  change inner ℝ (m.fredholmResolvent s hs hp (feature y))
    (densityOperator m.value (m.fredholmResolvent s hs hp (feature x)))=
    inner ℝ (feature y) (m.fredholmResolvent s hs hp
      (densityOperator m.value (m.fredholmResolvent s hs hp (feature x)))) at hsym
  have hfeature (a b : ℝ) : inner ℝ (feature a) (m.fredholmResolvent s hs hp (feature b))=
      2*m.fredholmGreen s hs hp b a := by
    unfold L1Source.fredholmGreen
    rw [real_inner_comm (m.fredholmResolvent s hs hp (feature b))]
    ring
  convert h using 1
  · funext t
    change (1/2:ℝ)*inner ℝ (Ring.inverse (m.fredholmPencil t) (feature x)) (feature y)=
      (1/2:ℝ)*inner ℝ (feature y) (Ring.inverse (m.fredholmPencil t) (feature x))
    rw [real_inner_comm]
  · change 2*(∫ z,m.value z*m.fredholmGreen s hs hp x z*m.fredholmGreen s hs hp y z)=
      (1/2:ℝ)*inner ℝ (feature y) (m.fredholmResolvent s hs hp
        (densityOperator m.value (m.fredholmResolvent s hs hp (feature x))))
    rw [← hsym,densityOperator_inner m.integrable,← integral_const_mul,← integral_const_mul]
    apply integral_congr_ae
    exact Eventually.of_forall fun z => by
      dsimp only
      rw [hfeature,hfeature]
      ring

end
end jacobi.Variational
