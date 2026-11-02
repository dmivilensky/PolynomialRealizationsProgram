import jacobi.Hankel.IncomingAmplitude

/-!
Article: jacobi, Lemma E.1.
Use: outgoingSlopeOperator and besselAmplitudeSlope_analytic retain the genuine slope integral as one bounded linear functional in the original Banach space.
-/
namespace jacobi.Hankel
noncomputable section
open Set Filter MeasureTheory
open scoped Topology BoundedContinuousFunction
set_option backward.isDefEq.respectTransparency false

/-- The actual outgoing Fourier slope evaluated at a fixed original spatial point is complex linear in the original amplitude.
Use: outgoingSlopeOperator and besselAmplitudeSlope_analytic retain the genuine slope integral as one bounded linear functional in the original Banach space.
Article: jacobi, Lemma E.1.
-/
def outgoingSlopeLinear {R : ℝ} (hR : 0<R) (x : ℝ) : OutgoingSpace →ₗ[ℂ] ℂ where
  toFun f := outgoingSlope (inverseSquare R) f x
  map_add' f g := by
    have hf := (outgoingFourier_integrable (outgoingSource_integrable (inverseSquare_integrable hR) f)).integrableOn (s := Ioi x)
    have hg := (outgoingFourier_integrable (outgoingSource_integrable (inverseSquare_integrable hR) g)).integrableOn (s := Ioi x)
    unfold outgoingSlope tailPrimitive
    simp only [BoundedContinuousFunction.add_apply,mul_add]
    rw [integral_add hf hg]
    ring
  map_smul' c f := by
    unfold outgoingSlope tailPrimitive
    simp only [BoundedContinuousFunction.smul_apply,smul_eq_mul]
    simp_rw [show ∀ y : ℝ,Complex.exp (2*(y:ℂ)*Complex.I)*((inverseSquare R y:ℂ)*(c*f y))=
      c*(Complex.exp (2*(y:ℂ)*Complex.I)*((inverseSquare R y:ℂ)*f y)) from fun y => by ring]
    rw [integral_const_mul]
    simp only [RingHom.id_apply]
    ring

/-- The genuine outgoing slope integral at a fixed original ray point is a complex bounded linear functional.
Use: besselAmplitudeSlope_analytic obtains actual order analyticity from the genuine Banach-valued amplitude, without assuming that a spatial derivative preserves parameter analyticity.
Article: jacobi, Lemma E.1.
-/
def outgoingSlopeOperator {R x : ℝ} (hR : 0<R) (hx : R≤x) : OutgoingSpace →L[ℂ] ℂ :=
  (outgoingSlopeLinear hR x).mkContinuous (1/x) (fun f =>
    (outgoingSlope_ray_bound hR hx f (fun y _ => f.norm_coe_le_norm y)).trans_eq (by ring))

/-- The genuine outgoing Bessel slope is holomorphic in original complex order on the actual common contraction domain.
Use: outgoing and incoming Bessel connection coefficients are formed from genuinely analytic original Jost Cauchy data.
Article: jacobi, Lemma E.1.
Proof: the actual slope is minus the original Bessel coefficient times the proved bounded linear Fourier functional of the actual analytic Banach amplitude. -/
theorem besselAmplitudeSlope_analytic {R x : ℝ} (hR : 0<R) (hx : R≤x) {a : ℂ}
    (ha : ‖besselCoefficient a‖/R<1) :
    AnalyticAt ℂ (fun b : ℂ => besselAmplitudeSlope hR b x) a := by
  have hS := ((outgoingSlopeOperator hR hx).analyticAt _).comp (besselAmplitude_analytic hR ha)
  have hc : AnalyticAt ℂ (fun b : ℂ => -besselCoefficient b) a := by unfold besselCoefficient; fun_prop
  exact hc.mul hS

/-- The genuine incoming Bessel slope is holomorphic in original complex order on the same common domain.
Use: the true Bessel connection coefficients admit a complex-order identity theorem, transferring their actual real numbered-zero phase to a common complex disk.
Article: jacobi, Lemma E.1.
Proof: conjugate both the original complex argument and the proved analytic outgoing slope. The actual coefficient norm domain is open and conjugation-invariant, so complex differentiability there gives genuine analyticity. -/
theorem incomingAmplitudeSlope_analytic {R x : ℝ} (hR : 0<R) (hx : R≤x) {a : ℂ}
    (ha : ‖besselCoefficient a‖/R<1) :
    AnalyticAt ℂ (fun b : ℂ => incomingAmplitudeSlope hR b x) a := by
  -- This uses a bounded functional of the actual Banach solution rather than an unproved mixed-derivative interchange.
  have hU : IsOpen {b : ℂ | ‖besselCoefficient b‖/R<1} :=
    isOpen_lt (by unfold besselCoefficient; fun_prop) continuous_const
  apply DifferentiableOn.analyticAt (s := {b : ℂ | ‖besselCoefficient b‖/R<1}) ?_ (hU.mem_nhds ha)
  intro b hb
  change ‖besselCoefficient b‖/R<1 at hb
  have hbc : ‖besselCoefficient (star b)‖/R<1 := by
    simpa only [besselCoefficient_star,norm_star] using hb
  have hd := (besselAmplitudeSlope_analytic hR hx hbc).differentiableAt.star_conj
  simp only [Function.comp_def,← Complex.star_def,star_star] at hd
  have he : DifferentiableAt ℂ (fun b : ℂ => incomingAmplitudeSlope hR b x) b := by
    convert! hd using 1
  exact he.differentiableWithinAt

end
end jacobi.Hankel
