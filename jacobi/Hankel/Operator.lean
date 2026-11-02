import jacobi.Hankel.Kernel
import jacobi.Hankel.Potential
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Topology.ContinuousMap.Bounded.Normed

/-!
Article: jacobi, Lemma E.1.
Use: outgoingOperator, outgoingPencil and the analytic Jost inverse keep one fixed function space for the whole complex-order neighborhood.
-/
namespace jacobi.Hankel
noncomputable section
open Real Set Filter MeasureTheory
open scoped Topology BoundedContinuousFunction
set_option backward.isDefEq.respectTransparency false

/-- The complex Banach space in which the outgoing Jost integral equation is solved.
Use: outgoingOperator, outgoingPencil and the analytic Jost inverse keep one fixed function space for the whole complex-order neighborhood.
Article: jacobi, Lemma E.1.
-/
abbrev OutgoingSpace := ℝ →ᵇ ℂ

/-- The literal outgoing oscillatory Volterra integral against a real integrable potential.
Use: outgoingOperator packages this same original integral, and differentiation later identifies its inverse with the outgoing inverse-square ODE solution.
Article: jacobi, Lemma E.1.
-/
def outgoingIntegral (m : ℝ → ℝ) (f : OutgoingSpace) (x : ℝ) : ℂ :=
  ∫ y : ℝ,outgoingKernel (y-x)*((m y:ℂ)*f y)

/-- Every actual outgoing-integral summand is genuinely integrable for an L1 potential and a bounded continuous amplitude.
Use: operator continuity, linearity and pointwise bounds may interchange and split only genuinely convergent original integrals.
Article: jacobi, Lemma E.1.
Proof: its norm is bounded by |m(y)| times the actual amplitude norm, since the original oscillatory kernel has modulus at most one. -/
theorem outgoingIntegrand_integrable {m : ℝ → ℝ} (hm : Integrable m) (f : OutgoingSpace) (x : ℝ) :
    Integrable (fun y : ℝ => outgoingKernel (y-x)*((m y:ℂ)*f y)) := by
  -- The same global norm majorant controls both sides of the Volterra diagonal.
  apply (hm.norm.mul_const ‖f‖).mono'
    ((((outgoingKernel_continuous.comp (continuous_id.sub continuous_const)).aestronglyMeasurable).mul
      (hm.ofReal.aestronglyMeasurable.mul f.continuous.aestronglyMeasurable)))
  exact Eventually.of_forall (fun y => by
    change ‖outgoingKernel (y-x)*((m y:ℂ)*f y)‖≤‖m y‖*‖f‖
    rw [norm_mul,norm_mul,Complex.norm_real]
    exact (mul_le_of_le_one_left (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      (outgoingKernel_norm_le _)).trans
        (mul_le_mul_of_nonneg_left (f.norm_coe_le_norm y) (norm_nonneg _)))

/-- The genuine outgoing integral preserves continuity in the actual spatial variable.
Use: outgoingBCF and outgoingOperator stay in the same original complex Banach function space.
Article: jacobi, Lemma E.1.
Proof: use dominated convergence with the actual integrable majorant |m(y)|*norm(f). The original clipped kernel is continuous in x for every fixed y, including its diagonal. -/
theorem outgoingIntegral_continuous {m : ℝ → ℝ} (hm : Integrable m) (f : OutgoingSpace) :
    Continuous (outgoingIntegral m f) := by
  -- The actual L1 potential times the true amplitude norm dominates every translated original kernel.
  apply continuous_of_dominated
    (fun x => (outgoingIntegrand_integrable hm f x).aestronglyMeasurable)
    (fun x => Eventually.of_forall (fun y => ?_)) (hm.norm.mul_const ‖f‖)
    (Eventually.of_forall (fun y => (outgoingKernel_continuous.comp (continuous_const.sub continuous_id)).mul continuous_const))
  change ‖outgoingKernel (y-x)*((m y:ℂ)*f y)‖≤‖m y‖*‖f‖
  rw [norm_mul,norm_mul,Complex.norm_real]
  exact (mul_le_of_le_one_left (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    (outgoingKernel_norm_le _)).trans
      (mul_le_mul_of_nonneg_left (f.norm_coe_le_norm y) (norm_nonneg _))

/-- The actual outgoing integral has its exact L1-potential norm bound.
Use: outgoingOperator is bounded in one fixed Banach space, and the true inverse-square mass later gives the uniform complex-order contraction constant.
Article: jacobi, Lemma E.1.
Proof: bound the norm of the genuine integral by the integral of its norm, then use the original uniform kernel bound and bounded amplitude. -/
theorem outgoingIntegral_norm_le {m : ℝ → ℝ} (hm : Integrable m) (f : OutgoingSpace) (x : ℝ) :
    ‖outgoingIntegral m f x‖≤(∫ y : ℝ,‖m y‖)*‖f‖ := by
  -- Both sides use the actual original integrable potential, not a separately specified tail mass.
  rw [outgoingIntegral,← integral_mul_const]
  apply (norm_integral_le_integral_norm _).trans
  apply integral_mono_ae (outgoingIntegrand_integrable hm f x).norm (hm.norm.mul_const ‖f‖)
  exact Eventually.of_forall (fun y => by
    change ‖outgoingKernel (y-x)*((m y:ℂ)*f y)‖≤‖m y‖*‖f‖
    rw [norm_mul,norm_mul,Complex.norm_real]
    exact (mul_le_of_le_one_left (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      (outgoingKernel_norm_le _)).trans
        (mul_le_mul_of_nonneg_left (f.norm_coe_le_norm y) (norm_nonneg _)))

/-- The actual outgoing integral as a bounded continuous complex function.
Use: outgoingLinear and outgoingOperator retain exactly the literal original oscillatory integral at every real spatial point.
Article: jacobi, Lemma E.1.
-/
def outgoingBCF {m : ℝ → ℝ} (hm : Integrable m) (f : OutgoingSpace) : OutgoingSpace :=
  BoundedContinuousFunction.ofNormedAddCommGroup (outgoingIntegral m f)
    (outgoingIntegral_continuous hm f) ((∫ y : ℝ,‖m y‖)*‖f‖) (outgoingIntegral_norm_le hm f)

/-- The genuine outgoing integral is complex linear in the original bounded continuous amplitude.
Use: outgoingOperator is a complex bounded linear operator, so the complex-order Jost inverse is an actual Banach-algebra inverse.
Article: jacobi, Lemma E.1.
Proof: pointwise distribute the original scalar kernel and potential, then apply linearity only to the independently proved absolutely convergent original integrals. -/
def outgoingLinear {m : ℝ → ℝ} (hm : Integrable m) : OutgoingSpace →ₗ[ℂ] OutgoingSpace where
  toFun := outgoingBCF hm
  map_add' f g := by
    apply BoundedContinuousFunction.ext
    intro x
    change outgoingIntegral m (f+g) x=outgoingIntegral m f x+outgoingIntegral m g x
    unfold outgoingIntegral
    simp only [BoundedContinuousFunction.add_apply,mul_add]
    exact integral_add (outgoingIntegrand_integrable hm f x) (outgoingIntegrand_integrable hm g x)
  map_smul' c f := by
    apply BoundedContinuousFunction.ext
    intro x
    change outgoingIntegral m (c • f) x=c*outgoingIntegral m f x
    unfold outgoingIntegral
    simp only [BoundedContinuousFunction.smul_apply,smul_eq_mul]
    simp_rw [show ∀ y : ℝ,outgoingKernel (y-x)*((m y:ℂ)*(c*f y))=
      c*(outgoingKernel (y-x)*((m y:ℂ)*f y)) from fun y => by ring]
    exact integral_const_mul _ _

/-- The actual outgoing oscillatory Volterra operator as a complex bounded linear endomorphism.
Use: the analytic outgoing Jost solution is obtained by inverting the literal original pencil I+c*T in this fixed Banach algebra.
Article: jacobi, Lemma E.1.
-/
def outgoingOperator {m : ℝ → ℝ} (hm : Integrable m) : OutgoingSpace →L[ℂ] OutgoingSpace :=
  (outgoingLinear hm).mkContinuous (∫ y : ℝ,‖m y‖) (fun f =>
    (BoundedContinuousFunction.norm_le (by positivity)).mpr (outgoingIntegral_norm_le hm f))

/-- The bounded operator is exactly the original outgoing oscillatory integral at every spatial point.
Use: the genuine inverse equation and ODE differentiation concern the literal original kernel and potential, not an abstract unspecified endomorphism.
Article: jacobi, Lemma E.1.
Proof: all operator packaging maps have the original outgoing integral as their defining value. -/
theorem outgoingOperator_apply {m : ℝ → ℝ} (hm : Integrable m) (f : OutgoingSpace) (x : ℝ) :
    outgoingOperator hm f x=outgoingIntegral m f x := rfl

/-- The actual complex outgoing operator norm is bounded by the genuine L1 mass of its original potential.
Use: inverseSquare_norm_integral turns this into a common 1/R bound, so a fixed real starting ray supports a uniform complex-order Jost inverse.
Article: jacobi, Lemma E.1.
Proof: the genuine pointwise bound controls the uniform function norm, and the bounded-linear operator-norm criterion gives the exact same L1 bound. -/
theorem outgoingOperator_norm_le {m : ℝ → ℝ} (hm : Integrable m) :
    ‖outgoingOperator hm‖≤∫ y : ℝ,‖m y‖ := by
  apply (outgoingOperator hm).opNorm_le_bound (by positivity)
  intro f
  exact (BoundedContinuousFunction.norm_le (by positivity)).mpr (outgoingIntegral_norm_le hm f)

end
end jacobi.Hankel
