import krylov.Secant.Metric
import krylov.Stability.MetricRootRegularity
import krylov.Stability.AnalyticSolve

set_option autoImplicit false
/-!
Article: main_krylov, apB:lem:mu(c), genuine positive quadratic shadow paths.
Use: realize every actual symmetric reference derivative by an analytic
positive-definite matrix curve, with the true prescribed base and first jet,
for the genuine globally CG-consistent absorbed information fibre.
Source: standard positive Gram factorization, the actual invertible
reference metric root and continuity of the true finite determinant.
-/

namespace krylov.Envelope
noncomputable section
open Matrix krylov.Secant krylov.Stability Filter Topology
open scoped Matrix.Norms.L2Operator
variable {n : ℕ}

/-- An actual analytic positive quadratic shadow curve with the true prescribed symmetric first derivative.
Use: An actual analytic positive quadratic shadow curve with the true prescribed symmetric first derivative.
Article: main_krylov, apB:lem:mu(c), genuine positive quadratic shadow paths.
Proof: Add the genuine quadratic Gram-factor term to the actual affine reference variation. -/
def positiveReferenceCurve (base D : Matrix (Fin n) (Fin n) ℝ) (t : ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  base+t • D+(t^2/4) • (D*(metricRoot base)⁻¹*(metricRoot base)⁻¹*D)

/-- The actual positive quadratic shadow curve starts at its genuine supplied reference matrix.
Use: The actual positive quadratic shadow curve starts at its genuine supplied reference matrix.
Article: main_krylov, apB:lem:mu(c), genuine positive quadratic shadow paths.
Proof: The true linear and quadratic perturbation terms vanish at zero. -/
theorem positiveReferenceCurve_zero (base D : Matrix (Fin n) (Fin n) ℝ) :
    positiveReferenceCurve base D 0=base := by simp only [positiveReferenceCurve,zero_smul,add_zero,zero_pow (by omega : 2≠0),zero_div]

/-- The genuine positive quadratic shadow curve has exactly the actual prescribed reference derivative.
Use: The genuine positive quadratic shadow curve has exactly the actual prescribed reference derivative.
Article: main_krylov, apB:lem:mu(c), genuine positive quadratic shadow paths.
Proof: Differentiate its true constant, linear and quadratic finite matrix terms. -/
theorem positiveReferenceCurve_hasDeriv (base D : Matrix (Fin n) (Fin n) ℝ) :
    HasDerivAt (positiveReferenceCurve base D) D 0 := by
  have ht := (hasDerivAt_id (0 : ℝ)).smul_const D
  have hq := (((hasDerivAt_id (0 : ℝ)).pow 2).div_const 4).smul_const (D*(metricRoot base)⁻¹*(metricRoot base)⁻¹*D)
  convert! (hasDerivAt_const (0 : ℝ) base).add ht |>.add hq using 1
  simp

/-- The actual positive quadratic shadow curve is exactly the genuine Gram matrix of an explicit true reference-root perturbation.
Use: The actual positive quadratic shadow curve is exactly the genuine Gram matrix of an explicit true reference-root perturbation.
Article: main_krylov, apB:lem:mu(c), genuine positive quadratic shadow paths.
Proof: Expand the actual transpose product, use genuine symmetric base and perturbation matrices, and cancel the true reference-root inverse on both sides. -/
theorem positiveReferenceCurve_factor (base D : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (hD : D.IsSymm) (t : ℝ) :
    let T := metricRoot base+(t/2) • ((metricRoot base)⁻¹*D)
    positiveReferenceCurve base D t=Tᵀ*T := by
  -- Expand the actual Gram factor and use the true symmetric root with its genuine two-sided inverse.
  let R := metricRoot base
  have hR : Rᵀ=R := (metricRoot_isSymm base).eq
  have hI : (R⁻¹)ᵀ=R⁻¹ := by rw [transpose_nonsing_inv,hR]
  have hl : R*R⁻¹=1 := Matrix.mul_nonsing_inv _ (metricRoot_det_unit base hb)
  have hr : R⁻¹*R=1 := Matrix.nonsing_inv_mul _ (metricRoot_det_unit base hb)
  change base+t • D+(t^2/4) • (D*R⁻¹*R⁻¹*D)=(R+(t/2) • (R⁻¹*D))ᵀ*(R+(t/2) • (R⁻¹*D))
  simp only [transpose_add,transpose_smul,transpose_mul,hR,hI,hD.eq,mul_add,add_mul,Matrix.smul_mul,Matrix.mul_smul]
  rw [show R*R=base from metricRoot_square base hb,
    show R*(R⁻¹*D)=D by rw [← Matrix.mul_assoc,hl,Matrix.one_mul],
    show D*R⁻¹*R=D by rw [Matrix.mul_assoc,hr,Matrix.mul_one]]
  rw [show D*R⁻¹*(R⁻¹*D)=D*R⁻¹*R⁻¹*D by simp only [Matrix.mul_assoc]]
  module

/-- Every genuine symmetric reference perturbation has an actual neighborhood where its true quadratic shadow curve is positive definite.
Use: Every genuine symmetric reference perturbation has an actual neighborhood where its true quadratic shadow curve is positive definite.
Article: main_krylov, apB:lem:mu(c), genuine positive quadratic shadow paths.
Proof: The actual reference-root perturbation has a genuine nonzero determinant at zero, which stays nonzero locally. Its true Gram factorization is therefore positive definite on that real neighborhood. -/
theorem positiveReferenceCurve_eventually_posDef (base D : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (hD : D.IsSymm) : ∀ᶠ t in 𝓝 (0 : ℝ), (positiveReferenceCurve base D t).PosDef := by
  -- Genuine determinant continuity preserves the actual invertibility of the explicit Gram factor near the true reference.
  let T := fun t : ℝ => metricRoot base+(t/2) • ((metricRoot base)⁻¹*D)
  have hc : Continuous T := continuous_const.add ((continuous_id.div_const 2).smul continuous_const)
  have hn : (T 0).det≠0 := by simpa only [T,zero_div,zero_smul,add_zero] using (metricRoot_det_unit base hb).ne_zero
  have he := hc.matrix_det.continuousAt.eventually_ne hn
  filter_upwards [he] with t ht
  rw [positiveReferenceCurve_factor base D hb hD t]
  have hp := Matrix.PosDef.one.conjTranspose_mul_mul_same (Matrix.mulVec_injective_iff_isUnit.mpr ((Matrix.isUnit_iff_isUnit_det (T t)).mpr (isUnit_iff_ne_zero.mpr ht)))
  simpa only [Matrix.mul_one,Matrix.conjTranspose_eq_transpose_of_trivial] using hp
/-- The actual positive quadratic reference shadow curve is genuinely real analytic.
Use: The actual positive quadratic reference shadow curve is genuinely real analytic.
Article: main_krylov, apB:lem:mu(c), genuine positive quadratic shadow paths.
Proof: Its true finite matrix formula uses only actual constant, linear and quadratic scalar-vector operations. -/
theorem positiveReferenceCurve_analytic (base D : Matrix (Fin n) (Fin n) ℝ) (t : ℝ) :
    AnalyticAt ℝ (positiveReferenceCurve base D) t :=
  (analyticAt_const.add (analyticAt_id.smul analyticAt_const)).add
    (((analyticAt_id.pow 2).div analyticAt_const (by norm_num : (4 : ℝ)≠0)).smul analyticAt_const)

end
end krylov.Envelope
