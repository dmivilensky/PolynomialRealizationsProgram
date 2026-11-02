import krylov.Convergence.WindowMetricGain
import krylov.Nonlinear.MetricCoordinates
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
Article: main_krylov, thm:grow and cor:xrF, original physical normalization.
Use: derive the canonical Hessian Lipschitz constant with precisely the
cubic inverse-root loss LH_E*lambda_min^(-3/2). The coordinate Hessian is
its actual inverse congruence on the true pulled-back neighborhood.
Source: genuine derivative-coordinate reconstruction, actual root energy
and the continuous-linear operator norm. No canonical budget is assumed.
-/

namespace krylov.Convergence
noncomputable section
open Matrix Set krylov.Methods krylov.Secant krylov.Reference krylov.Correction krylov.Nonlinear
open scoped InnerProductSpace Matrix.Norms.L2Operator NNReal
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/- Genuine derivative coordinate changes transport an original physical
Lipschitz constant with the cube of their actual inverse operator norm. -/
omit [CompleteSpace E] in
theorem coordinateDerivative_lipschitz_forward (T : E ≃L[ℝ] E) (H : E → E →L[ℝ] E)
    {S : Set E} {L : ℝ≥0} (hH : LipschitzOnWith L H S) :
    LipschitzOnWith (‖T.symm.toContinuousLinearMap‖₊^3*L) (coordinateDerivative T H) (T.symm ⁻¹' S) := by
  have he : coordinateDerivative T.symm (coordinateDerivative T H)=H := by
    funext x
    exact coordinateDerivative_reconstruct T H x
  have hs : LipschitzOnWith L (coordinateDerivative T.symm (coordinateDerivative T H)) S := by rwa [he]
  simpa only [ContinuousLinearEquiv.symm_symm] using coordinateDerivative_lipschitz_pullback T.symm (coordinateDerivative T H) hs

/-- A primitive physical lower Hessian endpoint bounds the genuine inverse
metric root by exactly lambda_min^(-1/2). -/
theorem metricCoordinates_inverse_norm_bound {n : ℕ} (H : Matrix (Fin n) (Fin n) ℝ)
    (hH : H.PosDef) {mu : ℝ} (hmu : 0<mu)
    (hlower : ∀ v : EuclideanSpace ℝ (Fin n),mu*‖v‖^2≤ inner ℝ v (cgOperator H v)) :
    ‖(metricCoordinates H hH).symm.toContinuousLinearMap‖≤(Real.sqrt mu)⁻¹ := by
  let T := metricCoordinates H hH
  apply ContinuousLinearMap.opNorm_le_bound _ (inv_nonneg.mpr (Real.sqrt_nonneg _))
  intro v
  have hh := hlower (T.symm v)
  rw [restart_root_pairing H hH,real_inner_self_eq_norm_sq] at hh
  have he : cgOperator (metricRoot H) (T.symm v)=v := T.apply_symm_apply v
  rw [he] at hh
  have hn : Real.sqrt mu*‖T.symm v‖≤‖v‖ := by
    apply (sq_le_sq₀ (by positivity) (norm_nonneg _)).mp
    simpa only [mul_pow,Real.sq_sqrt hmu.le] using hh
  exact (le_inv_mul_iff₀ (Real.sqrt_pos.mpr hmu)).mpr hn

/-- The source's square-root expression is exactly its printed real-power
lambda_min^(-3/2) factor. -/
theorem inverse_sqrt_cube_eq_rpow {mu : ℝ} (hmu : 0≤mu) :
    ((Real.sqrt mu)^3)⁻¹=mu^(-(3/2:ℝ)) := by
  rw [Real.rpow_neg hmu,Real.sqrt_eq_rpow,←Real.rpow_natCast,←Real.rpow_mul hmu]
  norm_num

/-- The actual canonical Hessian has exactly the original printed
physical-to-canonical Lipschitz allowance LH_E*lambda_min^(-3/2). -/
theorem metric_hessian_lipschitz_bound {n : ℕ} (base : Matrix (Fin n) (Fin n) ℝ)
    (hb : base.PosDef) (H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ]
      EuclideanSpace ℝ (Fin n)) {S : Set (EuclideanSpace ℝ (Fin n))} {L : ℝ≥0}
    (hH : LipschitzOnWith L H S) {mu : ℝ} (hmu : 0<mu)
    (hlower : ∀ v : EuclideanSpace ℝ (Fin n),mu*‖v‖^2≤ inner ℝ v (cgOperator base v)) :
    LipschitzOnWith (Real.toNNReal ((L:ℝ)*mu^(-(3/2:ℝ))))
      (coordinateDerivative (metricCoordinates base hb) H) ((metricCoordinates base hb).symm ⁻¹' S) := by
  have hh := coordinateDerivative_lipschitz_forward (metricCoordinates base hb) H hH
  have hcoeff : ‖(metricCoordinates base hb).symm.toContinuousLinearMap‖₊^3*L≤
      Real.toNNReal ((L:ℝ)*mu^(-(3/2:ℝ))) := by
    apply NNReal.coe_le_coe.mp
    rw [Real.coe_toNNReal _ (mul_nonneg L.coe_nonneg (Real.rpow_nonneg hmu.le _))]
    simp only [NNReal.coe_mul,NNReal.coe_pow,coe_nnnorm]
    have hn := metricCoordinates_inverse_norm_bound base hb hmu hlower
    have hpow := pow_le_pow_left₀ (norm_nonneg _) hn 3
    apply (mul_le_mul_of_nonneg_right hpow L.coe_nonneg).trans_eq
    rw [inv_pow,inverse_sqrt_cube_eq_rpow hmu.le]
    ring
  rw [lipschitzOnWith_iff_norm_sub_le] at hh ⊢
  intro x hx y hy
  exact (hh hx hy).trans (mul_le_mul_of_nonneg_right (NNReal.coe_le_coe.mpr hcoeff) (norm_nonneg _))


end
end krylov.Convergence
