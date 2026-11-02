import krylov.Functions.RFCFPrintedTensor
import krylov.Nonlinear.SelfConcordantFunction

/-!
Article: main_krylov, prop:Fcycle(i), genuine self-concordant tensor bound.
Use: derive the original tensor unit-ball hypothesis from the actual
standard self-concordant scalar function at its true minimizer Hessian,
then obtain the literal corrected native tensor coefficient bound.
Source: the original mixed self-concordance inequality, genuine metric
energy identity and the proved exact source Lambda_F coordinate dictionary.
-/
namespace krylov.Functions
noncomputable section
open Matrix Set Metric krylov.Reference krylov.Correction krylov.Secant krylov.Nonlinear krylov.Variation
open scoped InnerProductSpace Matrix.Norms.L2Operator
variable {n k : ℕ}

/-- The actual physical Hessian energy is exactly the norm squared in its genuine canonical metric.
Article: main_krylov, prop:Fcycle(i), true metric tensor normalization. -/
theorem physical_energy_metric_norm (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (v : EuclideanSpace ℝ (Fin n)) :
    inner ℝ v (cgOperator base v)=‖metricCoordinates base hb v‖^2 := by
  have hh := metric_drift_pairing base 1 v v
  simpa only [Matrix.mul_one,metricRoot_square base hb,map_one,one_apply_eq_self,
    real_inner_self_eq_norm_sq] using! hh

/-- The actual source scalar self-concordance inequality makes its genuine canonical third tensor a member of the original diagonal ball two.
Article: main_krylov, prop:Fcycle(i), genuine actual tensor admissibility. -/
theorem third_tensor_unit_ball (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (D : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (T : SymmetricCubic (EuclideanSpace ℝ (Fin n)))
    (hT : ∀ a b c,T.form (cgOperator (metricRoot base) a) (cgOperator (metricRoot base) b)
      (cgOperator (metricRoot base) c)=inner ℝ (D a b) c)
    (hsc : ∀ v,|inner ℝ v (D v v)|≤2*(Real.sqrt (inner ℝ v (cgOperator base v)))^3) :
    ∀ x,‖x‖=1 → |T.form x x x|≤2 := by
  intro x hx
  let S := metricCoordinates base hb
  let v := S.symm x
  have hv : S v=x := S.apply_symm_apply x
  have hp := hT v v v
  change T.form (S v) (S v) (S v)=_ at hp
  rw [hv] at hp
  have hbnd := hsc v
  rw [physical_energy_metric_norm base hb v,hv,hx] at hbnd
  norm_num only [one_pow,Real.sqrt_one,mul_one] at hbnd
  rw [hp,real_inner_comm]
  exact hbnd

/-- The actual standard self-concordant scalar data imply the printed bound on the genuine corrected own-reference cubic coefficient.
Article: main_krylov, prop:Fcycle(i), original nonlinear source hypotheses.
The scalar third tensor and its ball membership are both constructed from
real derivatives; neither a tensor field nor a leading response is assumed. -/
theorem rfcFOwnTensorCanonicalCoefficient_selfConcordant_bound
    (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (hb : base.PosDef)
    (f : EuclideanSpace ℝ (Fin (k+1)) → ℝ) (U : Set (EuclideanSpace ℝ (Fin (k+1))))
    (S : StandardSelfConcordantData f U)
    (hH₀ : S.hessian 0=cgOperator base) {r : ℝ} (hr : 0<r)
    (hU : ∀ z,‖metricCoordinates base hb z‖≤r → z∈U)
    (g : EuclideanSpace ℝ (Fin (k+1)))
    (hcount : referenceAtomCount base hb g=k+1) :
    ‖rfcFOwnTensorCanonicalCoefficient base hb (S.variation 0) g‖≤
      ‖canonicalCGStep base g k‖ *
        (4*(k+1)*Real.sqrt (k+1)*‖cgCanonicalError base g 0‖*‖cgCanonicalError base g 1‖) := by
  have h₀ : (0 : EuclideanSpace ℝ (Fin (k+1)))∈U := hU 0 (by simpa only [map_zero,norm_zero] using hr.le)
  have hD := S.hessian_derivative 0 h₀
  have hF z (hz : ‖metricCoordinates base hb z‖≤r) :
      HasFDerivAt f (innerSL ℝ (gradient f z)) z :=
    (S.differentiable.differentiableAt (S.open_domain.mem_nhds (hU z hz))).hasGradientAt.hasFDerivAt
  have hG z (hz : ‖metricCoordinates base hb z‖≤r) := S.gradient_derivative z (hU z hz)
  let T := metricThirdCubic base hb (metricCoordinates base hb) f (gradient f) S.hessian (S.variation 0) hD hr hF hG
  have hpair := metricThirdCubic_pair base hb (metricCoordinates base hb) f (gradient f) S.hessian
    (S.variation 0) hD hr hF hG
  have hsc v : |inner ℝ v (S.variation 0 v v)|≤2*(Real.sqrt (inner ℝ v (cgOperator base v)))^3 := by
    simpa only [hH₀] using S.diagonal f U 0 h₀ v
  exact rfcFOwnTensorCanonicalCoefficient_bound base hb (S.variation 0) T hpair g hcount
    (third_tensor_unit_ball base hb (S.variation 0) T hpair hsc)

end
end krylov.Functions
