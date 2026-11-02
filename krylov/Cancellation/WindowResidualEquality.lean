import krylov.Cancellation.WindowResidualMetric
import krylov.Reference.CanonicalSteps
set_option autoImplicit false
/-!
Article: main_krylov, apH:dcs2(a), genuine physical residual metric dictionary.
Use: derive the printed energy Gram and its inverse domain from actual
independent physical columns, and transfer exact native residual coordinates.
Source: the reused positive-root square and genuine positive operator Gram.
-/

namespace krylov.Cancellation
noncomputable section
open Matrix krylov.Methods krylov.Reference krylov.Secant krylov.Stability
open scoped InnerProductSpace Matrix.Norms.L2Operator
variable {n p : ℕ}

/-- The Gram of the actual canonical window is precisely the original physical
energy Gram, for arbitrary rectangular physical windows.
Use: identify G_A in the printed fresh-defect norm without an assumed metric.
Article: main_krylov, apH:dcs2(a), G_A equals S transpose A S.
Proof: move the true symmetric metric root across the real inner product
and use its proved square identity. -/
theorem primal_window_energy_gram (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (s : Fin p → EuclideanSpace ℝ (Fin n)) :
    crossGram (primalWindow base s) (primalWindow base s)=
      crossGram (fun i => cgOperator base (s i)) s := by
  let R := cgOperator (metricRoot base)
  have hR : R.toLinearMap.IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr
    (Matrix.isHermitian_iff_isSymm.mpr (metricRoot_isSymm base))
  ext i j
  change inner ℝ (R (s i)) (R (s j))=inner ℝ (cgOperator base (s i)) (s j)
  have hmove : inner ℝ (R (R (s i))) (s j)=inner ℝ (R (s i)) (R (s j)) := hR (R (s i)) (s j)
  rw [← hmove]
  have hsq : R (R (s i))=cgOperator base (s i) := by
    change Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base)
      (Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base) (s i))=_
    rw [← mul_apply_eq_comp,← map_mul,metricRoot_square base hb]
    rfl
  rw [hsq]

/-- Actual independence and a positive physical base derive the genuine
canonical window Gram's positive definiteness.
Use: all inverse-energy-Gram domains below follow from the source hypotheses.
Article: main_krylov, apH:dcs2(a), true physical residual inverse domain.
Proof: the actual canonical Gram equals the positive physical operator Gram. -/
theorem primal_window_gram_posDef (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (s : Fin p → EuclideanSpace ℝ (Fin n)) (hs : LinearIndependent ℝ s) :
    (crossGram (primalWindow base s) (primalWindow base s)).PosDef := by
  rw [primal_window_energy_gram base hb]
  exact operatorGram_posDef _ (cgOperator_positive base hb).1 (cgOperator_positive base hb).2 hs

/-- Equal genuine physical window pairings have exactly equal printed
inverse-energy-Gram residual norms.
Use: native exact fresh-coordinate cancellation transfers to the original norm.
Article: main_krylov, apH:dcs2(a), true residual-coordinate transfer.
Proof: derive the inverse domain from actual independence, then apply the
proved exact physical projection/inverse-Gram norm formula on both sides. -/
theorem window_metric_residual_congr (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (s : Fin p → EuclideanSpace ℝ (Fin n)) (hs : LinearIndependent ℝ s)
    (v w : EuclideanSpace ℝ (Fin n)) (hvw : coordinates s v=coordinates s w) :
    windowMetricResidual base s v=windowMetricResidual base s w := by
  have hu := isUnit_iff_ne_zero.mpr (primal_window_gram_posDef base hb s hs).det_pos.ne'
  rw [window_metric_residual_formula base hb s hu,window_metric_residual_formula base hb s hu,hvw]

/-- Every genuine physical fresh matrix obeys the exact source window bound.
Use: the attaining DC-slide coefficient is bounded on the original relative
spectral matrix ball, with no physical step-length denominator.
Article: main_krylov, apH:dcs2(a), universal physical fresh upper bound.
Proof: canonicalize the actual physical action with the genuine positive root;
the true orthogonal projection is contractive and the actual relative matrix
has precisely its Euclidean operator norm. -/
theorem window_metric_fresh_le (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (s : Fin p → EuclideanSpace ℝ (Fin n)) (step : EuclideanSpace ℝ (Fin n))
    (F : Matrix (Fin n) (Fin n) ℝ) (omega : ℝ) (hF : ‖relativeOperator base F‖≤omega) :
    windowMetricResidual base s (cgOperator F step)≤omega*‖cgOperator (metricRoot base) step‖ := by
  let K := Submodule.span ℝ (Set.range (primalWindow base s))
  have haction : cgOperator (metricRoot base)⁻¹ (cgOperator F step)=
      cgOperator (relativeOperator base F) (cgOperator (metricRoot base) step) := by
    change Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base)⁻¹
      (Matrix.toEuclideanCLM (𝕜 := ℝ) F step)=_
    simp only [relativeOperator,cgOperator,map_mul,mul_apply_eq_comp]
    rw [canonical_primal_dual_cancel base hb]
  change ‖K.starProjection (cgOperator (metricRoot base)⁻¹ (cgOperator F step))‖≤_
  rw [haction]
  exact (K.norm_starProjection_apply_le _).trans
    (((cgOperator (relativeOperator base F)).le_opNorm _).trans
      (mul_le_mul_of_nonneg_right hF (norm_nonneg _)))

end
end krylov.Cancellation
