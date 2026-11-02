import krylov.Reference.CanonicalSteps

/-!
Article: main_krylov, s2:eq:cg and lem:terminal-fibre, actual canonical reference gradients.
Use: prove the metric pairing and true reference-gradient recurrence before any
terminal perturbation or method-protocol argument.
Source: the concrete CG recurrence and actual positive-root inverse identities.
-/

namespace krylov.Reference
noncomputable section
open Matrix krylov.Secant
open scoped Matrix Matrix.Norms.L2Operator InnerProductSpace
variable {n : ℕ}

/-- The actual physical energy of the actual concrete CG step.
Use: identify the terminal factor √c with a computed physical reference quantity.
Article: main_krylov, s2:eq:cg, c_k=s_kᵀAs_k. -/
def cgEnergy (base : Matrix (Fin n) (Fin n) ℝ) (g : EuclideanSpace ℝ (Fin n)) (k : ℕ) : ℝ :=
  inner ℝ (cgStep base g k) (cgOperator base (cgStep base g k))

/-- The true primal/dual metric coordinate transforms preserve the actual search pairing.
Use: the physical exact-search scalar is computed from the same genuine canonical data.
Article: main_krylov, lem:terminal-fibre, canonical exact search.
Proof: move the actual symmetric root across the inner product and cancel it against its true inverse. -/
theorem canonical_search_pairing (base : Matrix (Fin n) (Fin n) ℝ) (hbase : base.PosDef)
    (d v : EuclideanSpace ℝ (Fin n)) :
    inner ℝ d v=inner ℝ (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (metricRoot base) d)
      (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (metricRoot base)⁻¹ v) := by
  -- The actual root's symmetry moves the primal coordinate transform to the dual side.
  have hs : (Matrix.toEuclideanLin (metricRoot base)).IsSymmetric :=
    Matrix.isSymmetric_toEuclideanLin_iff.mpr (Matrix.isHermitian_iff_isSymm.mpr (metricRoot_isSymm base))
  symm
  have he := hs d (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (metricRoot base)⁻¹ v)
  change inner ℝ (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (metricRoot base) d)
    (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (metricRoot base)⁻¹ v)=
      inner ℝ d (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (metricRoot base)
        (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (metricRoot base)⁻¹ v)) at he
  rw [he]
  rw [← mul_apply_eq_comp, ← map_mul, mul_nonsing_inv _ (metricRoot_det_unit base hbase),
    map_one, one_apply_eq_self]

/-- The true normalized physical reference action equals its genuine canonical primal direction.
Use: identify the actual reference curvature and canonical gradient recurrence.
Article: main_krylov, s2:eq:cg and lem:terminal-fibre, A^(−1/2)Ad=A^(1/2)d.
Proof: replace the actual positive base by its actual root square and cancel the true inverse root. -/
theorem canonical_reference_action (base : Matrix (Fin n) (Fin n) ℝ) (hbase : base.PosDef)
    (d : EuclideanSpace ℝ (Fin n)) :
    Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (metricRoot base)⁻¹ (cgOperator base d)=
      Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (metricRoot base) d := by
  change Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (metricRoot base)⁻¹
    (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) base d)=_
  have he : (metricRoot base)⁻¹*base=metricRoot base := by
    calc
      _ = (metricRoot base)⁻¹*(metricRoot base*metricRoot base) := by rw [metricRoot_square base hbase]
      _ = _ := by rw [← Matrix.mul_assoc, nonsing_inv_mul _ (metricRoot_det_unit base hbase), Matrix.one_mul]
  rw [← mul_apply_eq_comp, ← map_mul, he]

/-- The actual physical CG step energy is exactly its actual squared canonical step norm.
Use: the terminal data-fibre coefficient is the article's genuine energy normalization.
Article: main_krylov, s2:eq:cg and lem:terminal-fibre, c=‖A^(1/2)s‖².
Proof: transform the actual physical quadratic pairing by the genuine metric
root/inverse pair and use the proved actual canonical reference action. -/
theorem cgEnergy_eq_norm_sq (base : Matrix (Fin n) (Fin n) ℝ) (hbase : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (k : ℕ) :
    cgEnergy base g k=‖canonicalCGStep base g k‖^2 := by
  rw [cgEnergy, canonical_search_pairing base hbase, canonical_reference_action base hbase,
    real_inner_self_eq_norm_sq]
  rfl

/-- The actual terminal canonical step length is precisely the square root of its actual physical energy.
Use: converts the constructed residual coefficient to the printed x√c factor.
Article: main_krylov, lem:terminal-fibre, √c.
Proof: apply the nonnegative real square-root identity to the proved genuine squared-norm energy. -/
theorem cgEnergy_sqrt (base : Matrix (Fin n) (Fin n) ℝ) (hbase : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (k : ℕ) :
    Real.sqrt (cgEnergy base g k)=‖canonicalCGStep base g k‖ := by
  rw [cgEnergy_eq_norm_sq base hbase, Real.sqrt_sq (norm_nonneg _)]

/-- The concrete CG canonical gradient changes by exactly its actual canonical step.
Use: terminal reference residuals are derived from the actual run's completion, not assumed as fibre fields.
Article: main_krylov, lem:terminal-fibre, genuine reference last gradient.
Proof: apply the actual inverse root to the explicit true CG gradient update
and use the proved genuine canonical reference action. -/
theorem canonicalCG_gradient_step (base : Matrix (Fin n) (Fin n) ℝ) (hbase : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (k : ℕ) :
    Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (metricRoot base)⁻¹ (cgRun (cgOperator base) g (k+1)).gradient=
      Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (metricRoot base)⁻¹ (cgRun (cgOperator base) g k).gradient+
        canonicalCGStep base g k := by
  change Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (metricRoot base)⁻¹
    ((cgRun (cgOperator base) g k).gradient+cgLine base g k •
      cgOperator base (cgRun (cgOperator base) g k).direction)=_
  rw [map_add, map_smul, canonical_reference_action base hbase]
  simp only [canonicalCGStep, cgStep, map_smul]

end
end krylov.Reference
