import jacobi.Finite.Criticality

/-!
Article: jacobi, Proposition 1.1.
The forward logarithmic chart is an analytic function of the physical matrix
entries near every fibre point. Combined with analytic reconstruction and the
exact shift classification, this verifies both directions of the real-analytic
coordinate assertion modulo common constants.
Source: cofactor spectral probabilities and elementary finite determinant calculus.
Use: the forward weight map is a characteristic minor divided by a fixed derivative.
-/
namespace jacobi.Finite
noncomputable section
open chebyshev1 chebyshev2 Matrix
open scoped BigOperators Matrix.Norms.Elementwise
set_option backward.isDefEq.respectTransparency false

/-- Determinants of finite matrices with analytic entries are analytic.
Use: the forward weight map is a characteristic minor divided by a fixed derivative.
Article: jacobi, Proposition 1.1.
Source: the Leibniz determinant formula in mathlib.
Proof: its finite signed sum of finite products preserves analyticity. -/
theorem determinant_analytic {D ι : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    [Fintype ι] [DecidableEq ι] {f : D → Matrix ι ι ℝ} {x : D}
    (hf : ∀ i j, AnalyticAt ℝ (fun v => f v i j) x) :
    AnalyticAt ℝ (fun v => (f v).det) x := by
  simp_rw [Matrix.det_apply']
  apply Finset.analyticAt_fun_sum
  intro σ _
  apply AnalyticAt.mul analyticAt_const
  apply Finset.analyticAt_fun_prod
  intro i _
  exact hf (σ i) i

variable {n : ℕ} (S : Nodes (n+1))

/-- First-site spectral probabilities extended to ambient physical matrices by cofactors.
Use: makes the forward chart analytic without assuming analytic eigenvector choices.
Article: jacobi, Proposition 1.1.
-/
def matrixWeight (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (k : Fin (n+1)) : ℝ :=
  ((Matrix.scalar _ (S.value k)-A).submatrix Fin.succ Fin.succ).det /
    S.polynomial.derivative.eval (S.value k)

/-- The ambient cofactor weight is exactly the actual spectral weight on the fibre.
Use: transfers positivity and the inverse chart to the analytic matrix formula.
Article: jacobi, Proposition 1.1.
Proof: specialize the spectral diagonal adjugate formula at site zero. -/
theorem matrixWeight_eq (J : Fiber (n+1) S.polynomial) (k : Fin (n+1)) :
    matrixWeight S J.val.matrix k = (spectralWeights S J).val k := by
  -- Evaluate the spectral adjugate identity at site zero and cancel the nonzero characteristic derivative.
  let B := orderedBasis S J.val J.property
  have hi : Function.Injective B.eigenvalues :=
    (orderedBasis_values S J.val J.property).symm ▸ S.strictAnti.injective
  have h := B.adjugate_eigenvalue_diagonal hi 0 k
  rw [orderedBasis_values S J.val J.property, J.property.2,
    Matrix.adjugate_fin_succ_eq_det_submatrix] at h
  simp only [Fin.val_zero, zero_add, pow_zero, one_mul, Fin.succAbove_zero] at h
  change _ / _ = B.weight 0 k
  exact (div_eq_iff (S.derivative_ne_zero k)).mpr h

/-- Cofactor probabilities vary analytically in ambient matrix entries.
Use: compose their positive fibre values with the analytic logarithm.
Article: jacobi, Proposition 1.1.
Proof: fixed-entry coordinate projections, subtraction, the determinant and division. -/
theorem matrixWeight_analytic (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (k : Fin (n+1)) :
    AnalyticAt ℝ (fun C => matrixWeight S C k) A := by
  apply AnalyticAt.div ?_ analyticAt_const (S.derivative_ne_zero k)
  apply determinant_analytic
  intro i j
  have hp : AnalyticAt ℝ (fun C : Matrix (Fin (n+1)) (Fin (n+1)) ℝ => C i.succ j.succ) A :=
    ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (n+1) => ℝ) j.succ).comp
      (ContinuousLinearMap.proj (R := ℝ)
        (φ := fun _ : Fin (n+1) => Fin (n+1) → ℝ) i.succ)).analyticAt A
  exact analyticAt_const.sub hp

/-- Ambient logarithmic coordinates, defined wherever the cofactor probabilities are positive.
Use: gives the real-analytic forward chart near every actual fibre point.
Article: jacobi, Proposition 1.1.
-/
def matrixLogs (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (k : Fin (n+1)) : ℝ :=
  Real.log (matrixWeight S A k * |S.polynomial.derivative.eval (S.value k)|)

/-- The ambient logarithmic formula restricts to the actual fibre chart.
Use: identifies the analytic map with the inverse of the proved reconstruction.
Article: jacobi, Proposition 1.1.
Proof: Substitute the proved equality of the ambient cofactor and actual spectral probabilities. -/
theorem matrixLogs_eq (J : Fiber (n+1) S.polynomial) :
    matrixLogs S J.val.matrix = weightLogs S (spectralWeights S J) := by
  funext k
  simp only [matrixLogs, weightLogs, matrixWeight_eq]

/-- Every forward logarithmic coordinate is analytic near every actual fibre matrix.
Use: completes the two-sided real-analytic chart assertion, modulo common constants.
Article: jacobi, Proposition 1.1.
Proof: the cofactor expression is analytic and its value at the fibre point is positive. -/
theorem matrixLogs_analytic (J : Fiber (n+1) S.polynomial) (k : Fin (n+1)) :
    AnalyticAt ℝ (fun A => matrixLogs S A k) J.val.matrix := by
  have hp : 0 < matrixWeight S J.val.matrix k *
      |S.polynomial.derivative.eval (S.value k)| := by
    rw [matrixWeight_eq]
    exact mul_pos ((spectralWeights S J).property.1 k)
      (abs_pos.mpr (S.derivative_ne_zero k))
  exact (analyticAt_log hp).comp
    (f := fun A => matrixWeight S A k * |S.polynomial.derivative.eval (S.value k)|)
    ((matrixWeight_analytic S J.val.matrix k).mul analyticAt_const)

/-- Every actual fibre element is obtained by its logarithmic spectral coordinates.
Use: the coordinate map covers the full fibre, rather than a selected subfamily.
Article: jacobi, Proposition 1.1.
Proof: logarithms invert probabilities and the full spectral equivalence reconstructs J. -/
theorem logFiber_matrixLogs (J : Fiber (n+1) S.polynomial) :
    logFiber S (matrixLogs S J.val.matrix) = J := by
  rw [matrixLogs_eq, logFiber, logWeights_weightLogs, reconstruct_spectralWeights]

/-- Two logarithmic parameters give the same matrix precisely when they differ by a constant.
Use: verifies exactly the quotient R^n/R1 appearing in the article's proposition.
Article: jacobi, Proposition 1.1.
Proof: apply the proved spectral equivalence and logarithms for necessity;
common-shift invariance of the probabilities proves sufficiency. -/
theorem logFiber_eq_iff (ell v : Fin (n+1) → ℝ) :
    logFiber S ell = logFiber S v ↔ ∃ c : ℝ, ∀ k, ell k = v k+c := by
  -- Taking logarithms of equal probabilities isolates a single common additive constant.
  constructor
  · intro h
    have hw := congrArg (spectralWeights S) h
    simp only [logFiber, spectralWeights_reconstruct] at hw
    refine ⟨Real.log (logNormalizer S ell)-Real.log (logNormalizer S v), ?_⟩
    intro k
    have hk := congrArg (fun w => weightLogs S w k) hw
    rw [weightLogs_logWeights, weightLogs_logWeights] at hk
    linarith
  · rintro ⟨c, hc⟩
    have he : ell = fun k => v k+c := funext hc
    rw [he, logFiber, logFiber, logWeights_shift]

/-- The entire inverse chart is analytic as a map into the physical matrix space.
Use: packages the entrywise result into the actual finite-dimensional matrix topology.
Article: jacobi, Proposition 1.1.
Proof: the matrix has finitely many coordinates, all already proved analytic. -/
theorem logFiber_analytic (ell : Fin (n+1) → ℝ) :
    AnalyticAt ℝ (fun v => (logFiber S v).val.matrix) ell :=
  AnalyticAt.pi (fun i => AnalyticAt.pi (fun j => logFiber_matrix_analytic S ell i j))

/-- The entire forward logarithmic chart is analytic near every physical fibre matrix.
Use: completes the matrix-space form of the two-sided analytic coordinate statement.
Article: jacobi, Proposition 1.1.
Proof: the finitely many logarithmic coordinates are analytic by the cofactor formula. -/
theorem matrixLogs_analytic_all (J : Fiber (n+1) S.polynomial) :
    AnalyticAt ℝ (matrixLogs S) J.val.matrix :=
  AnalyticAt.pi (matrixLogs_analytic S J)


end
end jacobi.Finite
