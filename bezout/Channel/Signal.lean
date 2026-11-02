import bezout.Gains.MatrixAdmissible
import Mathlib.Analysis.Normed.Operator.NNNorm

/-!
Article: bezout, Equation `eq:experiment-T` and Appendix D channel measurements.
Use: the signal matrix is the actual derivative from a scalar temporal channel
profile to the terminal vector; its Euclidean operator norm is attained.
Proof: diagonal polynomial functional calculus identifies every matrix entry,
and compactness of the finite-dimensional unit sphere supplies a maximizing input.
-/

namespace bezout.Channel
noncomputable section
open Polynomial
open scoped BigOperators
variable {N : ℕ} {J : Type*} [Fintype J] [DecidableEq J]

/-- The physical insertion matrix for specified eigenvalues and initial amplitudes. -/
def signalMatrix (h : bezout.History N) (lam a : J → ℝ) : Matrix J (Fin N) ℝ :=
  fun j s => a j*bezout.Lower.physicalKernel h s (lam j) (lam j)

/-- The actual Euclidean linear map of the physical signal matrix. -/
def signalOperator (h : bezout.History N) (lam a : J → ℝ) :
    EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ J :=
  (Matrix.toEuclideanLin (signalMatrix h lam a)).toContinuousLinearMap

omit [DecidableEq J] in
/-- Entrywise action of the actual insertion matrix on a temporal profile. -/
theorem signalOperator_apply (h : bezout.History N) (lam a : J → ℝ)
    (e : EuclideanSpace ℝ (Fin N)) (j : J) :
    signalOperator h lam a e j=∑ s, a j*bezout.Lower.physicalKernel h s (lam j) (lam j)*e s := by
  change (signalMatrix h lam a).mulVec e.ofLp j=_
  rfl

/-- Diagonal matrix polynomial action is scalar evaluation in each physical eigenspace. -/
theorem diagonal_polynomial_apply (lam : J → ℝ) (p : ℝ[X]) (v : EuclideanSpace ℝ J) (j : J) :
    ((aeval (bezout.History.matrixEnd (Matrix.diagonal lam)) p) v) j=p.eval (lam j)*v j := by
  rw [Polynomial.aeval_algHom_apply bezout.History.matrixEnd (Matrix.diagonal lam) p,
    chebyshev1.aeval_diagonal]
  rw [bezout.History.matrixEnd_eq_toEuclideanLin]
  change (Matrix.diagonal (fun i => p.eval (lam i))).mulVec v.ofLp j=_
  simp [Matrix.mulVec, dotProduct, Matrix.diagonal]

/-- The differentiated actual channel oracle has terminal derivative exactly T e.
Use: the matrix describes the physical iteration, including every causal query. -/
theorem firstVariation_signalOperator (h : bezout.History N) (lam : J → ℝ)
    (a : EuclideanSpace ℝ J) (e : EuclideanSpace ℝ (Fin N)) :
    h.firstVariation (bezout.History.matrixEnd (Matrix.diagonal lam))
      (fun s => e s • (LinearMap.id : EuclideanSpace ℝ J →ₗ[ℝ] EuclideanSpace ℝ J)) a=
      signalOperator h lam a.ofLp e := by
  ext j
  simp only [bezout.History.firstVariation, bezout.History.variationNoise,
    WithLp.ofLp_sum, Finset.sum_apply, diagonal_polynomial_apply, LinearMap.smul_apply,
    LinearMap.id_apply, PiLp.smul_apply, smul_eq_mul, signalOperator_apply,
    bezout.Lower.physicalKernel]
  apply Finset.sum_congr rfl
  intro s _
  ring

/-- The insertion matrix is the derivative of the full actual perturbed-oracle output. -/
theorem hasDerivAt_signal_output (h : bezout.History N) (lam : J → ℝ)
    (a : EuclideanSpace ℝ J) (e : EuclideanSpace ℝ (Fin N)) :
    HasDerivAt (fun t => h.oracleOutput a
      (bezout.History.perturbedOracle (bezout.History.matrixEnd (Matrix.diagonal lam))
        (fun s => e s • (LinearMap.id : EuclideanSpace ℝ J →ₗ[ℝ] EuclideanSpace ℝ J)) t))
      (signalOperator h lam a.ofLp e) 0 := by
  rw [← firstVariation_signalOperator]
  exact h.hasDerivAt_perturbed_output _ _ _

/-- Every finite-dimensional real linear map attains its operator norm on the unit sphere. -/
theorem finite_operator_norm_attained {V W : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [FiniteDimensional ℝ V] [Nontrivial V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] (T : V →L[ℝ] W) :
    ∃ e : V, ‖e‖=1 ∧ ‖T e‖=‖T‖ := by
  have hn : (Metric.sphere (0:V) 1).Nonempty := NormedSpace.sphere_nonempty.mpr zero_le_one
  have hc : IsCompact ((fun e => ‖T e‖) '' Metric.sphere (0:V) 1) :=
    (isCompact_sphere (0:V) 1).image T.continuous.norm
  have hs := hc.sSup_mem (hn.image _)
  rw [T.sSup_sphere_eq_norm] at hs
  obtain ⟨e,he,hte⟩ := hs
  exact ⟨e, by simpa using he, hte⟩

omit [DecidableEq J] in
/-- The sharp unit-energy physical channel response is the actual matrix operator norm. -/
theorem signalOperator_sharp (h : bezout.History N) (hN : 0<N) (lam a : J → ℝ) :
    (∀ e : EuclideanSpace ℝ (Fin N), ‖e‖≤1 → ‖signalOperator h lam a e‖≤‖signalOperator h lam a‖) ∧
    ∃ e : EuclideanSpace ℝ (Fin N), ‖e‖=1 ∧ ‖signalOperator h lam a e‖=‖signalOperator h lam a‖ := by
  let _ : Nonempty (Fin N) := ⟨⟨0,hN⟩⟩
  exact ⟨fun e he => ((signalOperator h lam a).le_opNorm e).trans
    (by simpa using mul_le_mul_of_nonneg_left he (norm_nonneg _)),
    finite_operator_norm_attained _⟩

end
end bezout.Channel
