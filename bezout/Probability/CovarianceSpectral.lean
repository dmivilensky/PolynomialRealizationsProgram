import bezout.Probability.Covariance
import bezout.Channel.Signal

/-!
Article: bezout, Equation `eq:experiment-mse` and its general-covariance derivation.
Use: exact arbitrary-method bias and physical response variance split over
spectral modes, then over one rank-one mode and its orthogonal complement.
Proof: the actual covariance trace theorem and diagonal polynomial calculus;
all energies, dimensions and variances remain symbolic.
-/

namespace bezout.Probability
noncomputable section
open MeasureTheory Polynomial
open scoped BigOperators
variable {J : Type*} [Fintype J] [DecidableEq J]

/-- The exact additive-response variance profile of any fixed-coefficient history. -/
def varianceProfile {N : ℕ} (h : bezout.History N) (lam : ℝ) : ℝ :=
  ∑ s, (h.response s).eval lam^2

/-- A diagonal covariance response has precisely its coordinatewise variance energy. -/
theorem trace_diagonal_covariance (p v : J → ℝ) :
    Matrix.trace (Matrix.diagonal p*Matrix.diagonal v*(Matrix.diagonal p).transpose)=
      ∑ j, v j*p j^2 := by
  simp only [Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- A symbolic one-dimensional exceptional eigenspace and its bulk complement. -/
def twoLevelEigenvalues (j0 : J) (mu L : ℝ) (j : J) : ℝ := if j=j0 then L else mu

end
end bezout.Probability

namespace bezout.History
noncomputable section
open MeasureTheory Polynomial
open scoped BigOperators
variable {N : ℕ} {Ω J : Type*} [Fintype J] [DecidableEq J]
  {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {𝓕 : Filtration ℕ mΩ} {w : ℕ → Ω → EuclideanSpace ℝ J}

/-- Exact MSE in a genuine orthonormal eigenbasis with arbitrary coordinate variances. -/
theorem integral_stochasticOutput_spectral_covariance (h : bezout.History N)
    (lam v : J → ℝ) (a : EuclideanSpace ℝ J)
    (hw : bezout.Probability.MartingaleDifferences N 𝓕 w μ)
    (hV : ∀ s : Fin N, bezout.Probability.covarianceMatrix (w s.val) μ=Matrix.diagonal v) :
    (∫ ω, ‖h.stochasticOutput (matrixEnd (Matrix.diagonal lam)) a w ω‖^2 ∂μ)=
      (∑ j, a j^2*h.terminal.eval (lam j)^2)+
        ∑ j, v j*bezout.Probability.varianceProfile h (lam j) := by
  rw [h.integral_stochasticOutput_common_covariance _ _ hw (Matrix.diagonal v) hV]
  simp only [EuclideanSpace.norm_sq_eq, Real.norm_eq_abs, sq_abs,
    bezout.Channel.diagonal_polynomial_apply, mul_pow,
    chebyshev1.aeval_diagonal, bezout.Probability.trace_diagonal_covariance]
  congr 1
  · apply Finset.sum_congr rfl
    intro j _
    ring
  · rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    rw [← Finset.mul_sum]
    rfl

/-- The symbolic rank-one MSE split, including its actual bulk multiplicity.
Use: every compared method contributes its own finite terminal and response profile. -/
theorem integral_stochasticOutput_rankOne (h : bezout.History N)
    (j0 : J) (mu L variance : ℝ) (a : EuclideanSpace ℝ J)
    (hw : bezout.Probability.MartingaleDifferences N 𝓕 w μ)
    (hV : ∀ s : Fin N, bezout.Probability.covarianceMatrix (w s.val) μ=
      Matrix.diagonal (fun _ : J => variance)) :
    (∫ ω, ‖h.stochasticOutput (matrixEnd (Matrix.diagonal (bezout.Probability.twoLevelEigenvalues j0 mu L)))
      a w ω‖^2 ∂μ)=
      (∑ j ∈ Finset.univ.erase j0, a j^2)*h.terminal.eval mu^2+
      a j0^2*h.terminal.eval L^2+
      variance*((Fintype.card J-1 : ℕ)*bezout.Probability.varianceProfile h mu+
        bezout.Probability.varianceProfile h L) := by
  rw [h.integral_stochasticOutput_spectral_covariance _ _ a hw hV]
  have hI : j0∈(Finset.univ : Finset J) := Finset.mem_univ _
  rw [← Finset.sum_erase_add Finset.univ
    (fun j => a j^2*h.terminal.eval (bezout.Probability.twoLevelEigenvalues j0 mu L j)^2) hI,
    ← Finset.sum_erase_add Finset.univ
    (fun j => variance*bezout.Probability.varianceProfile h (bezout.Probability.twoLevelEigenvalues j0 mu L j)) hI]
  have hb : (∑ j ∈ Finset.univ.erase j0,
      a j^2*h.terminal.eval (bezout.Probability.twoLevelEigenvalues j0 mu L j)^2)=
      (∑ j ∈ Finset.univ.erase j0, a j^2)*h.terminal.eval mu^2 := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j hj
    simp [bezout.Probability.twoLevelEigenvalues, (Finset.mem_erase.mp hj).1]
  have hv : (∑ j ∈ Finset.univ.erase j0,
      variance*bezout.Probability.varianceProfile h (bezout.Probability.twoLevelEigenvalues j0 mu L j))=
      (Fintype.card J-1 : ℕ)*(variance*bezout.Probability.varianceProfile h mu) := by
    calc
      _ = ∑ _j ∈ Finset.univ.erase j0, variance*bezout.Probability.varianceProfile h mu := by
        apply Finset.sum_congr rfl
        intro j hj
        simp [bezout.Probability.twoLevelEigenvalues, (Finset.mem_erase.mp hj).1]
      _ = _ := by simp
  rw [hb,hv]
  simp only [bezout.Probability.twoLevelEigenvalues, ite_true]
  ring

end
end bezout.History
