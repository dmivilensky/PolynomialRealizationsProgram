import jacobi.Finite.ResolventLax
import chebyshev2.Green.Markov

/-!
Positive spectral calculus and matrix-power estimates for the actual flow.
All reciprocal-gap eigenvalues are positive and individually bounded by
their fixed sum. Conjugation by the actual orthonormal basis transfers
these scalar estimates to every physical diagonal.
Use: FlowBounds bounds the first two energy derivatives by the conserved
scaled trace, uniformly in the dimension and in real flow time.
Article: jacobi, Proposition 5.5, Equation (5.12).
Article role: the spectral trace bounds, paired energy derivative and acceleration estimate.
-/
namespace jacobi.Finite
noncomputable section
open Matrix Real chebyshev2
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} (S : Nodes (n+1))

/-- The fixed positive reciprocal-gap eigenvalues of the Green inverse.
Article: jacobi, Proposition 5.5, Equation (5.12).
-/
def flowEigenvalue (k : Fin (n+1)) : ℝ := (1-S.value k)⁻¹

/-- The fixed, unscaled Green trace. Division by the squared dimension
gives the conserved scalar in the differential estimates.
Article: jacobi, Proposition 5.5, Equation (5.12).
-/
def flowTrace : ℝ := ∑ k,flowEigenvalue S k

/-- The actual Green inverse transported by the canonical spectral basis.
Article: jacobi, Proposition 5.5, Equation (5.12).
-/
def flowGreen (w : WeightSimplex (n+1)) (t : ℝ) :
    Matrix (Fin (n+1)) (Fin (n+1)) ℝ := flowSpectral S w (flowEigenvalue S) t

/-- Every Green eigenvalue is positive because every root is below one.
Article: jacobi, Proposition 5.5, Equation (5.12).
-/
theorem flowEigenvalue_pos (k : Fin (n+1)) : 0<flowEigenvalue S k :=
  inv_pos.mpr (sub_pos.mpr (S.interval k).2)

/-- Each eigenvalue is bounded by the complete positive trace.
Article: jacobi, Proposition 5.5, Equation (5.12).
-/
theorem flowEigenvalue_le_trace (k : Fin (n+1)) : flowEigenvalue S k≤flowTrace S :=
  Finset.single_le_sum (fun l _ => (flowEigenvalue_pos S l).le) (Finset.mem_univ k)

/-- The spectral trace is positive in every nonempty dimension.
Article: jacobi, Proposition 5.5, Equation (5.12).
-/
theorem flowTrace_pos : 0<flowTrace S :=
  Finset.sum_pos (fun k _ => flowEigenvalue_pos S k) Finset.univ_nonempty

/-- Transported spectral observables multiply pointwise in the original
fixed node list.
Article: jacobi, Proposition 5.5, Equation (5.12).
-/
theorem flowSpectral_mul (w : WeightSimplex (n+1)) (f g : Fin (n+1) → ℝ) (t : ℝ) :
    flowSpectral S w f t*flowSpectral S w g t=flowSpectral S w (fun k => f k*g k) t := by
  unfold flowSpectral
  have h := (flowMeasure S w t).eigenvectors_transpose_mul
  change (flowBasis S w t)ᵀ*flowBasis S w t=1 at h
  calc
    _=flowBasis S w t*diagonal f*((flowBasis S w t)ᵀ*flowBasis S w t)*
        diagonal g*(flowBasis S w t)ᵀ := by simp only [Matrix.mul_assoc]
    _=flowBasis S w t*(diagonal f*diagonal g)*(flowBasis S w t)ᵀ := by
      rw [h,Matrix.mul_one]
      simp only [Matrix.mul_assoc]
    _=_ := by rw [Matrix.diagonal_mul_diagonal]

/-- The trace of a transported observable is the exact sum of its
spectral values; no basis-dependent estimate is used.
Article: jacobi, Proposition 5.5, Equation (5.12).
-/
theorem flowSpectral_trace (w : WeightSimplex (n+1)) (f : Fin (n+1) → ℝ) (t : ℝ) :
    trace (flowSpectral S w f t)=∑ k,f k := by
  rw [flowSpectral,Matrix.trace_mul_cycle]
  have h := (flowMeasure S w t).eigenvectors_transpose_mul
  change (flowBasis S w t)ᵀ*flowBasis S w t=1 at h
  rw [h,Matrix.one_mul,Matrix.trace_diagonal]

/-- The scaled spectral Green definition is the actual inverse of the
reconstructed matrix at every time.
Article: jacobi, Proposition 5.5, Equation (5.12).
-/
theorem flowGreen_eq (w : WeightSimplex (n+1)) (t : ℝ) :
    flowGreen S w t=(reconstructFiber S (resolventWeights S w t)).val.green :=
  flowSpectral_green S w t

/-- The transported Green matrix is symmetric in physical coordinates.
Article: jacobi, Proposition 5.5, Equation (5.12).
-/
theorem flowGreen_symmetric (w : WeightSimplex (n+1)) (t : ℝ) (i j : Fin (n+1)) :
    flowGreen S w t i j=flowGreen S w t j i := by
  simp only [flowGreen,flowSpectral_entry]
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- Every physical Green entry is strictly positive. This reuses the
proved Jacobi Green positivity for the actual reconstructed matrix.
Article: jacobi, Proposition 5.5, Equation (5.12).
-/
theorem flowGreen_pos (w : WeightSimplex (n+1)) (t : ℝ) (i j : Fin (n+1)) :
    0<flowGreen S w t i j := by
  let J := reconstructFiber S (resolventWeights S w t)
  have hp : (1-J.val.matrix).PosDef := by
    have h := J.val.affine_posDef 1 (-1) (fun x hx => by
      rw [S.spectrum_eq J.property] at hx
      obtain ⟨k,rfl⟩ := hx
      linarith [(S.interval k).2])
    simpa [Matrix.scalar,sub_eq_add_neg] using h
  rw [flowGreen_eq]
  exact J.val.green_entry_pos hp J.property.1 i j

/-- The diagonal of the squared Green matrix is bounded by trace times
the original diagonal. This is the first derivative estimate's matrix input.
Article: jacobi, Proposition 5.5, Equation (5.12).
-/
theorem flowGreen_square_diag_le (w : WeightSimplex (n+1)) (t : ℝ) (i : Fin (n+1)) :
    (flowGreen S w t*flowGreen S w t) i i≤flowTrace S*flowGreen S w t i i := by
  rw [flowGreen,flowSpectral_mul,flowSpectral_entry,flowSpectral_entry,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro k _
  have h := mul_le_mul_of_nonneg_right (flowEigenvalue_le_trace S k)
    (mul_nonneg (sq_nonneg (flowBasis S w t i k)) (flowEigenvalue_pos S k).le)
  nlinarith

/-- The diagonal of the cubed Green matrix is bounded by trace squared
times the original diagonal. This controls the second diagonal derivative.
Article: jacobi, Proposition 5.5, Equation (5.12).
-/
theorem flowGreen_cube_diag_le (w : WeightSimplex (n+1)) (t : ℝ) (i : Fin (n+1)) :
    (flowGreen S w t*flowGreen S w t*flowGreen S w t) i i≤
      (flowTrace S)^2*flowGreen S w t i i := by
  rw [flowGreen,flowSpectral_mul,flowSpectral_mul,flowSpectral_entry,flowSpectral_entry,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro k _
  have hl := flowEigenvalue_pos S k
  have ht := flowTrace_pos S
  have he := flowEigenvalue_le_trace S k
  have hsq := mul_self_le_mul_self hl.le he
  have h := mul_le_mul_of_nonneg_right hsq
    (mul_nonneg (sq_nonneg (flowBasis S w t i k)) hl.le)
  nlinarith

end
end jacobi.Finite
