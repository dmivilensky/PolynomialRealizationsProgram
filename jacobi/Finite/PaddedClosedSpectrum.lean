import jacobi.Finite.ClosedSpectrum
import jacobi.Finite.PrefixSorting

/-!
The actual closed spectrum after adjoining any number of minus-one roots.
The active roots retain their exact ordered resolvent coordinates. The
repeated tail contributes its exact trace, with no simplicity assumption.
Use: AllThreeTerm derives the quarter-scaled Bessel spectrum of the full
Nesterov polynomial, including every restarted realization of that polynomial.
Article: jacobi, Theorem 5.3.
Article role: the full repeated-root spectrum and its quarter-scaled l1 edge limit.
-/
namespace jacobi.Finite
noncomputable section
open chebyshev1 chebyshev2 chebyshev2.Continuum Matrix Polynomial
open scoped BigOperators Classical
set_option backward.isDefEq.respectTransparency false

/-- Adjoin a repeated left endpoint to an arbitrary simple interior
root list. The new fibre has the full degree, rather than its active degree.
Article: jacobi, Theorem 5.3.
-/
def Nodes.padMinusOne {N : ℕ} (S : Nodes N) (L : ℕ) : ClosedNodes (N+L) where
  value i := if hi : i.val < N then S.value ⟨i.val,hi⟩ else -1
  antitone := by
    intro i j hij
    change (if hj : j.val < N then S.value ⟨j.val,hj⟩ else -1)≤
      (if hi : i.val < N then S.value ⟨i.val,hi⟩ else -1)
    by_cases hi : i.val < N
    · by_cases hj : j.val < N
      · simp only [dite_eq_left hi,dite_eq_left hj]
        exact S.strictAnti.antitone hij
      · simp only [dite_eq_left hi,dite_eq_right hj]
        exact (S.interval _).1.le
    · have hj : ¬j.val < N := by omega
      simp only [dite_eq_right hi,dite_eq_right hj,le_refl]
  interval := by
    intro i
    split_ifs
    · exact ⟨(S.interval _).1.le,(S.interval _).2⟩
    · norm_num

/-- The padded polynomial is exactly the original monic polynomial
times the additional repeated endpoint factor.
Article: jacobi, Theorem 5.3.
-/
theorem Nodes.padMinusOne_polynomial {N : ℕ} (S : Nodes N) (L : ℕ) :
    (S.padMinusOne L).polynomial=S.polynomial*(X+1)^L := by
  rw [ClosedNodes.polynomial,Fin.prod_univ_add]
  simp [Nodes.padMinusOne,Nodes.polynomial]

/-- The diagonal representative has the literal normalized inverse gaps
as its diagonal. This includes every repeated endpoint eigenvalue.
Article: jacobi, Theorem 5.3.
-/
theorem ClosedNodes.normalizedGreen_diagonal {N : ℕ} (S : ClosedNodes N) :
    S.diagonalChain.normalizedGreen=
      diagonal (fun i => (1-S.value i)⁻¹/(N:ℝ)^2) := by
  rw [Jacobi.normalizedGreen,Jacobi.green,S.diagonalChain_matrix,
    ← Matrix.diagonal_one,Matrix.diagonal_sub,Matrix.inv_diagonal,← Matrix.diagonal_smul]
  congr 1
  funext i
  simp only [Pi.smul_apply,smul_eq_mul]
  have hu : IsUnit (fun j : Fin N => 1-S.value j) :=
    Pi.isUnit_iff.mpr (fun j => isUnit_iff_ne_zero.mpr (sub_pos.mpr (S.interval j).2).ne')
  have hi := congrFun (Ring.inverse_mul_cancel _ hu) i
  change Ring.inverse (fun j : Fin N => 1-S.value j) i*(1-S.value i)=1 at hi
  have he : Ring.inverse (fun j : Fin N => 1-S.value j) i=1/(1-S.value i) :=
    (eq_div_iff (sub_pos.mpr (S.interval i).2).ne').mpr hi
  rw [he]
  ring

/-- Sorting the actual diagonal Green inverse is exactly ordinary
positive spectral sorting, without an assumed enumeration of eigenvalues.
Article: jacobi, Theorem 5.3.
-/
theorem ClosedNodes.closedFibreSpectrum_sorted {N : ℕ} (S : ClosedNodes N) :
    closedFibreSpectrum S=spectralSorted (Summable.of_finite
      (f := fun i : Fin N => (1-S.value i)⁻¹/(N:ℝ)^2)) := by
  unfold closedFibreSpectrum closedSpectrum
  have hp (i : Fin N) : 0≤(1-S.value i)⁻¹/(N:ℝ)^2 := by
    exact div_nonneg (inv_nonneg.mpr (sub_pos.mpr (S.interval i).2).le) (sq_nonneg _)
  have he := matrix_eigenvalue_eq_of_charpoly S.diagonalChain.normalizedGreen
    (diagonal (fun i => (1-S.value i)⁻¹/(N:ℝ)^2))
    (normalizedGreen_posSemidef_of_posDef (S.endpoint_posDef S.diagonalChain_mem))
    (Matrix.posSemidef_diagonal_iff.mpr hp) (by rw [S.normalizedGreen_diagonal])
  rw [he,diagonal_matrix_eigenvalue _ hp]

/-- The active part of the sorted spectrum is unaffected by the repeated
endpoint tail, except for the full dimension in its normalization.
Article: jacobi, Theorem 5.3.
-/
theorem Nodes.padMinusOne_spectrum {N L j : ℕ} (S : Nodes N) (hj : j < N) :
    closedFibreSpectrum (S.padMinusOne L) j=
      (1-S.value ⟨j,hj⟩)⁻¹/(N+L:ℕ)^2 := by
  have hdim : 0<(N+L:ℕ) := by omega
  rw [ClosedNodes.closedFibreSpectrum_sorted]
  apply (spectralSorted_prefix (Nat.le_add_right N L) (n := j) _ _ Summable.of_finite hj).trans
    (by simp [Nodes.padMinusOne,hj])
  · intro i k hi hik
    have hi' : (S.padMinusOne L).value k<(S.padMinusOne L).value i := by
      dsimp only [Nodes.padMinusOne]
      rw [dite_eq_left hi]
      split_ifs with hk
      · exact S.strictAnti hik
      · exact (S.interval _).1
    exact div_lt_div_of_pos_right
      (inv_strictAnti₀ (sub_pos.mpr ((S.padMinusOne L).interval i).2) (by linarith))
      (pow_pos (Nat.cast_pos.mpr hdim) 2)
  · intro i
    exact div_pos (inv_pos.mpr (sub_pos.mpr ((S.padMinusOne L).interval i).2))
      (pow_pos (Nat.cast_pos.mpr hdim) 2)

/-- The whole common spectrum is summable, with its actual finite trace.
Article: jacobi, Theorem 5.3.
-/
theorem ClosedNodes.closedFibreSpectrum_sum {N : ℕ} (S : ClosedNodes N) :
    (∑' j,closedFibreSpectrum S j)=∑ i : Fin N,(1-S.value i)⁻¹/(N:ℝ)^2 := by
  unfold closedFibreSpectrum closedSpectrum
  rw [matrixSpectrum_tsum_trace,S.normalizedGreen_diagonal,Matrix.trace_diagonal]

/-- The repeated endpoint tail contributes exactly one half per added
root before division by the square of the full degree.
Article: jacobi, Theorem 5.3.
-/
theorem Nodes.padMinusOne_sum {N : ℕ} (S : Nodes N) (L : ℕ) :
    (∑' j,closedFibreSpectrum (S.padMinusOne L) j)=
      (∑ i : Fin N,(1-S.value i)⁻¹)/(N+L:ℕ)^2+(L:ℝ)/(2*(N+L:ℕ)^2) := by
  rw [ClosedNodes.closedFibreSpectrum_sum,Fin.sum_univ_add]
  simp only [Nodes.padMinusOne,Fin.val_castAdd,Fin.val_natAdd]
  have h1 : (∑ i : Fin N,(1-(if hi : i.val < N then S.value ⟨i.val,hi⟩ else -1))⁻¹/
      ((N+L:ℕ):ℝ)^2)=(∑ i : Fin N,(1-S.value i)⁻¹)/((N+L:ℕ):ℝ)^2 := by
    simp only [dite_eq_left (Fin.isLt _),Fin.eta,Finset.sum_div]
  rw [h1]
  congr 1
  norm_num [show ∀ i : Fin L,¬N+i.val < N from fun _ => by omega,div_eq_mul_inv,_root_.mul_inv_rev,mul_comm]

end
end jacobi.Finite
