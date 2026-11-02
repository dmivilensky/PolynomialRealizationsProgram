import jacobi.Finite.ClosedSpectrum
import jacobi.Finite.MatrixEncoding
import jacobi.Variational.ClosedTransfer
import Mathlib.Topology.Algebra.Group.Matrix

/-!
Attainment of the minimum over the entire closed polynomial fibre.
The admissible matrices form a closed subset of the compact operator-norm
unit ball. Their endpoint pencils are positive definite, so inversion and
the diagonal-square energy are continuous. Encoding a minimizing matrix
recovers an actual Jacobi chain, allowing every zero-link restart pattern.
Use: AllThreeTerm can state a minimum rather than an unattained infimum.
Article: jacobi, Lemma 5.2 and Theorem 5.3.
Article role: compactness and attainment of the full finite-fibre minimum.
-/
namespace jacobi.Finite
noncomputable section
open chebyshev1 chebyshev2 Matrix Polynomial Set Filter
open scoped Topology Matrix.Norms.L2Operator
set_option backward.isDefEq.respectTransparency false

/-- A matrix presentation of the full fibre. Polynomial equality is
expressed by all determinant evaluations to make closedness transparent.
Article: jacobi, Lemma 5.2 and Theorem 5.3.
-/
def closedMatrixFibre {N : ℕ} (S : ClosedNodes N) : Set (Matrix (Fin N) (Fin N) ℝ) :=
  {A | (∀ i j,A i j=A j i) ∧
    (∀ i j,i.val+1=j.val → 0≤A i j) ∧
    (∀ i j,i.val+1 < j.val ∨ j.val+1 < i.val → A i j=0) ∧
    ∀ x : ℝ,(Matrix.scalar (Fin N) x-A).det=S.polynomial.eval x}

/-- The symmetry constraints are exactly real Hermitian symmetry.
Article: jacobi, Lemma 5.2 and Theorem 5.3.
-/
theorem closedMatrixFibre_hermitian {N : ℕ} {S : ClosedNodes N}
    {A : Matrix (Fin N) (Fin N) ℝ} (hA : A∈closedMatrixFibre S) : A.IsHermitian := by
  ext i j
  simpa only [Matrix.conjTranspose_apply,star_trivial] using hA.1 j i

/-- A matrix in the closed presentation has precisely the prescribed
characteristic polynomial, including repeated roots and endpoint roots.
Article: jacobi, Lemma 5.2 and Theorem 5.3.
-/
theorem closedMatrixFibre_charpoly {N : ℕ} {S : ClosedNodes N}
    {A : Matrix (Fin N) (Fin N) ℝ} (hA : A∈closedMatrixFibre S) :
    A.charpoly=S.polynomial := by
  apply Polynomial.funext
  intro x
  rw [Matrix.eval_charpoly]
  exact hA.2.2.2 x

/-- The canonical nonnegative Jacobi encoding recovers every matrix in
the compact set, so the matrix proof does not enlarge the admissible fibre.
Article: jacobi, Lemma 5.2 and Theorem 5.3.
-/
theorem closedMatrixFibre_encode {N : ℕ} {S : ClosedNodes N}
    {A : Matrix (Fin N) (Fin N) ℝ} (hA : A∈closedMatrixFibre S) :
    (fromMatrix A).matrix=A ∧ InClosedFiber (fromMatrix A) S.polynomial := by
  have h := fromMatrix_eq A (closedMatrixFibre_hermitian hA) hA.2.1 hA.2.2.1
  exact ⟨h,by rw [InClosedFiber,h]; exact closedMatrixFibre_charpoly hA⟩

/-- Conversely, every actual closed-fibre chain belongs to the matrix
presentation; no irreducibility condition is introduced at the boundary.
Article: jacobi, Lemma 5.2 and Theorem 5.3.
-/
theorem ClosedNodes.matrix_mem {N : ℕ} (S : ClosedNodes N) {J : Jacobi N}
    (hJ : InClosedFiber J S.polynomial) : J.matrix∈closedMatrixFibre S := by
  refine ⟨fun i j => J.matrix_isHermitian.isSymm.apply j i,?_,?_,?_⟩
  · intro i j hij
    have hij' : i≠j := by intro h; subst j; omega
    simp only [Jacobi.matrix,JacobiData.matrix_apply,ite_eq_right hij',ite_eq_left hij]
    positivity
  · intro i j hij
    have hne : i≠j := by intro h; subst j; omega
    have hu : ¬i.val+1=j.val := by omega
    have hl : ¬j.val+1=i.val := by omega
    simp [Jacobi.matrix,JacobiData.matrix_apply,hne,hu,hl]
  · intro x
    rw [← Matrix.eval_charpoly,hJ]

/-- All matrix constraints are closed: linear symmetry, nonnegative
links, vanished remote entries, and continuous determinant evaluations.
Article: jacobi, Lemma 5.2 and Theorem 5.3.
-/
theorem closedMatrixFibre_closed {N : ℕ} (S : ClosedNodes N) :
    IsClosed (closedMatrixFibre S) := by
  have hc (i j : Fin N) : Continuous (fun A : Matrix (Fin N) (Fin N) ℝ => A i j) :=
    (continuous_apply j).comp (continuous_apply i)
  simp only [closedMatrixFibre,ofPred_and,ofPred_forall]
  refine (isClosed_iInter (fun i => isClosed_iInter (fun j =>
    isClosed_eq (hc i j) (hc j i)))).inter ?_
  refine (isClosed_iInter (fun i => isClosed_iInter (fun j => isClosed_iInter (fun _ =>
    isClosed_le continuous_const (hc i j))))).inter ?_
  refine (isClosed_iInter (fun i => isClosed_iInter (fun j => isClosed_iInter (fun _ =>
    isClosed_eq (hc i j) continuous_const)))).inter ?_
  exact isClosed_iInter (fun x : ℝ =>
    isClosed_eq (by fun_prop) continuous_const)

/-- The entire fibre is compact. Fixed roots in [-1,1) bound the
operator norm even at reducible and repeated-root boundary points.
Article: jacobi, Lemma 5.2 and Theorem 5.3.
-/
theorem closedMatrixFibre_compact {N : ℕ} (S : ClosedNodes N) :
    IsCompact (closedMatrixFibre S) := by
  apply (isCompact_closedBall (0 : Matrix (Fin N) (Fin N) ℝ) 1).of_isClosed_subset
    (closedMatrixFibre_closed S)
  intro A hA
  rw [mem_closedBall_zero_iff]
  obtain ⟨hmat,hmem⟩ := closedMatrixFibre_encode hA
  have h := S.norm_le_one hmem
  simpa only [opNorm,hmat] using h

/-- The literal matrix inverse energy is continuous everywhere on the
compact fibre, since all endpoint determinants are strictly positive.
Article: jacobi, Lemma 5.2 and Theorem 5.3.
-/
theorem closedMatrixFibre_energy_continuous {N : ℕ} (S : ClosedNodes N) :
    ContinuousOn (fun A : Matrix (Fin N) (Fin N) ℝ => ∑ i,((1-A)⁻¹ i i)^2)
      (closedMatrixFibre S) := by
  intro A hA
  obtain ⟨hmat,hmem⟩ := closedMatrixFibre_encode hA
  have hp : (1-A).PosDef := by simpa only [hmat] using S.endpoint_posDef hmem
  have hi : ContinuousAt (Inv.inv : Matrix (Fin N) (Fin N) ℝ → Matrix (Fin N) (Fin N) ℝ)
      (1-A) := by
    apply continuousAt_matrix_inv
    simpa only [Ring.inverse_eq_inv'] using continuousAt_inv₀ hp.det_pos.ne'
  have hg := hi.comp (continuousAt_const.sub continuousAt_id)
  apply ContinuousAt.continuousWithinAt
  exact tendsto_finsetSum _ (fun i _ =>
    (((continuous_apply i).continuousAt.comp ((continuous_apply i).continuousAt.comp hg)).pow 2).tendsto)

/-- Every finite closed polynomial fibre has an actual minimizing
Jacobi chain. Zero links and repeated roots require no extra premise.
Article: jacobi, Lemma 5.2 and Theorem 5.3.
-/
theorem ClosedNodes.exists_minimizer {N : ℕ} (S : ClosedNodes N) :
    ∃ J : Jacobi N,InClosedFiber J S.polynomial ∧
      ∀ K : Jacobi N,InClosedFiber K S.polynomial → J.energy≤K.energy := by
  obtain ⟨A,hA,hmin⟩ := (closedMatrixFibre_compact S).exists_isMinOn
    ⟨S.diagonalChain.matrix,S.matrix_mem S.diagonalChain_mem⟩
    (closedMatrixFibre_energy_continuous S)
  obtain ⟨hmat,hmem⟩ := closedMatrixFibre_encode hA
  refine ⟨fromMatrix A,hmem,fun K hK => ?_⟩
  have h : (∑ i,((1-A)⁻¹ i i)^2)≤∑ i,((1-K.matrix)⁻¹ i i)^2 := hmin (S.matrix_mem hK)
  simpa only [Jacobi.energy,Jacobi.green,hmat] using h

/-- The normalized infimum used in continuum transfer is attained by
the same actual finite minimizer. This is the finite minimum formulation.
Article: jacobi, Lemma 5.2 and Theorem 5.3.
-/
theorem ClosedNodes.exists_minimum_cost {N : ℕ} (S : ClosedNodes N) :
    ∃ J : Jacobi N,InClosedFiber J S.polynomial ∧
      jacobi.Variational.closedFibreEnergyInfimum S=jacobi.Variational.fibreCost J := by
  obtain ⟨J,hJ,hmin⟩ := S.exists_minimizer
  refine ⟨J,hJ,le_antisymm (sInf_le ⟨J,hJ,rfl⟩) ?_⟩
  apply le_sInf
  rintro _ ⟨K,hK,rfl⟩
  exact ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right (hmin K hK) (by positivity))

end
end jacobi.Finite
