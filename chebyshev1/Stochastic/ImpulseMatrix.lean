import chebyshev1.Stochastic.ScalarExpansion
import chebyshev1.Stochastic.GossipAsymptotics
import chebyshev1.Spectral.DiagonalResponse
import chebyshev1.Realization.Coordinates

/-! A single curvature impulse as the actual deterministic forcing response. -/
namespace chebyshev1
noncomputable section
open scoped BigOperators Matrix
set_option backward.isDefEq.respectTransparency false
variable {ι d : Type*} [Fintype ι] [DecidableEq ι] [Fintype d] [DecidableEq d]

namespace Realization

theorem linearResponse_single_time (R : Realization ι) {N s : ℕ} (hs : s<N)
    (H E : Matrix d d ℝ) :
    R.linearResponse N H (fun t => if t=s then E else 0) =
      R.scalarNoiseCoefficient N H (fun _ => E) {s} := by
  rw [linearResponse_eq_sum, scalarNoiseCoefficient_singleton _ hs]
  rw [Finset.sum_eq_single s]
  · simp
  · intro t _ hts
    simp only [hts, ite_false, operatorInsertion, Matrix.kronecker_zero,
      neg_zero, Matrix.mul_zero, Matrix.zero_mul]
    change R.contractLinear 0=0
    exact map_zero _
  · intro hh
    exact (hh (Finset.mem_range.mpr hs)).elim

end Realization

namespace TwoTerm

/-- The matrix mapping the initial state to a single curvature-noise response. -/
def curvatureImpulse (S : TwoTerm) (H : Matrix d d ℝ) (N s : ℕ)
    (E : Matrix d d ℝ) : Matrix d d ℝ :=
  -S.gamma s • ((orderedProduct (fun i => S.memoryStep (s+1+i) H) (N-(s+1)) 0 0) *
    E * S.realization.operatorTransfer s (fun _ => H))

theorem curvatureImpulse_eq_singleton (S : TwoTerm) {N s : ℕ} (hs : s<N)
    (H E : Matrix d d ℝ) :
    S.curvatureImpulse H N s E = S.realization.scalarNoiseCoefficient N H (fun _ => E) {s} := by
  rw [Realization.scalarNoiseCoefficient, S.insertionTerm_eq_memory,
    insertionTerm_singleton _ _ hs, curvatureImpulse, S.operatorTransfer_eq_memory]
  simp only [Matrix.mul_apply, Fin.sum_univ_two, memoryInsertion, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    mul_zero, zero_mul, add_zero, Matrix.mul_smul, smul_mul_assoc]

theorem curvatureImpulse_mulVec (S : TwoTerm) (H E : Matrix d d ℝ)
    (N s : ℕ) (v : d → ℝ) :
    (S.curvatureImpulse H N s E).mulVec v =
      -S.gamma s • S.forcingTail H N s (E.mulVec (S.quadraticError H v s)) := by
  rw [curvatureImpulse, Matrix.smul_mulVec, ← Matrix.mulVec_mulVec,
    ← Matrix.mulVec_mulVec, ← S.quadraticError_eq_transfer, S.forcingTail_eq_memoryProduct]

theorem curvatureImpulse_linearResponse (S : TwoTerm) {N s : ℕ} (hs : s<N)
    (H E : Matrix d d ℝ) :
    S.curvatureImpulse H N s E =
      S.realization.linearResponse N H (fun t => if t=s then E else 0) := by
  rw [S.realization.linearResponse_single_time hs, S.curvatureImpulse_eq_singleton hs]

theorem curvatureImpulse_diagonal_entry (S : TwoTerm) {N s : ℕ} (hs : s<N)
    (eig : d → ℝ) (E : Matrix d d ℝ) (i j : d) :
    S.curvatureImpulse (Matrix.diagonal eig) N s E i j =
      S.realization.kernel N s (eig i) (eig j)*E i j := by
  rw [S.curvatureImpulse_linearResponse hs, Realization.diagonal_linearResponse_entry]
  have hi (t : ℕ) : (if t=s then E else (0:Matrix d d ℝ)) i j =
      if t=s then E i j else 0 := by split_ifs <;> rfl
  simp_rw [hi, mul_ite, mul_zero]
  simp [Finset.mem_range.mpr hs]

theorem curvatureImpulse_coordinates (S : TwoTerm) {N s : ℕ} (hs : s<N)
    {H : Matrix d d ℝ} (B : SpectralBasis H) (E : Matrix d d ℝ) :
    B.coordinates (S.curvatureImpulse H N s E) =
      S.curvatureImpulse (Matrix.diagonal B.eigenvalues) N s (B.coordinates E) := by
  rw [S.curvatureImpulse_linearResponse hs, S.curvatureImpulse_linearResponse hs]
  have hh := S.realization.linearResponse_coordinates B.Q H B.transpose_mul B.mul_transpose N
    (fun t => if t=s then E else 0)
  rw [B.diagonalize] at hh
  simpa only [SpectralBasis.coordinates, mul_ite, ite_mul, Matrix.mul_zero,
    Matrix.zero_mul] using hh.symm

end TwoTerm
end
end chebyshev1
