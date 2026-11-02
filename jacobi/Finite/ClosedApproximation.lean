import jacobi.Finite.ClosedFiber
import jacobi.Finite.Affine
import Mathlib.Topology.Instances.Matrix

/-!
Approximating closed-fibre matrices by strictly contractive Jacobi chains.
The existing packing theorem already allows reducible chains. Shrinking
the entire matrix therefore suffices for transfer: repeated roots and zero
links need not first be removed by a separate irreducibility perturbation.
Matrix inversion and the actual energy converge by their finite-dimensional
continuity at the positive endpoint pencil.
Use: ClosedTransfer transports the packing bounds to spectra that include
the endpoint minus one, without introducing an energy or inverse-limit premise.
Article: jacobi, Lemma 5.2.
Article role: continuity and contractive approximation in the closed-fibre transfer proof.
-/
namespace jacobi.Finite
noncomputable section
open chebyshev1 chebyshev2 Matrix Polynomial Filter Set
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- Shrink a finite Jacobi matrix toward zero using its existing exact
affine coefficient encoding. Zero links remain zero.
Article: jacobi, Lemma 5.2.
-/
def closedApproximation {N : ℕ} (J : Jacobi N) (e : ℝ) : Jacobi N :=
  affine J (1-e) 0

/-- Every closed-fibre matrix has Euclidean operator norm at most one.
Article: jacobi, Lemma 5.2.
-/
theorem ClosedNodes.norm_le_one {N : ℕ} (S : ClosedNodes N) {J : Jacobi N}
    (hJ : InClosedFiber J S.polynomial) : opNorm J.matrix≤1 := by
  have he : aeval J.matrix (X:ℝ[X])=J.matrix := by simp
  rw [← he,opNorm_aeval_eq _ _ J.matrix_isHermitian]
  apply (pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ)≤1)).mpr
  intro i
  have h := J.matrix_isHermitian.eigenvalues_mem_spectrum_real i
  rw [S.spectrum_eq hJ] at h
  obtain ⟨k,hk⟩ := h
  rw [Polynomial.eval_X,← hk]
  simpa only [Real.norm_eq_abs] using abs_le.mpr ⟨(S.interval k).1,(S.interval k).2.le⟩

/-- On a genuine positive shrinking step, the new matrix is the intended
scalar multiple of the original symmetric matrix.
Article: jacobi, Lemma 5.2.
-/
theorem closedApproximation_matrix {N : ℕ} (J : Jacobi N) {e : ℝ} (he : e≤1) :
    (closedApproximation J e).matrix=(1-e) • J.matrix := by
  rw [closedApproximation,affine_matrix J (by linarith),map_zero,add_zero]

/-- Every positive shrinking step below one is strictly contractive,
even when the original fibre has repeated roots or zero links.
Article: jacobi, Lemma 5.2.
-/
theorem ClosedNodes.approximation_contractive {N : ℕ} (S : ClosedNodes N) {J : Jacobi N}
    (hJ : InClosedFiber J S.polynomial) {e : ℝ} (he : 0<e) (he1 : e<1) :
    opNorm (closedApproximation J e).matrix<1 := by
  rw [closedApproximation_matrix J he1.le,opNorm_smul,abs_of_pos (by linarith : 0<1-e)]
  exact (mul_le_mul_of_nonneg_left (S.norm_le_one hJ) (by linarith)).trans_lt
    (by simpa only [mul_one] using sub_lt_self (1:ℝ) he)

/-- The actual symmetric matrices converge to the original matrix in
the ordinary finite-dimensional matrix topology.
Article: jacobi, Lemma 5.2.
-/
theorem closedApproximation_matrix_limit {N : ℕ} (J : Jacobi N) :
    Tendsto (fun e : ℝ => (closedApproximation J e).matrix) (𝓝 0) (𝓝 J.matrix) := by
  have h : Tendsto (fun e : ℝ => (1-e) • J.matrix) (𝓝 0) (𝓝 J.matrix) := by
    simpa only [sub_zero,one_smul,id_eq] using
      ((tendsto_const_nhds (x := (1:ℝ))).sub (tendsto_id : Tendsto (fun e:ℝ => e) (𝓝 0) (𝓝 0))).smul
        (tendsto_const_nhds (x := J.matrix))
  apply h.congr'
  filter_upwards [eventually_lt_nhds (show (0:ℝ)<1 by norm_num)] with e he
  exact (closedApproximation_matrix J he.le).symm

/-- The actual Green inverses converge at every matrix with a positive
endpoint pencil. Invertibility is proved by its positive determinant.
Article: jacobi, Lemma 5.2.
-/
theorem closedApproximation_green_limit {N : ℕ} (J : Jacobi N)
    (hJ : (1-J.matrix).PosDef) :
    Tendsto (fun e : ℝ => (closedApproximation J e).green) (𝓝 0) (𝓝 J.green) := by
  have hi : ContinuousAt (Inv.inv : Matrix (Fin N) (Fin N) ℝ → Matrix (Fin N) (Fin N) ℝ)
      (1-J.matrix) := by
    apply continuousAt_matrix_inv
    simpa only [Ring.inverse_eq_inv'] using continuousAt_inv₀ hJ.det_pos.ne'
  exact hi.tendsto.comp (tendsto_const_nhds.sub (closedApproximation_matrix_limit J))

/-- The real energy itself converges, so the approximation does not
leave an assumed energy-continuity condition in the transfer argument.
Article: jacobi, Lemma 5.2.
-/
theorem closedApproximation_energy_limit {N : ℕ} (J : Jacobi N)
    (hJ : (1-J.matrix).PosDef) :
    Tendsto (fun e : ℝ => (closedApproximation J e).energy) (𝓝 0) (𝓝 J.energy) := by
  have h := closedApproximation_green_limit J hJ
  change Tendsto (fun e : ℝ => ∑ i,((closedApproximation J e).green i i)^2)
    (𝓝 0) (𝓝 (∑ i,(J.green i i)^2))
  apply tendsto_finsetSum
  intro i _
  exact (((continuous_apply i).tendsto _).comp (((continuous_apply i).tendsto _).comp h)).pow 2

end
end jacobi.Finite
