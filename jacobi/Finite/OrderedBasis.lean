import jacobi.Finite.SpectralUniqueness
import Mathlib.Analysis.Matrix.Spectrum

/-!
Article: jacobi, Equation (1.3) (unique persymmetric realization and its weights).
The ordinary finite spectral theorem is relabelled to match the article's
prescribed nodes. No ordered eigenbasis or spectral enumeration is assumed.
Source: mathlib, the finite real Hermitian spectral theorem.
Use: aligns a community spectral basis with the prescribed root enumeration.
-/

namespace jacobi.Finite
noncomputable section
open chebyshev1 chebyshev2 Matrix
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

variable {N : ℕ}

/-- Permute spectral columns while keeping the physical coordinate order fixed.
Use: aligns a community spectral basis with the prescribed root enumeration.
Article: jacobi, Equation (1.3) (unique persymmetric realization and its weights).
-/
def relabelBasis {A : Matrix (Fin N) (Fin N) ℝ} (B : SpectralBasis A)
    (e : Equiv.Perm (Fin N)) : SpectralBasis A where
  Q i j := B.Q i (e j)
  eigenvalues j := B.eigenvalues (e j)
  transpose_mul := by
    ext i j
    change (∑ k, B.Q k (e i) * B.Q k (e j)) = if i = j then 1 else 0
    have h := congrArg (fun C : Matrix (Fin N) (Fin N) ℝ => C (e i) (e j)) B.transpose_mul
    simpa only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, e.injective.eq_iff] using h
  mul_transpose := by
    ext i j
    change (∑ k, B.Q i (e k) * B.Q j (e k)) = (1 : Matrix (Fin N) (Fin N) ℝ) i j
    rw [Equiv.sum_comp e (fun k => B.Q i k * B.Q j k)]
    exact congrArg (fun C : Matrix (Fin N) (Fin N) ℝ => C i j) B.mul_transpose
  diagonalize := by
    ext i j
    change (∑ k, (∑ l, B.Q l (e i) * A l k) * B.Q k (e j)) =
      if i = j then B.eigenvalues (e i) else 0
    have h := congrArg (fun C : Matrix (Fin N) (Fin N) ℝ => C (e i) (e j)) B.diagonalize
    simpa only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.diagonal_apply,
      e.injective.eq_iff] using h

/-- Every arbitrary-fibre matrix admits a spectral basis in the prescribed node order.
Use: the spectral weight map is defined for every fibre element without extra inputs.
Article: jacobi, Equation (1.3) (unique persymmetric realization and its weights).
Proof: every node occurs in the ordinary spectral basis; distinctness makes the
chosen indexing an injection of a finite set into itself, hence a permutation. -/
theorem exists_ordered_basis (S : Nodes N) (J : Jacobi N) (hJ : InFiber J S.polynomial) :
    ∃ B : SpectralBasis J.matrix, B.eigenvalues = S.value := by
  -- Match each prescribed node to an eigenvalue and use finite injectivity to obtain a permutation.
  let B := SpectralBasis.ofHermitian J.matrix J.matrix_isHermitian
  have he (k : Fin N) : ∃ i : Fin N, B.eigenvalues i = S.value k := by
    have h : S.value k ∈ spectrum ℝ J.matrix := by
      rw [S.spectrum_eq hJ]
      exact ⟨k, rfl⟩
    rw [J.matrix_isHermitian.spectrum_real_eq_range_eigenvalues] at h
    exact h
  let f : Fin N → Fin N := fun k => Classical.choose (he k)
  have hf (k : Fin N) : B.eigenvalues (f k) = S.value k := Classical.choose_spec (he k)
  have hinj : Function.Injective f := by
    intro i j hij
    apply S.strictAnti.injective
    rw [← hf i, ← hf j, hij]
  let e := Equiv.ofBijective f ⟨hinj, Finite.surjective_of_injective hinj⟩
  refine ⟨relabelBasis B e, ?_⟩
  funext k
  exact hf k

/-- A chosen existing ordered basis for each actual fibre element.
Use: supplies the spectral probability chart while keeping choices out of theorem hypotheses.
Article: jacobi, Equation (1.3) (unique persymmetric realization and its weights).
-/
def orderedBasis (S : Nodes N) (J : Jacobi N) (hJ : InFiber J S.polynomial) :
    SpectralBasis J.matrix := Classical.choose (exists_ordered_basis S J hJ)

/-- The chosen basis has exactly the prescribed eigenvalue order.
Use: discharges all enumeration hypotheses in the reconstruction and uniqueness theorems.
Article: jacobi, Equation (1.3) (unique persymmetric realization and its weights).
Proof: the basis is chosen from the proved ordered-basis existence statement. -/
theorem orderedBasis_values (S : Nodes N) (J : Jacobi N) (hJ : InFiber J S.polynomial) :
    (orderedBasis S J hJ).eigenvalues = S.value :=
  Classical.choose_spec (exists_ordered_basis S J hJ)

end
end jacobi.Finite
