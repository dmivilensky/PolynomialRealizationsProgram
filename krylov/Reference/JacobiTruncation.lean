import jacobi.Finite.OrderedSpectrum
set_option autoImplicit false
/-!
Article: main_krylov, prop:phi(c), true finite original Jacobi restrictions.
Use: reuse the earlier article simple-spectrum theorem on the actual original finite block without spectral window assumptions.
Source: genuine chronological coefficient truncation and jacobi finite irreducible Jacobi spectral simplicity.
-/

namespace krylov.Reference
noncomputable section
open Matrix chebyshev1 chebyshev2

/-- The actual finite truncation of the original nonnegative-coupling Jacobi coefficient sequence.
Use: The actual finite truncation of the original nonnegative-coupling Jacobi coefficient sequence.
Article: main_krylov, prop:phi(c), true finite original Jacobi restrictions.
Proof: Retain every used original coefficient and set only the unused exterior data to zero. -/
def truncateJacobi (J : JacobiData) (hJ : ∀ n,0≤J.aSq n) (N : ℕ) : Jacobi N where
  data := ⟨fun n => if n<N then J.b n else 0,fun n => if 0<n ∧ n<N then J.aSq n else 0⟩
  coupling_nonneg n := by
    dsimp
    split
    · exact hJ n
    · exact le_rfl
  coupling_zero := by simp
  diagonal_tail n hn := by simp [show ¬ n<N by omega]
  coupling_tail n hn := by simp [show ¬ n<N by omega]

/-- The actual finite Jacobi truncation has exactly the original leading physical matrix.
Use: The actual finite Jacobi truncation has exactly the original leading physical matrix.
Article: main_krylov, prop:phi(c), true finite original Jacobi restrictions.
Proof: Compare the genuine diagonal and adjacent entries within the original finite index set. -/
theorem truncateJacobi_matrix (J : JacobiData) (hJ : ∀ n,0≤J.aSq n) (N : ℕ) :
    (truncateJacobi J hJ N).matrix=J.matrix 0 N := by
  -- Exterior normalization changes no actual diagonal or internal edge of the original finite block.
  ext i j
  simp only [Jacobi.matrix,JacobiData.matrix_apply,Nat.zero_add,truncateJacobi]
  by_cases hij : i=j
  · simp [hij]
  · by_cases h1 : i.val+1=j.val
    · simp [hij,h1,show 0<j.val by omega,j.isLt]
    · by_cases h2 : j.val+1=i.val
      · simp [hij,h1,h2,show 0 < i.val by omega,i.isLt]
      · simp [hij,h1,h2]

/-- Every genuine spectral basis of an original irreducible Jacobi block has distinct actual nodes.
Use: Every genuine spectral basis of an original irreducible Jacobi block has distinct actual nodes.
Article: main_krylov, prop:phi(c), true finite original Jacobi restrictions.
Proof: Transfer the proved finite irreducible simple-spectrum theorem through the actual matrix identity. -/
theorem jacobiData_values_injective (J : JacobiData) (hJ : ∀ n,0≤J.aSq n)
    (hpos : ∀ n,0<n → 0<J.aSq n) (N : ℕ) (B : SpectralBasis (J.matrix 0 N)) :
    Function.Injective B.eigenvalues := by
  -- Reuse finite irreducible spectral simplicity for the exact original block, without imposing its desired window.
  let T := truncateJacobi J hJ N
  have hi : T.Irreducible := by
    intro i hi hiN
    simp only [T,truncateJacobi,show 0 < i ∧ i < N from ⟨hi,hiN⟩]
    exact hpos i hi
  have hm : T.matrix=J.matrix 0 N := truncateJacobi_matrix J hJ N
  have h : ∀ C : SpectralBasis T.matrix,Function.Injective C.eigenvalues :=
    jacobi.Finite.basis_values_injective T hi
  rw [hm] at h
  exact h B
end
end krylov.Reference
