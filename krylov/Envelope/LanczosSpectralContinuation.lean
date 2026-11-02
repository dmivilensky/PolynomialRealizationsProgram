import krylov.Envelope.LanczosSchur
import krylov.Envelope.RawSchurJacobi
import krylov.LinearAlgebra.SpectralContinuation
set_option autoImplicit false
/-!
Article: main_krylov, prop:phi(a), actual original CG spectral continuation.
Use: identify the genuine measured polynomial with the actual Schur spectral product and prove all actual zeros simple.
Source: the original measured Schur determinant identity, genuine finite positive spectral theorem and actual Jacobi simplicity.
-/

namespace krylov.Envelope
noncomputable section
open krylov.Reference krylov.LinearAlgebra Matrix Polynomial
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The original actually measured CG continuation is exactly the spectral product of its genuine computed prefix Schur complement.
Use: The original actually measured CG continuation is exactly the spectral product of its genuine computed prefix Schur complement.
Article: main_krylov, prop:phi(a), actual original CG spectral continuation.
Proof: Identify evaluations at every real point through the proved actual determinant identities. -/
theorem lanczos_phi_spectral (Q : E →L[ℝ] E) (hQ : Q.toLinearMap.IsSymmetric)
    (hpos : ∀ v : E,v≠0 → 0 < inner ℝ v (Q v)) (g : E) (m : ℕ)
    (hpre : ∀ i<m,CG.gradient Q g i≠0) (j : ℕ) (hj : j≤m) :
    phi (CG.length Q g) (CG.beta Q g) j (m-j)=
      spectralContinuation (rawSchurComplement (CG.lanczosMatrix Q g m) j hj)
        (rawSchurComplement_posDef _ (CG.lanczosMatrix_posDef Q hQ hpos g m hpre) j hj) := by
  apply Polynomial.funext
  intro lam
  rw [spectralContinuation_eval,lanczos_phi_schur_determinant Q hQ hpos g m hpre j hj lam]

/-- Every real zero of the true original measured CG continuation is simple.
Use: Every real zero of the true original measured CG continuation is simple.
Article: main_krylov, prop:phi(a), actual original CG spectral continuation.
Proof: Use its actual spectral product, genuine Schur eigenvalue distinctness and the proved true nonvanishing derivative at each actual spectral factor. -/
theorem lanczos_phi_simple_zero (Q : E →L[ℝ] E) (hQ : Q.toLinearMap.IsSymmetric)
    (hpos : ∀ v : E,v≠0 → 0 < inner ℝ v (Q v)) (g : E) (m : ℕ)
    (hpre : ∀ i<m,CG.gradient Q g i≠0) (j : ℕ) (hj : j≤m) (lam : ℝ)
    (hz : (phi (CG.length Q g) (CG.beta Q g) j (m-j)).eval lam=0) :
    (phi (CG.length Q g) (CG.beta Q g) j (m-j)).derivative.eval lam≠0 := by
  -- The zero belongs to the genuine computed Schur spectrum, whose actual Jacobi activity proves simplicity.
  let T := CG.lanczosMatrix Q g m
  have hT := CG.lanczosMatrix_posDef Q hQ hpos g m hpre
  have hS := rawSchurComplement_posDef T hT j hj
  rw [lanczos_phi_spectral Q hQ hpos g m hpre j hj] at hz ⊢
  obtain ⟨i,hi⟩ := (spectralContinuation_roots _ hS lam).mp hz
  rw [← hi]
  exact spectralContinuation_simple _ hS
    (rawSchur_simple_spectrum T hT (CG.lanczosMatrix_tridiagonal Q hQ hpos g m hpre)
      (CG.lanczosMatrix_adjacent_neg Q hQ hpos g m hpre) j hj) i
end
end krylov.Envelope
