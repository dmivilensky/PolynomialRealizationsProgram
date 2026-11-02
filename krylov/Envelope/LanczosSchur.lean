import krylov.Envelope.LanczosPhiDeterminant
import krylov.Envelope.RawSchurShift
set_option autoImplicit false
/-!
Article: main_krylov, prop:phi(a), actual measured CG Schur representation.
Use: express the original finite continuation through the true Schur complement of its computed Lanczos matrix.
Source: actual measured continuation determinant and genuine positive Schur block factorization.
-/

namespace krylov.Envelope
noncomputable section
open krylov.Reference Matrix Polynomial
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The actual original CG continuation equals the genuine inverse-normalized computed Lanczos Schur determinant.
Use: The actual original CG continuation equals the genuine inverse-normalized computed Lanczos Schur determinant.
Article: main_krylov, prop:phi(a), actual measured CG Schur representation.
Proof: Combine the true measured continuation determinant with actual positive prefix Schur factorization. -/
theorem lanczos_phi_schur_determinant (Q : E →L[ℝ] E) (hQ : Q.toLinearMap.IsSymmetric)
    (hpos : ∀ v : E,v≠0 → 0 < inner ℝ v (Q v)) (g : E) (m : ℕ)
    (hpre : ∀ i<m,CG.gradient Q g i≠0) (j : ℕ) (hj : j≤m) (lam : ℝ) :
    (phi (CG.length Q g) (CG.beta Q g) j (m-j)).eval lam=
      (1-lam • (rawSchurComplement (CG.lanczosMatrix Q g m) j hj)⁻¹).det := by
  rw [lanczos_phi_suffix_determinant Q hQ hpos g m hpre j hj lam]
  exact raw_schur_shift_ratio _ (CG.lanczosMatrix_posDef Q hQ hpos g m hpre) j hj lam
end
end krylov.Envelope
