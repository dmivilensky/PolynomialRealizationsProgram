import krylov.Envelope.LanczosRawCoefficients
import krylov.Envelope.ContinuationCongruence
import krylov.Envelope.RawPhiDeterminant
set_option autoImplicit false
/-!
Article: main_krylov, prop:phi(a), actual-reference continuation determinant.
Use: express the original measured CG continuation through its genuine computed finite Lanczos compression.
Source: actual prefix pivot and coupling identities, the true unused-terminal-coefficient congruence and the proved physical insertion determinant.
-/

namespace krylov.Envelope
noncomputable section
open krylov.Reference krylov.Realization Matrix Polynomial
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The original measured CG continuation equals the genuine raw continuation of its actual finite Lanczos compression.
Use: The original measured CG continuation equals the genuine raw continuation of its actual finite Lanczos compression.
Article: main_krylov, prop:phi(a), actual-reference continuation determinant.
Proof: Transfer exactly the actual used line coefficients and internal recurrence ratios; the genuine last beta is unused. -/
theorem lanczos_phi_raw (Q : E →L[ℝ] E) (hQ : Q.toLinearMap.IsSymmetric)
    (hpos : ∀ v : E,v≠0 → 0 < inner ℝ v (Q v)) (g : E) (m : ℕ)
    (hpre : ∀ i<m,CG.gradient Q g i≠0) (j : ℕ) (hj : j≤m) :
    phi (rawAlpha (CG.lanczosMatrix Q g m)) (rawBeta (CG.lanczosMatrix Q g m)) j (m-j)=
      phi (CG.length Q g) (CG.beta Q g) j (m-j) := by
  apply phi_coefficients_congr
  · intro i hi
    exact lanczos_rawAlpha Q hQ hpos g m hpre (j+i) (by omega)
  · intro i hi
    exact lanczos_rawBeta Q hQ hpos g m hpre (j+i) (by omega)

/-- The original true CG continuation is exactly the partially shifted determinant of its actual Lanczos prefix.
Use: The original true CG continuation is exactly the partially shifted determinant of its actual Lanczos prefix.
Article: main_krylov, prop:phi(a), actual-reference continuation determinant.
Proof: Apply the genuine raw determinant identity with actual compression positivity, tridiagonality and strictly negative internal edges. -/
theorem lanczos_phi_suffix_determinant (Q : E →L[ℝ] E) (hQ : Q.toLinearMap.IsSymmetric)
    (hpos : ∀ v : E,v≠0 → 0 < inner ℝ v (Q v)) (g : E) (m : ℕ)
    (hpre : ∀ i<m,CG.gradient Q g i≠0) (j : ℕ) (hj : j≤m) (lam : ℝ) :
    (phi (CG.length Q g) (CG.beta Q g) j (m-j)).eval lam=
      (rawSuffixShift (CG.lanczosMatrix Q g m) j lam).det/(CG.lanczosMatrix Q g m).det := by
  rw [← lanczos_phi_raw Q hQ hpos g m hpre j hj]
  exact raw_phi_suffix_determinant _ (CG.lanczosMatrix_posDef Q hQ hpos g m hpre)
    (CG.lanczosMatrix_tridiagonal Q hQ hpos g m hpre)
    (CG.lanczosMatrix_adjacent_neg Q hQ hpos g m hpre) j hj lam
end
end krylov.Envelope
