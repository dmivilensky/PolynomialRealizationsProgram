import krylov.Reference.JacobiPivots
set_option autoImplicit false
/-!
Article: main_krylov, prop:phi(c), genuine common Gaussian CG coefficients.
Use: identify actual measured finite-prefix CG lines and recurrence ratios with the original common principal determinant pivots, including true termination.
Source: the proved supplied-matrix CG dictionary and genuine original Jacobi principal blocks.
-/

namespace krylov.Reference
noncomputable section
open Matrix chebyshev1 krylov.Realization

/-- Every actual finite Jacobi CG line equals the reciprocal of the original common determinant pivot before true termination.
Use: Every actual finite Jacobi CG line equals the reciprocal of the original common determinant pivot before true termination.
Article: main_krylov, prop:phi(c), genuine common Gaussian CG coefficients.
Proof: Use the genuine raw CG line theorem and actual leading-block determinant coherence. -/
theorem jacobi_cg_length (A B : ℕ → ℝ) (hB : ∀ n,0<B n) (N : ℕ)
    (hT : (jacobiPrefix A B N).PosDef) (k : ℕ) (hk : k<N) :
    CG.length (cgOperator (jacobiPrefix A B N)) (WithLp.toLp 2 (JacobiData.site N 0)) k=
      (jacobiPivot A B k)⁻¹ := by
  rw [raw_cg_length _ hT (jacobiPrefix_tridiagonal A B N) (jacobiPrefix_adjacent_neg A B hB N) k hk,
    rawAlpha_jacobiPivot A B hB N hT k hk]

/-- Every actual internal finite Jacobi CG recurrence ratio equals the squared original physical edge over its common determinant pivot.
Use: Every actual internal finite Jacobi CG recurrence ratio equals the squared original physical edge over its common determinant pivot.
Article: main_krylov, prop:phi(c), genuine common Gaussian CG coefficients.
Proof: Read the genuine adjacent entry in the actual raw CG recurrence dictionary. -/
theorem jacobi_cg_beta_internal (A B : ℕ → ℝ) (hB : ∀ n,0<B n) (N : ℕ)
    (hT : (jacobiPrefix A B N).PosDef) (k : ℕ) (hk : k+1<N) :
    CG.beta (cgOperator (jacobiPrefix A B N)) (WithLp.toLp 2 (JacobiData.site N 0)) k=
      (B k/jacobiPivot A B k)^2 := by
  -- Both true adjacent physical sites use the same original edge and determinant pivot.
  let i : Fin N := ⟨k,by omega⟩
  let j : Fin N := ⟨k+1,hk⟩
  have hedge : jacobiPrefix A B N i j= -B k := by simp [jacobiPrefix,i,j,Fin.ext_iff]
  rw [raw_cg_beta_internal _ hT (jacobiPrefix_tridiagonal A B N) (jacobiPrefix_adjacent_neg A B hB N) k hk,
    rawBeta_edge (jacobiPrefix A B N) i j rfl,hedge,rawAlpha_jacobiPivot A B hB N hT k (by omega)]
  simp only [neg_mul,neg_sq,div_eq_mul_inv]

/-- The actual final finite Jacobi CG recurrence ratio is zero at the true original active dimension.
Use: The actual final finite Jacobi CG recurrence ratio is zero at the true original active dimension.
Article: main_krylov, prop:phi(c), genuine common Gaussian CG coefficients.
Proof: Use genuine full first-site CG activity and actual termination in the original finite block. -/
theorem jacobi_cg_beta_terminal (A B : ℕ → ℝ) (hB : ∀ n,0<B n) (N : ℕ)
    (hT : (jacobiPrefix A B N).PosDef) (k : ℕ) (hk : k+1=N) :
    CG.beta (cgOperator (jacobiPrefix A B N)) (WithLp.toLp 2 (JacobiData.site N 0)) k=0 := by
  -- Actual irreducible first-site activity determines the real termination index before the final coefficient vanishes.
  have hzero : CG.gradient (cgOperator (jacobiPrefix A B N))
      (WithLp.toLp 2 (JacobiData.site N 0)) (k+1)=0 := by
    rw [hk]
    have hcount := raw_referenceAtomCount (jacobiPrefix A B N) hT (jacobiPrefix_tridiagonal A B N)
      (jacobiPrefix_adjacent_neg A B hB N)
    simpa only [hcount] using cg_terminates (jacobiPrefix A B N) hT (WithLp.toLp 2 (JacobiData.site N 0))
  rw [CG.beta,hzero,norm_zero,zero_pow (by decide : 2≠0),zero_div]
end
end krylov.Reference
