import krylov.Reference.HeavyBallMatrix
set_option autoImplicit false
/-!
Article: main_krylov, prop:phi(b), genuine heavy-ball CG parameters.
Use: identify the actual first-site CG line lengths and recurrence ratios from the real constructed finite Jacobi matrix, including true termination.
Source: genuine constant-pivot LDL determinants, original physical adjacent edges and the proved actual raw-matrix CG dictionary.
-/

namespace krylov.Reference
noncomputable section
open krylov.Realization Matrix
variable {N : ℕ}

/-- Every genuine used reciprocal pivot of the actual heavy-ball matrix equals the true constant reciprocal d.
Use: Every genuine used reciprocal pivot of the actual heavy-ball matrix equals the true constant reciprocal d.
Article: main_krylov, prop:phi(b), genuine heavy-ball CG parameters.
Proof: Use its actual leading determinant powers and cancel the genuine positive pivot. -/
theorem heavyBall_rawAlpha (d q : ℝ) (hd : 0 < d) (hq : 0 < q) (r : ℕ) (hr : r<N) :
    rawAlpha (heavyBallMatrix d q N) r=d⁻¹ := by
  rw [rawAlpha_det _ (heavyBallMatrix_posDef d q hd N) (heavyBallMatrix_tridiagonal d q N)
    (heavyBallMatrix_adjacent_neg d q hd hq N) r hr,
    heavyBallMatrix_prefix d q N r hr.le,heavyBallMatrix_prefix d q N (r+1) (by omega),
    heavyBallMatrix_det,heavyBallMatrix_det,pow_succ]
  field_simp [hd.ne']

/-- Every genuine internal raw recurrence ratio of the actual heavy-ball matrix equals the true squared coupling q.
Use: Every genuine internal raw recurrence ratio of the actual heavy-ball matrix equals the true squared coupling q.
Article: main_krylov, prop:phi(b), genuine heavy-ball CG parameters.
Proof: Use the actual adjacent physical entry and the true computed reciprocal pivot. -/
theorem heavyBall_rawBeta_internal (d q : ℝ) (hd : 0 < d) (hq : 0 < q) (r : ℕ) (hr : r+1<N) :
    rawBeta (heavyBallMatrix d q N) r=q^2 := by
  -- The genuine adjacent physical edge and actual positive pivot determine the true squared recurrence ratio.
  let i : Fin N := ⟨r,by omega⟩
  let j : Fin N := ⟨r+1,hr⟩
  rw [rawBeta_edge _ i j rfl,heavyBall_rawAlpha d q hd hq r (by omega)]
  have he : heavyBallMatrix d q N i j= -d*q := by
    rw [heavyBallMatrix,ite_eq_right (show i≠j by intro h;have hh := congrArg Fin.val h;dsimp [i,j] at hh;omega),
      ite_eq_left (show i.val+1=j.val ∨ j.val+1=i.val from Or.inl rfl)]
  rw [he]
  field_simp [hd.ne']

/-- Every genuine active first-site CG line length on the actual heavy-ball matrix is the printed constant reciprocal pivot.
Use: Every genuine active first-site CG line length on the actual heavy-ball matrix is the printed constant reciprocal pivot.
Article: main_krylov, prop:phi(b), genuine heavy-ball CG parameters.
Proof: Apply the actual raw-matrix CG line dictionary to the genuine determinant-derived pivot. -/
theorem heavyBall_cg_length (d q : ℝ) (hd : 0 < d) (hq : 0 < q) (r : ℕ) (hr : r<N) :
    CG.length (cgOperator (heavyBallMatrix d q N)) (WithLp.toLp 2 (chebyshev1.JacobiData.site N 0)) r=d⁻¹ := by
  rw [raw_cg_length _ (heavyBallMatrix_posDef d q hd N) (heavyBallMatrix_tridiagonal d q N)
    (heavyBallMatrix_adjacent_neg d q hd hq N) r hr]
  exact heavyBall_rawAlpha d q hd hq r hr

/-- Every genuine internal first-site CG recurrence ratio on the actual heavy-ball matrix is the printed q squared.
Use: Every genuine internal first-site CG recurrence ratio on the actual heavy-ball matrix is the printed q squared.
Article: main_krylov, prop:phi(b), genuine heavy-ball CG parameters.
Proof: Apply the actual raw-matrix CG ratio dictionary to the true internal edge. -/
theorem heavyBall_cg_beta_internal (d q : ℝ) (hd : 0 < d) (hq : 0 < q) (r : ℕ) (hr : r+1<N) :
    CG.beta (cgOperator (heavyBallMatrix d q N)) (WithLp.toLp 2 (chebyshev1.JacobiData.site N 0)) r=q^2 := by
  rw [raw_cg_beta_internal _ (heavyBallMatrix_posDef d q hd N) (heavyBallMatrix_tridiagonal d q N)
    (heavyBallMatrix_adjacent_neg d q hd hq N) r hr]
  exact heavyBall_rawBeta_internal d q hd hq r hr
/-- The genuine terminating first-site CG recurrence ratio on the actual heavy-ball matrix is zero.
Use: The genuine terminating first-site CG recurrence ratio on the actual heavy-ball matrix is zero.
Article: main_krylov, prop:phi(b), genuine heavy-ball CG parameters.
Proof: The original finite matrix has no true outgoing edge after its actual terminal site. -/
theorem heavyBall_cg_beta_terminal (d q : ℝ) (hd : 0 < d) (hq : 0 < q) (r : ℕ) (hr : r+1=N) :
    CG.beta (cgOperator (heavyBallMatrix d q N)) (WithLp.toLp 2 (chebyshev1.JacobiData.site N 0)) r=0 := by
  rw [raw_cg_beta _ (heavyBallMatrix_posDef d q hd N) (heavyBallMatrix_tridiagonal d q N)
    (heavyBallMatrix_adjacent_neg d q hd hq N) r (by omega)]
  simp [rawBeta,rawJacobi,hr]

end
end krylov.Reference
