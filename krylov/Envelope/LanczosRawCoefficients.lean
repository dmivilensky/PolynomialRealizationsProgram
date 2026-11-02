import krylov.Realization.RawCGCoefficients

set_option autoImplicit false
/-!
Article: main_krylov, prop:phi(a), genuine actual-reference Lanczos raw coefficients.
Use: identify true raw pivot and internal coupling coefficients of the computed Lanczos compression with the original actually measured CG line lengths and recurrence ratios.
Source: proved actual Lanczos principal-block entries, genuine determinant products and real adjacent-entry identities, with all true active positivity domains derived.
-/

namespace krylov.Envelope
noncomputable section
open krylov.Reference krylov.Realization Matrix Polynomial chebyshev1
open scoped BigOperators Matrix.Norms.L2Operator
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Every genuine leading principal block of the actual Lanczos compression is exactly its true shorter computed Lanczos matrix.
Use: Every genuine leading principal block of the actual Lanczos compression is exactly its true shorter computed Lanczos matrix.
Article: main_krylov, prop:phi(a), genuine actual-reference Lanczos raw coefficients.
Proof: Read the actual physical residual-basis entries at the true leading finite indices. -/
theorem lanczos_rawBlock_prefix (Q : E →L[ℝ] E) (g : E) (m r : ℕ) (hr : r≤m) :
    rawBlock (CG.lanczosMatrix Q g m) 0 r (by omega)=CG.lanczosMatrix Q g r := by
  ext i j
  simp only [rawBlock,Matrix.submatrix_apply,CG.lanczosMatrix,Nat.zero_add]

/-- The genuine raw reciprocal pivot of the actual Lanczos prefix equals the original true measured CG line length.
Use: The genuine raw reciprocal pivot of the actual Lanczos prefix equals the original true measured CG line length.
Article: main_krylov, prop:phi(a), genuine actual-reference Lanczos raw coefficients.
Proof: Use the actual consecutive Lanczos determinant products and cancel only their genuine positive leading factor. -/
theorem lanczos_rawAlpha (Q : E →L[ℝ] E) (hQ : Q.toLinearMap.IsSymmetric)
    (hpos : ∀ v : E,v≠0 → 0 < inner ℝ v (Q v)) (g : E) (m : ℕ)
    (hpre : ∀ i<m,CG.gradient Q g i≠0) (r : ℕ) (hr : r<m) :
    rawAlpha (CG.lanczosMatrix Q g m) r=CG.length Q g r := by
  -- All actual leading determinants and pivots belong to the genuine computed reference compression.
  let T := CG.lanczosMatrix Q g m
  have hT : T.PosDef := CG.lanczosMatrix_posDef Q hQ hpos g m hpre
  have ht := CG.lanczosMatrix_tridiagonal Q hQ hpos g m hpre
  have hn := CG.lanczosMatrix_adjacent_neg Q hQ hpos g m hpre
  have hdet (p : ℕ) (hp : p≤m) : (rawBlock T 0 p (by omega)).det=
      ∏ i : Fin p,(CG.length Q g i.val)⁻¹ := by
    rw [lanczos_rawBlock_prefix Q g m p hp]
    exact CG.lanczosMatrix_det Q hQ hpos g p (fun i hi => hpre i (hi.trans_le hp))
  have hd0 := hdet r hr.le
  have hd1 := hdet (r+1) (by omega)
  rw [Fin.prod_univ_castSucc] at hd1
  simp only [Fin.val_castSucc,Fin.val_last] at hd1
  have hp : (∏ i : Fin r,(CG.length Q g i.val)⁻¹)≠0 := by
    rw [← hd0]
    exact (rawBlock_posDef T hT 0 r (by omega)).det_pos.ne'
  rw [rawAlpha_det T hT ht hn r hr,hd0,hd1,div_mul_eq_div_div,div_self hp,one_div,inv_inv]

/-- Every genuine internal raw Lanczos coupling equals the original actually measured CG recurrence ratio.
Use: Every genuine internal raw Lanczos coupling equals the original actually measured CG recurrence ratio.
Article: main_krylov, prop:phi(a), genuine actual-reference Lanczos raw coefficients.
Proof: Use the true adjacent compression entry and actual pivot identity, retaining its genuine square-root sign and nonzero line domain. -/
theorem lanczos_rawBeta (Q : E →L[ℝ] E) (hQ : Q.toLinearMap.IsSymmetric)
    (hpos : ∀ v : E,v≠0 → 0 < inner ℝ v (Q v)) (g : E) (m : ℕ)
    (hpre : ∀ i<m,CG.gradient Q g i≠0) (r : ℕ) (hr : r+1<m) :
    rawBeta (CG.lanczosMatrix Q g m) r=CG.beta Q g r := by
  let T := CG.lanczosMatrix Q g m
  let i : Fin m := ⟨r,by omega⟩
  let j : Fin m := ⟨r+1,hr⟩
  -- The real internal edge and genuine nonzero measured line determine the actual squared recurrence coefficient.
  have he := CG.lanczosMatrix_adjacent Q hQ hpos g m hpre i j rfl
  change T i j= -Real.sqrt (CG.beta Q g r)/CG.length Q g r at he
  have hα : CG.length Q g r≠0 := (CG.invariant_line_pos Q hpos g r
    (CG.invariant Q hQ hpos g r (fun t ht => hpre t (by omega))) (hpre r (by omega))).2.1.ne'
  have hβ : 0≤CG.beta Q g r := by unfold CG.beta;positivity
  rw [rawBeta_edge T i j rfl,lanczos_rawAlpha Q hQ hpos g m hpre r (by omega),he,
    div_mul_cancel₀ _ hα,neg_sq,Real.sq_sqrt hβ]
end
end krylov.Envelope
