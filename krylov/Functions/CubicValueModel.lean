import krylov.Functions.CubicSegment
import krylov.Functions.TrapezoidAffine

/-!
Article: main_krylov, thm:Fexact, exact cubics with arbitrary anchors and splits.
Use: identify the genuine successive Frechet derivatives of a symmetric cubic
and prove the exact corrected-diagonal identity directly from observed values.
Source: Appendix G, exact cubic Taylor algebra and the actual product rule.
-/

namespace krylov.Functions.SymmetricCubic
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The genuine first differential of the cubic potential.
Article: main_krylov, thm:Fexact. -/
theorem potential_fderiv (T : SymmetricCubic E) (x : E) :
    fderiv ℝ T.potential x = (1 / 2 : ℝ) • T.form x x :=
  (T.potential_hasFDerivAt x).fderiv

/-- The actual first differential differentiates to the cubic's Hessian field.
Article: main_krylov, thm:Fexact.
Proof: differentiate both remaining tensor slots and use tensor symmetry. -/
theorem differential_hasFDerivAt (T : SymmetricCubic E) (x : E) :
    HasFDerivAt (fun x => (1 / 2 : ℝ) • T.form x x) (T.form x) x := by
  have h := (T.form.hasFDerivAt.clm_apply (hasFDerivAt_id x)).const_smul (1 / 2 : ℝ)
  convert! h using 1
  ext v w
  simp only [smul_apply, add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply, ContinuousLinearMap.id_apply, smul_eq_mul]
  simp only [id_eq]
  rw [T.swap₁ v x w]
  ring

/-- The displayed cubic Hessian is the actual second Frechet derivative.
Article: main_krylov, thm:Fexact. -/
theorem potential_second_fderiv (T : SymmetricCubic E) (x : E) :
    fderiv ℝ (fderiv ℝ T.potential) x = T.form x := by
  have he : fderiv ℝ T.potential = fun x => (1 / 2 : ℝ) • T.form x x :=
    funext T.potential_fderiv
  rw [he]
  exact (T.differential_hasFDerivAt x).fderiv

/-- The Hessian field differentiates to the original constant symmetric tensor.
Article: main_krylov, thm:Fexact. -/
theorem hessian_hasFDerivAt (T : SymmetricCubic E) (x : E) :
    HasFDerivAt (fun x => T.form x) T.form x := by
  convert! T.form.hasFDerivAt (𝕜 := ℝ) (F := E →L[ℝ] E →L[ℝ] ℝ) (x := x)

/-- The actual observed value defect of every symmetric cubic is exactly minus T(s,s,s)/12.
Article: main_krylov, thm:Fexact, the exact cubic defect identity. -/
theorem segmentValueDefect_potential (T : SymmetricCubic E) (a s : E) :
    segmentValueDefect T.potential (fderiv ℝ T.potential) a s = -T.form s s s / 12 := by
  simp only [segmentValueDefect, T.potential_fderiv, smul_apply, smul_eq_mul]
  convert! T.trapezoid_defect a s using 1
  ring

/-- Cubic value information gives the exact diagonal at every anchor, with its exact residual tensor.
Article: main_krylov, thm:Fexact, R=0 for all anchors and all splits. -/
theorem correctedValueDiagonal_potential (T : SymmetricCubic E) (a s x : E) (l : ℝ) :
    correctedValueDiagonal T.potential (fderiv ℝ T.potential) a s l -
      (fderiv ℝ (fderiv ℝ T.potential) x) s s =
      -T.form (x - (a + (1 / 2 : ℝ) • s) - l • s) s s := by
  rw [correctedValueDiagonal, T.segmentValueDefect_potential, T.potential_second_fderiv]
  simp only [sub_apply, T.potential_fderiv, smul_apply, smul_eq_mul]
  have hm := T.midpoint_diagonal a s
  have he : 1 / 2 * T.form (a + s) (a + s) s - 1 / 2 * T.form a a s =
      T.form (a + (1 / 2 : ℝ) • s) s s := by linarith only [hm]
  rw [he]
  simp only [map_sub, map_add, map_smul, sub_apply, add_apply, smul_apply, smul_eq_mul]
  ring

/-- Whenever the chosen split reaches the anchor exactly, the cubic diagonal is exact there.
Article: main_krylov, thm:Fexact, exactness at x-m=lambda s. -/
theorem correctedValueDiagonal_potential_exact (T : SymmetricCubic E) (a s x : E) (l : ℝ)
    (hx : x - (a + (1 / 2 : ℝ) • s) = l • s) :
    correctedValueDiagonal T.potential (fderiv ℝ T.potential) a s l =
      (fderiv ℝ (fderiv ℝ T.potential) x) s s := by
  have h := T.correctedValueDiagonal_potential a s x l
  rw [hx, sub_self, map_zero, zero_apply, zero_apply, neg_zero] at h
  exact sub_eq_zero.mp h

end
end krylov.Functions.SymmetricCubic
