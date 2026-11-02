import krylov.Convergence.SS1FDiagonal

/-!
Article: main_krylov, thm:ss1F, the scalar Davidon case.
Use: show that the original admissibility condition forces the actual
one-pair split to one half and gives exactly the printed cubic-interpolation
curvature. Source: the genuine endpoint anchor, observed trapezoid defect,
Davidon59 and Traub64 as cited in the article.
-/

namespace krylov.Convergence
noncomputable section
open krylov.Functions
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- When the current point is the true newer endpoint, (S) forces the
genuine split to one half for every nonzero observed step. -/
theorem endpoint_split_eq_half (a s : E) (hs : s≠0) (l C : ℝ)
    (hw : ‖splitRemainder a s (a+s) l‖≤C*‖(a+s)-(a+s)‖) : l=1/2 := by
  have hz : splitRemainder a s (a+s) l=0 := by
    apply norm_eq_zero.mp
    apply le_antisymm _ (norm_nonneg _)
    simpa only [sub_self,norm_zero,mul_zero] using hw
  have he : (l-1/2) • s=0 := by
    rw [splitRemainder_endpoint,sub_self,zero_sub,neg_eq_zero] at hz
    exact hz
  have hh := (smul_eq_zero.mp he).resolve_right hs
  linarith

/-- The actual one-pair value-corrected curvature is the original Davidon
formula y/s−6δ/s², with the genuine endpoint function-value defect. -/
theorem scalar_corrected_curvature (f G : ℝ → ℝ) (a s : ℝ) (hs : s≠0) :
    correctedValueDiagonal f (fun z=>innerSL ℝ (G z)) a s (1/2)/s^2=
      (G (a+s)-G a)/s-6*segmentValueDefect f (fun z=>innerSL ℝ (G z)) a s/s^2 := by
  simp only [correctedValueDiagonal,sub_apply,innerSL_apply_apply,Real.inner_apply]
  field_simp [hs]
  ring

end
end krylov.Convergence
