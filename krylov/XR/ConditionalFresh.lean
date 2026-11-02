import krylov.XR.ConditionalMonotonicity

/-!
Article: main_krylov, prop:cond, full conditional model-error radius.
Use: add a genuinely arbitrary fresh symmetric matrix increment to the
actual old hidden entry, with exact attainment in dimension two.
Source: spectral triangle inequality and the explicit signed diagonal
fresh adversary. Restrictions to additional observations preserve the bound.
-/
namespace krylov.XR
noncomputable section
open Matrix
open scoped Matrix.Norms.L2Operator

/-- The true rank-one old hidden error of a two-pair window.
Article: main_krylov, prop:cond. -/
def conditionalHiddenError (y : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := diagonal (![y,0] : Fin 2 → ℝ)

/-- Its actual spectral norm is exactly the hidden modulus.
Article: main_krylov, prop:cond. -/
theorem conditionalHiddenError_norm (y : ℝ) : ‖conditionalHiddenError y‖=|y| := by
  rw [conditionalHiddenError,Matrix.l2_opNorm_diagonal]
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg (abs_nonneg y)).mpr
    intro i
    fin_cases i <;> simp [Real.norm_eq_abs]
  · have hh := norm_le_pi_norm (![y,0] : Fin 2 → ℝ) 0
    simpa only [cons_val_zero,Real.norm_eq_abs] using hh

/-- The true old hidden error is symmetric. Article: prop:cond. -/
theorem conditionalHiddenError_isSymm (y : ℝ) : (conditionalHiddenError y).IsSymm := by
  simp only [conditionalHiddenError,IsSymm,diagonal_transpose]

/-- Actual hidden errors add by their physical scalar coefficients.
Article: main_krylov, prop:cond. -/
theorem conditionalHiddenError_add (a b : ℝ) :
    conditionalHiddenError a+conditionalHiddenError b=conditionalHiddenError (a+b) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [conditionalHiddenError]

/-- Every actually attained old hidden-modulus radius extends to the
exact full radius after an arbitrary fresh symmetric budget is admitted.
Article: main_krylov, prop:cond, sup|y|+omega'. -/
theorem conditional_fresh_radius (P : ℝ → Prop) (r fresh : ℝ) (hfresh : 0≤fresh)
    (hP : IsGreatest {v : ℝ | ∃ y : ℝ,P y ∧ v=|y|} r) :
    IsGreatest {v : ℝ | ∃ y : ℝ,∃ E : Matrix (Fin 2) (Fin 2) ℝ,
      P y ∧ E.IsSymm ∧ ‖E‖≤fresh ∧ v=‖conditionalHiddenError y+E‖} (r+fresh) := by
  obtain ⟨y,hy,hr⟩ := hP.1
  constructor
  · by_cases hsign : 0≤y
    · refine ⟨y,conditionalHiddenError fresh,hy,conditionalHiddenError_isSymm fresh,?_,?_⟩
      · rw [conditionalHiddenError_norm,abs_of_nonneg hfresh]
      · rw [conditionalHiddenError_add,conditionalHiddenError_norm,
          abs_of_nonneg (add_nonneg hsign hfresh),hr,abs_of_nonneg hsign]
    · have hsign' : y≤0 := (lt_of_not_ge hsign).le
      refine ⟨y,conditionalHiddenError (-fresh),hy,conditionalHiddenError_isSymm (-fresh),?_,?_⟩
      · rw [conditionalHiddenError_norm,abs_neg,abs_of_nonneg hfresh]
      · rw [conditionalHiddenError_add,conditionalHiddenError_norm,
          abs_of_nonpos (by linarith : y+-fresh≤0),hr,abs_of_nonpos hsign']
        ring
  · rintro v ⟨y,E,hy,_hs,hE,rfl⟩
    have hh := hP.2 ⟨y,hy,rfl⟩
    have hn := norm_add_le (conditionalHiddenError y) E
    rw [conditionalHiddenError_norm] at hn
    linarith

/-- The original known-base full two-pair model-error radius is exactly
attained over genuine old and fresh spectral-budget matrices.
Article: main_krylov, prop:cond(a). -/
theorem knownConditionalRadius_isGreatest {ω δ k fresh : ℝ} (hω : 0<ω)
    (hfeasible : δ^2+k^2≤ω^2) (hfresh : 0≤fresh) :
    IsGreatest {v : ℝ | ∃ y : ℝ,∃ E : Matrix (Fin 2) (Fin 2) ℝ,
      ‖conditionalMatrix y δ k‖≤ω ∧ E.IsSymm ∧ ‖E‖≤fresh ∧
      v=‖conditionalHiddenError y+E‖} (knownConditionalRadius ω δ k fresh) := by
  exact conditional_fresh_radius _ _ fresh hfresh (knownConditionalFibre hω hfeasible)

/-- The original data-only full radius is exactly attained over genuine
two-dimensional explanations of the original normalized observation.
Article: main_krylov, prop:cond(b). -/
theorem unknownConditionalRadius_isGreatest {ω δobs fresh : ℝ} (hω : 0<ω) (hω₁ : ω<1)
    (hfeasible : δobs^2≤2-2*Real.sqrt (1-ω^2)) (hfresh : 0≤fresh) :
    IsGreatest {v : ℝ | ∃ y : ℝ,∃ E : Matrix (Fin 2) (Fin 2) ℝ,
      (∃ δ k : ℝ,δ^2=δobs^2*(1+k) ∧ ‖conditionalMatrix y δ k‖≤ω) ∧
      E.IsSymm ∧ ‖E‖≤fresh ∧ v=‖conditionalHiddenError y+E‖}
      (unknownConditionalRadius ω δobs fresh) := by
  have he : {v : ℝ | ∃ y : ℝ,(∃ δ k : ℝ,δ^2=δobs^2*(1+k) ∧
      ‖conditionalMatrix y δ k‖≤ω) ∧ v=|y|}=
      {v : ℝ | ∃ δ k y : ℝ,δ^2=δobs^2*(1+k) ∧ ‖conditionalMatrix y δ k‖≤ω ∧ v=|y|} := by
    ext v
    constructor
    · rintro ⟨y,⟨δ,k,ho,hb⟩,hv⟩
      exact ⟨δ,k,y,ho,hb,hv⟩
    · rintro ⟨δ,k,y,ho,hb,hv⟩
      exact ⟨y,⟨δ,k,ho,hb⟩,hv⟩
  have hp := unknownConditionalFibre hω hω₁ hfeasible
  rw [←he] at hp
  have hh := conditional_fresh_radius _ _ fresh hfresh hp
  convert hh using 1
  unfold unknownConditionalRadius
  ring

end
end krylov.XR
