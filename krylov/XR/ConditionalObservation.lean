import krylov.XR.ConditionalFresh
import krylov.XR.CanonicalTwo
import krylov.LinearAlgebra.BlockCompletion

/-!
Article: main_krylov, prop:cond(b), original signed observed data.
Use: preserve the sign of the measured normalized cross entry, prove its
full consistency criterion and attained radius, and identify the exact
relative defect when the observed model is positive.
Source: the genuine scalar completion fibre and actual two-pair metric.
-/
namespace krylov.XR
noncomputable section
open Matrix krylov.Secant krylov.LinearAlgebra
open scoped Matrix.Norms.L2Operator

/-- The actual old cross entry compatible with the signed normalized
observation and a hidden base diagonal. Article: prop:cond(b). -/
def observedConditionalCross (δobs k : ℝ) : ℝ := δobs*Real.sqrt (1+k)

/-- The original measured ratio, with its sign, is recovered exactly.
Article: main_krylov, prop:cond(b). -/
theorem observedConditionalCross_ratio (δobs k : ℝ) (hk : 0<1+k) :
    observedConditionalCross δobs k/Real.sqrt (1+k)=δobs := by
  unfold observedConditionalCross
  exact mul_div_cancel_right₀ _ (Real.sqrt_pos.mpr hk).ne'

/-- The true signed observation has exactly the scalar squared relation
used to derive the data-only consistency interval. Article: prop:cond(b). -/
theorem observedConditionalCross_sq (δobs k : ℝ) (hk : 0≤1+k) :
    observedConditionalCross δobs k^2=δobs^2*(1+k) := by
  rw [observedConditionalCross,mul_pow,Real.sq_sqrt hk]

/-- The lower-root endpoint attains the data-only radius while retaining
the exact signed original observed cross information. Article: prop:cond(b). -/
theorem signed_conditional_attainment {ω δobs : ℝ} (hω : 0<ω) (hω₁ : ω<1)
    (hfeasible : δobs^2≤2-2*Real.sqrt (1-ω^2)) :
    ∃ k y : ℝ,0<1+k ∧ ‖conditionalMatrix y (observedConditionalCross δobs k) k‖≤ω ∧
      |y|=unknownConditionalRadius ω δobs 0 := by
  obtain ⟨_hd,hk,hkn,_horder,_habslo,_habshi,hq,_hqhi,_hkhi⟩ :=
    conditional_endpoint_geometry hω hω₁ (sq_nonneg δobs) hfeasible
  let k := conditionalKlo ω (δobs^2)
  have he : observedConditionalCross δobs k^2+k^2=ω^2 := by
    rw [observedConditionalCross_sq δobs k hk.le]
    dsimp only [k]
    nlinarith only [hq]
  refine ⟨k,-k,hk,?_,?_⟩
  · rw [conditionalMatrix_traceless_norm,he,Real.sqrt_sq hω.le]
  · rw [unknownConditionalRadius_root,add_zero,abs_of_nonneg (neg_nonneg.mpr hkn)]

/-- Signed original normalized data are consistent exactly on the
article's printed interval, with an actual spectral-budget matrix witness.
Article: main_krylov, prop:cond(b). -/
theorem signed_conditional_feasibility_iff {ω δobs : ℝ} (hω : 0<ω) (hω₁ : ω<1) :
    (∃ k y : ℝ,0<1+k ∧ ‖conditionalMatrix y (observedConditionalCross δobs k) k‖≤ω) ↔
      δobs^2≤2-2*Real.sqrt (1-ω^2) := by
  constructor
  · rintro ⟨k,y,hk,hbudget⟩
    have hf := conditionalMatrix_column_feasible y (observedConditionalCross δobs k) k ω hω.le hbudget
    rw [observedConditionalCross_sq δobs k hk.le] at hf
    apply conditional_feasibility_necessary hω hω₁ hk
    nlinarith only [hf]
  · intro hf
    obtain ⟨k,y,hk,hbudget,_he⟩ := signed_conditional_attainment hω hω₁ hf
    exact ⟨k,y,hk,hbudget⟩

/-- The old hidden-modulus maximum is exact even after the full signed
original observation, rather than just its square, is fixed.
Article: main_krylov, prop:cond(b). -/
theorem signed_conditional_hidden_radius {ω δobs : ℝ} (hω : 0<ω) (hω₁ : ω<1)
    (hfeasible : δobs^2≤2-2*Real.sqrt (1-ω^2)) :
    IsGreatest {v : ℝ | ∃ y : ℝ,(∃ k : ℝ,0<1+k ∧
      ‖conditionalMatrix y (observedConditionalCross δobs k) k‖≤ω) ∧ v=|y|}
      (unknownConditionalRadius ω δobs 0) := by
  constructor
  · obtain ⟨k,y,hk,hb,he⟩ := signed_conditional_attainment hω hω₁ hfeasible
    exact ⟨y,⟨k,hk,hb⟩,he.symm⟩
  · rintro v ⟨y,⟨k,hk,hb⟩,rfl⟩
    rw [unknownConditionalRadius_root,add_zero]
    exact unknown_conditional_upper hω hω₁ (sq_nonneg δobs)
      (observedConditionalCross_sq δobs k hk.le) hb

/-- The exact printed full data-only radius preserves the signed
original observation and admits a true arbitrary fresh symmetric error.
Article: main_krylov, prop:cond(b). -/
theorem signed_conditional_full_radius {ω δobs fresh : ℝ} (hω : 0<ω) (hω₁ : ω<1)
    (hfeasible : δobs^2≤2-2*Real.sqrt (1-ω^2)) (hfresh : 0≤fresh) :
    IsGreatest {v : ℝ | ∃ y : ℝ,∃ E : Matrix (Fin 2) (Fin 2) ℝ,
      (∃ k : ℝ,0<1+k ∧ ‖conditionalMatrix y (observedConditionalCross δobs k) k‖≤ω) ∧
      E.IsSymm ∧ ‖E‖≤fresh ∧ v=‖conditionalHiddenError y+E‖}
      (unknownConditionalRadius ω δobs fresh) := by
  have hh := conditional_fresh_radius _ _ fresh hfresh (signed_conditional_hidden_radius hω hω₁ hfeasible)
  convert hh using 1
  unfold unknownConditionalRadius
  ring

/-- The literal normalized observed pairing matrix has the measured
cross entry, with zero old lower entry. Article: prop:cond(b). -/
def normalizedConditionalObservation (δobs : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![1,δobs;0,1]

/-- The actual latest model is its printed symmetric completion.
Article: main_krylov, prop:cond(b). -/
theorem normalizedConditionalObservation_latest (δobs : ℝ) :
    latest (normalizedConditionalObservation δobs)=conditionalMatrix 1 δobs 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [latest,normalizedConditionalObservation,conditionalMatrix]

/-- Its true observed model is positive precisely in the strict
normalized-defect range used by the source formula. Article: prop:cond(b). -/
theorem normalizedConditionalObservation_posDef (δobs : ℝ) (hδ : |δobs|<1) :
    (latest (normalizedConditionalObservation δobs)).PosDef := by
  have hn : ‖conditionalMatrix 0 δobs 0‖<1 := by
    have he : ‖conditionalMatrix 0 δobs 0‖=|δobs| := by
      simpa [Real.sqrt_sq_eq_abs] using conditionalMatrix_traceless_norm δobs 0
    rwa [he]
  have hh := (strict_shifted_posDef (conditionalMatrix 0 δobs 0)
    (conditionalMatrix_isSymm _ _ _) hn).2
  have he : (1 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ)+conditionalMatrix 0 δobs 0=
      latest (normalizedConditionalObservation δobs) := by
    rw [normalizedConditionalObservation_latest]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [conditionalMatrix]
  rwa [he] at hh

/-- The original relative window defect is exactly the printed nonlinear
function of the actual measured signed normalized defect.
Article: main_krylov, prop:cond(b), Omega_star relation. -/
theorem normalizedConditionalObservation_relative (δobs : ℝ) (hδ : |δobs|<1) :
    relativeBudget (latest (normalizedConditionalObservation δobs))
      (defect (normalizedConditionalObservation δobs))=
      |δobs|/Real.sqrt (1-δobs^2) := by
  rw [relativeBudget_two _ _ (normalizedConditionalObservation_posDef δobs hδ)
    (defect_transpose _),normalizedConditionalObservation_latest]
  simp [defect,normalizedConditionalObservation,conditionalMatrix,Matrix.det_fin_two,pow_two]

end
end krylov.XR
