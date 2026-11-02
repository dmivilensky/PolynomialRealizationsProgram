import krylov.XR.ModelQuadratic

/-!
Article: main_krylov, lem:mm, the genuine zero-direction restriction.
Use: assign the positive quadratic only to the actual stored-step span,
with its uniquely determined coordinates; prove the original window-only
trial is its unique physical minimizer. Source: the proved block model
completion, with the nonexistent new-direction coordinate removed.
-/
namespace krylov.XR
noncomputable section
open Matrix Finset krylov.Methods
open scoped InnerProductSpace BigOperators
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {p : ℕ}

/-- Genuine finite stored-step synthesis. Article: lem:mm, d=0 branch. -/
def windowSynthesis (s : Fin p → E) : (Fin p → ℝ) →ₗ[ℝ] E where
  toFun a := combine s a
  map_add' a b := by simp only [combine,Pi.add_apply,add_smul,Finset.sum_add_distrib]
  map_smul' r a := by
    simp only [combine,Pi.smul_apply,smul_eq_mul,Finset.smul_sum,smul_smul,RingHom.id_apply]

/-- Its range is precisely the physical stored-step span, including an
empty window. Article: main_krylov, lem:mm. -/
theorem windowSynthesis_range (s : Fin p → E) :
    (windowSynthesis s).range=Submodule.span ℝ (Set.range s) := by
  apply le_antisymm
  · rintro v ⟨a,rfl⟩
    exact combine_mem_span s a
  · apply Submodule.span_le.mpr
    rintro v ⟨i,rfl⟩
    exact ⟨Pi.single i 1,by simp [windowSynthesis,combine,Pi.single_apply]⟩

/-- The physical window-only model uses the unique actual observed
coordinates. Article: main_krylov, lem:mm, zero-direction branch. -/
def physicalWindowModel (s y : Fin p → E) (T : Matrix (Fin p) (Fin p) ℝ)
    (g : E) (hinv : IsUnit (crossGram y s).det) (v : (windowSynthesis s).range) : ℝ :=
  let a := (LinearEquiv.ofInjective (windowSynthesis s)
    (model_window_combination_injective s y hinv)).symm v
  inner ℝ g (v : E)+(a ⬝ᵥ (T*ᵥ a))/2

/-- Genuine zero direction gives the specified zero trial length.
Article: main_krylov, lem:mm, tau=0. -/
theorem modelTrialLength_zero_direction (s y : Fin p → E)
    (T : Matrix (Fin p) (Fin p) ℝ) (g : E) (c : ℝ)
    (hd : modelDirection s y T g=0) : modelTrialLength s y T g c=0 := by
  simp only [modelTrialLength,hd,inner_zero_right,neg_zero,zero_div]

/-- The window-only physical model has exactly the computed trial as
its unique minimizer. No new-direction coordinate is retained when the
genuine solved direction is zero. Article: main_krylov, lem:mm. -/
theorem physicalWindowModel_minimizer (s y : Fin p → E)
    (T : Matrix (Fin p) (Fin p) ℝ) (hT : T.PosDef) (g : E)
    (hinv : IsUnit (crossGram y s).det) (c : ℝ) (hd : modelDirection s y T g=0) :
    ∃ u : (windowSynthesis s).range,(u : E)=modelTrialStep s y T g c ∧
      (∀ v,physicalWindowModel s y T g hinv u≤physicalWindowModel s y T g hinv v) ∧
      (∀ v,physicalWindowModel s y T g hinv v=physicalWindowModel s y T g hinv u ↔ v=u) := by
  let e := LinearEquiv.ofInjective (windowSynthesis s)
    (model_window_combination_injective s y hinv)
  let w := modelCoefficients s T g
  have he (a : Fin p → ℝ) : physicalWindowModel s y T g hinv (e a)=
      blockModelObjective s (modelDirection s y T g) T g 1 a 0 := by
    simp only [physicalWindowModel]
    change inner ℝ g (combine s a)+((e.symm (e a)) ⬝ᵥ (T*ᵥ e.symm (e a)))/2=_
    simp only [LinearEquiv.symm_apply_apply,blockModelObjective,zero_smul,add_zero,one_mul]
    norm_num
  refine ⟨e w,?_,?_,?_⟩
  · rw [modelTrialStep_zero_direction s y T g c hd]
    rfl
  · intro v
    obtain ⟨a,rfl⟩ := e.surjective v
    rw [he,he]
    have hh := blockModel_minimum s y T hT g 1 (by norm_num) a 0
    rw [modelTrialLength_zero_direction s y T g 1 hd] at hh
    exact hh
  · intro v
    obtain ⟨a,rfl⟩ := e.surjective v
    rw [he,he]
    have hh := blockModel_minimizer_iff s y T hT g 1 (by norm_num) a 0
    rw [modelTrialLength_zero_direction s y T g 1 hd] at hh
    simpa only [and_true,e.injective.eq_iff] using hh

end
end krylov.XR
