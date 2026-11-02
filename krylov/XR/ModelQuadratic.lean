import krylov.XR.ModelStep

/-!
Article: main_krylov, lem:mm, exact positive block-model minimization.
Use: complete the actual observed model quadratic at its computed normal
solve; prove its unique coefficient minimizer and the independence of the
physical [S,d] representation. Source: positive quadratic completion and
the already proved observed normal/conjugacy equations.
-/
namespace krylov.XR
noncomputable section
open Matrix Finset krylov.Methods
open scoped InnerProductSpace BigOperators
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {p : ℕ}

/-- The actual block model, in the genuine coefficients of [S,d].
Article: main_krylov, lem:mm. -/
def blockModelObjective (s : Fin p → E) (d : E) (T : Matrix (Fin p) (Fin p) ℝ)
    (g : E) (c : ℝ) (a : Fin p → ℝ) (t : ℝ) : ℝ :=
  inner ℝ g (combine s a+t • d)+(a ⬝ᵥ (T*ᵥ a)+c*t^2)/2

/-- Real symmetric model pairings have the actual cross symmetry.
Article: main_krylov, lem:mm. -/
theorem symmetric_model_cross (T : Matrix (Fin p) (Fin p) ℝ) (hT : T.IsHermitian)
    (a b : Fin p → ℝ) : a ⬝ᵥ (T*ᵥ b)=b ⬝ᵥ (T*ᵥ a) := by
  have hh := hT.star_dotProduct_mulVec_comm a b
  simpa only [star_trivial,dotProduct_comm] using hh

/-- The exact block quadratic completes at the actual computed observed
inverse solve and actual slope/curvature quotient. Article: lem:mm. -/
theorem blockModel_completion (s y : Fin p → E) (T : Matrix (Fin p) (Fin p) ℝ)
    (hT : T.PosDef) (g : E) (c : ℝ) (hc : 0<c) (a : Fin p → ℝ) (t : ℝ) :
    blockModelObjective s (modelDirection s y T g) T g c a t-
      blockModelObjective s (modelDirection s y T g) T g c (modelCoefficients s T g)
        (modelTrialLength s y T g c)=
      ((a-modelCoefficients s T g) ⬝ᵥ (T*ᵥ (a-modelCoefficients s T g))+
        c*(t-modelTrialLength s y T g c)^2)/2 := by
  have hu : IsUnit T.det := isUnit_iff_ne_zero.mpr hT.det_pos.ne'
  have hn := modelCoefficients_normal s T hu g
  have hr : coordinates s g= -(T*ᵥ modelCoefficients s T g) := by rw [hn,neg_neg]
  have hs := symmetric_model_cross T hT.1 a (modelCoefficients s T g)
  have hl : inner ℝ g (modelDirection s y T g)= -c*modelTrialLength s y T g c := by
    unfold modelTrialLength
    field_simp
  simp only [blockModelObjective,inner_add_right,inner_combine_coordinates,
    real_inner_smul_right,hr,dotProduct_neg,hl,mulVec_sub,dotProduct_sub,sub_dotProduct]
  rw [hs]
  ring

/-- The exact block model attains its minimum at the original observed
trial coefficients. Article: main_krylov, lem:mm. -/
theorem blockModel_minimum (s y : Fin p → E) (T : Matrix (Fin p) (Fin p) ℝ)
    (hT : T.PosDef) (g : E) (c : ℝ) (hc : 0<c) (a : Fin p → ℝ) (t : ℝ) :
    blockModelObjective s (modelDirection s y T g) T g c (modelCoefficients s T g)
      (modelTrialLength s y T g c)≤blockModelObjective s (modelDirection s y T g) T g c a t := by
  have hh := blockModel_completion s y T hT g c hc a t
  have hp : 0≤(a-modelCoefficients s T g) ⬝ᵥ (T*ᵥ (a-modelCoefficients s T g)) := by
    simpa only [star_trivial] using hT.posSemidef.dotProduct_mulVec_nonneg (a-modelCoefficients s T g)
  have ht := mul_nonneg hc.le (sq_nonneg (t-modelTrialLength s y T g c))
  linarith

/-- Its unique minimizer is precisely the original computed block trial.
Article: main_krylov, lem:mm, uniqueness clause. -/
theorem blockModel_minimizer_iff (s y : Fin p → E) (T : Matrix (Fin p) (Fin p) ℝ)
    (hT : T.PosDef) (g : E) (c : ℝ) (hc : 0<c) (a : Fin p → ℝ) (t : ℝ) :
    blockModelObjective s (modelDirection s y T g) T g c a t=
      blockModelObjective s (modelDirection s y T g) T g c (modelCoefficients s T g)
        (modelTrialLength s y T g c) ↔
      a=modelCoefficients s T g ∧ t=modelTrialLength s y T g c := by
  constructor
  · intro he
    have hh := blockModel_completion s y T hT g c hc a t
    have hp : 0≤(a-modelCoefficients s T g) ⬝ᵥ (T*ᵥ (a-modelCoefficients s T g)) := by
      simpa only [star_trivial] using hT.posSemidef.dotProduct_mulVec_nonneg (a-modelCoefficients s T g)
    have ht := mul_nonneg hc.le (sq_nonneg (t-modelTrialLength s y T g c))
    have ha : a=modelCoefficients s T g := by
      by_contra hne
      have hn : a-modelCoefficients s T g≠0 := sub_ne_zero.mpr hne
      have hs : 0<(a-modelCoefficients s T g) ⬝ᵥ (T*ᵥ (a-modelCoefficients s T g)) := by
        simpa only [star_trivial] using hT.dotProduct_mulVec_pos hn
      linarith
    refine ⟨ha,?_⟩
    have hz : (t-modelTrialLength s y T g c)^2=0 := by
      nlinarith
    exact sub_eq_zero.mp (sq_eq_zero_iff.mp hz)
  · rintro ⟨rfl,rfl⟩
    rfl

/-- Invertibility of the actual observed cross solve gives actual stored
column independence, before a block quadratic is assigned to physical
vectors. Article: main_krylov, lem:mm. -/
theorem model_window_combination_injective (s y : Fin p → E)
    (hinv : IsUnit (crossGram y s).det) : Function.Injective (combine s) := by
  intro a b he
  have hh := congrArg (coordinates y) he
  rw [coordinates_combine,coordinates_combine] at hh
  have hz := congrArg (fun v=>(crossGram y s)⁻¹*ᵥ v) hh
  simpa only [mulVec_mulVec,nonsing_inv_mul _ hinv,one_mulVec] using hz

/-- The actual observed solve proves independence of [S,d] when its
computed conjugate direction is nonzero. This makes the physical block
model well-defined, rather than assuming a coordinate representation.
Article: main_krylov, lem:mm. -/
theorem model_augmented_combination_injective (s y : Fin p → E)
    (T : Matrix (Fin p) (Fin p) ℝ) (g : E) (hinv : IsUnit (crossGram y s).det)
    (hd : modelDirection s y T g≠0) :
    Function.Injective (fun a : (Fin p → ℝ) × ℝ=>combine s a.1+a.2 • modelDirection s y T g) := by
  rintro ⟨a,t⟩ ⟨b,u⟩ he
  have ho := modelDirection_conjugate s y T hinv g
  have hc : crossGram y s*ᵥ a=crossGram y s*ᵥ b := by
    have h := congrArg (coordinates y) he
    ext i
    have hi := congrFun h i
    have hz := congrFun ho i
    change inner ℝ (y i) (modelDirection s y T g)=0 at hz
    change inner ℝ (y i) (combine s a+t • modelDirection s y T g)=
      inner ℝ (y i) (combine s b+u • modelDirection s y T g) at hi
    rw [inner_add_right,inner_add_right,real_inner_smul_right,real_inner_smul_right,hz,
      mul_zero,mul_zero,add_zero,add_zero] at hi
    simpa only [←coordinates_combine,coordinates] using hi
  have hab : a=b := by
    have hh := congrArg (fun v=>(crossGram y s)⁻¹*ᵥ v) hc
    simpa only [mulVec_mulVec,nonsing_inv_mul _ hinv,one_mulVec] using hh
  have htu : t=u := by
    rw [hab,add_right_inj] at he
    have hz : (t-u) • modelDirection s y T g=0 := by rw [sub_smul,he,sub_self]
    have hn := congrArg norm hz
    rw [norm_smul,Real.norm_eq_abs,norm_zero] at hn
    have hp := norm_pos_iff.mpr hd
    have hh : |t-u|=0 := by nlinarith [abs_nonneg (t-u)]
    exact sub_eq_zero.mp (abs_eq_zero.mp hh)
  exact Prod.ext hab htu

/-- The genuine linear synthesis of the augmented physical window.
Article: main_krylov, lem:mm. -/
def modelSynthesis (s : Fin p → E) (d : E) : ((Fin p → ℝ) × ℝ) →ₗ[ℝ] E where
  toFun a := combine s a.1+a.2 • d
  map_add' a b := by
    simp only [Prod.fst_add,Prod.snd_add,combine,Pi.add_apply,add_smul,Finset.sum_add_distrib]
    abel
  map_smul' r a := by
    simp only [Prod.smul_fst,Prod.smul_snd,combine,Pi.smul_apply,smul_eq_mul,
      smul_add,Finset.smul_sum,smul_smul,RingHom.id_apply]

/-- The actual augmented synthesis spans exactly the article's physical
window and new direction. Article: main_krylov, lem:mm. -/
theorem modelSynthesis_range (s : Fin p → E) (d : E) :
    (modelSynthesis s d).range=Submodule.span ℝ (insert d (Set.range s)) := by
  apply le_antisymm
  · rintro v ⟨⟨a,t⟩,rfl⟩
    apply Submodule.add_mem
    · exact Submodule.span_mono (Set.subset_insert d (Set.range s)) (combine_mem_span s a)
    · exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_insert d _))
  · apply Submodule.span_le.mpr
    rintro v (rfl|⟨i,rfl⟩)
    · exact ⟨(0,1),by simp [modelSynthesis,combine]⟩
    · refine ⟨(Pi.single i 1,0),?_⟩
      simp [modelSynthesis,combine,Pi.single_apply]

/-- The physical quadratic is obtained through the unique actual [S,d]
coordinates; its definition is restricted to the genuine observed inverse
and nonzero-direction domains. Article: main_krylov, lem:mm. -/
def physicalBlockModel (s y : Fin p → E) (T : Matrix (Fin p) (Fin p) ℝ) (g : E)
    (c : ℝ) (hinv : IsUnit (crossGram y s).det) (hd : modelDirection s y T g≠0)
    (v : (modelSynthesis s (modelDirection s y T g)).range) : ℝ :=
  let a := (LinearEquiv.ofInjective (modelSynthesis s (modelDirection s y T g))
    (model_augmented_combination_injective s y T g hinv hd)).symm v
  blockModelObjective s (modelDirection s y T g) T g c a.1 a.2

/-- On the genuine physical span the unique minimizer is exactly the
computed model trial. All representation independence and the minimum
are conclusions of the actual observed solve. Article: lem:mm. -/
theorem physicalBlockModel_minimizer (s y : Fin p → E)
    (T : Matrix (Fin p) (Fin p) ℝ) (hT : T.PosDef) (g : E) (c : ℝ) (hc : 0<c)
    (hinv : IsUnit (crossGram y s).det) (hd : modelDirection s y T g≠0) :
    ∃ u : (modelSynthesis s (modelDirection s y T g)).range,
      (u : E)=modelTrialStep s y T g c ∧
      (∀ v,physicalBlockModel s y T g c hinv hd u≤physicalBlockModel s y T g c hinv hd v) ∧
      (∀ v,physicalBlockModel s y T g c hinv hd v=physicalBlockModel s y T g c hinv hd u ↔ v=u) := by
  let e := LinearEquiv.ofInjective (modelSynthesis s (modelDirection s y T g))
    (model_augmented_combination_injective s y T g hinv hd)
  let a := (modelCoefficients s T g,modelTrialLength s y T g c)
  refine ⟨e a,rfl,?_,?_⟩
  · intro v
    change blockModelObjective _ _ _ _ _ (e.symm (e a)).1 (e.symm (e a)).2≤
      blockModelObjective _ _ _ _ _ (e.symm v).1 (e.symm v).2
    rw [LinearEquiv.symm_apply_apply]
    exact blockModel_minimum s y T hT g c hc (e.symm v).1 (e.symm v).2
  · intro v
    change blockModelObjective _ _ _ _ _ (e.symm v).1 (e.symm v).2=
      blockModelObjective _ _ _ _ _ (e.symm (e a)).1 (e.symm (e a)).2 ↔ _
    rw [LinearEquiv.symm_apply_apply,blockModel_minimizer_iff s y T hT g c hc]
    change (e.symm v).1=a.1 ∧ (e.symm v).2=a.2 ↔ v=e a
    rw [←Prod.ext_iff]
    exact e.symm_apply_eq

/-- On genuine affine-quadratic gradient data the tested conjugate
curvature is exactly the new-direction quadratic curvature; all old
window contributions cancel by the actual observed solve.
Article: main_krylov, lem:mm, last identity. -/
theorem modelTrial_quadratic_curvature (Q : E →L[ℝ] E) (b x : E)
    (s : Fin p → E) (T : Matrix (Fin p) (Fin p) ℝ)
    (hinv : IsUnit (crossGram (fun i=>Q (s i)) s).det) (c t : ℝ) :
    let y := fun i=>Q (s i)
    let g := Q x+b
    let d := modelDirection s y T g
    inner ℝ d (Q (x+t • modelTrialStep s y T g c)+b-modelVirtualGradient s y T g)=
      t*modelTrialLength s y T g c*inner ℝ d (Q d) := by
  dsimp only
  let y := fun i=>Q (s i)
  let g := Q x+b
  let d := modelDirection s y T g
  let w := modelCoefficients s T g
  have hQ : Q (combine s w)=combine y w := by simp only [combine,map_sum,map_smul,y]
  have hz : inner ℝ d (combine y w)=0 := by
    rw [inner_combine_coordinates,modelDirection_conjugate s y T hinv g,dotProduct_zero]
  change inner ℝ d (Q (x+t • modelTrialStep s y T g c)+b-modelVirtualGradient s y T g)=_
  have he : Q (x+t • modelTrialStep s y T g c)+b-modelVirtualGradient s y T g=
      t • Q (modelTrialStep s y T g c)-combine y w := by
    simp only [map_add,map_smul,modelVirtualGradient]
    change Q x+t • Q (modelTrialStep s y T g c)+b-(g+combine y w)=_
    dsimp only [g]
    abel
  rw [he,inner_sub_right,real_inner_smul_right,hz,sub_zero]
  have hu : Q (modelTrialStep s y T g c)=combine y w+modelTrialLength s y T g c • Q d := by
    simp only [modelTrialStep,modelVirtualCorrection,map_add,map_smul]
    exact congrArg (fun v=>v+modelTrialLength s y T g c • Q d) hQ
  rw [hu,inner_add_right,hz,zero_add,real_inner_smul_right,mul_assoc]

end
end krylov.XR
