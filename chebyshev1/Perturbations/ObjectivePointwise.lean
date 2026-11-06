import chebyshev1.Perturbations.VectorExpansion

/-! Pointwise third differentiability of the objective, transported through its
actual Riesz gradient and finite-dimensional coordinates. -/
namespace chebyshev1.Perturbations
noncomputable section
open Filter Set Asymptotics
open scoped Topology RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Pointwise third differentiability: the first two derivatives exist near
zero, and the second derivative is differentiable at zero. -/
structure ThreeTimesDifferentiableAtZero (f : E → ℝ) : Prop where
  first : ∀ᶠ x in 𝓝 (0:E), DifferentiableAt ℝ f x
  second : ∀ᶠ x in 𝓝 (0:E), DifferentiableAt ℝ (fderiv ℝ f) x
  third : DifferentiableAt ℝ (fderiv ℝ (fderiv ℝ f)) 0

theorem objective_gradient_pointwise (f : E → ℝ) (hf : ThreeTimesDifferentiableAtZero f) :
    (∀ᶠ x in 𝓝 (0:E), DifferentiableAt ℝ (gradient f) x) ∧
      DifferentiableAt ℝ (fderiv ℝ (gradient f)) 0 := by
  let R := (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv
  have hgrad : gradient f = R ∘ fderiv ℝ f := rfl
  constructor
  · exact hf.second.mono (fun x hx => R.differentiableAt.comp x hx)
  · have he : fderiv ℝ (gradient f) =
        fun x => R.toContinuousLinearMap.comp (fderiv ℝ (fderiv ℝ f) x) := by
      funext x
      rw [hgrad, R.comp_fderiv]
    rw [he]
    exact (differentiableAt_const R.toContinuousLinearMap).clm_comp hf.third

theorem objective_gradientCoordinates_pointwise {d : Type*} [Fintype d]
    (f : EuclideanSpace ℝ d → ℝ) (hf : ThreeTimesDifferentiableAtZero f) :
    (∀ᶠ x in 𝓝 (0 : d → ℝ), DifferentiableAt ℝ
      (Nonlinear.gradientCoordinates (gradient f)) x) ∧
      DifferentiableAt ℝ (fderiv ℝ (Nonlinear.gradientCoordinates (gradient f))) 0 := by
  let T := PiLp.continuousLinearEquiv 2 ℝ (fun _ : d => ℝ)
  let g := Nonlinear.gradientCoordinates (gradient f)
  have he : g = T ∘ (gradient f ∘ T.symm) := rfl
  have hh := objective_gradient_pointwise f hf
  have hpre : Tendsto T.symm (𝓝 (0 : d → ℝ)) (𝓝 (0 : EuclideanSpace ℝ d)) := by
    simpa only [map_zero] using T.symm.continuous.tendsto 0
  constructor
  · filter_upwards [hpre.eventually hh.1] with x hx
    exact T.differentiableAt.comp x (hx.comp x T.symm.differentiableAt)
  · have hfd : fderiv ℝ g = fun x => T.toContinuousLinearMap.comp
        ((fderiv ℝ (gradient f) (T.symm x)).comp T.symm.toContinuousLinearMap) := by
      funext x
      rw [he, T.comp_fderiv, T.symm.comp_right_fderiv]
    rw [hfd]
    have hc : DifferentiableAt ℝ (fun x : d → ℝ => fderiv ℝ (gradient f) (T.symm x)) 0 := by
      have h0 : DifferentiableAt ℝ (fderiv ℝ (gradient f)) (T.symm 0) := by
        simpa only [map_zero] using hh.2
      exact h0.comp 0 T.symm.differentiableAt
    exact (differentiableAt_const T.toContinuousLinearMap).clm_comp
      (hc.clm_comp (differentiableAt_const T.symm.toContinuousLinearMap))

theorem coordinate_gradientLinearization {d : Type*} [Fintype d] [DecidableEq d]
    (f : EuclideanSpace ℝ d → ℝ) :
    TwoTerm.gradientLinearization (Nonlinear.gradientCoordinates (gradient f)) =
      Nonlinear.hessianMatrix (fderiv ℝ (gradient f) 0) := by
  let T := PiLp.continuousLinearEquiv 2 ℝ (fun _ : d => ℝ)
  have hg : Nonlinear.gradientCoordinates (gradient f) = T ∘ (gradient f ∘ T.symm) := rfl
  apply (Matrix.toEuclideanCLM (n := d) (𝕜 := ℝ)).injective
  apply ContinuousLinearMap.ext
  intro v
  change WithLp.toLp 2 ((TwoTerm.gradientLinearization _).mulVec (WithLp.ofLp v)) = _
  rw [TwoTerm.gradientLinearization_mulVec, hg, T.comp_fderiv, T.symm.comp_right_fderiv]
  simp only [map_zero, ContinuousLinearMap.comp_apply]
  change WithLp.toLp 2 (WithLp.ofLp ((fderiv ℝ (gradient f) 0) v)) =
    Matrix.toEuclideanCLM (n := d) (𝕜 := ℝ) (Nonlinear.hessianMatrix (fderiv ℝ (gradient f) 0)) v
  rw [show Matrix.toEuclideanCLM (n := d) (𝕜 := ℝ)
    (Nonlinear.hessianMatrix (fderiv ℝ (gradient f) 0)) = fderiv ℝ (gradient f) 0 by
      exact (Matrix.toEuclideanCLM (n := d) (𝕜 := ℝ)).apply_symm_apply _]

theorem coordinate_gradient_second_derivative {d : Type*} [Fintype d]
    (f : EuclideanSpace ℝ d → ℝ) (u v : d → ℝ) :
    WithLp.toLp 2 ((fderiv ℝ (fderiv ℝ (Nonlinear.gradientCoordinates (gradient f))) 0 u) v) =
      (fderiv ℝ (fderiv ℝ (gradient f)) 0 (WithLp.toLp 2 u)) (WithLp.toLp 2 v) := by
  apply ext_inner_right ℝ
  intro w
  have hh := coordinate_gradient_second_derivative_inner f u v (WithLp.ofLp w)
  have hg := gradient_second_derivative_inner f 0 (WithLp.toLp 2 u) (WithLp.toLp 2 v) w
  simpa only [WithLp.toLp_ofLp] using hh.trans hg.symm

end
end chebyshev1.Perturbations

namespace chebyshev1.TwoTerm
noncomputable section
open Filter Asymptotics
open scoped Topology
variable {d : Type*} [Fintype d] [DecidableEq d]

/-- Corollary 8.1(a): pointwise third differentiability suffices for the
uniform full-initial-vector expansion, with its actual third-derivative tensor. -/
theorem objectiveError_vector_second_order (S : TwoTerm) (f : EuclideanSpace ℝ d → ℝ)
    (hf : Perturbations.ThreeTimesDifferentiableAtZero f) (hstationary : gradient f 0 = 0)
    (N : ℕ) :
    let g := Nonlinear.gradientCoordinates (gradient f)
    (fun v : EuclideanSpace ℝ d => (WithLp.toLp 2 (S.nonlinearError g (WithLp.ofLp v) N) : EuclideanSpace ℝ d)-
      ((WithLp.toLp 2 (S.quadraticError (gradientLinearization g) (WithLp.ofLp v) N) : EuclideanSpace ℝ d)+
        (WithLp.toLp 2 (S.quadraticCorrection g (WithLp.ofLp v) N) : EuclideanSpace ℝ d)))
      =o[𝓝 0] (fun v : EuclideanSpace ℝ d => ‖v‖^2) := by
  let T := PiLp.continuousLinearEquiv 2 ℝ (fun _ : d => ℝ)
  let V : EuclideanSpace ℝ d →L[ℝ] (d → ℝ) := T.toContinuousLinearMap
  let U : (d → ℝ) →L[ℝ] EuclideanSpace ℝ d := T.symm.toContinuousLinearMap
  let g := Nonlinear.gradientCoordinates (gradient f)
  have hg := Perturbations.objective_gradientCoordinates_pointwise f hf
  have hh := S.nonlinearError_vector_second_order g hg.1 hg.2
    (by simp [g, Nonlinear.gradientCoordinates, hstationary]) N
  have hpre : Tendsto V (𝓝 (0 : EuclideanSpace ℝ d)) (𝓝 (0 : d → ℝ)) := by
    simpa only [map_zero] using V.continuous.tendsto 0
  have hc := (hh.comp_tendsto hpre).trans_isBigO (V.isBigO_comp (fun v => v) (𝓝 0) |>.norm_norm.pow 2)
  have hout := (U.isBigO_comp _ (𝓝 0)).trans_isLittleO hc
  have hU (x : d → ℝ) : U x = WithLp.toLp 2 x := rfl
  have hV (x : EuclideanSpace ℝ d) : V x = WithLp.ofLp x := rfl
  simpa only [Function.comp_def, map_sub, map_add, hU, hV, g,
    WithLp.toLp_sub, WithLp.toLp_add] using hout

end
end chebyshev1.TwoTerm
