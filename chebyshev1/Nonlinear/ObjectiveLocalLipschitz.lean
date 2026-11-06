import chebyshev1.Nonlinear.ObjectiveModels

/-! The local Hessian-Lipschitz assumption in the objective model directly
implies the weighted second-variation bound. Ball controls are constructed,
including Hessian symmetry, rather than added as hypotheses. -/
namespace chebyshev1.Nonlinear
noncomputable section
open Filter Set
open scoped Topology RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false
variable {d : Type*} [Fintype d] [DecidableEq d]

omit [DecidableEq d] in
theorem objective_gradient_derivative_inner (f : EuclideanSpace ℝ d → ℝ)
    (u v : EuclideanSpace ℝ d) :
    ⟪fderiv ℝ (gradient f) 0 u, v⟫ = fderiv ℝ (fderiv ℝ f) 0 u v := by
  let R := (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ d)).symm.toContinuousLinearEquiv
  have he : gradient f = R ∘ fderiv ℝ f := rfl
  rw [he, R.comp_fderiv]
  change ⟪(InnerProductSpace.toDual ℝ (EuclideanSpace ℝ d)).symm _, v⟫ = _
  rw [← InnerProductSpace.toDual_apply_apply, LinearIsometryEquiv.apply_symm_apply]
  rfl

/-- Hessian symmetry follows from pointwise second differentiability of the objective. -/
theorem objective_hessian_hermitian (f : EuclideanSpace ℝ d → ℝ)
    (hf : Perturbations.ThreeTimesDifferentiableAtZero f) :
    (hessianMatrix (fderiv ℝ (gradient f) 0)).IsHermitian := by
  apply Matrix.isSymmetric_toEuclideanLin_iff.mp
  have he : (hessianMatrix (fderiv ℝ (gradient f) 0)).toEuclideanLin =
      (fderiv ℝ (gradient f) 0).toLinearMap := by
    change ((Matrix.toEuclideanCLM (n := d) (𝕜 := ℝ))
      ((Matrix.toEuclideanCLM (n := d) (𝕜 := ℝ)).symm _)).toLinearMap = _
    rw [(Matrix.toEuclideanCLM (n := d) (𝕜 := ℝ)).apply_symm_apply]
  rw [he]
  intro u v
  change ⟪fderiv ℝ (gradient f) 0 u, v⟫ = ⟪u, fderiv ℝ (gradient f) 0 v⟫
  rw [objective_gradient_derivative_inner, ← real_inner_comm u (fderiv ℝ (gradient f) 0 v),
    objective_gradient_derivative_inner]
  exact second_derivative_symmetric_of_eventually_of_real
    (hf.first.mono fun _ hx => hx.hasFDerivAt) hf.second.self_of_nhds.hasFDerivAt u v

/-- A Hessian Lipschitz on any neighborhood supplies all ball-control data. -/
theorem objective_hessianControl_exists (I : SpectralInterval)
    (f : EuclideanSpace ℝ d → ℝ) (hf : Perturbations.ThreeTimesDifferentiableAtZero f)
    (hstationary : gradient f 0 = 0)
    (hspec : spectrum ℝ (hessianMatrix (fderiv ℝ (gradient f) 0)) ⊆ Icc I.mu I.L)
    (rho : NNReal) (U : Set (EuclideanSpace ℝ d)) (hU : U ∈ 𝓝 0)
    (hlip : LipschitzOnWith rho (fderiv ℝ (gradient f)) U) :
    ∃ R : ℝ, 0 < R ∧ HessianControl I (gradient f)
      (fderiv ℝ (gradient f)) rho R := by
  have hg := (Perturbations.objective_gradient_pointwise f hf).1
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp (Filter.inter_mem hU hg)
  have hsub : Metric.closedBall (0 : EuclideanSpace ℝ d) (r/2) ⊆
      U ∩ {x | DifferentiableAt ℝ (gradient f) x} := by
    intro x hx
    apply hball
    rw [Metric.mem_closedBall, dist_zero_right] at hx
    rw [Metric.mem_ball, dist_zero_right]
    linarith
  have hzero : (0 : EuclideanSpace ℝ d) ∈ U := mem_of_mem_nhds hU
  refine ⟨r/2,by positivity,?_⟩
  refine {
    rho_nonneg := rho.coe_nonneg
    radius_nonneg := by positivity
    stationary := hstationary
    hermitian := objective_hessian_hermitian f hf
    spectrum := hspec
    continuous := hlip.continuousOn.mono (fun x hx => (hsub hx).1)
    derivative := ?_
    lipschitz := ?_ }
  · intro x hx
    exact (hsub (by simpa only [Metric.mem_closedBall, dist_zero_right] using hx)).2.hasFDerivAt
  · intro x hx
    have hxu := (hsub (by simpa only [Metric.mem_closedBall, dist_zero_right] using hx)).1
    simpa only [dist_eq_norm, sub_zero] using hlip.dist_le_mul x hxu 0 hzero

/-- The article's local Lipschitz hypothesis suffices directly; no continuity
or radius restriction is assumed separately and the bound holds for every v. -/
theorem objectiveSecondVariation_norm_le_of_lipschitz_near
    (family : MethodFamily) (I : SpectralInterval) {N : ℕ} (hN : 0 < N)
    (f : EuclideanSpace ℝ d → ℝ) (hf : Perturbations.ThreeTimesDifferentiableAtZero f)
    (hstationary : gradient f 0 = 0)
    (hspec : spectrum ℝ (hessianMatrix (fderiv ℝ (gradient f) 0)) ⊆ Icc I.mu I.L)
    (rho : NNReal) (U : Set (EuclideanSpace ℝ d)) (hU : U ∈ 𝓝 0)
    (hlip : LipschitzOnWith rho (fderiv ℝ (gradient f)) U)
    (v : EuclideanSpace ℝ d) :
    ‖objectiveSecondVariation family I N f v‖ ≤
      ((rho : ℝ)/I.delta)*I.epsilon N*secondOrderCoefficient (family.data N) I N*‖v‖^2 := by
  obtain ⟨R,hR,hcontrol⟩ := objective_hessianControl_exists I f hf hstationary hspec rho U hU hlip
  exact objectiveSecondVariation_norm_le family I hN f hf _ rho R hcontrol hR v

end
end chebyshev1.Nonlinear
