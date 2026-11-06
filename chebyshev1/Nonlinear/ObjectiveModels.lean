import chebyshev1.Nonlinear.SecondVariationBound

/-! The article's full-vector objective model and its sharp weighted bound. -/
namespace chebyshev1.Nonlinear
noncomputable section
open Filter Asymptotics
open scoped Topology
variable {d : Type*} [Fintype d] [DecidableEq d]

/-- The actual second variation, in Euclidean coordinates. Its tensor is the
Riesz representation of the objective's third derivative. -/
def objectiveSecondVariation (family : MethodFamily) (I : SpectralInterval) (N : ℕ)
    (f : EuclideanSpace ℝ d → ℝ) (v : EuclideanSpace ℝ d) : EuclideanSpace ℝ d :=
  WithLp.toLp 2 (((family.data N).method I).quadraticCorrection
    (gradientCoordinates (gradient f)) (WithLp.ofLp v) N)

/-- Pointwise third differentiability gives the expansion uniformly over the
whole initial vector. The stationary Hessian and terminal residual are actual
derivatives and the terminal Chebyshev polynomial. -/
theorem objectiveError_full_expansion (family : MethodFamily) (I : SpectralInterval)
    {N : ℕ} (hN : 0 < N) (f : EuclideanSpace ℝ d → ℝ)
    (hf : Perturbations.ThreeTimesDifferentiableAtZero f) (hstationary : gradient f 0 = 0) :
    (fun v : EuclideanSpace ℝ d => errorTrajectory family I N (gradient f) v N-
      quadraticTerminal I N (hessianMatrix (fderiv ℝ (gradient f) 0)) v-
        objectiveSecondVariation family I N f v)
      =o[𝓝 0] (fun v : EuclideanSpace ℝ d => ‖v‖^2) := by
  let J := family.data N
  let g := gradientCoordinates (gradient f)
  have heq (v : EuclideanSpace ℝ d) :
      (WithLp.toLp 2 ((J.method I).quadraticError (TwoTerm.gradientLinearization g)
        (WithLp.ofLp v) N) : EuclideanSpace ℝ d) =
        quadraticTerminal I N (hessianMatrix (fderiv ℝ (gradient f) 0)) v := by
    change WithLp.toLp 2 ((J.method I).quadraticError
      (TwoTerm.gradientLinearization (gradientCoordinates (gradient f))) (WithLp.ofLp v) N) = _
    rw [Perturbations.coordinate_gradientLinearization,
      J.quadraticError_exact I (family.admissible I hN) N le_rfl,
      J.terminal_residual I (by positivity : (2/(2:ℝ)^N) ≠ 0) (family.terminal hN)]
    rfl
  have hh := (J.method I).objectiveError_vector_second_order f hf hstationary N
  change (fun v : EuclideanSpace ℝ d => (WithLp.toLp 2 ((J.method I).nonlinearError g (WithLp.ofLp v) N) : EuclideanSpace ℝ d)-
    ((WithLp.toLp 2 ((J.method I).quadraticError (TwoTerm.gradientLinearization g) (WithLp.ofLp v) N) : EuclideanSpace ℝ d)+
      objectiveSecondVariation family I N f v)) =o[𝓝 0] (fun v : EuclideanSpace ℝ d => ‖v‖^2) at hh
  simp_rw [heq] at hh
  convert hh using 1
  funext v
  dsimp only [errorTrajectory, J, g]
  abel

/-- The separate all-vector bound on `Z`, including the trajectory-weighted
coefficient from the finite nonlinear discrepancy theorem. -/
theorem objectiveSecondVariation_norm_le (family : MethodFamily) (I : SpectralInterval)
    {N : ℕ} (hN : 0 < N) (f : EuclideanSpace ℝ d → ℝ)
    (hf : Perturbations.ThreeTimesDifferentiableAtZero f)
    (A : EuclideanSpace ℝ d → EuclideanSpace ℝ d →L[ℝ] EuclideanSpace ℝ d)
    (rho R : ℝ) (h : HessianControl I (gradient f) A rho R) (hR : 0 < R)
    (v : EuclideanSpace ℝ d) :
    ‖objectiveSecondVariation family I N f v‖ ≤
      (rho/I.delta)*I.epsilon N*secondOrderCoefficient (family.data N) I N*‖v‖^2 :=
  objective_quadraticCorrection_norm_le family I hN f hf A rho R h hR v

end
end chebyshev1.Nonlinear
