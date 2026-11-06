import chebyshev1.TwoTerm.Translation
import chebyshev1.Nonlinear.ObjectiveModels

/-! The origin-centered estimates act on the literal physical iteration around
any stationary point. Translation transports the oracle, Hessian and tensor. -/
namespace chebyshev1.Nonlinear
noncomputable section
open Filter Set Asymptotics Polynomial Polynomial.Chebyshev
open scoped Topology
variable {d : Type*} [Fintype d] [DecidableEq d]

omit [Fintype d] [DecidableEq d] in
/-- Actual physical iterates about an arbitrary center agree with the existing
error-coordinate trajectory through the used horizon. -/
theorem errorTrajectory_translate (family : MethodFamily) (I : SpectralInterval)
    {N : ℕ} (hN : 0 < N)
    (g : EuclideanSpace ℝ d → EuclideanSpace ℝ d)
    (a e0 : EuclideanSpace ℝ d) (n : ℕ) (hn : n ≤ N) :
    errorTrajectory family I N g (a+e0) n-a =
      errorTrajectory family I N (fun e => g (a+e)) e0 n := by
  have hf : ∀ s, 0 < s → s < N →
      ((family.data N).method I).a s + ((family.data N).method I).b s = 1 := by
    intro s hs hsN
    obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hs.ne'
    exact (family.data N).fixed_point I k
      ((family.admissible I hN) (k+2) (by omega)).ne'
  have hh := ((family.data N).method I).nonlinearError_translate_upto
    (gradientCoordinates g) (WithLp.ofLp a) (WithLp.ofLp e0) hf n hn
  have hshift : (fun e => gradientCoordinates g (WithLp.ofLp a+e)) =
      gradientCoordinates (fun e => g (a+e)) := by
    funext e
    simp only [gradientCoordinates, WithLp.toLp_add, WithLp.toLp_ofLp]
  rw [hshift] at hh
  have hc := congrArg (WithLp.toLp 2) hh
  simpa only [errorTrajectory, WithLp.ofLp_add, WithLp.toLp_sub, WithLp.toLp_ofLp] using hc

/-- Primitive Hessian data on a ball centered at `a` imply the existing
origin-centered control, without any trajectory assumption. -/
theorem hessianControl_translate (I : SpectralInterval)
    (g : EuclideanSpace ℝ d → EuclideanSpace ℝ d)
    (A : EuclideanSpace ℝ d → EuclideanSpace ℝ d →L[ℝ] EuclideanSpace ℝ d)
    (a : EuclideanSpace ℝ d) (rho R : ℝ) (hrho : 0 ≤ rho) (hR : 0 ≤ R)
    (hstationary : g a = 0) (hhermitian : (hessianMatrix (A a)).IsHermitian)
    (hspectrum : spectrum ℝ (hessianMatrix (A a)) ⊆ Icc I.mu I.L)
    (hcontinuous : ContinuousOn A (Metric.closedBall a R))
    (hderivative : ∀ x, ‖x-a‖ ≤ R → HasFDerivAt g (A x) x)
    (hlipschitz : ∀ x, ‖x-a‖ ≤ R → ‖A x-A a‖ ≤ rho*‖x-a‖) :
    HessianControl I (fun e => g (a+e)) (fun e => A (a+e)) rho R := by
  have hball (e : EuclideanSpace ℝ d) (he : ‖e‖ ≤ R) :
      a+e ∈ Metric.closedBall a R := by
    simpa only [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left] using he
  refine ⟨hrho,hR,?_,?_,?_,?_,?_,?_⟩
  · simpa only [add_zero] using hstationary
  · simpa only [add_zero] using hhermitian
  · simpa only [add_zero] using hspectrum
  · apply hcontinuous.comp (continuous_const.add continuous_id).continuousOn
    intro e he
    exact hball e (by simpa only [Metric.mem_closedBall, dist_zero_right] using he)
  · intro e he
    exact (hasFDerivAt_comp_add_left a).mpr
      (hderivative (a+e) (by simpa only [add_sub_cancel_left] using he))
  · intro e he
    simpa only [add_zero, add_sub_cancel_left] using
      hlipschitz (a+e) (by simpa only [add_sub_cancel_left] using he)

/-- Confinement for the literal run initialized at `a+e0`. -/
theorem lipschitzHessian_confinement_at (family : MethodFamily) (I : SpectralInterval)
    {N : ℕ} (hN : 0 < N)
    (g : EuclideanSpace ℝ d → EuclideanSpace ℝ d)
    (A : EuclideanSpace ℝ d → EuclideanSpace ℝ d →L[ℝ] EuclideanSpace ℝ d)
    (a e0 : EuclideanSpace ℝ d) (rho R : ℝ)
    (h : HessianControl I (fun e => g (a+e)) (fun e => A (a+e)) rho R)
    (he0 : ‖e0‖ ≤ R) (hsmall : rho*R ≤ 2*I.mu) :
    ∀ n ≤ N, ‖errorTrajectory family I N g (a+e0) n-a‖ ≤ ‖e0‖ := by
  intro n hn
  rw [errorTrajectory_translate family I hN g a e0 n hn]
  exact lipschitzHessian_confinement family I hN _ _ e0 rho R h he0 hsmall n hn

/-- The local terminal estimate, with the physical center displayed explicitly. -/
theorem lipschitzHessian_local_error_le_at (family : MethodFamily) (I : SpectralInterval)
    {N : ℕ} (hN : 0 < N)
    (g : EuclideanSpace ℝ d → EuclideanSpace ℝ d)
    (A : EuclideanSpace ℝ d → EuclideanSpace ℝ d →L[ℝ] EuclideanSpace ℝ d)
    (a e0 : EuclideanSpace ℝ d) (rho R : ℝ)
    (h : HessianControl I (fun e => g (a+e)) (fun e => A (a+e)) rho R)
    (he0 : ‖e0‖ ≤ R) (hsmall : rho*R ≤ 2*I.mu) :
    ‖errorTrajectory family I N g (a+e0) N-a‖ ≤
      I.epsilon N*(T ℝ N).eval (1+rho*‖e0‖/I.delta)*‖e0‖ := by
  rw [errorTrajectory_translate family I hN g a e0 N le_rfl]
  exact lipschitzHessian_local_error_le family I hN _ _ e0 rho R h he0 hsmall

/-- The weighted second-order estimate for a physical run around `a`. -/
theorem lipschitzHessian_weighted_discrepancy_le_at
    (family : MethodFamily) (I : SpectralInterval) {N : ℕ} (hN : 0 < N)
    (g : EuclideanSpace ℝ d → EuclideanSpace ℝ d)
    (A : EuclideanSpace ℝ d → EuclideanSpace ℝ d →L[ℝ] EuclideanSpace ℝ d)
    (a e0 : EuclideanSpace ℝ d) (rho R : ℝ)
    (h : HessianControl I (fun e => g (a+e)) (fun e => A (a+e)) rho R)
    (he0 : ‖e0‖ ≤ R) (hsmall : rho*‖e0‖ ≤ 2*I.mu) :
    ‖errorTrajectory family I N g (a+e0) N-a-
      quadraticTerminal I N (hessianMatrix (A a)) e0‖ ≤
      (rho/I.delta)*I.epsilon N*secondOrderCoefficient (family.data N) I N*
        Real.exp (2*(N:ℝ)^2*rho*‖e0‖/I.delta)*‖e0‖^2 := by
  rw [errorTrajectory_translate family I hN g a e0 N le_rfl]
  simpa only [add_zero] using
    lipschitzHessian_weighted_discrepancy_le family I hN _ _ e0 rho R h he0 hsmall

/-- Full-vector expansion of the actual run at an arbitrary stationary point.
All differentiability premises refer to the original objective near that point. -/
theorem objectiveError_full_expansion_at (family : MethodFamily) (I : SpectralInterval)
    {N : ℕ} (hN : 0 < N) (f : EuclideanSpace ℝ d → ℝ) (a : EuclideanSpace ℝ d)
    (hfirst : ∀ᶠ x in 𝓝 a, DifferentiableAt ℝ f x)
    (hsecond : ∀ᶠ x in 𝓝 a, DifferentiableAt ℝ (fderiv ℝ f) x)
    (hthird : DifferentiableAt ℝ (fderiv ℝ (fderiv ℝ f)) a)
    (hstationary : gradient f a = 0) :
    (fun v : EuclideanSpace ℝ d => errorTrajectory family I N (gradient f) (a+v) N-a-
      quadraticTerminal I N (hessianMatrix (fderiv ℝ (gradient f) a)) v-
        objectiveSecondVariation family I N (fun e => f (a+e)) v)
      =o[𝓝 0] (fun v : EuclideanSpace ℝ d => ‖v‖^2) := by
  have hf := Perturbations.threeTimesDifferentiableAtZero_translate
    f a hfirst hsecond hthird
  have hs : gradient (fun e => f (a+e)) 0 = 0 := by
    simpa only [Perturbations.gradient_translate, add_zero] using hstationary
  have he := objectiveError_full_expansion family I hN (fun e => f (a+e)) hf hs
  have hg : gradient (fun e => f (a+e)) = fun e => gradient f (a+e) :=
    funext (Perturbations.gradient_translate f a)
  simpa only [errorTrajectory_translate family I hN (gradient f) a _ N le_rfl,
    hg, fderiv_comp_add_left, add_zero] using he

end
end chebyshev1.Nonlinear
