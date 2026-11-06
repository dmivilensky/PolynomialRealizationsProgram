import chebyshev1.Nonlinear.LocalConvergence
import chebyshev1.Jacobi.EndpointProfile

/-! Quantitative nonlinear discrepancy and the weighted endpoint coefficient.
The finite discrepancy estimate retains its exact Chebyshev majorant. -/
namespace chebyshev1.Nonlinear
noncomputable section
open Polynomial Polynomial.Chebyshev
open scoped BigOperators Matrix.Norms.L2Operator
variable {d : Type*} [Fintype d] [DecidableEq d]

/-- The exact quadratic-objective terminal map at the stationary Hessian. -/
def quadraticTerminal (I : SpectralInterval) (N : ℕ)
    (H : Matrix d d ℝ) : EuclideanSpace ℝ d →L[ℝ] EuclideanSpace ℝ d :=
  Matrix.toEuclideanCLM (n := d) (𝕜 := ℝ) (aeval H (I.residual N))

/-- The nonlinear discrepancy has the exact finite-drift majorant, with the
trajectory bound supplied by confinement rather than assumed. -/
theorem lipschitzHessian_discrepancy_le (family : MethodFamily) (I : SpectralInterval)
    {N : ℕ} (hN : 0 < N)
    (g : EuclideanSpace ℝ d → EuclideanSpace ℝ d)
    (A : EuclideanSpace ℝ d → EuclideanSpace ℝ d →L[ℝ] EuclideanSpace ℝ d)
    (e0 : EuclideanSpace ℝ d) (rho R : ℝ)
    (h : HessianControl I g A rho R) (he0 : ‖e0‖ ≤ R)
    (hsmall : rho*‖e0‖ ≤ 2*I.mu) :
    ‖errorTrajectory family I N g e0 N - quadraticTerminal I N (hessianMatrix (A 0)) e0‖ ≤
      I.epsilon N*((T ℝ N).eval (1+rho*‖e0‖/I.delta)-1)*‖e0‖ := by
  have hr := h.restrict (norm_nonneg e0) he0
  have hc := lipschitzHessian_confinement family I hN g A e0 rho ‖e0‖ hr le_rfl hsmall
  let Hs : ℕ → Matrix d d ℝ := fun s =>
    hessianMatrix (averagedDerivative A 0 (errorTrajectory family I N g e0 s))
  have heq (s : ℕ) (hs : s < N) :
      gradientCoordinates g (((family.data N).method I).nonlinearError
        (gradientCoordinates g) (WithLp.ofLp e0) s) =
      (Hs s).mulVec (((family.data N).method I).nonlinearError
        (gradientCoordinates g) (WithLp.ofLp e0) s) := by
    have ha := h.averaged_gradient ((hc s (by omega)).trans he0)
    have ht : Matrix.toEuclideanCLM (n := d) (𝕜 := ℝ) (Hs s) =
        averagedDerivative A 0 (errorTrajectory family I N g e0 s) := by
      simp [Hs, hessianMatrix]
    rw [← ht] at ha
    exact (congrArg WithLp.ofLp ha).symm
  have herr (s : ℕ) (hs : s < N) :
      opNorm (Hs s-hessianMatrix (A 0)) ≤ rho*‖e0‖/2 :=
    (h.averaged_drift ((hc s (by omega)).trans he0)).trans
      (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hc s (by omega)) h.rho_nonneg) (by norm_num))
  have hb := family.finiteDrift_le I hN (hessianMatrix (A 0)) h.hermitian h.spectrum
    (fun s => Hs s-hessianMatrix (A 0)) (rho*‖e0‖/2)
    (by have := h.rho_nonneg; positivity) herr
  simp only [add_sub_cancel] at hb
  rw [show 1+2*(rho*‖e0‖/2)/I.delta = 1+rho*‖e0‖/I.delta by ring] at hb
  have hv := ((family.data N).method I).nonlinearError_eq_transfer_upto
    (gradientCoordinates g) (WithLp.ofLp e0) Hs N heq N le_rfl
  have he : errorTrajectory family I N g e0 N =
      Matrix.toEuclideanCLM (n := d) (𝕜 := ℝ)
        (((family.data N).realization I).operatorTransfer N Hs) e0 := by
    unfold errorTrajectory
    rw [hv]
    rfl
  rw [he]
  have hm := (Matrix.toEuclideanCLM (n := d) (𝕜 := ℝ)
    (((family.data N).realization I).operatorTransfer N Hs-
      aeval (hessianMatrix (A 0)) (I.residual N))).le_opNorm e0
  change ‖Matrix.toEuclideanCLM (n := d) (𝕜 := ℝ) _ e0-
    Matrix.toEuclideanCLM (n := d) (𝕜 := ℝ) _ e0‖ ≤ _
  rw [← sub_apply, ← map_sub]
  exact hm.trans (mul_le_mul_of_nonneg_right hb (norm_nonneg e0))

/-- A scalar exponential majorant with the correct first-order factor. -/
theorem chebyshev_sub_one_exp_le (N : ℕ) (u : ℝ) (hu : 0 ≤ u) :
    (T ℝ N).eval (1+u)-1 ≤ (N:ℝ)^2*u*Real.exp ((N:ℝ)^2*u) := by
  have hq : ((N:ℝ)*Real.sqrt (2*u))^2/2 = (N:ℝ)^2*u := by
    rw [mul_pow, Real.sq_sqrt (by positivity)]
    ring
  have ht := (chebyshev_cosh_upper N u hu).trans
    (Real.cosh_le_exp_half_sq ((N:ℝ)*Real.sqrt (2*u)))
  rw [hq] at ht
  have hh := mul_le_mul_of_nonneg_right (Real.add_one_le_exp (-((N:ℝ)^2*u)))
    (Real.exp_nonneg ((N:ℝ)^2*u))
  rw [← Real.exp_add, neg_add_cancel, Real.exp_zero] at hh
  nlinarith

/-- A quadratic error bound valid throughout the local ball. The finer
endpoint-weighted coefficient is defined separately below. -/
theorem lipschitzHessian_discrepancy_quadratic_le (family : MethodFamily) (I : SpectralInterval)
    {N : ℕ} (hN : 0 < N)
    (g : EuclideanSpace ℝ d → EuclideanSpace ℝ d)
    (A : EuclideanSpace ℝ d → EuclideanSpace ℝ d →L[ℝ] EuclideanSpace ℝ d)
    (e0 : EuclideanSpace ℝ d) (rho R : ℝ)
    (h : HessianControl I g A rho R) (he0 : ‖e0‖ ≤ R)
    (hsmall : rho*‖e0‖ ≤ 2*I.mu) :
    ‖errorTrajectory family I N g e0 N - quadraticTerminal I N (hessianMatrix (A 0)) e0‖ ≤
      (rho/I.delta)*I.epsilon N*(N:ℝ)^2*
        Real.exp ((N:ℝ)^2*rho*‖e0‖/I.delta)*‖e0‖^2 := by
  refine (lipschitzHessian_discrepancy_le family I hN g A e0 rho R h he0 hsmall).trans ?_
  have hu : 0 ≤ rho*‖e0‖/I.delta :=
    div_nonneg (mul_nonneg h.rho_nonneg (norm_nonneg e0)) I.delta_pos.le
  have hb := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (chebyshev_sub_one_exp_le N _ hu)
      (div_nonneg (by norm_num : (0:ℝ) ≤ 1) (I.den_pos N).le)) (norm_nonneg e0)
  change I.epsilon N * _ * ‖e0‖ ≤ _ at hb
  dsimp [SpectralInterval.epsilon] at hb ⊢
  convert hb using 1
  ring_nf

/-- Exact normalized linear-case radius of the `s`-th leading block. -/
def leadingRadius (J : JacobiData) (I : SpectralInterval) (s : ℕ) : ℝ :=
  (J.leading s).eval 1 / J.den I s

/-- The endpoint profile weighted by the exact unperturbed leading radii. -/
def secondOrderCoefficient (J : JacobiData) (I : SpectralInterval) (N : ℕ) : ℝ :=
  ∑ s ∈ Finset.range N, J.endpointProfile N s * leadingRadius J I s

theorem leadingRadius_nonneg (J : JacobiData) (I : SpectralInterval) {N s : ℕ}
    (ha : J.Admissible I N) (hm : J.EndpointMax N) (hs : s ≤ N) :
    0 ≤ leadingRadius J I s := by
  apply div_nonneg _ (ha s hs).le
  exact (abs_nonneg _).trans (hm 0 s (by omega) 1 (by norm_num))

theorem leadingRadius_le_one (J : JacobiData) (I : SpectralInterval) {N s : ℕ}
    (ha : J.Admissible I N) (hm : J.EndpointMax N) (hs : s ≤ N) :
    leadingRadius J I s ≤ 1 := by
  apply (div_le_one (ha s hs)).mpr
  exact J.leading_eval_mono I (fun k hk => ha k (hk.trans hs))
    (J.endpointMax_restrict hm hs) le_rfl I.eta_gt_one.le

theorem secondOrderCoefficient_nonneg (J : JacobiData) (I : SpectralInterval) {N : ℕ}
    (ha : J.Admissible I N) (hm : J.EndpointMax N) :
    0 ≤ secondOrderCoefficient J I N := by
  apply Finset.sum_nonneg
  intro s hs
  exact mul_nonneg (J.endpointProfile_nonneg hm s (Finset.mem_range.mp hs))
    (leadingRadius_nonneg J I ha hm (Finset.mem_range.mp hs).le)

theorem secondOrderCoefficient_le_sq (J : JacobiData) (I : SpectralInterval) {N : ℕ}
    (ha : J.Admissible I N) (hm : J.EndpointMax N)
    {c : ℝ} (hc : c ≠ 0) (ht : J.leading N = C c*T ℝ N) :
    secondOrderCoefficient J I N ≤ (N:ℝ)^2 := by
  rw [← J.endpointProfile_mass I ha hc ht]
  apply Finset.sum_le_sum
  intro s hs
  exact mul_le_of_le_one_right (J.endpointProfile_nonneg hm s (Finset.mem_range.mp hs))
    (leadingRadius_le_one J I ha hm (Finset.mem_range.mp hs).le)

end
end chebyshev1.Nonlinear
