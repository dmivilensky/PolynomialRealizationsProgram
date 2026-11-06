import chebyshev1.Nonlinear.LocalConvergence

/-! Restarted local convergence with an explicit integer block length. -/
namespace chebyshev1.Nonlinear
noncomputable section
open scoped Matrix.Norms.L2Operator
variable {d : Type*} [Fintype d] [DecidableEq d]

/-- A block length sufficient to halve the initial error in the smaller local ball. -/
def restartHorizon (I : SpectralInterval) : ℕ :=
  ⌈Real.sqrt I.kappa * Real.log 4⌉₊

theorem restartHorizon_pos (I : SpectralInterval) : 0 < restartHorizon I := by
  apply Nat.ceil_pos.mpr
  exact mul_pos (Real.sqrt_pos.mpr (div_pos (I.mu_pos.trans I.mu_lt_L) I.mu_pos))
    (Real.log_pos (by norm_num))

theorem restartHorizon_ge (I : SpectralInterval) :
    Real.sqrt I.kappa * Real.log 4 ≤ (restartHorizon I : ℝ) := Nat.le_ceil _

/-- One block halves the error under the initial-radius smallness hypothesis. -/
theorem lipschitzHessian_halving (family : MethodFamily) (I : SpectralInterval)
    {N : ℕ} (hN : 0 < N)
    (horizon : Real.sqrt I.kappa * Real.log 4 ≤ (N:ℝ))
    (g : EuclideanSpace ℝ d → EuclideanSpace ℝ d)
    (A : EuclideanSpace ℝ d → EuclideanSpace ℝ d →L[ℝ] EuclideanSpace ℝ d)
    (e0 : EuclideanSpace ℝ d) (rho R : ℝ)
    (h : HessianControl I g A rho R) (he0 : ‖e0‖ ≤ R)
    (hsmall : rho*‖e0‖ ≤ I.mu/2) :
    ‖errorTrajectory family I N g e0 N‖ ≤ ‖e0‖/2 := by
  have hr := h.restrict (norm_nonneg e0) he0
  have hb := lipschitzHessian_local_accelerated_le family I hN g A e0 rho ‖e0‖ hr
    le_rfl (by linarith [I.mu_pos])
  have hsqrt : Real.sqrt (rho*‖e0‖/(2*I.mu)) ≤ 1/2 := by
    apply (Real.sqrt_le_iff).mpr
    constructor
    · norm_num
    · apply (div_le_iff₀ (mul_pos (by norm_num : (0:ℝ) < 2) I.mu_pos)).mpr
      nlinarith
  have hk : 0 < Real.sqrt I.kappa :=
    Real.sqrt_pos.mpr (div_pos (I.mu_pos.trans I.mu_lt_L) I.mu_pos)
  have hN' : 0 ≤ (N:ℝ) := Nat.cast_nonneg _
  have hexp : -2*(N:ℝ)/Real.sqrt I.kappa *
      (1-Real.sqrt (rho*‖e0‖/(2*I.mu))) ≤ -Real.log 4 := by
    have hh : Real.log 4 ≤ (N:ℝ)/Real.sqrt I.kappa :=
      (le_div_iff₀ hk).mpr (by simpa only [mul_comm] using horizon)
    have hh' : 0 ≤ (N:ℝ)/Real.sqrt I.kappa := div_nonneg hN' hk.le
    rw [show -2*(N:ℝ)/Real.sqrt I.kappa = -2*((N:ℝ)/Real.sqrt I.kappa) by ring]
    nlinarith
  have hc : 2*Real.exp (-Real.log 4) = (1/2:ℝ) := by
    rw [Real.exp_neg, Real.exp_log (by norm_num : (0:ℝ) < 4)]
    norm_num
  calc
    _ ≤ _ := hb
    _ ≤ 2*Real.exp (-Real.log 4)*‖e0‖ := by
      gcongr
    _ = _ := by rw [hc]; ring

/-- Errors at successive restart boundaries, using the same finite-horizon method. -/
def restartedError (family : MethodFamily) (I : SpectralInterval) (N : ℕ)
    (g : EuclideanSpace ℝ d → EuclideanSpace ℝ d) (e0 : EuclideanSpace ℝ d) :
    ℕ → EuclideanSpace ℝ d
  | 0 => e0
  | k+1 => errorTrajectory family I N g (restartedError family I N g e0 k) N

/-- Every restarted block is valid in the original ball and gains a factor two. -/
theorem restartedError_le (family : MethodFamily) (I : SpectralInterval)
    {N : ℕ} (hN : 0 < N)
    (horizon : Real.sqrt I.kappa * Real.log 4 ≤ (N:ℝ))
    (g : EuclideanSpace ℝ d → EuclideanSpace ℝ d)
    (A : EuclideanSpace ℝ d → EuclideanSpace ℝ d →L[ℝ] EuclideanSpace ℝ d)
    (e0 : EuclideanSpace ℝ d) (rho R : ℝ)
    (h : HessianControl I g A rho R) (he0 : ‖e0‖ ≤ R)
    (hsmall : rho*‖e0‖ ≤ I.mu/2) (k : ℕ) :
    ‖restartedError family I N g e0 k‖ ≤ (1/2:ℝ)^k*‖e0‖ := by
  induction k with
  | zero => simp [restartedError]
  | succ k ih =>
    have hk : (1/2:ℝ)^k ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    have hi : ‖restartedError family I N g e0 k‖ ≤ ‖e0‖ :=
      ih.trans (mul_le_of_le_one_left (norm_nonneg e0) hk)
    have hb := lipschitzHessian_halving family I hN horizon g A
      (restartedError family I N g e0 k) rho R h (hi.trans he0)
      ((mul_le_mul_of_nonneg_left hi h.rho_nonneg).trans hsmall)
    change ‖errorTrajectory family I N g (restartedError family I N g e0 k) N‖ ≤ _
    refine hb.trans ?_
    calc
      _ ≤ ((1/2:ℝ)^k*‖e0‖)/2 := div_le_div_of_nonneg_right ih (by norm_num)
      _ = _ := by rw [pow_succ]; ring

/-- With the explicit rounded block length, `k` blocks use `k * restartHorizon I`
gradient queries and reduce the error by at least `2^k`. -/
theorem restartedError_horizon_le (family : MethodFamily) (I : SpectralInterval)
    (g : EuclideanSpace ℝ d → EuclideanSpace ℝ d)
    (A : EuclideanSpace ℝ d → EuclideanSpace ℝ d →L[ℝ] EuclideanSpace ℝ d)
    (e0 : EuclideanSpace ℝ d) (rho R : ℝ)
    (h : HessianControl I g A rho R) (he0 : ‖e0‖ ≤ R)
    (hsmall : rho*‖e0‖ ≤ I.mu/2) (k : ℕ) :
    ‖restartedError family I (restartHorizon I) g e0 k‖ ≤ (1/2:ℝ)^k*‖e0‖ :=
  restartedError_le family I (restartHorizon_pos I) (restartHorizon_ge I)
    g A e0 rho R h he0 hsmall k

/-- Number of blocks sufficient for a positive target, including the case in
which the initial error already meets the target. -/
def restartCount (r epsilon : ℝ) : ℕ := ⌈Real.log (r/epsilon) / Real.log 2⌉₊

theorem geometric_restartCount_le {r epsilon : ℝ} (hr : 0 ≤ r) (he : 0 < epsilon) :
    (1/2:ℝ)^(restartCount r epsilon)*r ≤ epsilon := by
  rcases eq_or_lt_of_le hr with hr | hr
  · subst r
    simpa using he.le
  have hlog := (div_le_iff₀ (Real.log_pos (by norm_num : (1:ℝ) < 2))).mp
    (Nat.le_ceil (Real.log (r/epsilon)/Real.log 2))
  change Real.log (r/epsilon) ≤ (restartCount r epsilon:ℝ)*Real.log 2 at hlog
  have heq : (1/2:ℝ)^(restartCount r epsilon) =
      Real.exp (-((restartCount r epsilon:ℝ)*Real.log 2)) := by
    rw [Real.exp_neg, Real.exp_nat_mul, Real.exp_log (by norm_num : (0:ℝ) < 2)]
    simp only [one_div, inv_pow]
  rw [heq, Real.exp_neg]
  have hh := Real.exp_le_exp.mpr (neg_le_neg hlog)
  simp_rw [Real.exp_neg] at hh
  rw [Real.exp_log (div_pos hr he)] at hh
  calc
    _ ≤ (r/epsilon)⁻¹*r := mul_le_mul_of_nonneg_right hh hr.le
    _ = epsilon := by field_simp

/-- Explicit target accuracy after the rounded number of rounded-length blocks. -/
theorem restartedError_target_le (family : MethodFamily) (I : SpectralInterval)
    (g : EuclideanSpace ℝ d → EuclideanSpace ℝ d)
    (A : EuclideanSpace ℝ d → EuclideanSpace ℝ d →L[ℝ] EuclideanSpace ℝ d)
    (e0 : EuclideanSpace ℝ d) (rho R : ℝ)
    (h : HessianControl I g A rho R) (he0 : ‖e0‖ ≤ R)
    (hsmall : rho*‖e0‖ ≤ I.mu/2) {epsilon : ℝ} (he : 0 < epsilon) :
    ‖restartedError family I (restartHorizon I) g e0
      (restartCount ‖e0‖ epsilon)‖ ≤ epsilon :=
  (restartedError_horizon_le family I g A e0 rho R h he0 hsmall _).trans
    (geometric_restartCount_le (norm_nonneg e0) he)

end
end chebyshev1.Nonlinear
