import chebyshev1.Nonlinear.IntermediateTransfer
import chebyshev1.Nonlinear.LipschitzHessian

/-! Local Hessian hypotheses on a ball imply confinement; no trajectory bound is
assumed. Existing segmentwise estimates remain available unchanged. -/
namespace chebyshev1.Nonlinear
noncomputable section
open Set Polynomial Polynomial.Chebyshev
open scoped Matrix.Norms.L2Operator
variable {d : Type*} [Fintype d] [DecidableEq d]

/-- Analytic hypotheses on the prescribed ball around a stationary point. -/
structure HessianControl (I : SpectralInterval)
    (g : EuclideanSpace ℝ d → EuclideanSpace ℝ d)
    (A : EuclideanSpace ℝ d → EuclideanSpace ℝ d →L[ℝ] EuclideanSpace ℝ d)
    (rho R : ℝ) : Prop where
  rho_nonneg : 0 ≤ rho
  radius_nonneg : 0 ≤ R
  stationary : g 0 = 0
  hermitian : (hessianMatrix (A 0)).IsHermitian
  spectrum : spectrum ℝ (hessianMatrix (A 0)) ⊆ Icc I.mu I.L
  continuous : ContinuousOn A (Metric.closedBall 0 R)
  derivative : ∀ e, ‖e‖ ≤ R → HasFDerivAt g (A e) e
  lipschitz : ∀ e, ‖e‖ ≤ R → ‖A e-A 0‖ ≤ rho*‖e‖

namespace HessianControl
variable {I : SpectralInterval}
variable {g : EuclideanSpace ℝ d → EuclideanSpace ℝ d}
variable {A : EuclideanSpace ℝ d → EuclideanSpace ℝ d →L[ℝ] EuclideanSpace ℝ d}
variable {rho R : ℝ} (h : HessianControl I g A rho R)

omit [DecidableEq d] in
theorem segment_norm_le {e : EuclideanSpace ℝ d} (he : ‖e‖ ≤ R)
    {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) : ‖t • e‖ ≤ R := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
  exact (mul_le_of_le_one_left (norm_nonneg e) ht.2).trans he

include h

theorem segment_continuous {e : EuclideanSpace ℝ d} (he : ‖e‖ ≤ R) :
    ContinuousOn (fun t : ℝ => A (t • e)) (Icc 0 1) := by
  apply h.continuous.comp (continuous_id.smul continuous_const).continuousOn
  intro t ht
  rw [Metric.mem_closedBall, dist_zero_right]
  change ‖t • e‖ ≤ R
  exact segment_norm_le he ht

theorem averaged_gradient {e : EuclideanSpace ℝ d} (he : ‖e‖ ≤ R) :
    averagedDerivative A 0 e e = g e := by
  have hh := averagedDerivative_apply g A 0 e
    (by simpa using h.segment_continuous he)
    (by intro t ht; simpa using h.derivative _ (segment_norm_le he ht))
  simpa only [zero_add, h.stationary, sub_zero] using hh

theorem averaged_drift {e : EuclideanSpace ℝ d} (he : ‖e‖ ≤ R) :
    opNorm (hessianMatrix (averagedDerivative A 0 e)-hessianMatrix (A 0)) ≤
      rho*‖e‖/2 := by
  have hn : opNorm (hessianMatrix (averagedDerivative A 0 e)-hessianMatrix (A 0)) =
      ‖averagedDerivative A 0 e-A 0‖ := by
    change opNorm ((Matrix.toEuclideanCLM (n := d) (𝕜 := ℝ)).symm _ -
      (Matrix.toEuclideanCLM (n := d) (𝕜 := ℝ)).symm _) = _
    rw [← map_sub]
    exact opNorm_hessianMatrix _
  rw [hn]
  apply averagedDerivative_sub_norm_le A 0 e rho
    (by simpa using h.segment_continuous he)
  intro t ht
  simpa using h.lipschitz _ (segment_norm_le he ht)

end HessianControl

theorem HessianControl.restrict {I : SpectralInterval}
    {g : EuclideanSpace ℝ d → EuclideanSpace ℝ d}
    {A : EuclideanSpace ℝ d → EuclideanSpace ℝ d →L[ℝ] EuclideanSpace ℝ d}
    {rho R r : ℝ} (h : HessianControl I g A rho R) (hr : 0 ≤ r) (hrR : r ≤ R) :
    HessianControl I g A rho r where
  rho_nonneg := h.rho_nonneg
  radius_nonneg := hr
  stationary := h.stationary
  hermitian := h.hermitian
  spectrum := h.spectrum
  continuous := h.continuous.mono (Metric.closedBall_subset_closedBall hrR)
  derivative := fun e he => h.derivative e (he.trans hrR)
  lipschitz := fun e he => h.lipschitz e (he.trans hrR)

/-- Every error of the fixed full-horizon recurrence stays inside the initial
radius. In particular, all Hessian queries stay in the prescribed ball. -/
theorem lipschitzHessian_confinement (family : MethodFamily) (I : SpectralInterval)
    {N : ℕ} (hN : 0 < N)
    (g : EuclideanSpace ℝ d → EuclideanSpace ℝ d)
    (A : EuclideanSpace ℝ d → EuclideanSpace ℝ d →L[ℝ] EuclideanSpace ℝ d)
    (e0 : EuclideanSpace ℝ d) (rho R : ℝ)
    (h : HessianControl I g A rho R) (he0 : ‖e0‖ ≤ R)
    (hsmall : rho*R ≤ 2*I.mu) :
    ∀ n ≤ N, ‖errorTrajectory family I N g e0 n‖ ≤ ‖e0‖ := by
  let Hs : ℕ → Matrix d d ℝ := fun s =>
    hessianMatrix (averagedDerivative A 0 (errorTrajectory family I N g e0 s))
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    have hprev (s : ℕ) (hs : s < n) : ‖errorTrajectory family I N g e0 s‖ ≤ ‖e0‖ :=
      ih s hs (by omega)
    have heq (s : ℕ) (hs : s < n) :
        gradientCoordinates g (((family.data N).method I).nonlinearError
          (gradientCoordinates g) (WithLp.ofLp e0) s) =
        (Hs s).mulVec (((family.data N).method I).nonlinearError
          (gradientCoordinates g) (WithLp.ofLp e0) s) := by
      have ha := h.averaged_gradient ((hprev s hs).trans he0)
      have ht : Matrix.toEuclideanCLM (n := d) (𝕜 := ℝ) (Hs s) =
          averagedDerivative A 0 (errorTrajectory family I N g e0 s) := by
        simp [Hs, hessianMatrix]
      rw [← ht] at ha
      exact (congrArg WithLp.ofLp ha).symm
    have herr (s : ℕ) (hs : s < n) :
        opNorm (Hs s-hessianMatrix (A 0)) ≤ rho*R/2 :=
      (h.averaged_drift ((hprev s hs).trans he0)).trans
        (div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left ((hprev s hs).trans he0) h.rho_nonneg) (by norm_num))
    have hb := family.intermediate_transfer_le_one I hN hn
      (hessianMatrix (A 0)) h.hermitian h.spectrum Hs (rho*R/2)
      (by have := h.rho_nonneg; have := h.radius_nonneg; positivity)
      (by linarith) herr
    have hv := ((family.data N).method I).nonlinearError_eq_transfer_upto
      (gradientCoordinates g) (WithLp.ofLp e0) Hs n heq n le_rfl
    change ‖WithLp.toLp 2 _‖ ≤ _
    rw [hv]
    have hm := (Matrix.toEuclideanCLM (n := d) (𝕜 := ℝ)
      (((family.data N).realization I).operatorTransfer n Hs)).le_opNorm e0
    exact hm.trans (by
      change opNorm (((family.data N).realization I).operatorTransfer n Hs)*‖e0‖ ≤ ‖e0‖
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hb (norm_nonneg e0))

/-- The local terminal estimate with confinement proved from ball hypotheses. -/
theorem lipschitzHessian_local_error_le (family : MethodFamily) (I : SpectralInterval)
    {N : ℕ} (hN : 0 < N)
    (g : EuclideanSpace ℝ d → EuclideanSpace ℝ d)
    (A : EuclideanSpace ℝ d → EuclideanSpace ℝ d →L[ℝ] EuclideanSpace ℝ d)
    (e0 : EuclideanSpace ℝ d) (rho R : ℝ)
    (h : HessianControl I g A rho R) (he0 : ‖e0‖ ≤ R)
    (hsmall : rho*R ≤ 2*I.mu) :
    ‖errorTrajectory family I N g e0 N‖ ≤
      I.epsilon N * (T ℝ N).eval (1+rho*‖e0‖/I.delta) * ‖e0‖ := by
  have hb := lipschitzHessian_confinement family I hN g A e0 rho R h he0 hsmall
  apply lipschitzHessian_error_le family I hN g A e0 rho ‖e0‖ h.rho_nonneg
    (norm_nonneg _) h.stationary h.hermitian h.spectrum
  · intro s hs
    exact h.segment_continuous ((hb s (by omega)).trans he0)
  · intro s hs t ht
    exact h.derivative _ (HessianControl.segment_norm_le ((hb s (by omega)).trans he0) ht)
  · intro s hs t ht
    exact h.lipschitz _ (HessianControl.segment_norm_le ((hb s (by omega)).trans he0) ht)
  · intro s hs
    exact hb s (by omega)

theorem lipschitzHessian_local_exp_le (family : MethodFamily) (I : SpectralInterval)
    {N : ℕ} (hN : 0 < N)
    (g : EuclideanSpace ℝ d → EuclideanSpace ℝ d)
    (A : EuclideanSpace ℝ d → EuclideanSpace ℝ d →L[ℝ] EuclideanSpace ℝ d)
    (e0 : EuclideanSpace ℝ d) (rho R : ℝ)
    (h : HessianControl I g A rho R) (he0 : ‖e0‖ ≤ R)
    (hsmall : rho*R ≤ 2*I.mu) :
    ‖errorTrajectory family I N g e0 N‖ ≤
      2*Real.exp (-2*(N:ℝ)*(Real.sqrt I.mu-Real.sqrt (rho*‖e0‖/2))/Real.sqrt I.L)*‖e0‖ := by
  refine (lipschitzHessian_local_error_le family I hN g A e0 rho R h he0 hsmall).trans ?_
  have hb := I.amplification_exp_le N (rho*‖e0‖/2)
    (by have := h.rho_nonneg; positivity)
    (by have := mul_le_mul_of_nonneg_left he0 h.rho_nonneg; linarith)
  have hb' := mul_le_mul_of_nonneg_right hb (norm_nonneg e0)
  rw [show 1+2*(rho*‖e0‖/2)/I.delta = 1+rho*‖e0‖/I.delta by ring] at hb'
  exact hb'

theorem lipschitzHessian_local_accelerated_le (family : MethodFamily) (I : SpectralInterval)
    {N : ℕ} (hN : 0 < N)
    (g : EuclideanSpace ℝ d → EuclideanSpace ℝ d)
    (A : EuclideanSpace ℝ d → EuclideanSpace ℝ d →L[ℝ] EuclideanSpace ℝ d)
    (e0 : EuclideanSpace ℝ d) (rho R : ℝ)
    (h : HessianControl I g A rho R) (he0 : ‖e0‖ ≤ R)
    (hsmall : rho*R ≤ 2*I.mu) :
    ‖errorTrajectory family I N g e0 N‖ ≤
      2*Real.exp (-2*(N:ℝ)/Real.sqrt I.kappa *
        (1-Real.sqrt (rho*‖e0‖/(2*I.mu))))*‖e0‖ := by
  have hb := lipschitzHessian_local_exp_le family I hN g A e0 rho R h he0 hsmall
  rw [I.drift_exponent_eq N (rho*‖e0‖/2) (by have := h.rho_nonneg; positivity)] at hb
  simpa only [div_div] using hb

end
end chebyshev1.Nonlinear
