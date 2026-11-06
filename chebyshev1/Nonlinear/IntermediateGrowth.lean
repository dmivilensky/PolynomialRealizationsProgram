import chebyshev1.Nonlinear.SecondOrder
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Extremal

/-! Growth relative to the unperturbed leading-block radius. -/
namespace chebyshev1.JacobiData
noncomputable section
open Polynomial Polynomial.Chebyshev
variable (J : JacobiData)

theorem block_natDegree_le (a n : ℕ) : (J.block a n).natDegree ≤ n := by
  induction n using Nat.twoStepInduction with
  | zero => simp [block]
  | one => simp [block]
  | more n ih0 ih1 =>
    rw [block]
    refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
    · exact (natDegree_mul_le.trans (add_le_add (natDegree_X_sub_C_le _) ih1)).trans
        (by omega)
    · exact (natDegree_mul_le.trans (add_le_add
        (show (C (J.aSq (a+n+1))).natDegree ≤ 0 by simp) ih0)).trans (by omega)

theorem leading_endpoint_exp_le {N s : ℕ} (hm : J.EndpointMax N) (hs : s ≤ N)
    (hp : 0 < (J.leading s).eval 1) (u : ℝ) (hu : 0 ≤ u) :
    (J.leading s).eval (1+u) ≤ (J.leading s).eval 1 * Real.exp ((s:ℝ)^2*u) := by
  let P := C ((J.leading s).eval 1)⁻¹ * J.leading s
  have hdeg : P.degree ≤ s := by
    apply degree_le_of_natDegree_le
    exact natDegree_mul_le.trans (by
      simpa only [natDegree_C, zero_add, JacobiData.leading] using (J.block_natDegree_le 0 s))
  have hnorm : ∀ x ∈ Set.Icc (-1) 1, |P.eval x| ≤ 1 := by
    intro x hx
    dsimp [P]
    rw [eval_mul, eval_C, abs_mul, abs_inv, abs_of_pos hp]
    calc
      _ ≤ ((J.leading s).eval 1)⁻¹ * (J.leading s).eval 1 :=
        mul_le_mul_of_nonneg_left (hm 0 s (by omega) x hx) (inv_nonneg.mpr hp.le)
      _ = 1 := inv_mul_cancel₀ hp.ne'
  have ht := eval_iterate_derivative_le_of_forall_abs_le_one (k := 0)
    (by linarith : (1:ℝ) ≤ 1+u) hdeg hnorm
  simp only [Function.iterate_zero, id_eq, P, eval_mul, eval_C] at ht
  have hq : ((s:ℝ)*Real.sqrt (2*u))^2/2 = (s:ℝ)^2*u := by
    rw [mul_pow, Real.sq_sqrt (by positivity)]
    ring
  have he := (chebyshev1.chebyshev_cosh_upper s u hu).trans
    (Real.cosh_le_exp_half_sq ((s:ℝ)*Real.sqrt (2*u)))
  rw [hq] at he
  have hh := mul_le_mul_of_nonneg_left (ht.trans he) hp.le
  simpa only [← mul_assoc, mul_inv_cancel₀ hp.ne', one_mul] using hh

end
end chebyshev1.JacobiData

namespace chebyshev1.Nonlinear
noncomputable section
open Polynomial Polynomial.Chebyshev
open scoped Matrix.Norms.L2Operator

theorem MethodFamily.terminal (family : MethodFamily) {N : ℕ} (hN : 0 < N) :
    (family.data N).leading N = C (2/(2:ℝ)^N)*T ℝ N := by
  cases family with
  | «prefix» => exact Prefix.jacobi_terminal hN
  | sine => exact SineJacobi.terminal N hN

theorem MethodFamily.leading_eval_one_pos (family : MethodFamily) {N s : ℕ}
    (hN : 0 < N) (hs : s ≤ N) : 0 < ((family.data N).leading s).eval 1 := by
  cases family with
  | «prefix» =>
    cases s with
    | zero => norm_num [MethodFamily.data]
    | succ s =>
      change 0 < (Prefix.jacobiData.leading (s+1)).eval 1
      rw [Prefix.jacobi_leading]
      simp only [eval_mul, eval_C, T_eval_one, mul_one]
      positivity
  | sine =>
    rcases lt_or_eq_of_le hs with hs | hs
    · exact SineJacobi.leading_eval_one_pos N s hs
    · subst s
      rw [show (MethodFamily.sine.data N).leading N = C (2/(2:ℝ)^N)*T ℝ N from
        SineJacobi.terminal N hN]
      simp only [eval_mul, eval_C, T_eval_one, mul_one]
      positivity

theorem MethodFamily.intermediate_transfer_exp_le (family : MethodFamily)
    (I : SpectralInterval) {N n : ℕ} (hN : 0 < N) (hn : n ≤ N)
    {d : Type*} [Fintype d] [DecidableEq d]
    (H : Matrix d d ℝ) (hH : H.IsHermitian)
    (hspec : spectrum ℝ H ⊆ Set.Icc I.mu I.L)
    (Hs : ℕ → Matrix d d ℝ) (delta : ℝ) (hd : 0 ≤ delta)
    (hE : ∀ s < n, opNorm (Hs s-H) ≤ delta) :
    opNorm (((family.data N).realization I).operatorTransfer n Hs) ≤
      leadingRadius (family.data N) I n * Real.exp ((N:ℝ)^2*(2*delta/I.delta)) := by
  let J := family.data N
  have ha : J.Admissible I n := fun k hk => family.admissible I hN k (hk.trans hn)
  have hm := family.endpointMax hN
  have hu : 0 ≤ 2*delta/I.delta := div_nonneg (by positivity) I.delta_pos.le
  have hg := J.leading_endpoint_exp_le hm hn (family.leading_eval_one_pos hN hn) _ hu
  have hb := J.opNorm_transfer_le_leading I ha (J.endpointMax_restrict hm hn)
    H hH hspec Hs delta hd hE
  have hexp : Real.exp ((n:ℝ)^2*(2*delta/I.delta)) ≤
      Real.exp ((N:ℝ)^2*(2*delta/I.delta)) := by
    apply Real.exp_le_exp.mpr
    apply mul_le_mul_of_nonneg_right _ hu
    exact sq_le_sq₀ (Nat.cast_nonneg _) (Nat.cast_nonneg _) |>.mpr (by exact_mod_cast hn)
  calc
    _ ≤ _ := hb
    _ ≤ ((J.leading n).eval 1 * Real.exp ((n:ℝ)^2*(2*delta/I.delta)))/J.den I n :=
      div_le_div_of_nonneg_right hg (ha n le_rfl).le
    _ ≤ leadingRadius J I n * Real.exp ((N:ℝ)^2*(2*delta/I.delta)) := by
      rw [mul_div_right_comm]
      exact mul_le_mul_of_nonneg_left hexp
        (leadingRadius_nonneg J I (family.admissible I hN) hm hn)

theorem lipschitzHessian_intermediate_growth_le (family : MethodFamily) (I : SpectralInterval)
    {N n : ℕ} (hN : 0 < N) (hn : n ≤ N)
    {d : Type*} [Fintype d] [DecidableEq d]
    (g : EuclideanSpace ℝ d → EuclideanSpace ℝ d)
    (A : EuclideanSpace ℝ d → EuclideanSpace ℝ d →L[ℝ] EuclideanSpace ℝ d)
    (e0 : EuclideanSpace ℝ d) (rho R : ℝ)
    (h : HessianControl I g A rho R) (he0 : ‖e0‖ ≤ R)
    (hsmall : rho*‖e0‖ ≤ 2*I.mu) :
    ‖errorTrajectory family I N g e0 n‖ ≤ leadingRadius (family.data N) I n *
      Real.exp ((N:ℝ)^2*rho*‖e0‖/I.delta)*‖e0‖ := by
  have hr := h.restrict (norm_nonneg e0) he0
  have hc := lipschitzHessian_confinement family I hN g A e0 rho ‖e0‖ hr le_rfl hsmall
  let Hs : ℕ → Matrix d d ℝ := fun s =>
    hessianMatrix (averagedDerivative A 0 (errorTrajectory family I N g e0 s))
  have heq (s : ℕ) (hs : s < n) :
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
  have herr (s : ℕ) (hs : s < n) :
      opNorm (Hs s-hessianMatrix (A 0)) ≤ rho*‖e0‖/2 :=
    (h.averaged_drift ((hc s (by omega)).trans he0)).trans
      (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hc s (by omega)) h.rho_nonneg) (by norm_num))
  have hb := family.intermediate_transfer_exp_le I hN hn
    (hessianMatrix (A 0)) h.hermitian h.spectrum Hs (rho*‖e0‖/2)
    (by have := h.rho_nonneg; positivity) herr
  have hv := ((family.data N).method I).nonlinearError_eq_transfer_upto
    (gradientCoordinates g) (WithLp.ofLp e0) Hs n heq n le_rfl
  change ‖WithLp.toLp 2 _‖ ≤ _
  rw [hv]
  have hm := (Matrix.toEuclideanCLM (n := d) (𝕜 := ℝ)
    (((family.data N).realization I).operatorTransfer n Hs)).le_opNorm e0
  refine hm.trans ?_
  change opNorm (((family.data N).realization I).operatorTransfer n Hs)*‖e0‖ ≤ _
  convert mul_le_mul_of_nonneg_right hb (norm_nonneg e0) using 1
  rw [show (N:ℝ)^2*(2*(rho*‖e0‖/2)/I.delta) = (N:ℝ)^2*rho*‖e0‖/I.delta by ring]

end
end chebyshev1.Nonlinear
