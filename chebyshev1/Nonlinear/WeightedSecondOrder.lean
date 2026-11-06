import chebyshev1.Nonlinear.IntermediateGrowth
import chebyshev1.Perturbations.Duhamel

/-! Duhamel estimates with the leading-block weights retained. -/
namespace chebyshev1.JacobiData
noncomputable section
open Polynomial Polynomial.Chebyshev
open scoped BigOperators Matrix.Norms.L2Operator
variable (J : JacobiData) (I : SpectralInterval)
variable {d : Type*} [Fintype d] [DecidableEq d]

theorem forcingTail_euclidean (H : Matrix d d ℝ) {N s : ℕ}
    (ha : J.Admissible I N) (hs : s < N) (v : EuclideanSpace ℝ d) :
    WithLp.toLp 2 ((J.method I).forcingTail H N s
      (-((J.method I).gamma s • WithLp.ofLp v))) =
      (-(2/I.delta)*J.den I s/J.den I N) •
        Matrix.toEuclideanCLM (n := d) (𝕜 := ℝ)
          (aeval H (J.spectralBlock I (s+1) (N-(s+1)))) v := by
  rw [TwoTerm.forcingTail_eq_memoryProduct, J.operator_tail I ha (s+1) (by omega) (by omega)]
  simp only [Matrix.smul_mulVec, Matrix.mulVec_smul,
    WithLp.toLp_smul, ← neg_smul, smul_smul]
  congr 1
  dsimp [method]
  field_simp [ne_of_gt (ha (s+1) (by omega))]

theorem forcingTail_norm_le (H : Matrix d d ℝ) (hH : H.IsHermitian)
    (hspec : spectrum ℝ H ⊆ Set.Icc I.mu I.L) {N s : ℕ}
    (ha : J.Admissible I N) (hm : J.EndpointMax N) (hs : s < N)
    (v : EuclideanSpace ℝ d) :
    ‖WithLp.toLp 2 ((J.method I).forcingTail H N s
      (-((J.method I).gamma s • WithLp.ofLp v)))‖ ≤
      ((2/I.delta)*J.den I s/J.den I N)*
        (J.block (s+1) (N-(s+1))).eval 1*‖v‖ := by
  rw [J.forcingTail_euclidean I H ha hs, norm_smul, Real.norm_eq_abs]
  have hc : 0 ≤ (2/I.delta)*J.den I s/J.den I N :=
    div_nonneg (mul_nonneg (div_nonneg (by norm_num) I.delta_pos.le) (ha s (by omega)).le)
      (ha N le_rfl).le
  rw [show -(2/I.delta)*J.den I s/J.den I N = -((2/I.delta)*J.den I s/J.den I N) by ring,
    abs_neg, abs_of_nonneg hc]
  have hp : 0 ≤ (J.block (s+1) (N-(s+1))).eval 1 :=
    (abs_nonneg _).trans (hm (s+1) (N-(s+1)) (by omega) 1 (by norm_num))
  have hb : opNorm (aeval H (J.spectralBlock I (s+1) (N-(s+1)))) ≤
      (J.block (s+1) (N-(s+1))).eval 1 :=
    opNorm_aeval_le _ I H hH hspec _ hp (fun x hx => by
      rw [J.spectralBlock_eval I]
      exact hm (s+1) (N-(s+1)) (by omega) _ (I.z_mem hx))
  have hv := (Matrix.toEuclideanCLM (n := d) (𝕜 := ℝ)
    (aeval H (J.spectralBlock I (s+1) (N-(s+1))))).le_opNorm v
  apply (mul_le_mul_of_nonneg_left (hv.trans
    (mul_le_mul_of_nonneg_right hb (norm_nonneg v))) hc).trans_eq
  ring

end
end chebyshev1.JacobiData

namespace chebyshev1.Nonlinear
noncomputable section
open Polynomial Polynomial.Chebyshev
open scoped BigOperators Matrix.Norms.L2Operator
variable {d : Type*} [Fintype d] [DecidableEq d]

theorem HessianControl.gradient_defect_le {I : SpectralInterval}
    {g : EuclideanSpace ℝ d → EuclideanSpace ℝ d}
    {A : EuclideanSpace ℝ d → EuclideanSpace ℝ d →L[ℝ] EuclideanSpace ℝ d}
    {rho R : ℝ} (h : HessianControl I g A rho R)
    {e : EuclideanSpace ℝ d} (he : ‖e‖ ≤ R) :
    ‖g e-A 0 e‖ ≤ rho/2*‖e‖^2 := by
  have hh := averagedDerivative_sub_norm_le A 0 e rho
    (by simpa using h.segment_continuous he)
    (by intro t ht; simpa using h.lipschitz _ (HessianControl.segment_norm_le he ht))
  rw [← h.averaged_gradient he, ← sub_apply]
  exact ((averagedDerivative A 0 e-A 0).le_opNorm e).trans
    ((mul_le_mul_of_nonneg_right hh (norm_nonneg e)).trans_eq (by ring))

theorem nonlinear_error_duhamel (family : MethodFamily) (I : SpectralInterval)
    {N : ℕ} (hN : 0 < N)
    (g : EuclideanSpace ℝ d → EuclideanSpace ℝ d)
    (A0 : EuclideanSpace ℝ d →L[ℝ] EuclideanSpace ℝ d)
    (e0 : EuclideanSpace ℝ d) :
    errorTrajectory family I N g e0 N - quadraticTerminal I N (hessianMatrix A0) e0 =
      ∑ s ∈ Finset.range N, WithLp.toLp 2
        (((family.data N).method I).forcingTail (hessianMatrix A0) N s
          (-(((family.data N).method I).gamma s •
            WithLp.ofLp (g (errorTrajectory family I N g e0 s) -
              A0 (errorTrajectory family I N g e0 s))))) := by
  let J := family.data N
  have hh := (J.method I).nonlinearError_eq_quadratic_add_forcing (gradientCoordinates g)
    (hessianMatrix A0) (WithLp.ofLp e0) N
  rw [J.quadraticError_exact I (family.admissible I hN) N le_rfl,
    J.terminal_residual I (by positivity : (2/(2:ℝ)^N) ≠ 0) (family.terminal hN)] at hh
  have hv : ∀ s, gradientCoordinates g ((J.method I).nonlinearError
      (gradientCoordinates g) (WithLp.ofLp e0) s) -
      (hessianMatrix A0).mulVec ((J.method I).nonlinearError
        (gradientCoordinates g) (WithLp.ofLp e0) s) =
      WithLp.ofLp (g (errorTrajectory family I N g e0 s) -
        A0 (errorTrajectory family I N g e0 s)) := by
    intro s
    have hm : Matrix.toEuclideanCLM (n := d) (𝕜 := ℝ) (hessianMatrix A0) = A0 := by
      simp [hessianMatrix]
    conv_rhs => rw [← hm]
    rfl
  simp_rw [hv] at hh
  have hh' := congrArg (WithLp.toLp 2) hh
  simp only [WithLp.toLp_add, WithLp.toLp_sum] at hh'
  change errorTrajectory family I N g e0 N =
    quadraticTerminal I N (hessianMatrix A0) e0 + _ at hh'
  rw [hh']
  abel

/-- The second-order nonlinear bound retains the exact endpoint-weighted
coefficient, uniformly on the local ball. -/
theorem lipschitzHessian_weighted_discrepancy_le (family : MethodFamily) (I : SpectralInterval)
    {N : ℕ} (hN : 0 < N)
    (g : EuclideanSpace ℝ d → EuclideanSpace ℝ d)
    (A : EuclideanSpace ℝ d → EuclideanSpace ℝ d →L[ℝ] EuclideanSpace ℝ d)
    (e0 : EuclideanSpace ℝ d) (rho R : ℝ)
    (h : HessianControl I g A rho R) (he0 : ‖e0‖ ≤ R)
    (hsmall : rho*‖e0‖ ≤ 2*I.mu) :
    ‖errorTrajectory family I N g e0 N - quadraticTerminal I N (hessianMatrix (A 0)) e0‖ ≤
      (rho/I.delta)*I.epsilon N*secondOrderCoefficient (family.data N) I N*
        Real.exp (2*(N:ℝ)^2*rho*‖e0‖/I.delta)*‖e0‖^2 := by
  let J := family.data N
  let Q := Real.exp ((N:ℝ)^2*rho*‖e0‖/I.delta)
  have ha := family.admissible I hN
  have hm := family.endpointMax hN
  have hc := lipschitzHessian_confinement family I hN g A e0 rho ‖e0‖
    (h.restrict (norm_nonneg e0) he0) le_rfl hsmall
  have heps : (J.leading N).eval 1 / J.den I N = I.epsilon N :=
    J.endpoint_ratio I (by positivity : (2/(2:ℝ)^N) ≠ 0) (family.terminal hN)
  have hQ : Q^2 = Real.exp (2*(N:ℝ)^2*rho*‖e0‖/I.delta) := by
    dsimp [Q]
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [nonlinear_error_duhamel family I hN g (A 0) e0]
  calc
    _ ≤ ∑ s ∈ Finset.range N, ‖WithLp.toLp 2
        ((J.method I).forcingTail (hessianMatrix (A 0)) N s
          (-((J.method I).gamma s • WithLp.ofLp
            (g (errorTrajectory family I N g e0 s)-A 0 (errorTrajectory family I N g e0 s)))))‖ :=
      norm_sum_le _ _
    _ ≤ ∑ s ∈ Finset.range N, (rho/I.delta)*I.epsilon N*
        (J.endpointProfile N s*leadingRadius J I s)*Q^2*‖e0‖^2 := by
      apply Finset.sum_le_sum
      intro s hs
      have hs' := Finset.mem_range.mp hs
      let e := errorTrajectory family I N g e0 s
      let K := ((2/I.delta)*J.den I s/J.den I N)*
        (J.block (s+1) (N-(s+1))).eval 1
      have hK : 0 ≤ K := by
        apply mul_nonneg
        · exact div_nonneg (mul_nonneg (div_nonneg (by norm_num) I.delta_pos.le)
            (ha s (by omega)).le) (ha N le_rfl).le
        · exact (abs_nonneg _).trans (hm (s+1) (N-(s+1)) (by omega) 1 (by norm_num))
      have hgrowth : ‖e‖ ≤ leadingRadius J I s*Q*‖e0‖ :=
        lipschitzHessian_intermediate_growth_le family I hN (by omega)
          g A e0 rho R h he0 hsmall
      have hdef : ‖g e-A 0 e‖ ≤ rho/2*‖e‖^2 :=
        h.gradient_defect_le ((hc s (by omega)).trans he0)
      have hforce := J.forcingTail_norm_le I (hessianMatrix (A 0)) h.hermitian h.spectrum
        ha hm hs' (g e-A 0 e)
      have heq : K*(rho/2*(leadingRadius J I s*Q*‖e0‖)^2) =
          (rho/I.delta)*I.epsilon N*(J.endpointProfile N s*leadingRadius J I s)*Q^2*‖e0‖^2 := by
        have hPN : (J.leading N).eval 1 ≠ 0 :=
          ne_of_gt (family.leading_eval_one_pos hN (le_refl N))
        rw [← heps]
        dsimp [K, leadingRadius, JacobiData.endpointProfile]
        field_simp [ne_of_gt (ha N le_rfl), ne_of_gt (ha s (by omega)),
          hPN]
      exact hforce.trans ((mul_le_mul_of_nonneg_left hdef hK).trans
        ((mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg e) hgrowth 2)
            (div_nonneg h.rho_nonneg (by norm_num))) hK).trans_eq heq))
    _ = _ := by
      simp_rw [show ∀ s, (rho/I.delta)*I.epsilon N*(J.endpointProfile N s*leadingRadius J I s)*
          Q^2*‖e0‖^2 = ((rho/I.delta)*I.epsilon N*Q^2*‖e0‖^2)*
            (J.endpointProfile N s*leadingRadius J I s) by intro s; ring]
      rw [← Finset.mul_sum, hQ]
      dsimp [secondOrderCoefficient]
      ring

end
end chebyshev1.Nonlinear
