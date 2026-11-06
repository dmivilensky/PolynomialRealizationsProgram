import chebyshev1.Perturbations.ObjectivePointwise
import chebyshev1.Nonlinear.WeightedSecondOrder

/-! The quadratic term of the actual objective expansion has the sharp
trajectory-weighted bound, with no smallness restriction on its argument. -/
namespace chebyshev1.Nonlinear
noncomputable section
open Filter Set Polynomial Polynomial.Chebyshev
open scoped Topology BigOperators Matrix.Norms.L2Operator
set_option backward.isDefEq.respectTransparency false
variable {d : Type*} [Fintype d] [DecidableEq d]

theorem objective_gradient_tensor_norm_le (I : SpectralInterval)
    (f : EuclideanSpace ℝ d → ℝ) (hf : Perturbations.ThreeTimesDifferentiableAtZero f)
    (A : EuclideanSpace ℝ d → EuclideanSpace ℝ d →L[ℝ] EuclideanSpace ℝ d)
    (rho R : ℝ) (h : HessianControl I (gradient f) A rho R) (hR : 0 < R) :
    ‖fderiv ℝ (fderiv ℝ (gradient f)) 0‖ ≤ rho := by
  have heq : A =ᶠ[𝓝 0] fderiv ℝ (gradient f) := by
    filter_upwards [Metric.ball_mem_nhds (0 : EuclideanSpace ℝ d) hR] with x hx
    have hn : ‖x‖ ≤ R := (show ‖x‖ < R by simpa only [Metric.mem_ball, dist_zero_right] using hx).le
    exact (h.derivative x hn).fderiv.symm
  have hd := (Perturbations.objective_gradient_pointwise f hf).2.hasFDerivAt.congr_of_eventuallyEq heq
  apply hd.le_of_lip' h.rho_nonneg
  filter_upwards [Metric.ball_mem_nhds (0 : EuclideanSpace ℝ d) hR] with x hx
  have hn : ‖x‖ ≤ R := (show ‖x‖ < R by simpa only [Metric.mem_ball, dist_zero_right] using hx).le
  simpa only [sub_zero] using h.lipschitz x hn

theorem objective_gradient_half_tensor_le (I : SpectralInterval)
    (f : EuclideanSpace ℝ d → ℝ) (hf : Perturbations.ThreeTimesDifferentiableAtZero f)
    (A : EuclideanSpace ℝ d → EuclideanSpace ℝ d →L[ℝ] EuclideanSpace ℝ d)
    (rho R : ℝ) (h : HessianControl I (gradient f) A rho R) (hR : 0 < R)
    (v : EuclideanSpace ℝ d) :
    ‖(1/2:ℝ) • (fderiv ℝ (fderiv ℝ (gradient f)) 0 v) v‖ ≤ rho/2*‖v‖^2 := by
  let B := fderiv ℝ (fderiv ℝ (gradient f)) 0
  have hB : ‖B‖ ≤ rho := objective_gradient_tensor_norm_le I f hf A rho R h hR
  have hh := ((B v).le_opNorm v).trans
    (mul_le_mul_of_nonneg_right ((B.le_opNorm v).trans
      (mul_le_mul_of_nonneg_right hB (norm_nonneg v))) (norm_nonneg v))
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1/2)]
  exact (mul_le_mul_of_nonneg_left hh (by norm_num : (0:ℝ) ≤ 1/2)).trans_eq (by ring)

/-- The `Z(v)` in Corollary 8.1(a), with the actual third-derivative tensor, has
the endpoint-weighted constant for every vector `v`. -/
theorem objective_quadraticCorrection_norm_le (family : MethodFamily) (I : SpectralInterval)
    {N : ℕ} (hN : 0 < N) (f : EuclideanSpace ℝ d → ℝ)
    (hf : Perturbations.ThreeTimesDifferentiableAtZero f)
    (A : EuclideanSpace ℝ d → EuclideanSpace ℝ d →L[ℝ] EuclideanSpace ℝ d)
    (rho R : ℝ) (h : HessianControl I (gradient f) A rho R) (hR : 0 < R)
    (v : EuclideanSpace ℝ d) :
    let g := gradientCoordinates (gradient f)
    ‖(WithLp.toLp 2 (((family.data N).method I).quadraticCorrection g (WithLp.ofLp v) N) : EuclideanSpace ℝ d)‖ ≤
      (rho/I.delta)*I.epsilon N*secondOrderCoefficient (family.data N) I N*‖v‖^2 := by
  let J := family.data N
  let S := J.method I
  let g := gradientCoordinates (gradient f)
  let H := TwoTerm.gradientLinearization g
  let B := fderiv ℝ (fderiv ℝ (gradient f)) 0
  let a : ℕ → EuclideanSpace ℝ d := fun s => WithLp.toLp 2 (S.quadraticError H (WithLp.ofLp v) s)
  have hH : H = hessianMatrix (A 0) := by
    change TwoTerm.gradientLinearization (gradientCoordinates (gradient f)) = hessianMatrix (A 0)
    rw [Perturbations.coordinate_gradientLinearization,
      (h.derivative 0 (by simpa using h.radius_nonneg)).fderiv]
  have hherm : H.IsHermitian := by simpa only [hH] using h.hermitian
  have hspec : spectrum ℝ H ⊆ Icc I.mu I.L := by simpa only [hH] using h.spectrum
  have ha := family.admissible I hN
  have hm := family.endpointMax hN
  have heps : (J.leading N).eval 1/J.den I N = I.epsilon N :=
    J.endpoint_ratio I (by positivity : (2/(2:ℝ)^N) ≠ 0) (family.terminal hN)
  have hlinear (s : ℕ) (hs : s ≤ N) : ‖a s‖ ≤ leadingRadius J I s*‖v‖ := by
    have hb := family.intermediate_transfer_exp_le I hN hs H hherm hspec (fun _ => H) 0
      (by norm_num) (by intro t _; simp [opNorm])
    simp only [mul_zero, zero_div, Real.exp_zero, mul_one] at hb
    have he : a s = Matrix.toEuclideanCLM (n := d) (𝕜 := ℝ)
        ((J.realization I).operatorTransfer s (fun _ => H)) v := by
      dsimp only [a]
      rw [S.quadraticError_eq_transfer]
      rfl
    rw [he]
    exact ((Matrix.toEuclideanCLM (n := d) (𝕜 := ℝ) _).le_opNorm v).trans
      (mul_le_mul_of_nonneg_right hb (norm_nonneg v))
  change ‖(WithLp.toLp 2 (S.quadraticCorrection g (WithLp.ofLp v) N) : EuclideanSpace ℝ d)‖ ≤ _
  unfold TwoTerm.quadraticCorrection
  rw [WithLp.toLp_sum]
  calc
    _ ≤ ∑ s ∈ Finset.range N, ‖(WithLp.toLp 2
        (-(S.gamma s) • S.forcingTail H N s ((1/2:ℝ) •
          (fderiv ℝ (fderiv ℝ g) 0 (S.quadraticError H (WithLp.ofLp v) s))
            (S.quadraticError H (WithLp.ofLp v) s))) : EuclideanSpace ℝ d)‖ := norm_sum_le _ _
    _ ≤ ∑ s ∈ Finset.range N, (rho/I.delta)*I.epsilon N*
        (J.endpointProfile N s*leadingRadius J I s)*‖v‖^2 := by
      apply Finset.sum_le_sum
      intro s hs
      have hs' := Finset.mem_range.mp hs
      let q := (1/2:ℝ) • B (a s) (a s)
      have htensor : (1/2:ℝ) •
          (fderiv ℝ (fderiv ℝ g) 0 (S.quadraticError H (WithLp.ofLp v) s))
            (S.quadraticError H (WithLp.ofLp v) s) = WithLp.ofLp q := by
        have hh := congrArg WithLp.ofLp
          (Perturbations.coordinate_gradient_second_derivative f
            (S.quadraticError H (WithLp.ofLp v) s) (S.quadraticError H (WithLp.ofLp v) s))
        simpa only [q, a, B, g, WithLp.ofLp_toLp, WithLp.ofLp_smul] using
          congrArg (fun x => (1/2:ℝ) • x) hh
      have hq : ‖q‖ ≤ rho/2*‖a s‖^2 := objective_gradient_half_tensor_le I f hf A rho R h hR _
      let K := ((2/I.delta)*J.den I s/J.den I N)*(J.block (s+1) (N-(s+1))).eval 1
      have hK : 0 ≤ K := mul_nonneg
        (div_nonneg (mul_nonneg (div_nonneg (by norm_num) I.delta_pos.le) (ha s (by omega)).le)
          (ha N le_rfl).le)
        ((abs_nonneg _).trans (hm (s+1) (N-(s+1)) (by omega) 1 (by norm_num)))
      rw [htensor]
      have hforce := J.forcingTail_norm_le I H hherm hspec ha hm hs' q
      simp only [map_neg, map_smul] at hforce
      have hprod := (mul_le_mul_of_nonneg_left hq hK).trans
        (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hlinear s hs'.le) 2)
            (div_nonneg h.rho_nonneg (by norm_num))) hK)
      rw [neg_smul]
      refine hforce.trans (hprod.trans_eq ?_)
      have hPN : (J.leading N).eval 1 ≠ 0 := (family.leading_eval_one_pos hN le_rfl).ne'
      rw [← heps]
      dsimp [K, leadingRadius, JacobiData.endpointProfile]
      field_simp [ne_of_gt (ha N le_rfl), ne_of_gt (ha s (by omega)), hPN]
    _ = _ := by
      dsimp [secondOrderCoefficient]
      rw [Finset.mul_sum, Finset.sum_mul]

end
end chebyshev1.Nonlinear
