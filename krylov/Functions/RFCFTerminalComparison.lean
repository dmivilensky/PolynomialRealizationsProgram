import krylov.Functions.NativeRFCFInputs

/-!
Article: main_krylov, prop:Fcycle, the actual new final-gradient query.
Use: replace the old RFC correction secant by the genuine gradient on the
new RFC-F correction segment. At a full-cycle terminal reference, both real
endpoints and the new query are quadratic in the initial scale; their true
Hessian Lipschitz bound makes the replacement fourth order.
Source: genuine gradient Taylor estimates and the actual averaged-Hessian
endpoint bound, with every queried segment inside the true metric domain.
-/
namespace krylov.Functions
noncomputable section
open Set Metric krylov.Nonlinear chebyshev1.Nonlinear
open scoped InnerProductSpace NNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- A genuine small terminal query may use the old actually observed secant
at quadratic cost in its terminal endpoint scale.
Article: main_krylov, prop:Fcycle, fourth-order native final-query replacement.
All three endpoints below are real physical points in the original derivative domain. -/
theorem metric_terminal_query_comparison (T : E ≃L[ℝ] E) (G : E → E)
    (H : E → E →L[ℝ] E) (Q : E →L[ℝ] E) {r : ℝ} (hr : 0≤r)
    (hG₀ : G 0=0) (hH₀ : H 0=Q) {L : ℝ≥0}
    (hH : LipschitzOnWith L (coordinateDerivative T H) (closedBall 0 r))
    (hG : ∀ z : E,‖T z‖≤r → HasFDerivAt G (H z) z)
    (a b u : E) (ha : ‖T a‖≤r) (hb : ‖T b‖≤r) (hu : ‖T (a+u)‖≤r)
    (A B U τ : ℝ) (hA : 0≤A) (hB : 0≤B) (hτ : 0≤τ)
    (han : ‖a‖≤A*τ) (hbn : ‖b‖≤B*τ) (hun : ‖u‖≤U*τ) :
    ‖G (a+u)-(G a+averagedDerivative H a (b-a) u)‖≤
      (((‖T.toContinuousLinearMap‖₊^3*L : ℝ≥0) : ℝ))/2*
        ((A+U)^2+A^2+(A+B)*U)*τ^2 := by
  let P : ℝ := (((‖T.toContinuousLinearMap‖₊^3*L : ℝ≥0) : ℝ))
  have hP : 0≤P := NNReal.coe_nonneg _
  have hseg t (ht : t∈Icc (0 : ℝ) 1) : a+t • (b-a)∈T ⁻¹' closedBall (0 : E) r := by
    change T (a+t • (b-a))∈closedBall (0 : E) r
    rw [map_add,map_smul,map_sub]
    apply (convex_closedBall (0 : E) r).add_smul_mem
      (by simpa only [mem_closedBall,dist_zero_right] using ha) _ ht
    simpa only [add_sub_cancel,mem_closedBall,dist_zero_right] using hb
  have hphys := coordinateDerivative_lipschitz_pullback T H hH
  have hc := hphys.continuousOn.comp
    (continuous_const.add (continuous_id.smul continuous_const)).continuousOn hseg
  have hz : (0 : E)∈T ⁻¹' closedBall (0 : E) r := by simp [hr]
  have hc₀ : ContinuousOn (fun t : ℝ=>H ((0 : E)+t • (0 : E))) (Icc 0 1) := by
    simpa only [smul_zero,add_zero] using (continuousOn_const : ContinuousOn (fun _ : ℝ=>H 0) (Icc 0 1))
  have havg := averagedHessian_endpoint_bound H a (b-a) 0 0 P hc hc₀ hP
    (fun t ht=>by simpa only [smul_zero,add_zero] using hphys.norm_sub_le (hseg t ht) hz)
  have hzero : averagedDerivative H 0 0=Q := by simpa only [averagedDerivative,smul_zero,add_zero,
    intervalIntegral.integral_const,sub_zero,one_smul] using hH₀
  rw [hzero] at havg
  simp only [sub_zero,add_sub_cancel,add_zero] at havg
  have hmat : ‖averagedDerivative H a (b-a)-Q‖≤P/2*(A+B)*τ :=
    havg.trans (by nlinarith [mul_le_mul_of_nonneg_left (add_le_add han hbn) hP])
  have hza : ‖a+u‖≤(A+U)*τ := (norm_add_le _ _).trans ((add_le_add han hun).trans_eq (by ring))
  have hga := metric_gradient_quadratic_error T G H Q hr hG₀ hH₀ hH hG a ha
  have hgz := metric_gradient_quadratic_error T G H Q hr hG₀ hH₀ hH hG (a+u) hu
  have he : G (a+u)-(G a+averagedDerivative H a (b-a) u)=
      (G (a+u)-Q (a+u))-(G a-Q a)-(averagedDerivative H a (b-a)-Q) u := by
    simp only [map_add,_root_.sub_apply]
    abel
  rw [he]
  have hop := ((averagedDerivative H a (b-a)-Q).le_opNorm u).trans
    (mul_le_mul hmat hun (norm_nonneg _) (by positivity : 0≤P/2*(A+B)*τ))
  have hgza : ‖G (a+u)-Q (a+u)‖≤P/2*((A+U)*τ)^2 :=
    hgz.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hza 2) (by positivity))
  have hgaa : ‖G a-Q a‖≤P/2*(A*τ)^2 :=
    hga.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) han 2) (by positivity))
  exact (norm_sub_le _ _).trans
    ((add_le_add ((norm_sub_le _ _).trans (add_le_add hgza hgaa)) hop).trans_eq (by ring))

end
end krylov.Functions
