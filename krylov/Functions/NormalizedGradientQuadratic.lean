import krylov.Functions.MidpointQuadratic
import chebyshev1.Nonlinear.AveragedHessian

/-!
Article: main_krylov, lem:cycle-transfer, true normalized gradient O(e²) jet.
Use: derive the precise quadratic initial-gradient remainder from an actual
Lipschitz derivative of the original Hessian. Source: true radial FTC and
the proved quadratic midpoint remainder, on the original physical domain.
-/
namespace krylov.Functions
noncomputable section
open Set Metric chebyshev1.Nonlinear
open scoped NNReal
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- The original actual normalized gradient has a uniform quadratic jet
remainder when the actual third derivative is Lipschitz. Article: lem:cycle-transfer. -/
theorem normalizedGradient_reference_quadratic_jet (T : E ≃L[ℝ] E)
    (G : E → E) (H : E → E →L[ℝ] E) (Q : E →L[ℝ] E)
    (D : E → E →L[ℝ] E →L[ℝ] E)
    {r : ℝ} (hr : 0<r) (hG0 : G 0=0) (hH0 : H 0=Q)
    (hG : ∀ z : E, ‖T z‖≤r → HasFDerivAt G (H z) z)
    (hD : ∀ z : E, ‖T z‖≤r → HasFDerivAt H (D z) z)
    {L : ℝ≥0} (hL : LipschitzOnWith L D (T ⁻¹' closedBall (0:E) r))
    (B : ℝ) (hB : 0<B) :
    ∃ ep C : ℝ, 0<ep ∧ 0<C ∧ ∀ ε : ℝ, 0<ε → ε<ep → ∀ u : E, ‖u‖≤B →
      ‖ε⁻¹ • G (ε • u)-Q u-ε • ((1/2 : ℝ) • D 0 u u)‖≤C*ε^2 := by
  let S := T ⁻¹' closedBall (0:E) r
  have hS : Convex ℝ S := by
    intro a ha b hb u v hu hv huv
    change T (u • a+v • b)∈closedBall (0:E) r
    simpa only [map_add,map_smul] using (convex_closedBall (0:E) r) ha hb hu hv huv
  have hz : (0:E)∈S := by simp [S,hr.le]
  have hd z (hz : z∈S) : HasFDerivAt H (D z) z := hD z
    (by simpa only [S,mem_preimage,mem_closedBall,dist_zero_right] using hz)
  refine ⟨r/(‖T.toContinuousLinearMap‖*B+1),(L:ℝ)*B^3+1,by positivity,by positivity,?_⟩
  intro ε hε he u hu
  have hx : ε • u∈S := by
    have hh := (lt_div_iff₀ (by positivity : 0<‖T.toContinuousLinearMap‖*B+1)).mp he
    change T (ε • u)∈closedBall (0:E) r
    rw [mem_closedBall,dist_zero_right,map_smul,norm_smul,Real.norm_of_nonneg hε.le]
    have hb := mul_le_mul_of_nonneg_left
      ((T.toContinuousLinearMap.le_opNorm u).trans (mul_le_mul_of_nonneg_left hu (norm_nonneg _))) hε.le
    change ε*‖T u‖≤ε*(‖T.toContinuousLinearMap‖*B) at hb
    nlinarith only [hh,hb,hε]
  have hseg (t : ℝ) (ht : t∈Icc (0:ℝ) 1) :
      (0:E)+t • (ε • u)∈S ∧ ‖(0:E)+t • (ε • u)‖≤B*ε := by
    refine ⟨hS.add_smul_mem hz (by simpa only [zero_add] using hx) ht,?_⟩
    rw [zero_add,norm_smul,norm_smul,Real.norm_of_nonneg ht.1,Real.norm_of_nonneg hε.le]
    have hb := mul_le_mul_of_nonneg_left hu hε.le
    have ht' := mul_le_mul_of_nonneg_right ht.2 (by positivity : 0≤ε*‖u‖)
    nlinarith only [hb,ht']
  have hcont : ContinuousOn H S := fun z hz => (hd z hz).continuousAt.continuousWithinAt
  have hc : ContinuousOn (fun t : ℝ => H ((0:E)+t • (ε • u))) (Icc 0 1) :=
    hcont.comp (by fun_prop) (fun t ht => (hseg t ht).1)
  have hFTC := averagedDerivative_apply G H 0 (ε • u) hc
    (fun t ht => hG _ (by simpa only [S,mem_preimage,mem_closedBall,dist_zero_right] using (hseg t ht).1))
  rw [zero_add,hG0,sub_zero,map_smul] at hFTC
  have hnorm : ε⁻¹ • G (ε • u)=averagedDerivative H 0 (ε • u) u := by
    rw [←hFTC,smul_smul,inv_mul_cancel₀ hε.ne',one_smul]
  have hp := averagedHessian_midpoint_quadratic H D S hS hz hd hL 0 (ε • u) (B*ε) (by positivity) hseg
  rw [hH0,zero_add] at hp
  have heq : ε⁻¹ • G (ε • u)-Q u-ε • ((1/2 : ℝ) • D 0 u u)=
      (averagedDerivative H 0 (ε • u)-Q-D 0 ((1/2 : ℝ) • (ε • u))) u := by
    rw [hnorm]
    simp only [_root_.sub_apply,map_smul,_root_.smul_apply,smul_smul,mul_comm]
  rw [heq]
  calc
    _ ≤ ‖averagedDerivative H 0 (ε • u)-Q-D 0 ((1/2 : ℝ) • (ε • u))‖*‖u‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ ((L:ℝ)*(B*ε)^2)*B := by gcongr
    _ ≤ ((L:ℝ)*B^3+1)*ε^2 := by nlinarith only [sq_nonneg ε]

end
end krylov.Functions
