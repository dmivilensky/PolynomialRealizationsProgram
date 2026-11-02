import krylov.Functions.NativeRFCOperators

/-!
Article: main_krylov, s7:N and thm:Htransfer, primitive first-query source.
Use: obtain the real first secant and normalized initial-gradient bounds
before imposing any full-reference assumption. This removes a circular
frozen-reference nondegeneracy premise from the native RFC transfer.
Source: true local chord minimization and original scalar derivative Taylor.
-/
namespace krylov.Functions
noncomputable section
open Set Metric krylov.Methods krylov.Reference krylov.Nonlinear chebyshev1.Nonlinear
open scoped InnerProductSpace NNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

set_option maxHeartbeats 800000 in
/-- The genuine first RFC search secant and observed initial gradient have
uniform first-order normalized drift for every bounded start, without any
CG nonstagnation or prior trajectory assumption.
Article: main_krylov, thm:Htransfer, noncircular original-reference source. -/
theorem nativeRFC_first_reference_drift (T : E ≃L[ℝ] E)
    (hT : T.symm.toContinuousLinearMap.IsSymmetric)
    (f : E → ℝ) (G : E → E) (H : E → E →L[ℝ] E) (Q : E →L[ℝ] E)
    {r : ℝ} (hr : 0<r) (hG₀ : G 0=0) (hH₀ : H 0=Q)
    (hHc₀ : coordinateDerivative T H 0=ContinuousLinearMap.id ℝ E)
    {L : ℝ≥0} (hLr : (L : ℝ)*r≤1/2)
    (hH : LipschitzOnWith L (coordinateDerivative T H) (closedBall 0 r))
    (hF : ∀ z, ‖T z‖≤r → HasFDerivAt f (innerSL ℝ (G z)) z)
    (hG : ∀ z, ‖T z‖≤r → HasFDerivAt G (H z) z)
    (R : ℝ) (hR : 0<R) :
    ∃ ε₀ C : ℝ, 0<ε₀ ∧ 0<C ∧ ∀ ε : ℝ, 0<ε → ε<ε₀ →
      ∀ u : E, ‖u‖≤R →
      ‖(rfcFunctionSearchOperator T f G H fullMemory r (ε • u) 0-Q,
        ε⁻¹ • G (ε • u)-Q u)‖≤C*ε := by
  let J := ‖T.toContinuousLinearMap‖
  let P : ℝ := (((‖T.toContinuousLinearMap‖₊^3*L : ℝ≥0) : ℝ))
  let Y := ‖T.symm.toContinuousLinearMap‖*Real.sqrt 3*J*R
  let Da := P/2*(R+Y)
  let Dg := P/2*R^2
  let C := Da+Dg+1
  have hP : 0≤P := NNReal.coe_nonneg _
  have hY : 0≤Y := by dsimp only [Y,J]; positivity
  have hDa : 0≤Da := by dsimp only [Da]; positivity
  have hDg : 0≤Dg := by dsimp only [Dg]; positivity
  refine ⟨r/(4*(J*R+1)),C,by dsimp only [J]; positivity,by dsimp only [C]; positivity,?_⟩
  intro ε hε he u hu
  let x := ε • u
  let d := rfcFunctionDirection fullMemory (⟨G x,[]⟩ : History E)
  let y := metricLocalExactPoint T f x d r
  have hx : ‖T x‖<r/2 := by
    have hh := (lt_div_iff₀ (by dsimp only [J]; positivity : 0<4*(J*R+1))).mp he
    have hn := T.toContinuousLinearMap.le_opNorm x
    rw [show x=ε • u from rfl,norm_smul,Real.norm_of_nonneg hε.le] at hn
    change ‖T x‖≤J*(ε*‖u‖) at hn
    have hm := mul_le_mul_of_nonneg_left hu (by dsimp only [J]; positivity : 0≤J*ε)
    nlinarith only [hn,hm,hh,hε,norm_nonneg (T x)]
  have hxball : ‖T x‖≤r := by linarith only [hx,hr]
  have hy := metricLocalExactPoint_bound T hT f G H hr hG₀ hHc₀ hLr hH hF hG x d hx
  have hxn : ‖x‖≤R*ε := by
    rw [show x=ε • u from rfl,norm_smul,Real.norm_of_nonneg hε.le]
    exact (mul_le_mul_of_nonneg_left hu hε.le).trans_eq (mul_comm _ _)
  have hyn : ‖y‖≤Y*ε := by
    have hh := T.symm.toContinuousLinearMap.le_opNorm (T y)
    change ‖T.symm (T y)‖≤‖T.symm.toContinuousLinearMap‖*‖T y‖ at hh
    rw [T.symm_apply_apply] at hh
    have hb := hh.trans (mul_le_mul_of_nonneg_left hy.1 (norm_nonneg _))
    have ht := (T.toContinuousLinearMap.le_opNorm x).trans (mul_le_mul_of_nonneg_left hxn (norm_nonneg _))
    change ‖T x‖≤‖T.toContinuousLinearMap‖*(R*ε) at ht
    calc
      _ ≤ ‖T.symm.toContinuousLinearMap‖*(Real.sqrt 3*‖T x‖) := hb
      _ = (‖T.symm.toContinuousLinearMap‖*Real.sqrt 3)*‖T x‖ := by ring
      _ ≤ (‖T.symm.toContinuousLinearMap‖*Real.sqrt 3)*(‖T.toContinuousLinearMap‖*(R*ε)) :=
        mul_le_mul_of_nonneg_left ht (by positivity)
      _ = Y*ε := by dsimp only [Y,J]; ring
  have hAeq : rfcFunctionSearchOperator T f G H fullMemory r x 0=averagedDerivative H x (y-x) := by
    simp only [rfcFunctionSearchOperator,rfcFunctionRun,rfcFunctionLineStep,rfcFunctionLinePoint,
      History.displacement,List.map_nil,List.sum_nil,add_zero]
    rfl
  have hA : ‖rfcFunctionSearchOperator T f G H fullMemory r x 0-Q‖≤Da*ε := by
    have hh := metric_segment_operator_bound T H hr.le hH x y hxball hy.2.le
    rw [hH₀] at hh
    rw [hAeq]
    exact hh.trans ((mul_le_mul_of_nonneg_left (add_le_add hxn hyn) (by positivity : 0≤P/2)).trans_eq (by dsimp only [Da]; ring))
  have hv : ‖ε⁻¹ • G x-Q u‖≤Dg*ε := by
    have hh := metric_gradient_quadratic_error T G H Q hr.le hG₀ hH₀ hH hG x hxball
    have heq : ε⁻¹ • G x-Q u=ε⁻¹ • (G x-Q x) := by
      dsimp only [x]
      rw [smul_sub,map_smul,smul_smul,inv_mul_cancel₀ hε.ne',one_smul]
    rw [heq,norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hε.le)]
    have hs : ‖u‖^2≤R^2 := (sq_le_sq₀ (norm_nonneg _) hR.le).mpr hu
    rw [show x=ε • u from rfl,norm_smul,Real.norm_of_nonneg hε.le] at hh
    calc
      _ ≤ ε⁻¹*(P/2*(ε*‖u‖)^2) := mul_le_mul_of_nonneg_left hh (inv_nonneg.mpr hε.le)
      _ = P/2*‖u‖^2*ε := by field_simp
      _ ≤ Dg*ε := by dsimp only [Dg]; nlinarith only [mul_le_mul_of_nonneg_left hs (by positivity : 0≤P/2*ε)]
  rw [Prod.norm_def,max_le_iff]
  exact ⟨hA.trans (mul_le_mul_of_nonneg_right (by dsimp only [C]; linarith only [hDg]) hε.le),
    hv.trans (mul_le_mul_of_nonneg_right (by dsimp only [C]; linarith only [hDa]) hε.le)⟩

end
end krylov.Functions
