import krylov.Functions.MetricFCOperatorJet
import krylov.Functions.FCLeadingFields

/-!
Article: main_krylov, lem:cycle-transfer, actual normalized finite FC inputs.
Use: provide the genuine operator-response map with its real initial gradient
and actual physical Bochner secants. Their smallness follows from the original
objective, and the actual terminal gradient is identified exactly.
Source: native metric search embedding, gradient Taylor and FC homogeneity.
-/

namespace krylov.Functions
noncomputable section
open Set Metric krylov.Methods krylov.Reference krylov.Nonlinear
open scoped InnerProductSpace NNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The genuine normalized initial-gradient and finite actual-secant perturbations.
Article: main_krylov, lem:cycle-transfer, actual finite operator inputs. -/
def metricFCInput (T : E ≃L[ℝ] E) (f : E → ℝ) (G : E → E) (H : E → E →L[ℝ] E)
    (Q : E →L[ℝ] E) (r ε : ℝ) (u : E) (N : ℕ) : E × (Fin N → E →L[ℝ] E) :=
  (ε⁻¹ • G (ε • u) - Q u,
    fun i => metricFCOperator T f G H fullMemory r (ε • u) i.val - Q)

/-- All original normalized FC inputs are uniformly of first order in the cycle scale.
Article: main_krylov, lem:cycle-transfer, genuine source bound.
Proof: derive every actual query bound from the real objective, integrate its
true physical Hessian and apply its true gradient Taylor estimate. The radius
and constant are independent of both the initial direction and the cycle length. -/
theorem metricFCInput_bound (T : E ≃L[ℝ] E)
    (hT : T.symm.toContinuousLinearMap.IsSymmetric)
    (f : E → ℝ) (G : E → E) (H : E → E →L[ℝ] E) (Q : E →L[ℝ] E)
    {r : ℝ} (hr : 0 < r) (hG₀ : G 0 = 0) (hH₀ : H 0 = Q)
    (hHc₀ : coordinateDerivative T H 0 = ContinuousLinearMap.id ℝ E)
    {L : ℝ≥0} (hLr : (L : ℝ) * r ≤ 1 / 2)
    (hH : LipschitzOnWith L (coordinateDerivative T H) (closedBall 0 r))
    (hF : ∀ z : E, ‖T z‖ ≤ r → HasFDerivAt f (innerSL ℝ (G z)) z)
    (hG : ∀ z : E, ‖T z‖ ≤ r → HasFDerivAt G (H z) z)
    (B : ℝ) (hB : 0 < B) :
    ∃ ε₀ C : ℝ, 0 < ε₀ ∧ 0 < C ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      ∀ u : E, ‖u‖ ≤ B → ‖T (ε • u)‖ < r / 4 ∧
        ∀ N : ℕ, ‖metricFCInput T f G H Q r ε u N‖ ≤ C * ε := by
  let J := ‖T.toContinuousLinearMap‖
  let P : ℝ := (((‖T.toContinuousLinearMap‖₊ ^ 3 * L : ℝ≥0) : ℝ))
  let Dg := P / 2 * B ^ 2
  let Da := P * ‖T.symm.toContinuousLinearMap‖ * Real.sqrt 3 * J * B
  let C := Dg + Da + 1
  have hP : 0 ≤ P := NNReal.coe_nonneg _
  have hDg : 0 ≤ Dg := by dsimp only [Dg]; positivity
  have hDa : 0 ≤ Da := by dsimp only [Da]; positivity
  refine ⟨r / (4 * (J * B + 1)), C, by positivity, by dsimp only [C]; positivity, ?_⟩
  intro ε hε he u hu
  have huT : ‖T u‖ ≤ J * B :=
    (T.toContinuousLinearMap.le_opNorm u).trans (mul_le_mul_of_nonneg_left hu (norm_nonneg _))
  have hx : ‖T (ε • u)‖ < r / 4 := by
    rw [map_smul, norm_smul, Real.norm_of_nonneg hε.le]
    have he' := (lt_div_iff₀ (by positivity : 0 < 4 * (J * B + 1))).mp he
    have hb := mul_le_mul_of_nonneg_left huT hε.le
    nlinarith
  refine ⟨hx, ?_⟩
  intro N
  have hx' : ‖T (ε • u)‖ ≤ r := by linarith [norm_nonneg (T (ε • u))]
  have hv : ‖ε⁻¹ • G (ε • u) - Q u‖ ≤ Dg * ε := by
    have ht := metric_gradient_quadratic_error T G H Q hr.le hG₀ hH₀ hH hG (ε • u) hx'
    have heq : ε⁻¹ • G (ε • u) - Q u = ε⁻¹ • (G (ε • u) - Q (ε • u)) := by
      rw [smul_sub, map_smul, smul_smul, inv_mul_cancel₀ hε.ne', one_smul]
    rw [heq, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hε.le)]
    rw [norm_smul, Real.norm_of_nonneg hε.le] at ht
    have hsq : ‖u‖ ^ 2 ≤ B ^ 2 := (sq_le_sq₀ (norm_nonneg _) hB.le).mpr hu
    calc
      _ ≤ ε⁻¹ * (P / 2 * (ε * ‖u‖) ^ 2) := mul_le_mul_of_nonneg_left ht (inv_nonneg.mpr hε.le)
      _ = P / 2 * ‖u‖ ^ 2 * ε := by field_simp
      _ ≤ Dg * ε := by
        dsimp only [Dg]
        nlinarith [mul_le_mul_of_nonneg_left hsq (by positivity : 0 ≤ P / 2 * ε)]
  have ha j : ‖metricFCOperator T f G H fullMemory r (ε • u) j - Q‖ ≤ Da * ε := by
    have hb := metricFCOperator_local_bound T hT f G H hr hG₀ hHc₀ hLr hH hF hG
      fullMemory (ε • u) (by linarith) j
    rw [hH₀, map_smul, norm_smul, Real.norm_of_nonneg hε.le] at hb
    apply hb.trans
    have hm := mul_le_mul_of_nonneg_left huT
      (by positivity : 0 ≤ P * ‖T.symm.toContinuousLinearMap‖ * Real.sqrt 3 * ε)
    dsimp only [Da]
    nlinarith only [hm]
  rw [metricFCInput, Prod.norm_def, max_le_iff]
  constructor
  · exact hv.trans (by dsimp only [C]; nlinarith)
  · apply (pi_norm_le_iff_of_nonneg (by dsimp only [C]; positivity : 0 ≤ C * ε)).mpr
    intro i
    exact (ha i.val).trans (by dsimp only [C]; nlinarith)

/-- The real physical gradient equals the existing operator FC executor on its actual Hessian averages.
Article: main_krylov, lem:cycle-transfer, exact native output dictionary. -/
theorem metricFCPoint_gradient_eq_fcGradient (T : E ≃L[ℝ] E)
    (hT : T.symm.toContinuousLinearMap.IsSymmetric)
    (f : E → ℝ) (G : E → E) (H : E → E →L[ℝ] E)
    {r : ℝ} (hr : 0 < r) (hG₀ : G 0 = 0)
    (hHc₀ : coordinateDerivative T H 0 = ContinuousLinearMap.id ℝ E)
    {L : ℝ≥0} (hLr : (L : ℝ) * r ≤ 1 / 2)
    (hH : LipschitzOnWith L (coordinateDerivative T H) (closedBall 0 r))
    (hF : ∀ z : E, ‖T z‖ ≤ r → HasFDerivAt f (innerSL ℝ (G z)) z)
    (hG : ∀ z : E, ‖T z‖ ≤ r → HasFDerivAt G (H z) z)
    (x₀ : E) (hx₀ : ‖T x₀‖ < r / 4) (N : ℕ) :
    G (metricFCPoint T f G fullMemory r x₀ N) =
      fcGradient fullMemory (metricFCOperator T f G H fullMemory r x₀) (G x₀) N := by
  have he := congrArg History.gradient
    (metricFCObservedHistory_eq_fcHistory T hT f G H hr hG₀ hHc₀ hLr hH hF hG fullMemory x₀ hx₀ N)
  simpa only [metricFCObservedHistory, observedSearchHistory_gradient, fcGradient] using he

/-- The actual physical terminal gradient is exactly the scaled genuine finite FC map at its actual normalized inputs.
Article: main_krylov, lem:cycle-transfer, genuine response substitution.
Proof: identify the complete real observed run, restrict its actual operator
prefix to finite coordinates, and apply the proved true FC homogeneity. -/
theorem metricFCPoint_gradient_eq_finiteTerminal (T : E ≃L[ℝ] E)
    (hT : T.symm.toContinuousLinearMap.IsSymmetric)
    (f : E → ℝ) (G : E → E) (H : E → E →L[ℝ] E) (Q : E →L[ℝ] E)
    {r : ℝ} (hr : 0 < r) (hG₀ : G 0 = 0)
    (hHc₀ : coordinateDerivative T H 0 = ContinuousLinearMap.id ℝ E)
    {L : ℝ≥0} (hLr : (L : ℝ) * r ≤ 1 / 2)
    (hH : LipschitzOnWith L (coordinateDerivative T H) (closedBall 0 r))
    (hF : ∀ z : E, ‖T z‖ ≤ r → HasFDerivAt f (innerSL ℝ (G z)) z)
    (hG : ∀ z : E, ‖T z‖ ≤ r → HasFDerivAt G (H z) z)
    (ε : ℝ) (hε : ε ≠ 0) (u : E) (hx₀ : ‖T (ε • u)‖ < r / 4) (N : ℕ) :
    let I := metricFCInput T f G H Q r ε u N
    G (metricFCPoint T f G fullMemory r (ε • u) N) =
      ε • fcFiniteTerminal Q N (Q u + I.1, I.2) := by
  let I := metricFCInput T f G H Q r ε u N
  let A := metricFCOperator T f G H fullMemory r (ε • u)
  have hinit : G (ε • u) = ε • (Q u + I.1) := by
    dsimp only [I, metricFCInput]
    rw [add_sub_cancel, smul_smul, mul_inv_cancel₀ hε, one_smul]
  have hpath j (hj : j < N) : A j = fcFiniteOperatorPath Q N I.2 j := by
    simp only [fcFiniteOperatorPath, dite_eq_left hj, I, metricFCInput]
    dsimp only [A]
    abel
  rw [metricFCPoint_gradient_eq_fcGradient T hT f G H hr hG₀ hHc₀ hLr hH hF hG (ε • u) hx₀ N,
    hinit, fcGradient_congr_operator_prefix A (fcFiniteOperatorPath Q N I.2) (ε • (Q u + I.1)) N hpath,
    (fullFC_scalar (fcFiniteOperatorPath Q N I.2) (Q u + I.1) ε hε N).1]
  rfl

end
end krylov.Functions
