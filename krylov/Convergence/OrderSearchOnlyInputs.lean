import krylov.Convergence.OrderSearchOnlySource
import krylov.Functions.MetricFCLeadingSource

/-!
Article: main_krylov, thm:D, native deferred search-only source bounds.
Use: actual Hessian averages and normalized starting gradients of a causal
search-only scalar execution are uniformly small, before any smooth-policy
or CG nondegeneracy assumptions. Source: genuine query localization and
endpoint-weighted Hessian integration on the actual physical segments.
-/
namespace krylov.Convergence
noncomputable section
open Set Metric krylov.Methods krylov.Reference krylov.Functions krylov.Nonlinear
  chebyshev1.Nonlinear
open scoped InnerProductSpace NNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The real physical Hessian average on a genuine scalar search segment.
Article: main_krylov, thm:D, DC. -/
def scalarSearchOnlyOperator (m : ProbedMethod E) (T : E ≃L[ℝ] E)
    (f : E → ℝ) (G : E → E) (H : E → E →L[ℝ] E) (r : ℝ) (x₀ : E) (i : ℕ) : E →L[ℝ] E :=
  averagedDerivative H (scalarFunctionPoint m T f G r x₀ i)
    (scalarFunctionPoint m T f G r x₀ (i+1)-scalarFunctionPoint m T f G r x₀ i)

/-- Every real scalar search-only segment has a derived linear Hessian
perturbation bound at the initial true error scale. Article: thm:D. -/
theorem scalarSearchOnlyOperator_local_bound
    (m : ProbedMethod E) (hm : CorrectionFree m) (T : E ≃L[ℝ] E)
    (hT : T.symm.toContinuousLinearMap.IsSymmetric)
    (f : E → ℝ) (G : E → E) (H : E → E →L[ℝ] E)
    {r : ℝ} (hr : 0 < r) (hG₀ : G 0 = 0)
    (hH₀ : coordinateDerivative T H 0 = ContinuousLinearMap.id ℝ E)
    {L : ℝ≥0} (hLr : (L : ℝ) * r ≤ 1 / 2)
    (hH : LipschitzOnWith L (coordinateDerivative T H) (closedBall 0 r))
    (hF : ∀ z : E, ‖T z‖ ≤ r → HasFDerivAt f (innerSL ℝ (G z)) z)
    (hG : ∀ z : E, ‖T z‖ ≤ r → HasFDerivAt G (H z) z)
    (x₀ : E) (hx₀ : ‖T x₀‖ < r / 2) :
    ∀ k : ℕ, ‖scalarSearchOnlyOperator m T f G H r x₀ k - H 0‖ ≤
      ((‖T.toContinuousLinearMap‖₊ ^ 3 * L : ℝ≥0) : ℝ) *
        ‖T.symm.toContinuousLinearMap‖ * Real.sqrt 3 * ‖T x₀‖ := by
  have hl := scalarSearchOnlyPoint_localization m hm T hT f G H hr hG₀ hH₀ hLr hH hF hG x₀ hx₀
  have hphys := coordinateDerivative_lipschitz_pullback T H hH
  have hball j : scalarFunctionPoint m T f G r x₀ j ∈ T ⁻¹' closedBall (0 : E) r := by
    change T (scalarFunctionPoint m T f G r x₀ j) ∈ closedBall (0 : E) r
    simpa only [mem_closedBall, dist_zero_right] using (hl j).2.2.le
  have hb j : ‖scalarFunctionPoint m T f G r x₀ j‖ ≤
      ‖T.symm.toContinuousLinearMap‖ * (Real.sqrt 3 * ‖T x₀‖) := by
    calc
      _ = ‖T.symm (T (scalarFunctionPoint m T f G r x₀ j))‖ := by rw [T.symm_apply_apply]
      _ ≤ ‖T.symm.toContinuousLinearMap‖ * ‖T (scalarFunctionPoint m T f G r x₀ j)‖ :=
        T.symm.toContinuousLinearMap.le_opNorm _
      _ ≤ _ := mul_le_mul_of_nonneg_left (hl j).1 (norm_nonneg _)
  intro k
  let a := scalarFunctionPoint m T f G r x₀ k
  let b := scalarFunctionPoint m T f G r x₀ (k + 1)
  have hseg t (ht : t ∈ Icc (0 : ℝ) 1) : a + t • (b - a) ∈ T ⁻¹' closedBall (0 : E) r := by
    change T (a + t • (b - a)) ∈ closedBall (0 : E) r
    rw [map_add, map_smul, map_sub]
    apply (convex_closedBall (0 : E) r).add_smul_mem (hball k) _ ht
    change T a + (T b - T a) ∈ closedBall (0 : E) r
    simpa only [add_sub_cancel, mem_preimage, b] using hball (k + 1)
  have hc := hphys.continuousOn.comp
    (continuous_const.add (continuous_id.smul continuous_const)).continuousOn hseg
  have hz : (0 : E) ∈ T ⁻¹' closedBall (0 : E) r := by simp [hr.le]
  have hc₀ : ContinuousOn (fun t : ℝ => H ((0 : E) + t • (0 : E))) (Icc 0 1) := by
    simpa only [smul_zero, add_zero] using (continuousOn_const : ContinuousOn (fun _ : ℝ => H 0) (Icc 0 1))
  have hcomp := averagedHessian_endpoint_bound H a (b - a) 0 0
    (((‖T.toContinuousLinearMap‖₊ ^ 3 * L : ℝ≥0) : ℝ)) hc hc₀ (NNReal.coe_nonneg _)
    (fun t ht => by simpa only [smul_zero, add_zero] using hphys.norm_sub_le (hseg t ht) hz)
  have he : averagedDerivative H 0 0 = H 0 := by simp [averagedDerivative]
  rw [he] at hcomp
  simp only [sub_zero, add_sub_cancel, add_zero] at hcomp
  exact hcomp.trans (by
    have hsum := add_le_add (hb k) (hb (k + 1))
    change _ ≤ _
    nlinarith [mul_le_mul_of_nonneg_left hsum
      (NNReal.coe_nonneg (‖T.toContinuousLinearMap‖₊ ^ 3 * L))])

/-- All genuine normalized inputs of a finite correction-free scalar cycle.
Article: main_krylov, thm:D and lem:cycle-transfer. -/
def scalarSearchOnlyInput (m : ProbedMethod E) (T : E ≃L[ℝ] E)
    (f : E → ℝ) (G : E → E) (H : E → E →L[ℝ] E) (Q : E →L[ℝ] E)
    (r ε : ℝ) (u : E) (N : ℕ) : E × (Fin N → E →L[ℝ] E) :=
  (ε⁻¹ • G (ε • u)-Q u,fun i=>scalarSearchOnlyOperator m T f G H r (ε • u) i.val-Q)

/-- The entire actual search-only finite source is uniformly first order.
No source bound, direction angle or domain assumption is supplied.
Article: main_krylov, thm:D and lem:cycle-transfer. -/
theorem scalarSearchOnlyInput_bound
    (m : ProbedMethod E) (hm : CorrectionFree m) (T : E ≃L[ℝ] E)
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
        ∀ N : ℕ, ‖scalarSearchOnlyInput m T f G H Q r ε u N‖ ≤ C * ε := by
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
  have ha j : ‖scalarSearchOnlyOperator m T f G H r (ε • u) j - Q‖ ≤ Da * ε := by
    have hb := scalarSearchOnlyOperator_local_bound m hm T hT f G H hr hG₀ hHc₀ hLr hH hF hG
      (ε • u) (by linarith) j
    rw [hH₀, map_smul, norm_smul, Real.norm_of_nonneg hε.le] at hb
    apply hb.trans
    have hm := mul_le_mul_of_nonneg_left huT
      (by positivity : 0 ≤ P * ‖T.symm.toContinuousLinearMap‖ * Real.sqrt 3 * ε)
    dsimp only [Da]
    nlinarith only [hm]
  rw [scalarSearchOnlyInput, Prod.norm_def, max_le_iff]
  constructor
  · exact hv.trans (by dsimp only [C]; nlinarith)
  · apply (pi_norm_le_iff_of_nonneg (by dsimp only [C]; positivity : 0 ≤ C * ε)).mpr
    intro i
    exact (ha i.val).trans (by dsimp only [C]; nlinarith)

end
end krylov.Convergence
