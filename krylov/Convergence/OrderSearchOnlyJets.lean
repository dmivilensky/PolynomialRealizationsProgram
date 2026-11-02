import krylov.Convergence.OrderSearchOnlyReference
import krylov.Functions.MetricFCInputJet

/-!
Article: main_krylov, thm:D and lem:cycle-transfer, genuine deferred source jets.
Use: actual scalar search-only Hessian averages have the true third-derivative
jet at their genuine quadratic CG midpoints, uniformly on a compact family.
No query enclosure, trajectory shadow or desired response jet is assumed.
Source: actual native bootstrap, uniform Bochner midpoint differentiation
and the derived quadratic CG shadow.
-/
namespace krylov.Convergence
noncomputable section
open Set Metric Filter Topology krylov.Methods krylov.Reference krylov.Functions krylov.Nonlinear
  chebyshev1.Nonlinear
open scoped InnerProductSpace NNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

/-- The real third derivative supplies the genuine first source jet of
all actual search-only segment averages. Article: thm:D, DC. -/
theorem scalarSearchOnlyOperator_reference_jet
    (method : ProbedMethod E) (hm : CorrectionFree method) (hc : CGConsistent method) (hh : method.Homogeneous) (T : E ≃L[ℝ] E)
    (hT : T.symm.toContinuousLinearMap.IsSymmetric)
    (f : E → ℝ) (G : E → E) (H : E → E →L[ℝ] E) (Q : E →L[ℝ] E)
    (D : E →L[ℝ] E →L[ℝ] E) (hD : HasFDerivAt H D 0)
    {r : ℝ} (hr : 0 < r) (hG₀ : G 0 = 0) (hH₀ : H 0 = Q)
    (hHc₀ : coordinateDerivative T H 0 = ContinuousLinearMap.id ℝ E)
    {L : ℝ≥0} (hLr : (L : ℝ) * r ≤ 1 / 2)
    (hH : LipschitzOnWith L (coordinateDerivative T H) (closedBall 0 r))
    (hF : ∀ z : E, ‖T z‖ ≤ r → HasFDerivAt f (innerSL ℝ (G z)) z)
    (hG : ∀ z : E, ‖T z‖ ≤ r → HasFDerivAt G (H z) z)
    (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v : E, v ≠ 0 → 0 < inner ℝ v (Q v))
    (N : ℕ) (K : Set E) (hK : IsCompact K)
    (hpre : ∀ g ∈ K, ∀ i < N, CG.gradient Q g i ≠ 0)
    (hs : ∀ g∈K,SmoothProbedCycleAt method 2 Q g N)
    (B : ℝ) (hB : 0 < B) :
    ∀ η : ℝ, 0 < η → ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      ∀ u : E, ‖u‖ ≤ B → Q u ∈ K → ∀ i : ℕ, i < N →
      ‖scalarSearchOnlyOperator method T f G H r (ε • u) i - Q -
        ε • D (fcReferenceMidpoint Q u i)‖ ≤ η * ε := by
  intro η hη
  let J := ‖T.toContinuousLinearMap‖
  let M := ‖T.symm.toContinuousLinearMap‖ * Real.sqrt 3 * J * B + 1
  have hJ : 0 ≤ J := norm_nonneg _
  have hM : 0 < M := by dsimp only [M]; positivity
  obtain ⟨ρ, hρ, _, hrem⟩ := averagedHessian_midpoint_expansion H D
    (by positivity : 0 < r / (‖T.toContinuousLinearMap‖ + 1))
    (metric_hessian_continuous_ball T H hH) hD (η / (2 * M)) (by positivity)
  obtain ⟨εp, C, hεp, hC, hpoints⟩ := scalarSearchOnlyPoint_reference_points method hm hc hh T hT f G H Q hr hG₀ hH₀ hHc₀
    hLr hH hF hG hQ hpos N K hK hpre hs B hB
  let F := ‖D‖ * C
  have hF₀ : 0 ≤ F := by dsimp only [F]; positivity
  let ε₀ := min εp (min (r / (4 * (J * B + 1))) (min (ρ / M) (η / (2 * (F + 1)))))
  have hε₀ : 0 < ε₀ := by dsimp only [ε₀]; positivity
  refine ⟨ε₀, hε₀, ?_⟩
  intro ε hε he u hu hKu i hi
  let x := scalarFunctionPoint method T f G r (ε • u)
  let a := x i
  let b := x (i + 1)
  let m := a + (1 / 2 : ℝ) • (b - a)
  let mq := fcReferenceMidpoint Q u i
  have huT : ‖T u‖ ≤ J * B :=
    (T.toContinuousLinearMap.le_opNorm u).trans (mul_le_mul_of_nonneg_left hu hJ)
  have hx₀ : ‖T (ε • u)‖ < r / 2 := by
    rw [map_smul, norm_smul, Real.norm_of_nonneg hε.le]
    have he' := (lt_div_iff₀ (by positivity : 0 < 4 * (J * B + 1))).mp
      (he.trans_le ((min_le_right _ _).trans (min_le_left _ _)))
    have hb := mul_le_mul_of_nonneg_left huT hε.le
    nlinarith
  have hloc := scalarSearchOnlyPoint_localization method hm T hT f G H hr hG₀ hHc₀ hLr hH hF hG
    (ε • u) hx₀
  have hb j : ‖x j‖ ≤ M * ε := by
    calc
      _ = ‖T.symm (T (x j))‖ := by rw [T.symm_apply_apply]
      _ ≤ ‖T.symm.toContinuousLinearMap‖ * ‖T (x j)‖ := T.symm.toContinuousLinearMap.le_opNorm _
      _ ≤ ‖T.symm.toContinuousLinearMap‖ * (Real.sqrt 3 * ‖T (ε • u)‖) := by
        exact mul_le_mul_of_nonneg_left (hloc j).1 (norm_nonneg _)
      _ ≤ M * ε := by
        rw [map_smul, norm_smul, Real.norm_of_nonneg hε.le]
        have hm := mul_le_mul_of_nonneg_left huT
          (by positivity : 0 ≤ ‖T.symm.toContinuousLinearMap‖ * Real.sqrt 3 * ε)
        dsimp only [M]
        nlinarith
  have hseg t (ht : t ∈ Icc (0 : ℝ) 1) : ‖a + t • (b - a)‖ ≤ M * ε := by
    have ha : a ∈ closedBall (0 : E) (M * ε) := by
      simpa only [mem_closedBall, dist_zero_right] using hb i
    have hb' : a + (b - a) ∈ closedBall (0 : E) (M * ε) := by
      simpa only [add_sub_cancel, mem_closedBall, dist_zero_right] using hb (i + 1)
    simpa only [mem_closedBall, dist_zero_right] using
      (convex_closedBall (0 : E) (M * ε)).add_smul_mem ha hb' ht
  have hρε : M * ε < ρ := by
    have he' := (lt_div_iff₀ hM).mp
      (he.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))
    nlinarith
  have hbase : ‖averagedDerivative H a (b - a) - Q - D m‖ ≤ η / 2 * ε := by
    have hs := hrem (M * ε) (by positivity) hρε a (b - a) hseg
    rw [hH₀] at hs
    exact hs.trans_eq (by field_simp)
  have hmid : ‖m - ε • mq‖ ≤ C * ε ^ 2 := by
    have hp j (hj : j ≤ N) := hpoints ε hε (he.trans_le (min_le_left _ _)) u hu hKu j hj
    have hm := midpoint_error_bound a b (ε • fcQuadraticReferencePoint Q u i)
      (ε • fcQuadraticReferencePoint Q u (i + 1))
    have heq : m - ε • mq = (a + (1 / 2 : ℝ) • (b - a)) -
        (ε • fcQuadraticReferencePoint Q u i + (1 / 2 : ℝ) •
          (ε • fcQuadraticReferencePoint Q u (i + 1) - ε • fcQuadraticReferencePoint Q u i)) := by
      dsimp only [m, mq, fcReferenceMidpoint]
      rw [← fcQuadraticReferencePoint_step Q u i]
      module
    rw [heq]
    exact hm.trans (by nlinarith only [hp i (by omega), hp (i + 1) (by omega)])
  have hs : ‖D m - ε • D mq‖ ≤ η / 2 * ε := by
    rw [← map_smul, ← map_sub]
    have hbound := (D.le_opNorm _).trans (mul_le_mul_of_nonneg_left hmid (norm_nonneg _))
    have he' := (lt_div_iff₀ (by positivity : 0 < 2 * (F + 1))).mp
      (he.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))))
    apply hbound.trans
    rw [show ‖D‖ * (C * ε ^ 2) = F * ε ^ 2 by dsimp only [F]; ring]
    nlinarith [mul_le_mul_of_nonneg_right he'.le hε.le]
  change ‖averagedDerivative H a (b - a) - Q - ε • D mq‖ ≤ η * ε
  have heq : averagedDerivative H a (b - a) - Q - ε • D mq =
      (averagedDerivative H a (b - a) - Q - D m) + (D m - ε • D mq) := by abel
  rw [heq]
  exact (norm_add_le _ _).trans ((add_le_add hbase hs).trans_eq (by ring))


/-- Every actual finite source coordinate has its genuine uniform first jet.
Article: main_krylov, thm:D, native DC. -/
theorem scalarSearchOnlyInput_reference_jet
    (method : ProbedMethod E) (hm : CorrectionFree method) (hc : CGConsistent method) (hh : method.Homogeneous) (T : E ≃L[ℝ] E)
    (hT : T.symm.toContinuousLinearMap.IsSymmetric)
    (f : E → ℝ) (G : E → E) (H : E → E →L[ℝ] E) (Q : E →L[ℝ] E)
    (D : E →L[ℝ] E →L[ℝ] E) (hD : HasFDerivAt H D 0)
    {r : ℝ} (hr : 0<r) (hG₀ : G 0=0) (hH₀ : H 0=Q)
    (hHc₀ : coordinateDerivative T H 0=ContinuousLinearMap.id ℝ E)
    {L : ℝ≥0} (hLr : (L : ℝ)*r≤1/2)
    (hH : LipschitzOnWith L (coordinateDerivative T H) (closedBall 0 r))
    (hF : ∀ z : E, ‖T z‖≤r → HasFDerivAt f (innerSL ℝ (G z)) z)
    (hG : ∀ z : E, ‖T z‖≤r → HasFDerivAt G (H z) z)
    (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v : E, v≠0 → 0 < inner ℝ v (Q v))
    (N : ℕ) (K : Set E) (hK : IsCompact K)
    (hpre : ∀ g∈K, ∀ i<N, CG.gradient Q g i≠0)
    (hs : ∀ g∈K,SmoothProbedCycleAt method 2 Q g N)
    (B : ℝ) (hB : 0<B) :
    ∀ η : ℝ, 0<η → ∃ ε₀ : ℝ, 0<ε₀ ∧ ∀ ε : ℝ, 0<ε → ε<ε₀ →
      ∀ u : E, ‖u‖≤B → Q u∈K →
        ‖scalarSearchOnlyInput method T f G H Q r ε u N-ε • metricFCReferenceInputJet Q D u N‖≤η*ε := by
  have hphys (z : E) (hz : z∈ball 0 (r/(‖T.toContinuousLinearMap‖+1))) :
      HasFDerivAt G (H z) z := by
    apply hG z
    have hz' : ‖z‖<r/(‖T.toContinuousLinearMap‖+1) := by simpa only [mem_ball,dist_zero_right] using hz
    have hh := (lt_div_iff₀ (by positivity : 0<‖T.toContinuousLinearMap‖+1)).mp hz'
    exact (T.toContinuousLinearMap.le_opNorm z).trans (by nlinarith only [hh,norm_nonneg z])
  intro η hη
  obtain ⟨eg,heg,hgj⟩ := normalizedGradient_reference_jet G H Q D
    (by positivity : 0<r/(‖T.toContinuousLinearMap‖+1)) hG₀ hH₀
    (metric_hessian_continuous_ball T H hH) hD hphys B hB η hη
  obtain ⟨ea,hea,haj⟩ := scalarSearchOnlyOperator_reference_jet method hm hc hh T hT f G H Q D hD hr hG₀ hH₀ hHc₀
    hLr hH hF hG hQ hpos N K hK hpre hs B hB η hη
  refine ⟨min eg ea,lt_min heg hea,?_⟩
  intro ε hε he u hu hKu
  change max ‖ε⁻¹ • G (ε • u)-Q u-ε • ((1/2 : ℝ) • D u u)‖
    ‖fun i : Fin N => scalarSearchOnlyOperator method T f G H r (ε • u) i.val-Q-
      ε • D (fcReferenceMidpoint Q u i.val)‖≤η*ε
  apply max_le
  · exact hgj ε hε (he.trans_le (min_le_left _ _)) u hu
  · apply (pi_norm_le_iff_of_nonneg (by positivity : 0≤η*ε)).mpr
    intro i
    exact haj ε hε (he.trans_le (min_le_right _ _)) u hu hKu i.val i.isLt

end
end krylov.Convergence
