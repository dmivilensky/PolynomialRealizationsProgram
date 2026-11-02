import krylov.Convergence.OrderSearchOnlyFields

/-!
Article: main_krylov, thm:D and lem:cycle-transfer, actual deferred shadows.
Use: true query points of the scalar search-only executor differ from the
genuine quadratic CG points by second order, uniformly on the original
compact full reference family. All actual histories and source bounds
come from the native bootstrap, not assumed trajectory comparisons.
Source: primitive smooth policy fields and positive scalar homogeneity.
-/
namespace krylov.Convergence
noncomputable section
open Set Metric Filter Topology krylov.Methods krylov.Reference krylov.Functions krylov.Stability krylov.Nonlinear
open scoped InnerProductSpace NNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

/-- Every actual search-only function query has its genuine compact-uniform
quadratic CG shadow, derived from primitive source and policy data.
Article: main_krylov, thm:D, DC. -/
theorem scalarSearchOnlyPoint_reference_points
    (m : ProbedMethod E) (hm : CorrectionFree m) (hc : CGConsistent m) (hh : m.Homogeneous) (T : E ≃L[ℝ] E)
    (hT : T.symm.toContinuousLinearMap.IsSymmetric)
    (f : E → ℝ) (G : E → E) (H : E → E →L[ℝ] E) (Q : E →L[ℝ] E)
    {r : ℝ} (hr : 0 < r) (hG₀ : G 0 = 0) (hH₀ : H 0 = Q)
    (hHc₀ : coordinateDerivative T H 0 = ContinuousLinearMap.id ℝ E)
    {L : ℝ≥0} (hLr : (L : ℝ) * r ≤ 1 / 2)
    (hH : LipschitzOnWith L (coordinateDerivative T H) (closedBall 0 r))
    (hF : ∀ z : E, ‖T z‖ ≤ r → HasFDerivAt f (innerSL ℝ (G z)) z)
    (hG : ∀ z : E, ‖T z‖ ≤ r → HasFDerivAt G (H z) z)
    (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v : E, v ≠ 0 → 0 < inner ℝ v (Q v))
    (N : ℕ) (K : Set E) (hK : IsCompact K)
    (hpre : ∀ g ∈ K, ∀ i < N, CG.gradient Q g i ≠ 0)
    (hs : ∀ g∈K,SmoothProbedCycleAt m 2 Q g N)
    (B : ℝ) (hB : 0 < B) :
    ∃ ε₀ C : ℝ, 0 < ε₀ ∧ 0 < C ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      ∀ u : E, ‖u‖ ≤ B → Q u ∈ K → ∀ k ≤ N,
      ‖scalarFunctionPoint m T f G r (ε • u) k - ε • fcQuadraticReferencePoint Q u k‖ ≤ C * ε ^ 2 := by
  obtain ⟨es,D,hes,hD,hboot⟩:=scalarSearchOnly_compact_bootstrap m hm hc hh T hT f G H Q
    hr hG₀ hH₀ hHc₀ hLr hH hF hG hQ hpos N K hK hpre hs B hB
  obtain ⟨δ,C,hδ,hC,hfields⟩:=compact_searchOnly_points_changes m hc Q hQ hpos N K hK hpre hs
  refine ⟨min es (δ/(D+1)),C*D+1,by positivity,by positivity,?_⟩
  intro ε hε he u hu hKu i hi
  have hp:=hboot ε hε (he.trans_le (min_le_left _ _)) u hu hKu
  let I:=scalarSearchOnlyInput m T f G H Q r ε u N
  let A:=scalarSearchOnlyOperator m T f G H r (ε • u)
  let P:=fcFiniteOperatorPath Q N I.2
  have hpath j (hj : j<N) : A j=P j := by
    dsimp only [P,fcFiniteOperatorPath]
    rw [dite_eq_left hj]
    dsimp only [I,scalarSearchOnlyInput]
    abel
  have hinit : G (ε • u)=ε • (Q u+I.1) := by
    dsimp only [I,scalarSearchOnlyInput]
    rw [add_sub_cancel,smul_smul,mul_inv_cancel₀ hε.ne',one_smul]
  have hpoint : scalarFunctionPoint m T f G r (ε • u) i=
      ε • (u+(methodRun m P P (Q u+I.1) i).displacement) := by
    rw [scalarFunctionPoint,hp.2 i hi]
    rw [methodRun_congr_prefix m A A P P _ i (fun j hj=>hpath j (hj.trans_le hi))
      (fun j hj=>hpath j (hj.trans_le hi)),hinit,methodRun_scalar m hh P P _ ε hε,
      searchOnly_scaleHistory_displacement,smul_add]
  have hsmall : ‖I‖≤δ := by
    have hε':=(lt_div_iff₀ (by positivity : 0<D+1)).mp (he.trans_le (min_le_right _ _))
    exact hp.1.trans (by nlinarith only [hε',hε])
  have hf:=hfields (Q u) hKu I.1 I.2 hsmall i hi
  have heq : scalarFunctionPoint m T f G r (ε • u) i-ε • fcQuadraticReferencePoint Q u i=
      ε • ((methodRun m P P (Q u+I.1) i).displacement-CG.displacement Q (Q u) i) := by
    rw [hpoint,fcQuadraticReferencePoint]
    module
  rw [heq,norm_smul,Real.norm_of_nonneg hε.le]
  calc
    _ ≤ ε*(C*‖I‖) := mul_le_mul_of_nonneg_left hf hε.le
    _ ≤ ε*(C*(D*ε)) := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hp.1 hC.le) hε.le
    _ ≤ (C*D+1)*ε^2 := by nlinarith only [sq_nonneg ε]

end
end krylov.Convergence
