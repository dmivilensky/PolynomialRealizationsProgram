import krylov.Convergence.RestartFrozenExecution

/-!
Article: main_krylov, thm:D, full actual FC plus k frozen final corrections.
Use: prove the printed k+2 source degree for the genuine scalar-function
queries. Full measured model conditioning and all intermediate query bounds
are conclusions derived from the full CG reference and primitive local
function data. The same observed model is retained at every correction.
Source: native FC quadratic termination, actual frozen-model regularity,
and the proved invariant-ball frozen-query induction.
-/
namespace krylov.Convergence
noncomputable section
open Matrix Set Metric krylov.Methods krylov.Reference krylov.Functions krylov.Nonlinear
open scoped InnerProductSpace NNReal Matrix.Norms.L2Operator
variable {k : ℕ}

/-- Every genuine final frozen correction raises the actual full-cycle
error degree by one; no real output bound or measured-model hypothesis is
supplied. Article: main_krylov, thm:D, FC with k final corrections. -/
theorem nativeFC_frozen_corrections_degree
    (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (hb : base.PosDef)
    (T : EuclideanSpace ℝ (Fin (k+1)) ≃L[ℝ] EuclideanSpace ℝ (Fin (k+1)))
    (hT : T.symm.toContinuousLinearMap.IsSymmetric)
    (f : EuclideanSpace ℝ (Fin (k+1)) → ℝ)
    (G : EuclideanSpace ℝ (Fin (k+1)) → EuclideanSpace ℝ (Fin (k+1)))
    (H : EuclideanSpace ℝ (Fin (k+1)) → EuclideanSpace ℝ (Fin (k+1)) →L[ℝ] EuclideanSpace ℝ (Fin (k+1)))
    {r : ℝ} (hr : 0<r) (hG₀ : G 0=0) (hH₀ : H 0=cgOperator base)
    (hHc₀ : coordinateDerivative T H 0=ContinuousLinearMap.id ℝ _)
    {L : ℝ≥0} (hLr : (L:ℝ)*r≤1/2)
    (hH : LipschitzOnWith L (coordinateDerivative T H) (closedBall 0 r))
    (hF : ∀ z,‖T z‖≤r → HasFDerivAt f (innerSL ℝ (G z)) z)
    (hG : ∀ z,‖T z‖≤r → HasFDerivAt G (H z) z)
    (K : Set (EuclideanSpace ℝ (Fin (k+1)))) (hK : IsCompact K)
    (hpre : ∀ g∈K,∀ i<k+1,CG.gradient (cgOperator base) g i≠0)
    (R : ℝ) (hR : 0<R) :
    ∃ ep B C : ℝ,0<ep ∧0<B ∧0<C ∧∀ ε : ℝ,0<ε → ε<ep →
      ∀ u,‖u‖≤R →cgOperator base u∈K →∀ j : ℕ,
      ‖T (nativeFCFrozenPoints T f G r (ε • u) j)‖≤B*C^j*ε^(j+2) ∧
        ‖T (nativeFCFrozenPoints T f G r (ε • u) j)‖<r := by
  obtain ⟨em,Cm,J,hem,hCm,hJ,hmodel⟩ := nativeFC_frozen_model_bounds base hb T hT f G H
    hr hG₀ hH₀ hHc₀ hLr hH hF hG K hK hpre R hR
  obtain ⟨eq,Cq,heq,hCq,hquadratic⟩ := nativeFC_error_quadratic base hb T hT f G H
    hr hG₀ hH₀ hHc₀ hLr hH hF hG K hK hpre R hR
  let B := ‖T.symm.toContinuousLinearMap‖*Cq+1
  have hB : 0<B := by dsimp only [B]; positivity
  obtain ⟨ef,C,hef,hC,hdegree⟩ := frozenModelPoints_source_degree base T G H hr hG₀ hH₀ hH hG
    B Cm J hB hCm.le hJ
  obtain ⟨ei,Di,hei,_,hinput⟩ := metricFCInput_bound T hT f G H (cgOperator base)
    hr hG₀ hH₀ hHc₀ hLr hH hF hG R hR
  refine ⟨min em (min eq (min ef ei)),‖T.toContinuousLinearMap‖*B+1,C,
    by positivity,by positivity,hC,?_⟩
  intro ε hε he u hu hKu
  have hmodels := hmodel ε hε (he.trans_le (min_le_left _ _)) u hu hKu
  have hquad := hquadratic ε hε (he.trans_le ((min_le_right _ _).trans (min_le_left _ _))) u hu hKu
  have hloc := (hinput ε hε
    (he.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))) u hu).1
  obtain ⟨hs,_,hM⟩ := nativeFCFrozen_observations T hT f G H
    hr hG₀ hHc₀ hLr hH hF hG (ε • u) hloc
  have hstepUnit : IsUnit (windowMatrix (nativeFCFrozenSteps T f G r (ε • u))).det := by
    rw [hs]
    exact hmodels.1
  have hx : ‖metricFCPoint T f G fullMemory r (ε • u) (k+1)‖≤B*ε^2 := by
    have hh := T.symm.toContinuousLinearMap.le_opNorm
      (T (metricFCPoint T f G fullMemory r (ε • u) (k+1)))
    simp only [ContinuousLinearEquiv.coe_coe,T.symm_apply_apply] at hh
    exact hh.trans ((mul_le_mul_of_nonneg_left hquad (norm_nonneg _)).trans (by
      dsimp only [B]
      nlinarith only [sq_nonneg ε]))
  have hp := hdegree ε hε
    (he.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))
    (nativeFCFrozenMatrix T f G r (ε • u))
    (by rw [hM]; exact hmodels.2.1) (by rw [hM]; exact hmodels.2.2.1)
    (by rw [hM]; exact hmodels.2.2.2)
    (metricFCPoint T f G fullMemory r (ε • u) (k+1)) hx
  intro j
  rw [nativeFCFrozenPoints_eq T f G r (ε • u) hstepUnit]
  refine ⟨?_,(hp j).2⟩
  have hn := (T.toContinuousLinearMap.le_opNorm _).trans
    (mul_le_mul_of_nonneg_left (hp j).1 (norm_nonneg _))
  exact hn.trans (by nlinarith only [mul_nonneg (pow_nonneg hC.le j) (pow_nonneg hε.le (j+2))])

end
end krylov.Convergence
