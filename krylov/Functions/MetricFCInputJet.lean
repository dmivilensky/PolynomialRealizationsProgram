import krylov.Functions.MetricFCLeadingSource
import krylov.Functions.NormalizedGradientJet

/-!
Article: main_krylov, lem:cycle-transfer, the complete genuine native FC jet.
Use: derive both actual normalized initial-gradient and actual physical
secant coordinates of the independent finite operator source, uniformly on
the original compact nondegenerate reference family.
Source: actual gradient FTC and true native query midpoint localization.
-/

namespace krylov.Functions
noncomputable section
open Set Metric krylov.Methods krylov.Nonlinear krylov.Reference
open scoped InnerProductSpace NNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

/-- The complete first jet of the genuine finite FC input source, including
its actual normalized starting gradient. Article: main_krylov, lem:cycle-transfer. -/
def metricFCReferenceInputJet (Q : E →L[ℝ] E) (D : E →L[ℝ] E →L[ℝ] E)
    (u : E) (N : ℕ) : E × (Fin N → E →L[ℝ] E) :=
  ((1/2 : ℝ) • D u u, fun i => D (fcReferenceMidpoint Q u i.val))

/-- Every actual normalized FC source coordinate has its genuine true-D
first jet, with a common remainder radius for the whole compact family.
Article: main_krylov, lem:cycle-transfer, complete native source jet. -/
theorem metricFCInput_reference_jet (T : E ≃L[ℝ] E)
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
    (B : ℝ) (hB : 0<B) :
    ∀ η : ℝ, 0<η → ∃ ε₀ : ℝ, 0<ε₀ ∧ ∀ ε : ℝ, 0<ε → ε<ε₀ →
      ∀ u : E, ‖u‖≤B → Q u∈K →
        ‖metricFCInput T f G H Q r ε u N-ε • metricFCReferenceInputJet Q D u N‖≤η*ε := by
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
  obtain ⟨ea,hea,haj⟩ := metricFCOperator_reference_jet T hT f G H Q D hD hr hG₀ hH₀ hHc₀
    hLr hH hF hG hQ hpos N K hK hpre B hB η hη
  refine ⟨min eg ea,lt_min heg hea,?_⟩
  intro ε hε he u hu hKu
  change max ‖ε⁻¹ • G (ε • u)-Q u-ε • ((1/2 : ℝ) • D u u)‖
    ‖fun i : Fin N => metricFCOperator T f G H fullMemory r (ε • u) i.val-Q-
      ε • D (fcReferenceMidpoint Q u i.val)‖≤η*ε
  apply max_le
  · exact hgj ε hε (he.trans_le (min_le_left _ _)) u hu
  · apply (pi_norm_le_iff_of_nonneg (by positivity : 0≤η*ε)).mpr
    intro i
    exact haj ε hε (he.trans_le (min_le_right _ _)) u hu hKu i.val i.isLt

end
end krylov.Functions
