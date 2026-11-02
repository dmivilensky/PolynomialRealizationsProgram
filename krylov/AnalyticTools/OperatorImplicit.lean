import krylov.AnalyticTools.Implicit

/-!
Article: main_krylov, apC:prop:LV, analytic saddle background.
Use: solve an actual nonlinear integral equation w=L(N(z,w)) analytically when
the derivative of N in w vanishes at the base point. The bounded linear map L
can be the weighted dilation inverse of a regular-singular differential operator.
Source: the analytic implicit function theorem and the identity derivative in w.
-/

namespace krylov.AnalyticTools
noncomputable section
open Filter
open scoped Topology

/-- Analytic, locally unique solutions to a Banach-space integral equation
whose nonlinear part has zero derivative in the unknown at the base point. -/
theorem exists_analytic_operator_fixedPoint
    {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
    (L : G →L[ℝ] F) (N : E × F → G)
    (hN : AnalyticAt ℝ N (0, 0)) (hzero : N (0, 0) = 0)
    (A : E →L[ℝ] G) (hd : HasFDerivAt N (A.coprod 0) (0, 0)) :
    ∃ w : E → F, AnalyticAt ℝ w 0 ∧ w 0 = 0 ∧
      (∀ᶠ z in 𝓝 (0 : E), w z = L (N (z, w z))) ∧
      ∀ᶠ p in 𝓝 ((0 : E), (0 : F)), p.2 = L (N p) → p.2 = w p.1 := by
  let Q : E × F → F := fun p ↦ p.2 - L (N p)
  have hQ : AnalyticAt ℝ Q (0, 0) :=
    analyticAt_snd.sub ((L.analyticAt _).comp hN)
  have hQd : HasFDerivAt Q
      ((-(L.comp A)).coprod (ContinuousLinearMap.id ℝ F)) (0, 0) := by
    have h := (hasFDerivAt_snd (𝕜 := ℝ) (p := ((0 : E), (0 : F)))).sub
      (L.hasFDerivAt.comp ((0 : E), (0 : F)) hd)
    convert h using 1
    · rfl
    · apply ContinuousLinearMap.ext
      intro p
      simp [ContinuousLinearMap.coprod_apply, sub_eq_add_neg, add_comm]
  obtain ⟨w, hw, hw₀, heq, huniq⟩ := exists_analytic_implicit hQ
    (by simp [Q, hzero]) (-(L.comp A)) (ContinuousLinearEquiv.refl ℝ F) hQd
  refine ⟨w, hw, hw₀, ?_, ?_⟩
  · filter_upwards [heq] with z hz
    exact sub_eq_zero.mp hz
  · filter_upwards [huniq] with p hp heq
    exact hp (sub_eq_zero.mpr heq)

end
end krylov.AnalyticTools
