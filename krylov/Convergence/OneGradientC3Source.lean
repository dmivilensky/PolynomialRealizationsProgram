import Mathlib.Analysis.Calculus.MeanValue

/-!
Article: main_krylov, thm:V and prop:EL, original C-three source regularity.
Use: derive the Hessian Lipschitz neighborhood needed by actual native
localization from a genuine continuous third derivative, with no additional
Lipschitz-third assumption in the little-o leading formula.
Source: continuity of the real derivative and the convex mean-value theorem.
-/
namespace krylov.Convergence
noncomputable section
open Set Metric Filter Topology
open scoped NNReal
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A genuine continuous third derivative gives a real local Hessian
Lipschitz constant. This does not assume Lip D3. Article: thm:V, prop:EL. -/
theorem exists_hessian_lipschitz_ball
    (H : E → F) (D : E → E →L[ℝ] F) {r : ℝ} (hr : 0<r)
    (hD : ∀ z∈ball 0 r,HasFDerivAt H (D z) z) (hDc : ContinuousAt D 0) :
    ∃ s : ℝ,∃ L : ℝ≥0,0<s ∧s≤r ∧LipschitzOnWith L H (ball 0 s) := by
  let L : ℝ≥0 := ⟨‖D 0‖+1,by positivity⟩
  have hbound : ∀ᶠ z in 𝓝 (0:E),‖D z‖≤(L:ℝ) :=
    (hDc.norm.eventually (gt_mem_nhds (show ‖D 0‖<(L:ℝ) by change ‖D 0‖<‖D 0‖+1;linarith))).mono
      (fun _ hz=>hz.le)
  obtain ⟨δ,hδ,hδbound⟩ := Metric.eventually_nhds_iff.mp hbound
  refine ⟨min r δ,L,lt_min hr hδ,min_le_left _ _,?_⟩
  apply Convex.lipschitzOnWith_of_nnnorm_hasFDerivWithin_le
    (fun z hz=>(hD z (ball_subset_ball (min_le_left _ _) hz)).hasFDerivWithinAt) _ (convex_ball _ _)
  intro z hz
  apply NNReal.coe_le_coe.mp
  exact hδbound (ball_subset_ball (min_le_right _ _) hz)

end
end krylov.Convergence
