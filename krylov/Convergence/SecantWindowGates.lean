import krylov.Convergence.SecantWindowSource
import krylov.Correction.ObservedGateAcceptance

/-!
Article: main_krylov, thm:Ip and the paragraph preceding thm:G.
Use: derive actual RFC observed defects tending to zero and acceptance of
every fixed positive threshold from genuine convergent function queries.
Source: the true segment FTC estimate and the original measured-energy
normalization. Neither window independence nor defect bounds are assumed.
-/

namespace krylov.Convergence
noncomputable section
open Set Filter Topology krylov.Methods krylov.Correction
open scoped InnerProductSpace Matrix.Norms.L2Operator NNReal
variable {p : ℕ} {α : Type*} {l : Filter α}
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The actual measured-energy normalized skew defects of any fixed-size
moving nonzero secant window tend to zero, without independence. -/
theorem source_window_defects_tendsto
    (G : E → E) (H : E → E →L[ℝ] E) (S : Set E) (hS : Convex ℝ S)
    (h₀ : (0:E)∈S) {L : ℝ≥0} (hH : LipschitzOnWith L H S)
    (hH₀ : H 0=ContinuousLinearMap.id ℝ E) (hG : ∀ z∈S,HasFDerivAt G (H z) z)
    (a b : α → Fin p → E)
    (ha : ∀ i,Tendsto (fun z=>a z i) l (𝓝 0))
    (hb : ∀ i,Tendsto (fun z=>b z i) l (𝓝 0))
    (hm : ∀ᶠ z in l,(∀ i,a z i∈S) ∧(∀ i,b z i∈S))
    (hne : ∀ᶠ z in l,∀ i,b z i-a z i≠0) :
    Tendsto (fun z=>pairDefect (fun i=>b z i-a z i) (fun i=>G (b z i)-G (a z i))) l (𝓝 0) := by
  let ε := fun z=>(L:ℝ)/2*sourceWindowRadius (a z) (b z)
  have hε : Tendsto ε l (𝓝 0) := by
    have hh := tendsto_finsetSum Finset.univ (fun i _=>(ha i).norm.add (hb i).norm)
    have hr : Tendsto (fun z=>sourceWindowRadius (a z) (b z)) l (𝓝 0) := by
      simpa only [sourceWindowRadius,norm_zero,add_zero,Finset.sum_const_zero] using hh
    simpa only [mul_zero] using hr.const_mul ((L:ℝ)/2)
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero' (g:=fun z=>(p:ℝ)*(4*ε z))
  · exact Filter.Eventually.of_forall fun _=>norm_nonneg _
  · have hsmall := (hε.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1/2))).mono fun _ h=>h.le
    filter_upwards [hm,hne,hsmall] with z hz hn hs
    apply relative_pairDefect_norm_bound _ _ hn
      (mul_nonneg (by positivity) (sourceWindowRadius_nonneg _ _)) hs
    intro i
    have hh := secant_image_endpoint_bound G H S hS h₀ hH hG _ _ (hz.1 i) (hz.2 i)
    rw [hH₀,ContinuousLinearMap.id_apply] at hh
    apply hh.trans
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact Finset.single_le_sum (fun j _=>add_nonneg (norm_nonneg (a z j)) (norm_nonneg (b z j)))
      (Finset.mem_univ i)
  · simpa only [mul_zero] using (hε.const_mul 4).const_mul (p:ℝ)

/-- Every original positive RFC defect threshold eventually accepts the
true observed secant window, under the original source assumptions. -/
theorem source_window_eventually_defect_gate
    (G : E → E) (H : E → E →L[ℝ] E) (S : Set E) (hS : Convex ℝ S)
    (h₀ : (0:E)∈S) {L : ℝ≥0} (hH : LipschitzOnWith L H S)
    (hH₀ : H 0=ContinuousLinearMap.id ℝ E) (hG : ∀ z∈S,HasFDerivAt G (H z) z)
    (a b : α → Fin p → E)
    (ha : ∀ i,Tendsto (fun z=>a z i) l (𝓝 0))
    (hb : ∀ i,Tendsto (fun z=>b z i) l (𝓝 0))
    (hm : ∀ᶠ z in l,(∀ i,a z i∈S) ∧(∀ i,b z i∈S))
    (hne : ∀ᶠ z in l,∀ i,b z i-a z i≠0) {γ : ℝ} (hγ : 0<γ) :
    ∀ᶠ z in l,‖pairDefect (fun i=>b z i-a z i) (fun i=>G (b z i)-G (a z i))‖<γ := by
  have hh := source_window_defects_tendsto G H S hS h₀ hH hH₀ hG a b ha hb hm hne
  have hn : Tendsto (fun z=>‖pairDefect (fun i=>b z i-a z i)
      (fun i=>G (b z i)-G (a z i))‖) l (𝓝 0) := by simpa only [norm_zero] using hh.norm
  exact hn.eventually (gt_mem_nhds hγ)

end
end krylov.Convergence
