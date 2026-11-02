import krylov.Convergence.SS1FOriginalRegularity
import krylov.Convergence.WindowFullValueExecution

/-!
Article: main_krylov, (S), thm:ss1F and cor:xrF.
Use: derive (S) for the actual endpoint-covector policy from genuine
convergent secants. No split-admissibility conclusion is a source field.
Source: the local secant FTC and the proved oblique projection estimate.
-/
namespace krylov.Convergence
noncomputable section
open Matrix Set Filter Topology krylov.Functions krylov.Methods
open scoped InnerProductSpace Matrix.Norms.L2Operator NNReal
variable {n : ℕ}
set_option maxHeartbeats 800000

/-- Actual model-metric splits eventually satisfy (S), with an absolute
constant, on any genuinely convergent independent source window. -/
theorem observed_split_eventually_admissible
    (G : EuclideanSpace ℝ (Fin (n+1)) → EuclideanSpace ℝ (Fin (n+1)))
    (H : EuclideanSpace ℝ (Fin (n+1)) → EuclideanSpace ℝ (Fin (n+1)) →L[ℝ]
      EuclideanSpace ℝ (Fin (n+1)))
    (S : Set (EuclideanSpace ℝ (Fin (n+1)))) (hS : Convex ℝ S)
    (h₀ : (0:EuclideanSpace ℝ (Fin (n+1)))∈S) (hnbhd : S∈𝓝 0)
    {L : ℝ≥0} (hH : LipschitzOnWith L H S) (hH₀ : H 0=ContinuousLinearMap.id ℝ _)
    (hG : ∀ z∈S,HasFDerivAt G (H z) z)
    (x : ℕ → EuclideanSpace ℝ (Fin (n+1))) (hconv : Tendsto x atTop (𝓝 0))
    (hs : ∀ᶠ k in atTop,∀ i : Fin (n+1),windowStep x k i≠0) :
    ∀ᶠ k in atTop,∀ i : Fin (n+1),
      ‖splitRemainder (x (k+i.val)) (windowStep x k i) (x (k+n+1))
        (ss1FObservedSplit G (fun j=>x (k+j.val)) i)‖≤
      3*‖x (k+n+1)-x (k+i.val+1)‖ := by
  have ha (i : Fin (n+1)) : Tendsto (fun k=>x (k+i.val)) atTop (𝓝 0) :=
    hconv.comp (tendsto_add_atTop_nat i.val)
  have hb (i : Fin (n+1)) : Tendsto (fun k=>x (k+i.val+1)) atTop (𝓝 0) := by
    simpa only [Function.comp_def,Nat.add_assoc] using hconv.comp (tendsto_add_atTop_nat (i.val+1))
  have hm : ∀ᶠ k in atTop,∀ i : Fin (n+1),x (k+i.val)∈S ∧x (k+i.val+1)∈S :=
    Filter.eventually_all.mpr (fun i=>((ha i).eventually hnbhd).and ((hb i).eventually hnbhd))
  have he : ∀ᶠ k in atTop,∀ i : Fin (n+1),
      (L:ℝ)/2*(‖x (k+i.val)‖+‖x (k+i.val+1)‖)≤1/2 := by
    apply Filter.eventually_all.mpr
    intro i
    have ht : Tendsto (fun k=>(L:ℝ)/2*(‖x (k+i.val)‖+‖x (k+i.val+1)‖)) atTop (𝓝 0) := by
      simpa only [norm_zero,add_zero,mul_zero] using ((ha i).norm.add (hb i).norm).const_mul ((L:ℝ)/2)
    exact (ht.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1/2))).mono fun _ h=>h.le
  filter_upwards [hm,he,hs] with k hk hε hsk i
  have hy := secant_image_endpoint_bound G H S hS h₀ hH hG _ _ (hk i).1 (hk i).2
  rw [hH₀,ContinuousLinearMap.id_apply] at hy
  have hy' : ‖G (x (k+i.val+1))-G (x (k+i.val))-windowStep x k i‖≤(1/2:ℝ)*‖windowStep x k i‖ :=
    hy.trans (mul_le_mul_of_nonneg_right (hε i) (norm_nonneg _))
  have hh := (covectorSplit_near_identity_admissible (x (k+i.val)) (windowStep x k i)
    (x (k+n+1)) (G (x (k+i.val+1))-G (x (k+i.val))) (hsk i)
    (by norm_num : (0:ℝ)≤1/2) (by norm_num : (1/2:ℝ)<1) hy').2
  simpa only [ss1FObservedSplit,Fin.val_succ,Fin.val_castSucc,Fin.val_last,
    windowStep,add_sub_cancel,Nat.add_assoc,show ((1+(1/2:ℝ))/(1-1/2))=3 by norm_num] using hh

end
end krylov.Convergence
