import krylov.Convergence.SlidingFCSharpSource
import krylov.Convergence.SlidingFCRate

/-!
Article: main_krylov, thm:G, extra-superlinear coefficient L_H/2.
Use: close the sharpened original estimate for the literal sliding FC
executor. Source: the unique oldest/next staircase pair, the automatic
orthonormal-frame limit, and the genuine radial gradient Taylor estimate.
All other true pair contributions are derived lower order. Zero errors
are included; no division by an error or independence assumption occurs.
-/
namespace krylov.Convergence
noncomputable section
open Matrix Set Filter Topology Asymptotics krylov.Methods krylov.Functions
open scoped InnerProductSpace Matrix.Norms.L2Operator NNReal
variable {n : ℕ}
set_option maxHeartbeats 1200000

/-- A quantitative neighbourhood of the printed half coefficient, on the
actual superlinear sliding FC trajectory. -/
theorem slidingFCSequence_half_product_aux
    (f : EuclideanSpace ℝ (Fin (n+2)) → ℝ)
    (G : EuclideanSpace ℝ (Fin (n+2)) → EuclideanSpace ℝ (Fin (n+2)))
    (H : EuclideanSpace ℝ (Fin (n+2)) → EuclideanSpace ℝ (Fin (n+2)) →L[ℝ]
      EuclideanSpace ℝ (Fin (n+2)))
    {r : ℝ} (hr : 0<r) (hG₀ : G 0=0) (hH₀ : H 0=ContinuousLinearMap.id ℝ _)
    {L : ℝ≥0} (hLr : (L:ℝ)*r≤1/2)
    (hH : LipschitzOnWith L H (Metric.closedBall 0 r))
    (hf : ∀ z∈Metric.closedBall (0:EuclideanSpace ℝ (Fin (n+2))) r,
      HasFDerivAt f (innerSL ℝ (G z)) z)
    (hG : ∀ z∈Metric.closedBall (0:EuclideanSpace ℝ (Fin (n+2))) r,HasFDerivAt G (H z) z)
    (seed : Fin (n+2) → EuclideanSpace ℝ (Fin (n+2)))
    (hconv : Tendsto (slidingFCSequence f G r seed) atTop (𝓝 0))
    (hsolve : ∀ᶠ k in atTop,IsUnit (slidingFCSolveMatrix (n:=n) G (slidingFCSequence f G r seed) k).det)
    (hs : (fun k=>slidingFCSequence f G r seed (k+1))=o[atTop]
      (fun k=>‖slidingFCSequence f G r seed k‖))
    {δ : ℝ} (hδ : 0<δ) :
    ∀ᶠ k in atTop,‖slidingFCSequence f G r seed (k+n+2)‖≤
      ((1+δ)^2*((L:ℝ)/2*(1+δ)^3+δ))*
        ‖slidingFCSequence f G r seed k‖*‖slidingFCSequence f G r seed (k+1)‖ := by
  let x := slidingFCSequence f G r seed
  let θ := 1+δ
  have hθ : 0<θ := by dsimp only [θ];linarith
  let V := fun k=>windowMatrix (unitWindow (windowStep (n:=n+2) x k))
  have hframe := slidingFCSequence_frame_conditioning f G H hr hH₀ hLr hH hf hG seed hconv hsolve
  have hinv : ∀ᶠ k in atTop,‖(V k)⁻¹‖≤θ :=
    (hframe.2.2.eventually (gt_mem_nhds (by dsimp only [θ];linarith : (1:ℝ)<θ))).mono fun _ h=>h.le
  have hsearch := slidingFCSequence_eventually_chord f G H hr hH₀ hLr hH hf hG seed hconv
  have hconj := slidingFC_full_window_conjugate f G x r hsolve hsearch
  have hline := slidingFCSequence_step_stationary f G H hr hG₀ hH₀ hLr hH hf hG seed hconv
  have hlines : ∀ᶠ k in atTop,∀ j : Fin (n+2),
      inner ℝ (x (k+j.val+1)-x (k+j.val)) (G (x (k+j.val+1)))=0 :=
    Filter.eventually_all.mpr fun j=>(tendsto_add_atTop_nat j.val).eventually hline
  have hmem : ∀ᶠ k in atTop,∀ j : Fin (n+3),‖x (k+j.val)‖<r := by
    apply Filter.eventually_all.mpr
    intro j
    have ht : Tendsto (fun k=>‖x (k+j.val)‖) atTop (𝓝 0) := by
      simpa only [x,Function.comp_def,norm_zero] using (hconv.comp (tendsto_add_atTop_nat j.val)).norm
    exact ht.eventually (gt_mem_nhds hr)
  have hsmall : ∀ᶠ k in atTop,θ*((L:ℝ)/2*‖x (k+n+2)‖)≤δ := by
    have hh : Tendsto (fun k=>θ*((L:ℝ)/2*‖x (k+n+2)‖)) atTop (𝓝 0) := by
      have ht := (hconv.comp (tendsto_add_atTop_nat (n+2))).norm
      simpa only [x,Function.comp_def,norm_zero,mul_zero,Nat.add_assoc] using (ht.const_mul ((L:ℝ)/2)).const_mul θ
    exact (hh.eventually (gt_mem_nhds hδ)).mono fun _ h=>h.le
  have he : ∀ᶠ k in atTop,‖x (k+1)‖≤δ*‖x k‖ := by
    simpa only [norm_norm] using hs.def hδ
  have he' := (tendsto_add_atTop_nat 1).eventually he
  have hmass := (fcPathNewerMass_littleo (n:=n) H (Metric.closedBall 0 r) (convex_closedBall _ _)
    (Metric.closedBall_mem_nhds (0:EuclideanSpace ℝ (Fin (n+2))) hr) hH x hconv hs).def hδ
  filter_upwards [hframe.2.1,hinv,hconj,hlines,hmem,hsmall,he,he',hmass]
    with k hu hi hc hl hm hsm he₀ he₁ hmass
  have hstep₀ : ‖x (k+1)-x k‖≤θ*‖x k‖ := by
    have hh := (norm_sub_le (x (k+1)) (x k)).trans (add_le_add he₀ le_rfl)
    dsimp only [θ];nlinarith only [hh]
  have hstep₁ : ‖x (k+2)-x (k+1)‖≤θ*‖x (k+1)‖ := by
    have hh := (norm_sub_le (x (k+2)) (x (k+1))).trans
      (add_le_add (by simpa only [show k+1+1=k+2 by omega] using he₁) le_rfl)
    dsimp only [θ];nlinarith only [hh]
  have hsum : ‖x (k+1)-x k‖+‖x (k+2)-x (k+1)‖≤θ^2*‖x k‖ := by
    have hb := hstep₁.trans (mul_le_mul_of_nonneg_left he₀ hθ.le)
    have hh := add_le_add hstep₀ hb
    dsimp only [θ] at hh ⊢
    nlinarith only [hh]
  have hmass' : fcPathNewerMass (n:=n) H x k≤δ*‖x k‖*‖x (k+1)‖ := by
    have hh := (le_abs_self (fcPathNewerMass (n:=n) H x k)).trans hmass
    simpa only [Real.norm_eq_abs,abs_mul,abs_norm,mul_assoc] using hh
  have hsrc := source_fc_sharp_path_residual f G H hH hf hG x k
    (fun j hj=>hm ⟨j,by omega⟩) (fun j hj=>hl ⟨j,by omega⟩)
    (fun i j hij hj=>by
      simpa only [windowImage,windowStep] using hc
        (⟨i,by omega⟩ : Fin (n+2)) (⟨j,by omega⟩ : Fin (n+2)) hij) hu
  have hlead : (L:ℝ)/2*(‖x (k+1)-x k‖+‖x (k+2)-x (k+1)‖)*‖x (k+2)-x (k+1)‖≤
      ((L:ℝ)/2*θ^3)*‖x k‖*‖x (k+1)‖ := by
    have hh := mul_le_mul
      (mul_le_mul_of_nonneg_left hsum (by positivity : 0≤(L:ℝ)/2)) hstep₁
      (norm_nonneg _) (by positivity : 0≤(L:ℝ)/2*(θ^2*‖x k‖))
    convert hh using 1; ring
  have htotal := add_le_add hlead hmass'
  have hsrc' : ‖G (x (k+n+2))‖≤θ*(((L:ℝ)/2*θ^3+δ)*‖x k‖*‖x (k+1)‖) := by
    apply hsrc.trans
    apply (mul_le_mul_of_nonneg_left htotal (norm_nonneg ((V k)⁻¹))).trans
    convert mul_le_mul_of_nonneg_right hi
      (by positivity : 0≤((L:ℝ)/2*θ^3)*‖x k‖*‖x (k+1)‖+δ*‖x k‖*‖x (k+1)‖) using 1; ring
  have hgrad : ‖x (k+n+2)‖≤θ*‖G (x (k+n+2))‖ := by
    have hxm : x (k+n+2)∈Metric.closedBall (0:EuclideanSpace ℝ (Fin (n+2))) r := by
      simpa only [Metric.mem_closedBall,dist_zero_right,Nat.add_assoc] using (hm ⟨n+2,by omega⟩).le
    have he := radial_gradient_endpoint_bound G H (Metric.closedBall 0 r) (convex_closedBall _ _)
      (by simpa using hr.le) hH hG hG₀ (x (k+n+2)) hxm
    rw [hH₀,ContinuousLinearMap.id_apply] at he
    have ht := norm_add_le (G (x (k+n+2))) (x (k+n+2)-G (x (k+n+2)))
    rw [add_sub_cancel,norm_sub_rev] at ht
    have hmul := mul_le_mul_of_nonneg_right hsm (norm_nonneg (x (k+n+2)))
    have ht' := ht.trans (add_le_add le_rfl he)
    have ht'' := mul_le_mul_of_nonneg_left ht' hθ.le
    dsimp only [θ] at hmul ht'' ⊢
    nlinarith only [hmul,ht'']
  apply hgrad.trans
  convert mul_le_mul_of_nonneg_left hsrc' hθ.le using 1
  dsimp only [θ]
  ring

/-- The original sharpened FC constant L_H/2, in the exact epsilon
formulation of the printed limsup bound. This applies to the actual
executor, requires no independence, and includes zero error values. -/
theorem slidingFCSequence_half_product
    (f : EuclideanSpace ℝ (Fin (n+2)) → ℝ)
    (G : EuclideanSpace ℝ (Fin (n+2)) → EuclideanSpace ℝ (Fin (n+2)))
    (H : EuclideanSpace ℝ (Fin (n+2)) → EuclideanSpace ℝ (Fin (n+2)) →L[ℝ]
      EuclideanSpace ℝ (Fin (n+2)))
    {r : ℝ} (hr : 0<r) (hG₀ : G 0=0) (hH₀ : H 0=ContinuousLinearMap.id ℝ _)
    {L : ℝ≥0} (hLr : (L:ℝ)*r≤1/2)
    (hH : LipschitzOnWith L H (Metric.closedBall 0 r))
    (hf : ∀ z∈Metric.closedBall (0:EuclideanSpace ℝ (Fin (n+2))) r,
      HasFDerivAt f (innerSL ℝ (G z)) z)
    (hG : ∀ z∈Metric.closedBall (0:EuclideanSpace ℝ (Fin (n+2))) r,HasFDerivAt G (H z) z)
    (seed : Fin (n+2) → EuclideanSpace ℝ (Fin (n+2)))
    (hconv : Tendsto (slidingFCSequence f G r seed) atTop (𝓝 0))
    (hsolve : ∀ᶠ k in atTop,IsUnit (slidingFCSolveMatrix (n:=n) G (slidingFCSequence f G r seed) k).det)
    (hs : (fun k=>slidingFCSequence f G r seed (k+1))=o[atTop]
      (fun k=>‖slidingFCSequence f G r seed k‖))
    {η : ℝ} (hη : 0<η) :
    ∀ᶠ k in atTop,‖slidingFCSequence f G r seed (k+n+2)‖≤
      ((L:ℝ)/2+η)*‖slidingFCSequence f G r seed k‖*‖slidingFCSequence f G r seed (k+1)‖ := by
  have hc : ContinuousAt (fun t : ℝ=>(1+t)^2*((L:ℝ)/2*(1+t)^3+t)) 0 := by fun_prop
  have he : ∀ᶠ t : ℝ in 𝓝 0,(1+t)^2*((L:ℝ)/2*(1+t)^3+t)<(L:ℝ)/2+η := by
    exact hc.tendsto.eventually (gt_mem_nhds (by simp only [add_zero,one_pow,one_mul];linarith))
  obtain ⟨ρ,hρ,hnear⟩ := Metric.eventually_nhds_iff.mp he
  have hδ : 0<ρ/2 := by linarith
  have hcoeff := hnear (y:=ρ/2) (by rw [Real.dist_eq,sub_zero,abs_of_pos hδ];linarith)
  filter_upwards [slidingFCSequence_half_product_aux f G H hr hG₀ hH₀ hLr hH hf hG seed
    hconv hsolve hs hδ] with k hk
  exact hk.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hcoeff.le (norm_nonneg _)) (norm_nonneg _))

end
end krylov.Convergence
