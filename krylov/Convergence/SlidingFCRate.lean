import krylov.Convergence.SlidingFCSourceResidual
import krylov.Convergence.SlidingNearMonotone
import krylov.Convergence.RecurrenceOrder

/-!
Article: main_krylov, thm:G, genuine sliding FC rate without independence.
Use: derive the original delayed error product from actual objective
searches and stored observed solves, then apply the characteristic theorem.
Source: Appendix G's residual staircase, the automatic Gram bootstrap,
and finite-window sublevel control. No recurrence or uniform independence
is imposed on the actual execution.
-/

namespace krylov.Convergence
noncomputable section
open Matrix Set Filter Topology krylov.Methods krylov.Functions
open scoped InnerProductSpace Matrix.Norms.L2Operator NNReal
variable {n : ℕ}
set_option maxHeartbeats 800000

/-- The actual sliding FC executor satisfies the printed delayed product,
with a factor arbitrarily close to one and the exact leading constant.
Only convergence and defined actual observed solves supplement the local
source assumptions. -/
theorem slidingFCSequence_product_bound
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
    {δ : ℝ} (hδ : 0<δ) :
    ∀ᶠ k in atTop,‖slidingFCSequence f G r seed (k+n+2)‖≤
      (4*(L:ℝ)*((n+1:ℕ):ℝ)*Real.sqrt (n+1)*(1+δ)^4)*
        ‖slidingFCSequence f G r seed k‖*‖slidingFCSequence f G r seed (k+1)‖ := by
  let x := slidingFCSequence f G r seed
  let θ := 1+δ
  have hθ : 0<θ := by dsimp only [θ]; linarith
  let V := fun k=>windowMatrix (unitWindow (windowStep (n:=n+2) x k))
  have hframe := slidingFCSequence_frame_conditioning f G H hr hH₀ hLr hH hf hG seed hconv hsolve
  have hunit : ∀ᶠ k in atTop,IsUnit (V k).det := hframe.2.1
  have hinv : ∀ᶠ k in atTop,‖(V k)⁻¹‖≤θ :=
    (hframe.2.2.eventually (gt_mem_nhds (by dsimp only [θ]; linarith : (1:ℝ)<θ))).mono fun _ h=>h.le
  have hsearch := slidingFCSequence_eventually_chord f G H hr hH₀ hLr hH hf hG seed hconv
  have hconj := slidingFC_full_window_conjugate f G x r hsolve hsearch
  have hline := slidingFCSequence_step_stationary f G H hr hG₀ hH₀ hLr hH hf hG seed hconv
  have hnear := slidingFCSequence_window_near_monotone f G H hr hG₀ hH₀ hLr hH hf hG
    seed hconv (n+2) hδ
  have hnear' : ∀ᶠ k in atTop,∀ j≤n+2,‖x (k+1+j)‖≤θ*‖x (k+1)‖ :=
    (tendsto_add_atTop_nat 1).eventually hnear
  have hmem : ∀ᶠ k in atTop,‖x k‖<r := by
    have hh : Tendsto (fun k=>‖x k‖) atTop (𝓝 0) := by simpa only [norm_zero] using hconv.norm
    exact hh.eventually (gt_mem_nhds hr)
  have hsmall : ∀ᶠ k in atTop,θ*((L:ℝ)/2*‖x k‖)≤δ := by
    have hh : Tendsto (fun k=>θ*((L:ℝ)/2*‖x k‖)) atTop (𝓝 0) := by
      simpa only [norm_zero,mul_zero] using (hconv.norm.const_mul ((L:ℝ)/2)).const_mul θ
    exact (hh.eventually (gt_mem_nhds hδ)).mono fun _ h=>h.le
  obtain ⟨N,hN⟩ := eventually_atTop.mp (hmem.and (hline.and hsmall))
  filter_upwards [eventually_ge_atTop N,hunit,hinv,hconj,hnear,hnear'] with k hk hu hi hc hn hn'
  have hball j (hj : j≤n+2) : ‖x (k+j)‖≤θ*‖x k‖ := hn j hj
  have hnew j (hj₀ : 0<j) (hj : j≤n+2) : ‖x (k+j)‖≤θ*‖x (k+1)‖ := by
    have hh := hn' (j-1) (by omega)
    simpa only [show k+1+(j-1)=k+j by omega] using hh
  have hsteps : windowStep (n:=n+2) (fun j=>x (k+j)) 0=windowStep x k := by
    funext i
    simp only [windowStep,Nat.zero_add,Nat.add_assoc]
  have hsrc := source_conjugate_path_residual f G H hH hf hG (fun j=>x (k+j))
    (mul_nonneg hθ.le (norm_nonneg _)) (mul_nonneg hθ.le (norm_nonneg _))
    (fun j _=> (hN (k+j) (by omega)).1) hball hnew
    (fun j _=>by simpa only [Nat.add_assoc] using (hN (k+j) (by omega)).2.1)
    (fun i j hij hj=>by
      simpa only [windowImage,windowStep,Nat.add_assoc] using hc
        (⟨i,by omega⟩ : Fin (n+2)) (⟨j,by omega⟩ : Fin (n+2)) hij)
    (by rw [hsteps]; exact hu)
  have hgrad : ‖x (k+n+2)‖≤θ*‖G (x (k+n+2))‖ := by
    have hm : x (k+n+2)∈Metric.closedBall (0:EuclideanSpace ℝ (Fin (n+2))) r := by
      simpa only [Metric.mem_closedBall,dist_zero_right] using (hN (k+n+2) (by omega)).1.le
    have he := radial_gradient_endpoint_bound G H (Metric.closedBall 0 r) (convex_closedBall _ _)
      (by simpa using hr.le) hH hG hG₀ (x (k+n+2)) hm
    rw [hH₀,ContinuousLinearMap.id_apply] at he
    have ht := norm_add_le (G (x (k+n+2))) (x (k+n+2)-G (x (k+n+2)))
    rw [add_sub_cancel,norm_sub_rev] at ht
    have hs := (hN (k+n+2) (by omega)).2.2
    have hmul := mul_le_mul_of_nonneg_right hs (norm_nonneg (x (k+n+2)))
    have ht' := ht.trans (add_le_add le_rfl he)
    have ht'' := mul_le_mul_of_nonneg_left ht' hθ.le
    dsimp only [θ] at hmul ht'' ⊢
    nlinarith only [hmul,ht'']
  have hsrc' : ‖G (x (k+n+2))‖≤‖(V k)⁻¹‖*
      (Real.sqrt (n+1)*(((n+1:ℕ):ℝ)*(4*(L:ℝ)*(θ*‖x k‖)*(θ*‖x (k+1)‖)))) := by
    simpa only [hsteps,←Nat.add_assoc,Nat.cast_add,Nat.cast_one] using hsrc
  have hb := hgrad.trans (mul_le_mul_of_nonneg_left hsrc' hθ.le)
  apply hb.trans
  have hh := mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right hi (by positivity : 0≤Real.sqrt (n+1)*
      (((n+1:ℕ):ℝ)*(4*(L:ℝ)*(θ*‖x k‖)*(θ*‖x (k+1)‖))))) hθ.le
  convert hh using 1
  simp only [θ,Nat.cast_add,Nat.cast_one]
  ring

/-- The original leading constant in its precise epsilon formulation of
the printed (1+o(1)) inequality. In particular this includes a zero
Lipschitz constant without division by it. -/
theorem slidingFCSequence_sharp_product
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
    {η : ℝ} (hη : 0<η) :
    ∀ᶠ k in atTop,‖slidingFCSequence f G r seed (k+n+2)‖≤
      (4*(L:ℝ)*((n+1:ℕ):ℝ)*Real.sqrt (n+1)+η)*
        ‖slidingFCSequence f G r seed k‖*‖slidingFCSequence f G r seed (k+1)‖ := by
  let C₀ := 4*(L:ℝ)*((n+1:ℕ):ℝ)*Real.sqrt (n+1)
  have hc : ContinuousAt (fun t : ℝ=>C₀*(1+t)^4) 0 := by fun_prop
  have he : ∀ᶠ t : ℝ in 𝓝 0,C₀*(1+t)^4<C₀+η := by
    have hh := hc.tendsto.eventually (gt_mem_nhds (by simp only [add_zero,one_pow,mul_one]; linarith :
      C₀*(1+(0:ℝ))^4<C₀+η))
    exact hh
  obtain ⟨ρ,hρ,hnear⟩ := Metric.eventually_nhds_iff.mp he
  have hδ : 0<ρ/2 := by linarith
  have hcoeff := hnear (y:=ρ/2) (by
    rw [Real.dist_eq,sub_zero,abs_of_pos hδ]
    linarith)
  filter_upwards [slidingFCSequence_product_bound f G H hr hG₀ hH₀ hLr hH hf hG seed hconv hsolve hδ]
    with k hk
  exact hk.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hcoeff.le (norm_nonneg _)) (norm_nonneg _))

/-- The actual independence-free sliding FC method has the characteristic
R-order τ_FC(dimension), per iteration and hence per gradient. -/
theorem slidingFCSequence_rorder
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
    : HasROrder (fun k=>‖slidingFCSequence f G r seed k‖) (fullConjugacyRoot (n+2)) := by
  let x := slidingFCSequence f G r seed
  let C₀ := 4*(L:ℝ)*((n+1:ℕ):ℝ)*Real.sqrt (n+1)
  have hC₀ : 0≤C₀ := by dsimp only [C₀]; positivity
  have hb := slidingFCSequence_product_bound f G H hr hG₀ hH₀ hLr hH hf hG seed hconv hsolve
    (by norm_num : (0:ℝ)<1)
  obtain ⟨N,hN⟩ := eventually_atTop.mp hb
  have hrec : ∃ K : ℝ,0<K ∧∀ᶠ k in atTop,
      ‖x (k+1)‖≤K*‖x (k-(n+1))‖*‖x (k-n)‖ := by
    refine ⟨C₀*16+1,by positivity,?_⟩
    filter_upwards [eventually_ge_atTop (N+n+1)] with k hk
    let o := k-(n+1)
    have ho : N≤o := by dsimp only [o]; omega
    have hh := hN o ho
    have he₀ : o+n+2=k+1 := by dsimp only [o]; omega
    have he₁ : o+1=k-n := by dsimp only [o]; omega
    have hcoef : 4*(L:ℝ)*((n+1:ℕ):ℝ)*Real.sqrt (n+1)*(1+1)^4≤C₀*16+1 := by
      dsimp only [C₀]
      norm_num
    have ht := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hcoef (norm_nonneg (x o))) (norm_nonneg (x (o+1)))
    have hh' : ‖x (k+1)‖≤(C₀*16+1)*‖x o‖*‖x (k-n)‖ := by
      simpa only [he₀,he₁] using hh.trans ht
    exact hh'
  have hh := rorder_product_recurrence (fun k=>‖x k‖) (fun _=>norm_nonneg _)
    (by simpa only [norm_zero] using hconv.norm) (n+1) n (by omega) hrec
  simpa only [fullConjugacyRoot,show n+2-1=n+1 by omega,show n+2-2=n by omega] using hh

end
end krylov.Convergence
