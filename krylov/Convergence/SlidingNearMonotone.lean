import krylov.Convergence.SlidingFCExecution

/-!
Article: main_krylov, thm:G, finite-window near monotonicity.
Use: derive the source's (1+o(1)) endpoint enclosure from the genuine local
search bound. Monotonicity of the error norms is not a hypothesis.
Source: finite products of the actual one-step sublevel factors.
-/

namespace krylov.Convergence
noncomputable section
open Filter Topology krylov.Functions
open scoped InnerProductSpace NNReal
variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A vanishing multiplicative one-step inflation gives the uniform sharp
factor one on every fixed finite forward window, including zero errors. -/
theorem near_monotone_fixed_window (e a : ℕ → ℝ)
    (he : ∀ k,0≤e k) (ha : ∀ k,0≤a k) (halim : Tendsto a atTop (𝓝 0))
    (hstep : ∀ᶠ k in atTop,e (k+1)≤(1+a k)*e k) (m : ℕ)
    {η : ℝ} (hη : 0<η) :
    ∀ᶠ k in atTop,∀ j≤m,e (k+j)≤(1+η)*e k := by
  let P := fun j k=>∏ l∈Finset.range j,(1+a (k+l))
  obtain ⟨N,hN⟩ := eventually_atTop.mp hstep
  have hp (j : ℕ) (k : ℕ) (hk : N≤k) : e (k+j)≤P j k*e k := by
    induction j with
    | zero => simp only [P,Finset.range_zero,Finset.prod_empty,one_mul,Nat.add_zero]; exact le_rfl
    | succ j ih =>
      have hfac : 0≤1+a (k+j) := by linarith [ha (k+j)]
      have hh := (hN (k+j) (by omega)).trans (mul_le_mul_of_nonneg_left ih hfac)
      simpa only [P,Finset.prod_range_succ,Nat.add_assoc,Nat.succ_eq_add_one,mul_assoc,mul_comm,
        mul_left_comm] using hh
  have hlim (j : ℕ) : Tendsto (P j) atTop (𝓝 1) := by
    have hh := tendsto_finsetProd (Finset.range j) (fun l _=>
      (tendsto_const_nhds : Tendsto (fun _ : ℕ=>(1:ℝ)) atTop (𝓝 1)).add
        (halim.comp (tendsto_add_atTop_nat l)))
    simpa only [P,add_zero,Finset.prod_const_one,Function.comp_def] using hh
  have hsmall : ∀ᶠ k in atTop,∀ j : Fin (m+1),P j.val k≤1+η :=
    Filter.eventually_all.mpr fun j=>((hlim j.val).eventually
      (gt_mem_nhds (by linarith : (1:ℝ)<1+η))).mono fun _ h=>h.le
  filter_upwards [eventually_ge_atTop N,hsmall] with k hk hs j hj
  exact (hp j k hk).trans (mul_le_mul_of_nonneg_right (hs ⟨j,by omega⟩) (he k))

/-- The literal sliding FC source satisfies finite-window near monotonicity
through genuine objective chord minimization. -/
theorem slidingFCSequence_window_near_monotone
    [CompleteSpace E]
    (f : E → ℝ) (G : E → E) (H : E → E →L[ℝ] E)
    {r : ℝ} (hr : 0<r) (hG₀ : G 0=0) (hH₀ : H 0=ContinuousLinearMap.id ℝ E)
    {L : ℝ≥0} (hLr : (L:ℝ)*r≤1/2)
    (hH : LipschitzOnWith L H (Metric.closedBall 0 r))
    (hf : ∀ z∈Metric.closedBall (0:E) r,HasFDerivAt f (innerSL ℝ (G z)) z)
    (hG : ∀ z∈Metric.closedBall (0:E) r,HasFDerivAt G (H z) z)
    (seed : Fin (n+2) → E) (hconv : Tendsto (slidingFCSequence f G r seed) atTop (𝓝 0))
    (m : ℕ) {η : ℝ} (hη : 0<η) :
    ∀ᶠ k in atTop,∀ j≤m,‖slidingFCSequence f G r seed (k+j)‖≤
      (1+η)*‖slidingFCSequence f G r seed k‖ := by
  let x := slidingFCSequence f G r seed
  have hs := slidingFCSequence_eventually_chord f G H hr hH₀ hLr hH hf hG seed hconv
  have hx : ∀ᶠ k in atTop,‖x (k+n+1)‖<r/2 := by
    have hh : Tendsto (fun k=>‖x (k+n+1)‖) atTop (𝓝 0) := by
      simpa only [norm_zero,Nat.add_assoc,Function.comp_def] using
        (hconv.comp (tendsto_add_atTop_nat (n+1))).norm
    exact hh.eventually (gt_mem_nhds (by linarith : (0:ℝ)<r/2))
  have hrec : ∀ᶠ k in atTop,‖x (k+1)‖≤(1+2*(L:ℝ)*‖x k‖)*‖x k‖ := by
    obtain ⟨N,hN⟩ := eventually_atTop.mp (hs.and hx)
    filter_upwards [eventually_ge_atTop (N+n+1)] with k hk
    let o := k-(n+1)
    have ho : N≤o := by dsimp only [o]; omega
    have he : o+n+1=k := by dsimp only [o]; omega
    have hh := (local_chord_minimum_spec f G H hr hG₀ hH₀ hLr hH hf hG
      (x (o+n+1)) (slidingFCDirection (n:=n) G x o) (x (o+n+2))
      (hN o ho).2 (hN o ho).1).1
    apply (by simpa only [he,show o+n+2=k+1 by omega] using hh :
      ‖x (k+1)‖≤min (Real.sqrt 3) (1+2*(L:ℝ)*‖x k‖)*‖x k‖).trans
    exact mul_le_mul_of_nonneg_right (min_le_right _ _) (norm_nonneg _)
  exact near_monotone_fixed_window (fun k=>‖x k‖) (fun k=>2*(L:ℝ)*‖x k‖)
    (fun _=>norm_nonneg _) (fun _=>by positivity)
    (by simpa only [norm_zero,mul_zero] using hconv.norm.const_mul (2*(L:ℝ))) hrec m hη

/-- The actual searched step, including a zero line displacement, has its
true terminal-gradient orthogonality. -/
theorem slidingFCSequence_step_stationary [CompleteSpace E]
    (f : E → ℝ) (G : E → E) (H : E → E →L[ℝ] E)
    {r : ℝ} (hr : 0<r) (hG₀ : G 0=0) (hH₀ : H 0=ContinuousLinearMap.id ℝ E)
    {L : ℝ≥0} (hLr : (L:ℝ)*r≤1/2)
    (hH : LipschitzOnWith L H (Metric.closedBall 0 r))
    (hf : ∀ z∈Metric.closedBall (0:E) r,HasFDerivAt f (innerSL ℝ (G z)) z)
    (hG : ∀ z∈Metric.closedBall (0:E) r,HasFDerivAt G (H z) z)
    (seed : Fin (n+2) → E) (hconv : Tendsto (slidingFCSequence f G r seed) atTop (𝓝 0)) :
    ∀ᶠ k in atTop,inner ℝ (slidingFCSequence f G r seed (k+1)-slidingFCSequence f G r seed k)
      (G (slidingFCSequence f G r seed (k+1)))=0 := by
  let x := slidingFCSequence f G r seed
  have hs := slidingFCSequence_eventually_chord f G H hr hH₀ hLr hH hf hG seed hconv
  have hx : ∀ᶠ k in atTop,‖x (k+n+1)‖<r/2 := by
    have hh : Tendsto (fun k=>‖x (k+n+1)‖) atTop (𝓝 0) := by
      simpa only [norm_zero,Nat.add_assoc,Function.comp_def] using
        (hconv.comp (tendsto_add_atTop_nat (n+1))).norm
    exact hh.eventually (gt_mem_nhds (by linarith : (0:ℝ)<r/2))
  obtain ⟨N,hN⟩ := eventually_atTop.mp (hs.and hx)
  filter_upwards [eventually_ge_atTop (N+n+1)] with k hk
  let o := k-(n+1)
  have ho : N≤o := by dsimp only [o]; omega
  have he : o+n+1=k := by dsimp only [o]; omega
  have hs' := (hN o ho).1
  have hstat := (local_chord_minimum_spec f G H hr hG₀ hH₀ hLr hH hf hG
    _ _ _ (hN o ho).2 hs').2.2.1
  obtain ⟨α,hα⟩ := hs'.2.1
  change x (o+n+2)=x (o+n+1)+α • slidingFCDirection (n:=n) G x o at hα
  change inner ℝ (G (x (o+n+2))) (slidingFCDirection (n:=n) G x o)=0 at hstat
  have hvec : x (o+n+2)-x (o+n+1)=α • slidingFCDirection (n:=n) G x o := by
    rw [hα,add_sub_cancel_left]
  have hh : inner ℝ (x (o+n+2)-x (o+n+1)) (G (x (o+n+2)))=0 := by
    rw [hvec,real_inner_smul_left,real_inner_comm,hstat,mul_zero]
  simpa only [he,show o+n+2=k+1 by omega] using hh

end
end krylov.Convergence
