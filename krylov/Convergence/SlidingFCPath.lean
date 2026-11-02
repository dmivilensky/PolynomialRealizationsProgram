import krylov.Convergence.SlidingFCHalf

/-!
Article: main_krylov, thm:G, coordinate-independent source-path proof.
Use: retain actual objective chord searches and exact observed conjugacy
under a nonorthogonal metric change. The forcing vector used to compute
an FC direction need not itself transform covariantly; no such assertion
is used. Source: actual chord stationarity, true secant FTC, and the
observed triangular staircase. The final metric executor supplies every
path identity rather than assuming a desired rate or model estimate.
-/
namespace krylov.Convergence
noncomputable section
open Matrix Set Filter Topology Asymptotics krylov.Methods krylov.Functions
open scoped InnerProductSpace Matrix.Norms.L2Operator NNReal
variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
set_option maxHeartbeats 1200000

/-- True source chord searches imply both actual stationarity and the
one-step sublevel bound, independently of how the direction was chosen. -/
theorem source_path_chord_control (f : E → ℝ) (G : E → E) (H : E → E →L[ℝ] E)
    {r : ℝ} (hr : 0<r) (hG₀ : G 0=0) (hH₀ : H 0=ContinuousLinearMap.id ℝ E)
    {L : ℝ≥0} (hLr : (L:ℝ)*r≤1/2) (hH : LipschitzOnWith L H (Metric.closedBall 0 r))
    (hf : ∀ z∈Metric.closedBall (0:E) r,HasFDerivAt f (innerSL ℝ (G z)) z)
    (hG : ∀ z∈Metric.closedBall (0:E) r,HasFDerivAt G (H z) z)
    (x d : ℕ → E) (hconv : Tendsto x atTop (𝓝 0))
    (hsearch : ∀ᶠ k in atTop,IsChordMinimum f (x k) (d k) r (x (k+1))) :
    (∀ᶠ k in atTop,inner ℝ (x (k+1)-x k) (G (x (k+1)))=0) ∧
    (∀ᶠ k in atTop,‖x (k+1)‖≤(1+2*(L:ℝ)*‖x k‖)*‖x k‖) := by
  have hx : ∀ᶠ k in atTop,‖x k‖<r/2 := by
    have ht : Tendsto (fun k=>‖x k‖) atTop (𝓝 0) := by simpa only [norm_zero] using hconv.norm
    exact ht.eventually (gt_mem_nhds (by linarith : (0:ℝ)<r/2))
  have hh : ∀ᶠ k in atTop,
      inner ℝ (x (k+1)-x k) (G (x (k+1)))=0 ∧
      ‖x (k+1)‖≤(1+2*(L:ℝ)*‖x k‖)*‖x k‖ := by
    filter_upwards [hx,hsearch] with k hk hs
    have hc:=local_chord_minimum_spec f G H hr hG₀ hH₀ hLr hH hf hG _ _ _ hk hs
    obtain ⟨α,hα⟩:=hs.2.1
    have hvec : x (k+1)-x k=α • d k := by rw [hα,add_sub_cancel_left]
    constructor
    · rw [hvec,real_inner_smul_left,real_inner_comm,hc.2.2.1,mul_zero]
    · exact hc.1.trans (mul_le_mul_of_nonneg_right (min_le_right _ _) (norm_nonneg _))
  exact ⟨hh.mono fun _ h=>h.1,hh.mono fun _ h=>h.2⟩

/-- Finite true-error windows inherit the sharp factor one from the
actual one-step source chord bound. -/
theorem source_path_near_monotone (f : E → ℝ) (G : E → E) (H : E → E →L[ℝ] E)
    {r : ℝ} (hr : 0<r) (hG₀ : G 0=0) (hH₀ : H 0=ContinuousLinearMap.id ℝ E)
    {L : ℝ≥0} (hLr : (L:ℝ)*r≤1/2) (hH : LipschitzOnWith L H (Metric.closedBall 0 r))
    (hf : ∀ z∈Metric.closedBall (0:E) r,HasFDerivAt f (innerSL ℝ (G z)) z)
    (hG : ∀ z∈Metric.closedBall (0:E) r,HasFDerivAt G (H z) z)
    (x d : ℕ → E) (hconv : Tendsto x atTop (𝓝 0))
    (hsearch : ∀ᶠ k in atTop,IsChordMinimum f (x k) (d k) r (x (k+1)))
    (m : ℕ) {η : ℝ} (hη : 0<η) :
    ∀ᶠ k in atTop,∀ j≤m,‖x (k+j)‖≤(1+η)*‖x k‖ := by
  exact near_monotone_fixed_window (fun k=>‖x k‖) (fun k=>2*(L:ℝ)*‖x k‖)
    (fun _=>norm_nonneg _) (fun _=>by positivity)
    (by simpa only [norm_zero,mul_zero] using hconv.norm.const_mul (2*(L:ℝ)))
    (source_path_chord_control f G H hr hG₀ hH₀ hLr hH hf hG x d hconv hsearch).2 m hη

/- Actual triangular observed conjugacy alone bootstraps a full source
frame to orthonormality, without an independence premise. -/
omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] in
theorem source_path_frame_conditioning
    (G : EuclideanSpace ℝ (Fin (n+2)) → EuclideanSpace ℝ (Fin (n+2)))
    (H : EuclideanSpace ℝ (Fin (n+2)) → EuclideanSpace ℝ (Fin (n+2)) →L[ℝ]
      EuclideanSpace ℝ (Fin (n+2)))
    {r : ℝ} (hr : 0<r) (hH₀ : H 0=ContinuousLinearMap.id ℝ _)
    {L : ℝ≥0} (hH : LipschitzOnWith L H (Metric.closedBall 0 r))
    (hG : ∀ z∈Metric.closedBall (0:EuclideanSpace ℝ (Fin (n+2))) r,HasFDerivAt G (H z) z)
    (x : ℕ → EuclideanSpace ℝ (Fin (n+2))) (hconv : Tendsto x atTop (𝓝 0))
    (hsteps : ∀ᶠ k in atTop,∀ i : Fin (n+2),windowStep (n:=n+2) x k i≠0)
    (hconj : ∀ᶠ k in atTop,∀ i j : Fin (n+2),i<j →
      inner ℝ (windowImage G x k i) (windowStep x k j)=0) :
    let V:=fun k=>windowMatrix (unitWindow (windowStep (n:=n+2) x k))
    Tendsto (fun k=>(V k)ᵀ*V k) atTop (𝓝 1) ∧
      (∀ᶠ k in atTop,IsUnit (V k).det) ∧ Tendsto (fun k=>‖(V k)⁻¹‖) atTop (𝓝 1) := by
  have ha (i : Fin (n+2)) : Tendsto (fun k=>x (k+i.val)) atTop (𝓝 0) :=
    hconv.comp (tendsto_add_atTop_nat i.val)
  have hb (i : Fin (n+2)) : Tendsto (fun k=>x (k+i.val+1)) atTop (𝓝 0) := by
    simpa only [Nat.add_assoc,Function.comp_def] using hconv.comp (tendsto_add_atTop_nat (i.val+1))
  have hn:=Metric.closedBall_mem_nhds (0:EuclideanSpace ℝ (Fin (n+2))) hr
  have hm : ∀ᶠ k in atTop,(∀ i : Fin (n+2),x (k+i.val)∈Metric.closedBall 0 r) ∧
      (∀ i : Fin (n+2),x (k+i.val+1)∈Metric.closedBall 0 r) :=
    (Filter.eventually_all.mpr fun i=>(ha i).eventually hn).and
      (Filter.eventually_all.mpr fun i=>(hb i).eventually hn)
  exact conjugate_source_window_conditioning G H (Metric.closedBall 0 r) (convex_closedBall 0 r)
    (by simpa using hr.le) hH hH₀ hG (fun k i=>x (k+i.val)) (fun k i=>x (k+i.val+1))
    ha hb hm hsteps hconj

end
end krylov.Convergence
