import krylov.Convergence.WindowCenteredCoordinates
import krylov.Convergence.SlidingFCPath

/-!
Article: main_krylov, thm:G, genuine physical sliding FC under metric coordinates.
Use: execute the original Euclidean observed direction and genuine metric
chord search, then transport its actual point, secant, and conjugacy
identities. Source: the observed inverse cancellation and actual objective
search. No equality of nonorthogonally transformed FC directions is claimed.
-/
namespace krylov.Convergence
noncomputable section
open Matrix Set Filter Topology krylov.Methods krylov.Functions krylov.Nonlinear
open scoped InnerProductSpace Matrix.Norms.L2Operator NNReal
variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
set_option maxHeartbeats 1000000

/-- A true physical chord search around the physical centre, with only
the scalar objective pulled back for its actual minimization. -/
def centeredMetricExactPoint (T : E ≃L[ℝ] E) (center : E) (f : E → ℝ)
    (x d : E) (r : ℝ) : E :=
  center+T.symm (localExactPoint (centeredMetricObjective T center f) (T (x-center)) (T d) r)

/-- The physical sliding FC rule retains its original Euclidean observed
conjugacy solve, followed by a genuine physical scalar objective search. -/
def metricSlidingFCWindowRule (T : E ≃L[ℝ] E) (center : E) (f : E → ℝ) (G : E → E)
    (r : ℝ) (q : Fin (n+2) → E) : E :=
  centeredMetricExactPoint T center f (q (Fin.last (n+1))) (slidingFCWindowDirection G q) r

/-- The literal physical observed sliding FC executor, including arbitrary
true initial point observations. Its direction uses no Hessian or reference. -/
def metricSlidingFCSequence (T : E ≃L[ℝ] E) (center : E) (f : E → ℝ) (G : E → E)
    (r : ℝ) (seed : Fin (n+2) → E) : ℕ → E :=
  slidingSequence (metricSlidingFCWindowRule T center f G r) seed

/-- Every actual physical metric-FC step is its real searched step. -/
theorem metricSlidingFCSequence_step (T : E ≃L[ℝ] E) (center : E) (f : E → ℝ) (G : E → E)
    (r : ℝ) (seed : Fin (n+2) → E) (k : ℕ) :
    metricSlidingFCSequence T center f G r seed (k+n+2)=
      centeredMetricExactPoint T center f (metricSlidingFCSequence T center f G r seed (k+n+1))
        (slidingFCDirection (n:=n) G (metricSlidingFCSequence T center f G r seed) k) r := by
  rw [metricSlidingFCSequence,slidingSequence_step]
  rfl

/-- Primal steps transport linearly, with no loss or normalization premise. -/
theorem centered_metric_windowStep (T : E ≃L[ℝ] E) (center : E) (x : ℕ → E) (k : ℕ) :
    windowStep (n:=n) (fun j=>T (x j-center)) k=fun i=>T (windowStep (n:=n) x k i) := by
  funext i
  simp only [windowStep,←map_sub,sub_sub_sub_cancel_right]

/-- True endpoint-gradient secants transport dually under the actual
coordinate gradient of the physical scalar source. -/
theorem centered_metric_windowImage (T : E ≃L[ℝ] E) (center : E) (G : E → E)
    (x : ℕ → E) (k : ℕ) :
    windowImage (n:=n) (centeredMetricGradient T center G) (fun j=>T (x j-center)) k=
      fun i=>T.symm (windowImage (n:=n) G x k i) := by
  funext i
  have hc (v : E) : center+(v-center)=v := by abel_nf
  simp only [windowImage,centeredMetricGradient,coordinateGradient,T.symm_apply_apply,hc,←map_sub]

/-- A physical step and actual observed secant have exactly their
canonical primal/dual pairing. -/
theorem centered_metric_window_pair (T : E ≃L[ℝ] E)
    (hT : T.symm.toContinuousLinearMap.IsSymmetric) (center : E) (G : E → E)
    (x : ℕ → E) (k : ℕ) (i j : Fin n) :
    inner ℝ (windowImage (centeredMetricGradient T center G) (fun l=>T (x l-center)) k i)
      (windowStep (fun l=>T (x l-center)) k j)=
      inner ℝ (windowImage G x k i) (windowStep x k j) := by
  rw [centered_metric_windowImage,centered_metric_windowStep,real_inner_comm,
    inverse_symmetric_pairing T hT,real_inner_comm]

/-- A convergent actual physical FC execution supplies all true canonical
source-path identities, including nonzero steps from future defined solves
and observed conjugacy. Its physical direction itself is left unchanged. -/
theorem metricSlidingFCSequence_source_data [CompleteSpace E]
    (T : E ≃L[ℝ] E) (hT : T.symm.toContinuousLinearMap.IsSymmetric)
    (center : E) (f : E → ℝ) (G : E → E) (H : E → E →L[ℝ] E)
    {r : ℝ} (hr : 0<r)
    (hH₀ : centeredMetricHessian T center H 0=ContinuousLinearMap.id ℝ E)
    {L : ℝ≥0} (hLr : (L:ℝ)*r≤1/2)
    (hH : LipschitzOnWith L (centeredMetricHessian T center H) (Metric.closedBall 0 r))
    (hf : ∀ z∈Metric.closedBall (0:E) r,HasFDerivAt (centeredMetricObjective T center f)
      (innerSL ℝ (centeredMetricGradient T center G z)) z)
    (hG : ∀ z∈Metric.closedBall (0:E) r,HasFDerivAt (centeredMetricGradient T center G)
      (centeredMetricHessian T center H z) z)
    (seed : Fin (n+2) → E)
    (hconv : Tendsto (metricSlidingFCSequence T center f G r seed) atTop (𝓝 center))
    (hsolve : ∀ᶠ k in atTop,IsUnit (slidingFCSolveMatrix (n:=n) G
      (metricSlidingFCSequence T center f G r seed) k).det) :
    let x:=metricSlidingFCSequence T center f G r seed
    let z:=fun k=>T (x k-center)
    Tendsto z atTop (𝓝 0) ∧
    (∀ᶠ k in atTop,∀ i : Fin (n+2),windowStep (n:=n+2) z k i≠0) ∧
    (∀ᶠ k in atTop,∀ i j : Fin (n+2),i<j →
      inner ℝ (windowImage (centeredMetricGradient T center G) z k i) (windowStep z k j)=0) ∧
    (∀ᶠ k in atTop,IsChordMinimum (centeredMetricObjective T center f)
      (z k) (T (slidingFCDirection (n:=n) G x (k-(n+1)))) r (z (k+1))) := by
  let x:=metricSlidingFCSequence T center f G r seed
  let z:=fun k=>T (x k-center)
  have hz : Tendsto z atTop (𝓝 0) := by
    have hx0 : Tendsto (fun k=>x k-center) atTop (𝓝 0) := by
      simpa only [sub_self] using hconv.sub_const center
    have hh:=(T.continuous.tendsto 0).comp hx0
    simpa only [Function.comp_def,map_zero] using hh
  have hstep (k : ℕ) : z (k+n+2)=localExactPoint (centeredMetricObjective T center f)
      (z (k+n+1)) (T (slidingFCDirection (n:=n) G x k)) r := by
    dsimp only [z,x]
    rw [metricSlidingFCSequence_step]
    simp only [centeredMetricExactPoint,add_sub_cancel_left,T.apply_symm_apply]
  have hsearch : ∀ᶠ k in atTop,IsChordMinimum (centeredMetricObjective T center f)
      (z (k+n+1)) (T (slidingFCDirection (n:=n) G x k)) r (z (k+n+2)) := by
    have hh:=(hz.comp (tendsto_add_atTop_nat (n+1))).eventually (Metric.closedBall_mem_nhds (0:E) hr)
    filter_upwards [hh] with k hk
    rw [hstep]
    exact localExactPoint_spec _ _ _ r
      (existsUnique_local_chord_minimum _ _ _ hr hH₀ hLr hH hf hG _ _ hk)
  have hs : ∀ᶠ k in atTop,∀ i : Fin (n+2),windowStep (n:=n+2) z k i≠0 := by
    filter_upwards [slidingFC_full_window_step_ne_zero G x hsolve] with k hk i
    rw [centered_metric_windowStep]
    exact fun h=>hk i (T.injective (h.trans T.map_zero.symm))
  have hconj : ∀ᶠ k in atTop,∀ i j : Fin (n+2),i<j →
      inner ℝ (windowImage (centeredMetricGradient T center G) z k i) (windowStep z k j)=0 := by
    obtain ⟨N,hN⟩:=eventually_atTop.mp (hsolve.and hsearch)
    filter_upwards [eventually_ge_atTop (N+n+1)] with o ho i j hij
    let k:=o+j.val-(n+1)
    have hk : N≤k := by dsimp only [k];omega
    let a : Fin (n+1):=⟨o+i.val-k,by dsimp only [k];have hijv : i.val<j.val:=hij;omega⟩
    have hiidx : k+a.val=o+i.val := by dsimp only [a,k];omega
    have hjidx : k+n+1=o+j.val := by dsimp only [k];omega
    have hjnext : k+n+2=o+j.val+1 := by omega
    obtain ⟨α,hα⟩:=(hN k hk).2.2.1
    have hphys : x (k+n+2)-x (k+n+1)=α • slidingFCDirection (n:=n) G x k := by
      apply T.injective
      have hh:=congrArg (fun v=>v-z (k+n+1)) hα
      simpa only [z,add_sub_cancel_left,←map_sub,sub_sub_sub_cancel_right,map_smul] using hh
    have hpair : inner ℝ (windowImage G x o i) (windowStep x o j)=0 := by
      have hc:=slidingFC_direction_conjugate G x k (hN k hk).1 a
      rw [windowImage,hiidx] at hc
      change inner ℝ (G (x (o+i.val+1))-G (x (o+i.val))) (x (o+j.val+1)-x (o+j.val))=0
      rw [←hjidx,show k+n+1+1=k+n+2 by omega,hphys,real_inner_smul_right,hc,mul_zero]
    rw [centered_metric_window_pair T hT]
    exact hpair
  refine ⟨hz,hs,hconj,?_⟩
  obtain ⟨N,hN⟩:=eventually_atTop.mp hsearch
  filter_upwards [eventually_ge_atTop (N+n+1)] with k hk
  let o:=k-(n+1)
  have ho : N≤o := by dsimp only [o];omega
  simpa only [show o+n+1=k by dsimp only [o];omega,
    show o+n+2=k+1 by dsimp only [o];omega] using hN o ho

end
end krylov.Convergence
