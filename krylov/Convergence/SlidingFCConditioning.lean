import krylov.Convergence.SlidingFCExecution
import krylov.Convergence.SlidingSourceGram

/-!
Article: main_krylov, thm:G, automatic sliding FC conditioning.
Use: derive the full normalized frame's rank and inverse factor from the
literal observed-data FC executor. Defined solves and genuine exact search
imply the triangular observed conjugacy; no independence is assumed.
Source: exact FC solve cancellation, true chord minimization, and the proved
source Gram bootstrap.
-/

namespace krylov.Convergence
noncomputable section
open Matrix Set Filter Topology krylov.Methods krylov.Functions
open scoped InnerProductSpace Matrix.Norms.L2Operator NNReal
variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- All real steps in a late full frame are nonzero because they enter an
actually defined future observed solve. No descent premise is needed. -/
theorem slidingFC_full_window_step_ne_zero (G : E → E) (x : ℕ → E)
    (hsolve : ∀ᶠ k in atTop,IsUnit (slidingFCSolveMatrix (n:=n) G x k).det) :
    ∀ᶠ k in atTop,∀ i : Fin (n+2),windowStep (n:=n+2) x k i≠0 := by
  obtain ⟨N,hN⟩ := eventually_atTop.mp hsolve
  filter_upwards [eventually_ge_atTop N] with k hk i
  have hh := observed_solve_step_ne_zero (windowStep (n:=n+1) x (k+i.val))
    (windowImage G x (k+i.val)) (hN (k+i.val) (by omega)) 0
  simpa only [windowStep,Fin.val_zero,Nat.add_zero] using hh

/-- Every pair of distinct chronological steps in a late full frame has
the genuine observed triangular FC conjugacy. -/
theorem slidingFC_full_window_conjugate (f : E → ℝ) (G : E → E) (x : ℕ → E) (r : ℝ)
    (hsolve : ∀ᶠ k in atTop,IsUnit (slidingFCSolveMatrix (n:=n) G x k).det)
    (hsearch : ∀ᶠ k in atTop,IsChordMinimum f (x (k+n+1))
      (slidingFCDirection (n:=n) G x k) r (x (k+n+2))) :
    ∀ᶠ k in atTop,∀ i j : Fin (n+2),i<j →
      inner ℝ (windowImage G x k i) (windowStep x k j)=0 := by
  obtain ⟨N,hN⟩ := eventually_atTop.mp (hsolve.and hsearch)
  filter_upwards [eventually_ge_atTop (N+n+1)] with o ho i j hij
  have hijv : i.val<j.val := hij
  let k := o+j.val-(n+1)
  have hk : N≤k := by dsimp only [k]; omega
  have hki : k≤o+i.val := by dsimp only [k]; omega
  let a : Fin (n+1) := ⟨o+i.val-k,by dsimp only [k]; omega⟩
  have hh := slidingFC_searched_step_conjugate f G x r k (hN k hk).1 (hN k hk).2 a
  have hiidx : k+a.val=o+i.val := by dsimp only [a]; omega
  have hjidx : k+n+1=o+j.val := by dsimp only [k]; omega
  have hjnext : k+n+2=o+j.val+1 := by omega
  simpa only [windowImage,windowStep,hiidx,hjidx,hjnext] using hh

/-- The actual full sliding FC frame becomes orthonormal and nonsingular,
with inverse norm tending to one, under (A1),(A2) alone. The genuine
observed solve domains are the article's "defined iterations" condition. -/
theorem slidingFCSequence_frame_conditioning
    (f : EuclideanSpace ℝ (Fin (n+2)) → ℝ)
    (G : EuclideanSpace ℝ (Fin (n+2)) → EuclideanSpace ℝ (Fin (n+2)))
    (H : EuclideanSpace ℝ (Fin (n+2)) → EuclideanSpace ℝ (Fin (n+2)) →L[ℝ]
      EuclideanSpace ℝ (Fin (n+2)))
    {r : ℝ} (hr : 0<r) (hH₀ : H 0=ContinuousLinearMap.id ℝ _)
    {L : ℝ≥0} (hLr : (L:ℝ)*r≤1/2)
    (hH : LipschitzOnWith L H (Metric.closedBall 0 r))
    (hf : ∀ z∈Metric.closedBall (0:EuclideanSpace ℝ (Fin (n+2))) r,
      HasFDerivAt f (innerSL ℝ (G z)) z)
    (hG : ∀ z∈Metric.closedBall (0:EuclideanSpace ℝ (Fin (n+2))) r,HasFDerivAt G (H z) z)
    (seed : Fin (n+2) → EuclideanSpace ℝ (Fin (n+2)))
    (hconv : Tendsto (slidingFCSequence f G r seed) atTop (𝓝 0))
    (hsolve : ∀ᶠ k in atTop,IsUnit (slidingFCSolveMatrix (n:=n) G (slidingFCSequence f G r seed) k).det) :
    let V := fun k=>windowMatrix (unitWindow (windowStep (n:=n+2) (slidingFCSequence f G r seed) k))
    Tendsto (fun k=>(V k)ᵀ*V k) atTop (𝓝 1) ∧
    (∀ᶠ k in atTop,IsUnit (V k).det) ∧Tendsto (fun k=>‖(V k)⁻¹‖) atTop (𝓝 1) := by
  let x := slidingFCSequence f G r seed
  have hsearch := slidingFCSequence_eventually_chord f G H hr hH₀ hLr hH hf hG seed hconv
  have ha (i : Fin (n+2)) : Tendsto (fun k=>x (k+i.val)) atTop (𝓝 0) :=
    hconv.comp (tendsto_add_atTop_nat i.val)
  have hb (i : Fin (n+2)) : Tendsto (fun k=>x (k+i.val+1)) atTop (𝓝 0) := by
    simpa only [x,Nat.add_assoc,Function.comp_def] using hconv.comp (tendsto_add_atTop_nat (i.val+1))
  have hnbhd : Metric.closedBall (0:EuclideanSpace ℝ (Fin (n+2))) r∈𝓝 0 :=
    Metric.closedBall_mem_nhds 0 hr
  have hm : ∀ᶠ k in atTop,(∀ i : Fin (n+2),x (k+i.val)∈Metric.closedBall 0 r) ∧
      (∀ i : Fin (n+2),x (k+i.val+1)∈Metric.closedBall 0 r) :=
    (Filter.eventually_all.mpr fun i=>(ha i).eventually hnbhd).and
      (Filter.eventually_all.mpr fun i=>(hb i).eventually hnbhd)
  exact conjugate_source_window_conditioning G H (Metric.closedBall 0 r) (convex_closedBall 0 r)
    (by simpa using hr.le) hH hH₀ hG (fun k i=>x (k+i.val)) (fun k i=>x (k+i.val+1))
    ha hb hm (slidingFC_full_window_step_ne_zero G x hsolve)
    (slidingFC_full_window_conjugate f G x r hsolve hsearch)

end
end krylov.Convergence
