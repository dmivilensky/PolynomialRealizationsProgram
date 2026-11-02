import krylov.Functions.ScalarProbedExecution
import krylov.Methods.CorrectionFree
import krylov.Functions.MetricFCQuadraticJet

/-!
Article: main_krylov, thm:D, native search-only function cycles.
Use: derive all query domains and linear localization for a genuine causal
scalar executor with no correction queries, in particular deferred DC.
The direction may depend on the entire actual measured history. No
independence, descent margin or trajectory enclosure is assumed.
Source: actual unique chord minima and the objective sublevel argument.
-/
namespace krylov.Convergence
noncomputable section
open Set Metric krylov.Methods krylov.Functions krylov.Nonlinear
open scoped InnerProductSpace NNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A genuine correction-free scalar program moves to its actual searched
point, with no unrecorded displacement. Article: main_krylov, thm:D. -/
theorem scalarSearchOnlyPoint_succ
    (m : ProbedMethod E) (hm : CorrectionFree m) (T : E ≃L[ℝ] E)
    (f : E → ℝ) (G : E → E) (r : ℝ) (x₀ : E) (k : ℕ) :
    scalarFunctionPoint m T f G r x₀ (k+1)=
      metricLocalExactPoint T f (scalarFunctionPoint m T f G r x₀ k)
        (m.direction (scalarFunctionRun m T f G r x₀ k)) r := by
  have hc : ∀ h z,m.correction h z=.done := hm
  simp only [scalarFunctionPoint,scalarFunctionRun,History.displacement,List.map_cons,List.sum_cons]
  simp only [scalarFunctionRecord,hc,scalarFunctionCorrections,add_zero]
  simp only [History.displacement]
  abel

/-- Every retained gradient of the genuine search-only scalar execution is
the actual function gradient at its actual point. Article: thm:D. -/
theorem scalarSearchOnlyRun_gradient
    (m : ProbedMethod E) (hm : CorrectionFree m) (T : E ≃L[ℝ] E)
    (f : E → ℝ) (G : E → E) (r : ℝ) (x₀ : E) (k : ℕ) :
    (scalarFunctionRun m T f G r x₀ k).gradient=
      G (scalarFunctionPoint m T f G r x₀ k) := by
  have hc : ∀ h z,m.correction h z=.done := hm
  cases k with
  | zero=>simp only [scalarFunctionRun,History.gradient,scalarFunctionPoint,History.displacement,List.map_nil,List.sum_nil,add_zero]
  | succ k=>
    rw [scalarSearchOnlyPoint_succ m hm]
    simp only [scalarFunctionRun,History.gradient,scalarFunctionRecord,hc,scalarFunctionCorrections,scalarFunctionPoint]

variable [CompleteSpace E]

omit [CompleteSpace E] in
/-- Every actual search-only query is its genuine local metric-chord
minimum. The theorem proves existence before invoking localization.
Article: main_krylov, thm:D and lem:cycle-transfer. -/
theorem scalarSearchOnlyPoint_chord_steps
    (m : ProbedMethod E) (hm : CorrectionFree m)
    (T : E ≃L[ℝ] E) (hT : T.symm.toContinuousLinearMap.IsSymmetric)
    (f : E → ℝ) (G : E → E) (H : E → E →L[ℝ] E)
    {r : ℝ} (hr : 0<r) (hH₀ : coordinateDerivative T H 0=ContinuousLinearMap.id ℝ E)
    {L : ℝ≥0} (hLr : (L:ℝ)*r≤1/2)
    (hH : LipschitzOnWith L (coordinateDerivative T H) (closedBall 0 r))
    (hF : ∀ z,‖T z‖≤r →HasFDerivAt f (innerSL ℝ (G z)) z)
    (hG : ∀ z,‖T z‖≤r →HasFDerivAt G (H z) z)
    (x₀ : E) (hx₀ : ‖T x₀‖≤r) :
    ∀ k : ℕ,IsChordMinimum (coordinateObjective T f)
      (T (scalarFunctionPoint m T f G r x₀ k))
      (T (m.direction (scalarFunctionRun m T f G r x₀ k))) r
      (T (scalarFunctionPoint m T f G r x₀ (k+1))) := by
  have hFc z (hz : z∈closedBall (0:E) r) :
      HasFDerivAt (coordinateObjective T f) (innerSL ℝ (coordinateGradient T G z)) z := by
    apply coordinateObjective_hasFDerivAt T hT f G z
    apply hF
    simpa only [T.apply_symm_apply,mem_closedBall,dist_zero_right] using hz
  have hGc z (hz : z∈closedBall (0:E) r) :
      HasFDerivAt (coordinateGradient T G) (coordinateDerivative T H z) z := by
    apply coordinateGradient_hasFDerivAt T G H z
    apply hG
    simpa only [T.apply_symm_apply,mem_closedBall,dist_zero_right] using hz
  have hball : ∀ k : ℕ,T (scalarFunctionPoint m T f G r x₀ k)∈closedBall (0:E) r := by
    intro k
    induction k with
    | zero=>simpa only [scalarFunctionPoint,scalarFunctionRun,History.displacement,List.map_nil,List.sum_nil,add_zero,mem_closedBall,dist_zero_right] using hx₀
    | succ k ih=>
      rw [scalarSearchOnlyPoint_succ m hm,metricLocalExactPoint,T.apply_symm_apply]
      exact (localExactPoint_spec _ _ _ r (existsUnique_local_chord_minimum _ _ _ hr hH₀ hLr hH hFc hGc _ _ ih)).1
  intro k
  rw [scalarSearchOnlyPoint_succ m hm,metricLocalExactPoint,T.apply_symm_apply]
  exact localExactPoint_spec _ _ _ r (existsUnique_local_chord_minimum _ _ _ hr hH₀ hLr hH hFc hGc _ _ (hball k))

/-- Genuine search-only scalar queries have the common original metric
localization, independent of the method or number of iterations.
Article: main_krylov, thm:D, native DC bootstrap. -/
theorem scalarSearchOnlyPoint_localization
    (m : ProbedMethod E) (hm : CorrectionFree m)
    (T : E ≃L[ℝ] E) (hT : T.symm.toContinuousLinearMap.IsSymmetric)
    (f : E → ℝ) (G : E → E) (H : E → E →L[ℝ] E)
    {r : ℝ} (hr : 0<r) (hG₀ : G 0=0)
    (hH₀ : coordinateDerivative T H 0=ContinuousLinearMap.id ℝ E)
    {L : ℝ≥0} (hLr : (L:ℝ)*r≤1/2)
    (hH : LipschitzOnWith L (coordinateDerivative T H) (closedBall 0 r))
    (hF : ∀ z,‖T z‖≤r →HasFDerivAt f (innerSL ℝ (G z)) z)
    (hG : ∀ z,‖T z‖≤r →HasFDerivAt G (H z) z)
    (x₀ : E) (hx₀ : ‖T x₀‖<r/2) :
    ∀ k : ℕ,‖T (scalarFunctionPoint m T f G r x₀ k)‖≤Real.sqrt 3*‖T x₀‖ ∧
      ‖T (scalarFunctionPoint m T f G r x₀ k)‖≤(1+2*(L:ℝ)*‖T x₀‖)*‖T x₀‖ ∧
      ‖T (scalarFunctionPoint m T f G r x₀ k)‖<r := by
  have hFc z (hz : z∈closedBall (0:E) r) :
      HasFDerivAt (coordinateObjective T f) (innerSL ℝ (coordinateGradient T G z)) z := by
    apply coordinateObjective_hasFDerivAt T hT f G z
    apply hF
    simpa only [T.apply_symm_apply,mem_closedBall,dist_zero_right] using hz
  have hGc z (hz : z∈closedBall (0:E) r) :
      HasFDerivAt (coordinateGradient T G) (coordinateDerivative T H z) z := by
    apply coordinateGradient_hasFDerivAt T G H z
    apply hG
    simpa only [T.apply_symm_apply,mem_closedBall,dist_zero_right] using hz
  have hg₀ : coordinateGradient T G 0=0 := by simp only [coordinateGradient,map_zero,hG₀]
  have hsteps:=scalarSearchOnlyPoint_chord_steps m hm T hT f G H hr hH₀ hLr hH hF hG x₀
    (by linarith [norm_nonneg (T x₀)])
  intro k
  have hh:=exact_search_trajectory_localization (coordinateObjective T f) (coordinateGradient T G)
    (coordinateDerivative T H) hr hg₀ hH₀ hLr hH hFc hGc
    (fun i=>T (scalarFunctionPoint m T f G r x₀ i))
    (fun i=>T (m.direction (scalarFunctionRun m T f G r x₀ i))) k
    (by simpa only [scalarFunctionPoint,scalarFunctionRun,History.displacement,List.map_nil,List.sum_nil,add_zero] using hx₀)
    (fun i _=>hsteps i) k le_rfl
  simpa only [scalarFunctionPoint,scalarFunctionRun,History.displacement,List.map_nil,List.sum_nil,add_zero,
    mem_ball,dist_zero_right] using hh

end
end krylov.Convergence
