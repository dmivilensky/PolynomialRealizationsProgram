import krylov.Convergence.SlidingMetricSource
import krylov.Convergence.RFCPathSuperlinear

/-!
Article: main_krylov, thm:Ip, exact physical RFC query transport.
Use: carry the original physical observed probe and actual gated full-model
query into the true Hstar metric without changing its direction policy.
Source: invariance of primal/dual endpoint pairings and the actual scalar
latest-information model solve. Every path identity is derived here.
-/
namespace krylov.Convergence
noncomputable section
open Matrix Set Filter Topology krylov.Methods krylov.Functions krylov.Nonlinear krylov.Reference
open scoped InnerProductSpace Matrix.Norms.L2Operator NNReal BigOperators
variable {n m : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
set_option maxHeartbeats 1000000

/-- The true observed skew gate is exactly invariant under metric
primal/dual coordinates. -/
theorem pairDefect_metric (T : E ≃L[ℝ] E) (hT : T.symm.toContinuousLinearMap.IsSymmetric)
    (s y : Fin m → E) : pairDefect (fun i=>T (s i)) (fun i=>T.symm (y i))=pairDefect s y := by
  ext i j
  simp only [pairDefect,inverse_symmetric_pairing T hT]

/-- The real chronological latest model is the same scalar matrix in
the physical and actual metric-coordinate observed windows. -/
theorem ss1Model_metric (T : E ≃L[ℝ] E) (hT : T.symm.toContinuousLinearMap.IsSymmetric)
    (s y : Fin m → E) : ss1Model (fun i=>T (s i)) (fun i=>T.symm (y i))=ss1Model s y := by
  ext i j
  simp only [ss1Model,krylov.Secant.latest,crossGram,inverse_symmetric_pairing T hT]

/-- The original evaluated RFC query, including its actual observed gate,
commutes with the true centred metric coordinate map. -/
theorem evaluatedRFCPoint_centered_metric (T : E ≃L[ℝ] E)
    (hT : T.symm.toContinuousLinearMap.IsSymmetric) (center : E) (G : E → E)
    (s y : Fin (n+1) → E) (x v : E) (γ : ℝ) :
    T (evaluatedRFCPoint G s y x v γ-center)=
      evaluatedRFCPoint (centeredMetricGradient T center G) (fun i=>T (s i)) (fun i=>T.symm (y i))
        (T (x-center)) (T v) γ := by
  classical
  have hg (a : E) : centeredMetricGradient T center G (T (a-center))=T.symm (G a) := by
    have hc : center+(a-center)=a := by abel_nf
    simp only [centeredMetricGradient,coordinateGradient,T.symm_apply_apply,hc]
  have hplus : T (x-center)+T v=T (x+v-center) := by
    rw [←map_add]
    congr 1
    abel_nf
  have hSnoc : (Fin.snoc (fun i=>T (s i)) (T v):Fin (n+2) → E)=
      fun i=>T ((Fin.snoc s v:Fin (n+2) → E) i) := by
    funext i
    exact Fin.lastCases (by rw [Fin.snoc_last,Fin.snoc_last]) (fun j=>by rw [Fin.snoc_castSucc,Fin.snoc_castSucc]) i
  have hYsnoc : (Fin.snoc (fun i=>T.symm (y i))
      (centeredMetricGradient T center G (T (x-center)+T v)-centeredMetricGradient T center G (T (x-center))) :
      Fin (n+2) → E)=fun i=>T.symm ((Fin.snoc y (G (x+v)-G x):Fin (n+2) → E) i) := by
    rw [hplus,hg,hg]
    funext i
    refine Fin.lastCases ?_ (fun j=>?_) i
    · simp only [Fin.snoc_last,map_sub]
    · rw [Fin.snoc_castSucc,Fin.snoc_castSucc]
  have hcoords : coordinates (fun i=>T ((Fin.snoc s v:Fin (n+2) → E) i)) (T.symm (G (x+v)))=
      coordinates (Fin.snoc s v) (G (x+v)) := by
    funext i
    exact inverse_symmetric_pairing T hT _ _
  by_cases hgate : ‖pairDefect s y‖<γ
  · simp only [evaluatedRFCPoint,pairDefect_metric T hT,ite_eq_left hgate]
    rw [hYsnoc,hSnoc,ss1Model_metric T hT,hplus,hg]
    simp only [modelCoefficients,hcoords,combine,map_sub,map_add,map_sum,map_smul]
    abel_nf
  · simp only [evaluatedRFCPoint,pairDefect_metric T hT,ite_eq_right hgate,map_sub,map_add]
    abel_nf

/-- Exact canonical path data of the original physical bounded-probe RFC,
with its actual unchanged observed direction policy. -/
theorem slidingRFCSequence_metric_data (T : E ≃L[ℝ] E)
    (hT : T.symm.toContinuousLinearMap.IsSymmetric) (center : E) (G : E → E)
    (probe : (Fin (n+2) → E) → E → ℝ) (γ : ℝ) (seed : Fin (n+2) → E)
    (hconv : Tendsto (slidingRFCSequence G probe γ seed) atTop (𝓝 center))
    (hsolve : ∀ᶠ k in atTop,IsUnit (slidingRFCSolveMatrix (n:=n) G (slidingRFCSequence G probe γ seed) k).det) :
    let x:=slidingRFCSequence G probe γ seed
    let z:=fun k=>T (x k-center)
    let v:=fun k=>T (slidingRFCProbe G probe x k)
    (∀ k,z (k+n+2)=evaluatedRFCPoint (centeredMetricGradient T center G)
      (windowStep (n:=n+1) z k) (windowImage (centeredMetricGradient T center G) z k) (z (k+n+1)) (v k) γ) ∧
    Tendsto z atTop (𝓝 0) ∧
    (∀ᶠ k in atTop,IsUnit (slidingRFCSolveMatrix (n:=n) (centeredMetricGradient T center G) z k).det) ∧
    (∀ᶠ k in atTop,∀ i : Fin (n+1),inner ℝ (windowImage (centeredMetricGradient T center G) z k i) (v k)=0) := by
  let x:=slidingRFCSequence G probe γ seed
  let z:=fun k=>T (x k-center)
  let v:=fun k=>T (slidingRFCProbe G probe x k)
  refine ⟨?_,?_,?_,?_⟩
  · intro k
    change T (slidingRFCSequence G probe γ seed (k+n+2)-center)=_
    rw [slidingRFCSequence_step_eq_evaluated,evaluatedRFCPoint_centered_metric T hT,
      centered_metric_windowStep,centered_metric_windowImage]
  · have hx : Tendsto (fun k=>x k-center) atTop (𝓝 0) := by simpa only [sub_self] using hconv.sub_const center
    simpa only [Function.comp_def,map_zero] using (T.continuous.tendsto 0).comp hx
  · filter_upwards [hsolve] with k hk
    have he : slidingRFCSolveMatrix (n:=n) (centeredMetricGradient T center G) z k=
        slidingRFCSolveMatrix (n:=n) G x k := by
      ext i j
      exact centered_metric_window_pair T hT center G x k i j
    rw [he]
    exact hk
  · filter_upwards [hsolve] with k hk i
    rw [centered_metric_windowImage]
    change inner ℝ (T.symm (windowImage G x k i)) (T (slidingRFCProbe G probe x k))=0
    rw [real_inner_comm,inverse_symmetric_pairing T hT,real_inner_comm]
    exact slidingRFCProbe_conjugate G probe x k hk i

/- Any actual nonempty unit-column gain is automatically at most one. -/
omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
theorem unit_window_gain_le_one
    (s : Fin (m+1) → EuclideanSpace ℝ (Fin n)) (hs : ∀ i,s i≠0)
    {σ : ℝ} (hσ : 0≤σ)
    (hgain : ∀ c : Fin (m+1) → ℝ,σ^2*‖WithLp.toLp 2 c‖^2≤‖combine (unitWindow s) c‖^2) : σ≤1 := by
  have hh:=hgain (Pi.single 0 1)
  have he : WithLp.toLp 2 (Pi.single 0 (1:ℝ))=(PiLp.single 2 0 (1:ℝ):EuclideanSpace ℝ (Fin (m+1))) := rfl
  have hc : combine (unitWindow s) (Pi.single 0 1)=unitWindow s 0 := by simp [combine,Pi.single_apply]
  rw [he,hc,unitWindow_norm s hs 0,PiLp.norm_single] at hh
  norm_num at hh
  simpa only [abs_of_nonneg hσ] using hh

end
end krylov.Convergence
