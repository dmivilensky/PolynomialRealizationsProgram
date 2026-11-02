import krylov.Convergence.WindowNativeRate
import krylov.XR.CorrectedGrowthSource

/-!
Article: main_krylov, thm:grow, ordinary full-memory branch of the unified source.
Use: identify selected-model G3 with ordinary G3 when values are disabled,
then reuse the genuine full SS1 trajectory and physical R-order. Source:
the actual model selection definition; no successful phase is assumed.
-/
namespace krylov.Convergence
noncomputable section
open Matrix Set Filter Topology krylov.XR krylov.Methods krylov.Nonlinear krylov.Reference
open scoped InnerProductSpace Matrix.Norms.L2Operator NNReal
variable {n : ℕ}

/-- With the value flag off, the primitive selected-source trial condition
is exactly the original ordinary trial condition. -/
def selectedSourceToOrdinary (P : Parameters)
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (x₀ center : EuclideanSpace ℝ (Fin n)) (bounds : SpectralBounds)
    (D : SelectedGrowthSource P f G H x₀ center bounds) (hoff : P.valuesEnabled=false) :
    GrowthSource P f G H x₀ center bounds where
  mu:=D.mu
  sigma:=D.sigma
  upper:=D.upper
  ell:=D.ell
  trialUpper:=D.trialUpper
  eta:=D.eta
  mu_pos:=D.mu_pos
  sigma_pos:=D.sigma_pos
  upper_pos:=D.upper_pos
  ell_pos:=D.ell_pos
  trialUpper_pos:=D.trialUpper_pos
  eta_pos:=D.eta_pos
  f_deriv:=D.f_deriv
  g_deriv:=D.g_deriv
  h_cont:=D.h_cont
  coercive:=D.coercive
  h_norm:=D.h_norm
  converges:=D.converges
  distinct:=D.distinct
  gainStart:=D.gainStart
  gain:=D.gain
  trialStart:=D.trialStart
  trial:=by
    intro k hk
    dsimp only
    intro hp hn hd
    let S:=algorithmRun P f G x₀ bounds k
    have hmodel (W : List (PairObservation (EuclideanSpace ℝ (Fin n)))) :
        selectedModel P W=storedModel W := by simp [selectedModel,hoff]
    have hdir : algorithmSelectedDirection P S=
        modelDirection (storedSteps (algorithmModel P S).pairs) (storedImages (algorithmModel P S).pairs)
          (storedModel (algorithmModel P S).pairs) S.gradient := by
      rw [algorithmSelectedDirection,hmodel]
    change modelDirection (storedSteps (algorithmModel P S).pairs) (storedImages (algorithmModel P S).pairs)
      (storedModel (algorithmModel P S).pairs) S.gradient≠0 at hd
    rw [←hdir] at hd ⊢
    exact D.trial k hk hp hn hd
  safeguard_descent:=D.safeguard_descent
  safeguard_norm:=D.safeguard_norm

/-- Unified original G1--G4 with the value flag off imply the actual
full-window SS1 tail, with its own accepted seed points. -/
theorem selected_source_full_eq_ss1Sequence (P : Parameters)
    (f : EuclideanSpace ℝ (Fin (n+1)) → ℝ)
    (G : EuclideanSpace ℝ (Fin (n+1)) → EuclideanSpace ℝ (Fin (n+1)))
    (H : EuclideanSpace ℝ (Fin (n+1)) → EuclideanSpace ℝ (Fin (n+1)) →L[ℝ]
      EuclideanSpace ℝ (Fin (n+1)))
    (x₀ center : EuclideanSpace ℝ (Fin (n+1))) (bounds : SpectralBounds)
    (D : SelectedGrowthSource P f G H x₀ center bounds) (hP : P.Valid (n+1))
    (hoff : P.valuesEnabled=false) (hmax : P.maximumCapacity=n+1) :
    ∃ K,∀ j,(algorithmRun P f G x₀ bounds (K+j)).point=
      ss1Sequence G (fun i : Fin (n+2)=>(algorithmRun P f G x₀ bounds (K+i.val)).point) j := by
  exact source_full_eq_ss1Sequence P f G H x₀ center bounds
    (selectedSourceToOrdinary P f G H x₀ center bounds D hoff) hP hoff hmax

/-- The literal ordinary full-window rate follows from unified source
hypotheses in the true physical Hessian norm. This includes source data
constructed by the G3-free initially-full theorem. -/
theorem selected_source_full_XR_physical_rorder (P : Parameters)
    (f : EuclideanSpace ℝ (Fin (n+1)) → ℝ)
    (G : EuclideanSpace ℝ (Fin (n+1)) → EuclideanSpace ℝ (Fin (n+1)))
    (H : EuclideanSpace ℝ (Fin (n+1)) → EuclideanSpace ℝ (Fin (n+1)) →L[ℝ]
      EuclideanSpace ℝ (Fin (n+1)))
    (x₀ center : EuclideanSpace ℝ (Fin (n+1))) (bounds : SpectralBounds)
    (D : SelectedGrowthSource P f G H x₀ center bounds) (hP : P.Valid (n+1))
    (hoff : P.valuesEnabled=false) (hmax : P.maximumCapacity=n+1)
    (base : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hb : base.PosDef)
    (hbase : H center=cgOperator base)
    (S : Set (EuclideanSpace ℝ (Fin (n+1)))) (hS : Convex ℝ S)
    (hc : center∈S) (hn : S∈𝓝 center) {L : ℝ≥0} (hH : LipschitzOnWith L H S)
    (hG : ∀ z∈S,HasFDerivAt G (H z) z) :
    HasROrder (fun k=>‖(metricCoordinates base hb)
      ((algorithmRun P f G x₀ bounds k).point-center)‖) (oneGradientRoot (n+2)) := by
  exact source_full_XR_physical_rorder P f G H x₀ center bounds
    (selectedSourceToOrdinary P f G H x₀ center bounds D hoff) hP hoff hmax base hb hbase S hS hc hn hH hG

end
end krylov.Convergence
