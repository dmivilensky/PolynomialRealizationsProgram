import krylov.Cancellation.DCRadauEstimate
import krylov.Completion.DampingBand
import krylov.Completion.QuadraticObservedWindow
import krylov.Reference.CanonicalSteps
set_option autoImplicit false
/-!
Article: main_krylov, s8:dcsdef and thm:dcs, genuine native window feasibility.
Use: derive the source physical completion policy's rank, new-direction and
feasibility domains from actual independent quadratic observations and the
original observed descent pairing.
Source: true positive native conjugacy solve, genuine physical matrix/operator
coordinates and finite synthesis; no completion-domain witness is assumed.
-/

namespace krylov.Cancellation
noncomputable section
open Matrix krylov.Methods krylov.Reference krylov.Completion krylov.OneGradient
open scoped BigOperators
variable {n : ℕ}

/-- A genuine independent quadratic observed window with positive original
descent pairing automatically supplies every original physical completion
domain for its untilted direction.
Use: the actual observed Gauss--Radau DC rule needs no supplied rank, outside-span
or feasible-completion hypothesis once its real reference data are known.
Article: main_krylov, s8:dcsdef and thm:dcs(b,c).
Proof: true independent quadratic secants make the native conjugacy Gram
positive definite. Physical columns preserve independence. The actual native
direction annihilates every old quadratic image and is nonzero by its positive
observed slope, so positivity keeps it outside the old span. Genuine physical
matrix/operator coordinates identify the observed compression and conjugacy
constraints exactly; the original matrix itself is a real feasible completion. -/
theorem dc_quadratic_window_feasible (memory : ℕ → ℕ)
    (H : History (EuclideanSpace ℝ (Fin n)))
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef) (mu L : ℝ)
    (hlo : (base-mu • 1).PosSemidef) (hhi : (L • 1-base).PosSemidef)
    (hy : ∀ j,windowImages (selectedWindow memory H) j=
      cgOperator base (windowSteps (selectedWindow memory H) j))
    (hLI : LinearIndependent ℝ (windowSteps (selectedWindow memory H)))
    (hq : 0<dcCurvatureSlope memory H) :
    Function.Injective (dcObservedColumns memory H).mulVec ∧
      dcObservedUntilted memory H∉LinearMap.range (dcObservedColumns memory H).mulVecLin ∧
      base∈windowCurvatureCompletions (dcObservedColumns memory H) (dcObservedUntilted memory H)
        (windowModel (selectedWindow memory H)) mu L := by
  have hd : windowDirection (selectedWindow memory H) H.gradient≠0 := by
    intro hz
    change 0 < -inner ℝ (virtualGradient (selectedWindow memory H) H.gradient)
      (windowDirection (selectedWindow memory H) H.gradient) at hq
    rw [hz,inner_zero_right,neg_zero] at hq
    exact lt_irrefl _ hq
  exact quadratic_observed_window_feasible (selectedWindow memory H) base hb mu L hlo hhi
    H.gradient hy hLI hd

/-- The actual observed arithmetic DC estimate has the original uniform
spectral damping factor at every genuine feasible quadratic observed window.
Use: all completion domains are derived from the real native observations,
including the empty window and singular shifted old spectral models.
Article: main_krylov, thm:dcs(c), |epsilonHat|≤rho_kappa.
Proof: the genuine native quadratic window supplies rank, a new direction
and the original matrix as a feasible physical completion. Actual positive
known-data endpoint range and the proved physical arithmetic band theorem
then give the source bound for every real consistent matrix scenario. -/
theorem dc_quadratic_gauss_radau_bound (memory : ℕ → ℕ)
    (H : History (EuclideanSpace ℝ (Fin n)))
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef) (mu L : ℝ) (hmu : 0<mu) (hmuL : mu≤L)
    (hlo : (base-mu • 1).PosSemidef) (hhi : (L • 1-base).PosSemidef)
    (hy : ∀ j,windowImages (selectedWindow memory H) j=
      cgOperator base (windowSteps (selectedWindow memory H) j))
    (hLI : LinearIndependent ℝ (windowSteps (selectedWindow memory H)))
    (hq : 0<dcCurvatureSlope memory H) :
    0<dcGaussRadauEstimate memory mu L H ∧
      ∀ A∈windowCurvatureCompletions (dcObservedColumns memory H) (dcObservedUntilted memory H)
        (windowModel (selectedWindow memory H)) mu L,
      |1-physicalTrialLength (dcObservedUntilted memory H) (dcCurvatureSlope memory H) A/
        dcGaussRadauEstimate memory mu L H|≤(L-mu)/(L+mu) := by
  obtain ⟨hS,hd,hbase⟩ := dc_quadratic_window_feasible memory H base hb mu L hlo hhi hy hLI hq
  have hC := Set.nonempty_of_mem hbase
  have hmin := dc_gauss_radau_minimax memory mu L H hmu hmuL hS hd hC hq
  obtain ⟨hl,horder,hrange⟩ := observed_window_curvature_range _ hS _ hd _ mu L hmu hmuL hC
  refine ⟨hmin.1,?_⟩
  intro A hA
  exact physical_arithmetic_damping_bound _ _ _ _ _ mu L hq hmu hmuL hl horder hrange
    (fun _ hmem => ⟨hmem.2.1,hmem.2.2.1⟩) A hA

end
end krylov.Cancellation
