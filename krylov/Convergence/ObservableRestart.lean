import krylov.Functions.NativeRFCExecution

/-!
Article: main_krylov, apG:Dunif, literal observable restart protocol.
Use: implement the actual finite FC/RFC cycle using only true function
and gradient observations, the current inverse solve, descent, correction
energy and the value acceptance test. Its output/rate is not a data field.
Source: the observable restart rules in Proposition apG:Dunif. The local
metric chord is the existing actual exact-search implementation; analytic
theorems prove that its minimizing point is interior in the admitted phase.
-/
namespace krylov.Convergence
noncomputable section
open Matrix krylov.Methods krylov.Functions
open scoped InnerProductSpace Matrix.Norms.L2Operator
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The actual reason a finite observable cycle terminates.
Article: main_krylov, apG:Dunif. -/
inductive ObservableRestartReason
  | horizon
  | stationary
  | direction
  | energy
  deriving DecidableEq

/-- Current actual observations and an optional observable stopping
reason. Every new cycle starts with empty memory at this returned point.
Article: main_krylov, apG:Dunif. -/
structure ObservableCycleState (E : Type*) where
  history : History E
  reason : Option ObservableRestartReason

/-- Append an actually queried endpoint as one genuine iteration record.
The correction list records the real additional gradient query only.
Article: main_krylov, apG:Dunif, actual observed pair convention. -/
def observableRecord (T : E ≃L[ℝ] E) (f : E → ℝ) (G : E → E)
    (r : ℝ) (x₀ : E) (H : History E) (u : E) (queried : Bool) : IterationRecord E :=
  let y := rfcFunctionLinePoint T f fullMemory r x₀ H
  let s := rfcFunctionLineStep T f fullMemory r x₀ H
  let d := rfcFunctionDirection fullMemory H
  let alpha := observedLineParameter d s
  ⟨d,alpha⁻¹ • (G y-H.gradient),s+u,G (y+u),if queried then [(u,G (y+u))] else []⟩

/-- The literal computed model energy of the proposed RFC correction.
The ordinary original defect gate is retained, including its empty case.
Article: main_krylov, apG:Dunif, w transpose H w. -/
def observableCorrectionEnergy (T : E ≃L[ℝ] E) (f : E → ℝ) (G : E → E)
    (r : ℝ) (x₀ : E) (H : History E) : ℝ := by
  classical
  let y := rfcFunctionLinePoint T f fullMemory r x₀ H
  let s := rfcFunctionLineStep T f fullMemory r x₀ H
  let U := (s,G y-H.gradient)::selectedWindow fullMemory H
  let w := modelCoefficients (windowSteps U) (windowModel U) (G y)
  exact if rfcFunctionGate fullMemory H then w ⬝ᵥ (windowModel U*ᵥw) else 0

/-- The observed correction-to-line model-energy ratio, computed from
the real searched step and actual newest gradient difference.
Article: main_krylov, apG:Dunif, varpi_k. -/
def observableCorrectionRatio (T : E ≃L[ℝ] E) (f : E → ℝ) (G : E → E)
    (r : ℝ) (x₀ : E) (H : History E) : ℝ :=
  let y := rfcFunctionLinePoint T f fullMemory r x₀ H
  let s := rfcFunctionLineStep T f fullMemory r x₀ H
  Real.sqrt (observableCorrectionEnergy T f G r x₀ H/inner ℝ s (G y-H.gradient))

/-- One actual observable iteration. A failed energy gate returns the
already evaluated line endpoint and restarts there; a value-increasing
correction is omitted. FC is precisely the corrections=false branch.
Article: main_krylov, apG:Dunif. -/
def observableRestartAdvance (corrections : Bool) (bar : ℝ)
    (T : E ≃L[ℝ] E) (f : E → ℝ) (G : E → E) (r : ℝ) (x₀ : E) (H : History E) :
    ObservableCycleState E := by
  classical
  let W := selectedWindow fullMemory H
  let d := rfcFunctionDirection fullMemory H
  let y := rfcFunctionLinePoint T f fullMemory r x₀ H
  let u := rfcFunctionCorrectionStep T f G fullMemory r x₀ H
  let lineH : History E := ⟨H.initial,observableRecord T f G r x₀ H 0 false::H.records⟩
  exact if H.gradient=0 then ⟨H,some .stationary⟩
    else if ¬IsUnit (crossGram (windowImages W) (windowSteps W)).det ∨ ¬inner ℝ H.gradient d<0 then
      ⟨H,some .direction⟩
    else if corrections=true ∧ bar<observableCorrectionRatio T f G r x₀ H then
      ⟨lineH,some .energy⟩
    else if corrections=true ∧ rfcFunctionGate fullMemory H ∧ f (y+u)≤f y then
      ⟨⟨H.initial,observableRecord T f G r x₀ H u true::H.records⟩,none⟩
    else ⟨lineH,none⟩

/-- The actual finite cycle stops at the first observable restart or
after the prescribed number of iterations. No future successful test
or nondegeneracy assumption enters this recursion.
Article: main_krylov, apG:Dunif. -/
def observableCycleFrom (corrections : Bool) (bar : ℝ)
    (T : E ≃L[ℝ] E) (f : E → ℝ) (G : E → E) (r : ℝ) (x₀ : E) :
    ℕ → History E → ObservableCycleState E
  | 0,H => ⟨H,some .horizon⟩
  | k+1,H =>
      let S := observableRestartAdvance corrections bar T f G r x₀ H
      if S.reason.isSome then S else observableCycleFrom corrections bar T f G r x₀ k S.history

/-- A real observable restarted cycle begins with exactly one initial
gradient and empty memory. Article: main_krylov, apG:Dunif. -/
def observableRestartCycle (corrections : Bool) (bar : ℝ)
    (T : E ≃L[ℝ] E) (f : E → ℝ) (G : E → E) (r : ℝ) (N : ℕ) (x₀ : E) : ObservableCycleState E :=
  observableCycleFrom corrections bar T f G r x₀ N ⟨G x₀,[]⟩

/-- The genuine returned endpoint of the complete observable cycle.
Article: main_krylov, apG:Dunif. -/
def observableRestartPoint (corrections : Bool) (bar : ℝ)
    (T : E ≃L[ℝ] E) (f : E → ℝ) (G : E → E) (r : ℝ) (N : ℕ) (x₀ : E) : E :=
  x₀+(observableRestartCycle corrections bar T f G r N x₀).history.displacement

end
end krylov.Convergence
