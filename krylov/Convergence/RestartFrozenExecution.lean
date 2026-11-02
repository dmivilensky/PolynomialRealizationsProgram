import krylov.Convergence.RestartFrozenInputs
import krylov.Convergence.RestartFrozenQueries

/-!
Article: main_krylov, thm:D, literal frozen final corrections.
Use: define the final model solely from the actual FC points and their
observed gradients, execute all extra gradient queries with that same model,
and prove its exact coupling to the ambient inverse-model analysis.
Source: the actual scalar FC transcript and Burdakov's square model identity.
-/
namespace krylov.Convergence
noncomputable section
open Matrix Set Metric krylov.Methods krylov.Reference krylov.Functions krylov.Nonlinear krylov.Secant
open scoped InnerProductSpace NNReal Matrix.Norms.L2Operator
variable {n : ℕ}

/-- The complete chronological step data actually observed in one FC
cycle. Article: thm:D, same frozen full window for every extra correction. -/
def nativeFCFrozenSteps (T : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (r : ℝ)
    (x₀ : EuclideanSpace ℝ (Fin n)) : Fin n → EuclideanSpace ℝ (Fin n) :=
  fun i=>metricFCPoint T f G fullMemory r x₀ (i.val+1)-metricFCPoint T f G fullMemory r x₀ i.val

/-- Actual gradient differences on the complete frozen FC window.
The Hessian is absent from these data. Article: thm:D. -/
def nativeFCFrozenImages (T : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (r : ℝ)
    (x₀ : EuclideanSpace ℝ (Fin n)) : Fin n → EuclideanSpace ℝ (Fin n) :=
  fun i=>G (metricFCPoint T f G fullMemory r x₀ (i.val+1))-G (metricFCPoint T f G fullMemory r x₀ i.val)

/-- The actual full matrix formed exclusively from the observed frozen
window, without access to the unknown Hessian. Article: thm:D. -/
def nativeFCFrozenMatrix (T : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (r : ℝ)
    (x₀ : EuclideanSpace ℝ (Fin n)) : Matrix (Fin n) (Fin n) ℝ :=
  inverseCongruence (windowMatrix (nativeFCFrozenSteps T f G r x₀))
    (ss1Model (nativeFCFrozenSteps T f G r x₀) (nativeFCFrozenImages T f G r x₀))

/-- Every extra query uses the unchanged full observed coefficient model
and the actual current gradient. Article: main_krylov, thm:D. -/
def nativeFCFrozenPoints (T : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (r : ℝ)
    (x₀ : EuclideanSpace ℝ (Fin n)) : ℕ → EuclideanSpace ℝ (Fin n)
  | 0=>metricFCPoint T f G fullMemory r x₀ n
  | j+1=>ss1Point (nativeFCFrozenSteps T f G r x₀) (nativeFCFrozenImages T f G r x₀)
      (G (nativeFCFrozenPoints T f G r x₀ j)) (nativeFCFrozenPoints T f G r x₀ j)

/-- Primitive local derivatives identify every actual frozen observation
with the corresponding genuinely executed operator step and image.
Article: thm:D, no trajectory or measured-secant identity is assumed. -/
theorem nativeFCFrozen_observations
    (T : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (hT : T.symm.toContinuousLinearMap.IsSymmetric)
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    {r : ℝ} (hr : 0<r) (hG₀ : G 0=0)
    (hHc₀ : coordinateDerivative T H 0=ContinuousLinearMap.id ℝ _)
    {L : ℝ≥0} (hLr : (L:ℝ)*r≤1/2)
    (hH : LipschitzOnWith L (coordinateDerivative T H) (closedBall 0 r))
    (hF : ∀ z,‖T z‖≤r → HasFDerivAt f (innerSL ℝ (G z)) z)
    (hG : ∀ z,‖T z‖≤r → HasFDerivAt G (H z) z)
    (x₀ : EuclideanSpace ℝ (Fin n)) (hx₀ : ‖T x₀‖<r/4) :
    let A := metricFCOperator T f G H fullMemory r x₀
    nativeFCFrozenSteps T f G r x₀=fcFrozenColumns A (G x₀) ∧
      nativeFCFrozenImages T f G r x₀=(fun i=>A i.val (fcFrozenColumns A (G x₀) i)) ∧
      nativeFCFrozenMatrix T f G r x₀=fcFrozenMatrix A (G x₀) := by
  dsimp only
  let A := metricFCOperator T f G H fullMemory r x₀
  have hs : nativeFCFrozenSteps T f G r x₀=fcFrozenColumns A (G x₀) := by
    funext i
    exact metricFCPoint_step_eq_fcStep T hT f G H hr hG₀ hHc₀ hLr hH hF hG fullMemory x₀ hx₀ i.val
  have hg j : fcGradient fullMemory A (G x₀) j=G (metricFCPoint T f G fullMemory r x₀ j) := by
    have hh := congrArg History.gradient
      (metricFCObservedHistory_eq_fcHistory T hT f G H hr hG₀ hHc₀ hLr hH hF hG fullMemory x₀ hx₀ j)
    simp only [metricFCObservedHistory,observedSearchHistory_gradient] at hh
    exact hh.symm
  have hy : nativeFCFrozenImages T f G r x₀=(fun i=>A i.val (fcFrozenColumns A (G x₀) i)) := by
    funext i
    change G (metricFCPoint T f G fullMemory r x₀ (i.val+1))-
      G (metricFCPoint T f G fullMemory r x₀ i.val)=_
    rw [←hg (i.val+1),←hg i.val,fcGradient_succ,add_sub_cancel_left]
    rfl
  exact ⟨hs,hy,by rw [nativeFCFrozenMatrix,hs,hy]; rfl⟩

/-- Once the true measured full window is independent, every actual
extra correction equals the corresponding genuine ambient model query.
Article: main_krylov, thm:D. -/
theorem nativeFCFrozenPoints_eq
    (T : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (r : ℝ)
    (x₀ : EuclideanSpace ℝ (Fin n))
    (hu : IsUnit (windowMatrix (nativeFCFrozenSteps T f G r x₀)).det) :
    nativeFCFrozenPoints T f G r x₀=
      frozenModelPoints (nativeFCFrozenMatrix T f G r x₀) G
        (metricFCPoint T f G fullMemory r x₀ n) := by
  funext j
  induction j with
  | zero=>rfl
  | succ j ih=>
    rw [nativeFCFrozenPoints,ss1Point_eq_model_step _ _ _ _ hu,ih]
    rfl

/-- A genuinely solved FC cycle remains solved through every extra
frozen correction, without a nonzero-step or inverse-domain assumption.
Article: thm:D, stationary tails. -/
theorem nativeFCFrozenPoints_stationary
    (T : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (r : ℝ)
    (hG : G 0=0) (hFC : metricFCPoint T f G fullMemory r 0 n=0) (j : ℕ) :
    nativeFCFrozenPoints T f G r 0 j=0 := by
  induction j with
  | zero=>exact hFC
  | succ j ih=>
    rw [nativeFCFrozenPoints,ih,hG,ss1Point,
      modelCoefficients_zero _ _ _ (by ext i; simp only [coordinates,inner_zero_right,Pi.zero_apply])]
    simp only [combine,Pi.zero_apply,zero_smul,Finset.sum_const_zero,zero_add]

end
end krylov.Convergence
