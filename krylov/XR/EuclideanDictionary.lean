import krylov.XR.EuclideanLocalSelected
import krylov.XR.CorrectedDictionary
import krylov.Convergence.SplitSourceAsymptotic

/-!
Article: main_krylov, cor:xrF, literal Euclidean endpoint-value dictionary.
Use: identify the real cached/gated Euclidean model and full computed
query with the original SS1-F endpoint-value map, before rate arguments.
Source: genuine observed values/gradients, Euclidean midpoint projection,
and the literal full-window executor branch.
-/
namespace krylov.XR
noncomputable section
open Matrix krylov.Methods krylov.Secant krylov.Functions
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- On a real nonzero observed segment, the native Euclidean split is
exactly the article's midpoint split. -/
theorem euclideanStoredSplit_eq_innerSplit (x : E) (W : List (PairObservation E))
    (i : Fin W.length) (hs : storedSteps W i≠0) :
    euclideanStoredSplit x W i=innerSplit (storedAnchors W i) (storedSteps W i) x := by
  have hn : ‖storedSteps W i‖^2≠0:=ne_of_gt (sq_pos_of_pos (norm_pos_iff.mpr hs))
  simp only [euclideanStoredSplit,innerSplit,inner_sub_right,inner_add_right,
    real_inner_smul_right,real_inner_self_eq_norm_sq,storedAnchors]
  field_simp [hn]
  ring

/-- A full Euclidean model has no independent new-direction trial. -/
theorem euclideanTrialParameter_full {n : ℕ} (P : Parameters)
    (S : State (EuclideanSpace ℝ (Fin n))) (hn : 0<n)
    (hp : (euclideanAlgorithmModel P S).pairs.length=n) : euclideanTrialParameter P S=0 := by
  classical
  unfold euclideanTrialParameter
  dsimp only
  rw [ite_eq_right (by omega),ite_eq_left (Or.inl hp)]

/-- Every genuine observed scalar diagonal is retained exactly when its
actual oversized-term bound holds. -/
theorem euclideanStoredValueTerm_eq_raw (x : E) (W : List (PairObservation E)) (i : Fin W.length)
    (hgate : |12 * euclideanStoredSplit x W i * (W.get i).valueDefect| ≤ storedPairing W i i / 2) :
    euclideanStoredValueTerm x W i = 12 * euclideanStoredSplit x W i * (W.get i).valueDefect := by
  classical
  exact ite_eq_right (not_lt.mpr hgate)

/-- The actually cached and gated XR value model is the genuine endpoint
function-value model when its exact oversized-term gates pass. -/
theorem euclideanStoredValueModel_eq_actual (f : E → ℝ) (G : E → E) (x : E)
    (W : List (PairObservation E)) (hW : ∀ a ∈ W, PairFaithful f G x a)
    (hgate : ∀ i : Fin W.length,
      |12 * euclideanStoredSplit x W i * (W.get i).valueDefect| ≤ storedPairing W i i / 2) :
    euclideanStoredValueModel x W = valueCorrectedModel f (fun z => innerSL ℝ (G z))
      (storedAnchors W) (storedSteps W) (euclideanStoredSplit x W) := by
  rw [krylov.Convergence.valueCorrectedModel_eq_ss1Model]
  have hy : (fun i : Fin W.length => G (storedAnchors W i + storedSteps W i) - G (storedAnchors W i)) =
      storedImages W := by
    funext i
    exact (hW _ (List.get_mem _ i)).1.symm
  rw [hy]
  unfold euclideanStoredValueModel
  congr 1
  apply congrArg diagonal
  funext i
  rw [euclideanStoredValueTerm_eq_raw x W i (hgate i), (hW _ (List.get_mem _ i)).valueDefect_eq]
  rfl

/-- The full actual corrected XR branch is precisely the data-only SS1-F
query, after source estimates have forced both genuine value gates. -/
theorem euclideanAlgorithm_full_ss1FPoint {n : ℕ} (P : Parameters) (hon : P.valuesEnabled = true)
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (S : State (EuclideanSpace ℝ (Fin n))) (hn : 0 < n)
    (hfull : (euclideanAlgorithmModel P S).pairs.length = n) (hg : S.gradient = G S.point)
    (hW : ∀ a ∈ (euclideanAlgorithmModel P S).pairs, PairFaithful f G S.point a)
    (hgate : ∀ i : Fin (euclideanAlgorithmModel P S).pairs.length,
      |12 * euclideanStoredSplit S.point (euclideanAlgorithmModel P S).pairs i * ((euclideanAlgorithmModel P S).pairs.get i).valueDefect| ≤
        storedPairing (euclideanAlgorithmModel P S).pairs i i / 2)
    (hpass : euclideanCorrectedWindowPasses P.windowThreshold S.point (euclideanAlgorithmModel P S).pairs) :
    S.point + (euclideanAlgorithmModel P S).direction =
      krylov.Convergence.ss1FPoint f G (storedAnchors (euclideanAlgorithmModel P S).pairs)
        (storedSteps (euclideanAlgorithmModel P S).pairs) (euclideanStoredSplit S.point (euclideanAlgorithmModel P S).pairs) S.point := by
  classical
  have hu := euclideanAlgorithmModel_direction_decomposition P S (by omega)
  rw [euclideanTrialParameter_full P S hn hfull, zero_smul, add_zero] at hu
  have hselected : selectedEuclideanModel P S.point (euclideanAlgorithmModel P S).pairs = euclideanStoredValueModel S.point (euclideanAlgorithmModel P S).pairs :=
    ite_eq_left ⟨hon, hpass⟩
  rw [hselected, euclideanStoredValueModel_eq_actual f G S.point _ hW hgate, hg] at hu
  rw [hu]
  rfl

end
end krylov.XR
