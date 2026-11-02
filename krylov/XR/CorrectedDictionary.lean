import krylov.XR.CorrectedPairBounds
import krylov.XR.GrowthPhase
import krylov.Convergence.SS1FModel

/-!
Article: main_krylov, cor:xrF, exact actual corrected-model dictionary.
Use: connect genuinely cached XR endpoint values/gradients and covector
splits to the existing SS1-F function rule. Gate activation is a separate
source theorem; no derivative or desired output formula is a data field.
Source: exact faithful-observation and full-window ModelStep identities.
-/

namespace krylov.XR
noncomputable section
open Matrix krylov.Methods krylov.Secant krylov.Functions
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Genuine chronological segment starts cached by XR. -/
def storedAnchors (W : List (PairObservation E)) (i : Fin W.length) : E := (W.get i).anchor

/-- On genuine cached observations the implemented split is exactly the
observable secant-covector split, with no unknown Hessian input. -/
theorem storedSplit_eq_covectorSplit (f : E → ℝ) (G : E → E) (x : E)
    (W : List (PairObservation E)) (hW : ∀ a ∈ W, PairFaithful f G x a) (i : Fin W.length)
    (hdiag : storedPairing W i i ≠ 0) :
    storedSplit W i = covectorSplit (innerSL ℝ (storedImages W i))
      (storedAnchors W i) (storedSteps W i) x := by
  have ha := hW _ (List.get_mem _ i)
  simp only [storedSplit, storedPairing, crossGram, storedImages, storedSteps, storedAnchors,
    covectorSplit, innerSL_apply_apply, ha.2.2]
  have hq : inner ℝ (W.get i).step (W.get i).image ≠ 0 := hdiag
  have hq' : inner ℝ (W.get i).image (W.get i).step ≠ 0 := by
    rwa [real_inner_comm]
  have he : x - ((W.get i).anchor + (1 / 2 : ℝ) • (W.get i).step) =
      (x - (W.get i).anchor) - (1 / 2 : ℝ) • (W.get i).step := by abel
  simp only [he, inner_sub_right, real_inner_smul_right]
  rw [real_inner_comm (W.get i).image (W.get i).step]
  field_simp [hq, hq']

/-- Every genuine observed scalar diagonal is retained exactly when its
actual oversized-term bound holds. -/
theorem storedValueTerm_eq_raw (W : List (PairObservation E)) (i : Fin W.length)
    (hgate : |12 * storedSplit W i * (W.get i).valueDefect| ≤ storedPairing W i i / 2) :
    storedValueTerm W i = 12 * storedSplit W i * (W.get i).valueDefect := by
  classical
  exact ite_eq_right (not_lt.mpr hgate)

/-- The actually cached and gated XR value model is the genuine endpoint
function-value model when its exact oversized-term gates pass. -/
theorem storedValueModel_eq_actual (f : E → ℝ) (G : E → E) (x : E)
    (W : List (PairObservation E)) (hW : ∀ a ∈ W, PairFaithful f G x a)
    (hgate : ∀ i : Fin W.length,
      |12 * storedSplit W i * (W.get i).valueDefect| ≤ storedPairing W i i / 2) :
    storedValueModel W = valueCorrectedModel f (fun z => innerSL ℝ (G z))
      (storedAnchors W) (storedSteps W) (storedSplit W) := by
  rw [krylov.Convergence.valueCorrectedModel_eq_ss1Model]
  have hy : (fun i : Fin W.length => G (storedAnchors W i + storedSteps W i) - G (storedAnchors W i)) =
      storedImages W := by
    funext i
    exact (hW _ (List.get_mem _ i)).1.symm
  rw [hy]
  unfold storedValueModel
  congr 1
  apply congrArg diagonal
  funext i
  rw [storedValueTerm_eq_raw W i (hgate i), (hW _ (List.get_mem _ i)).valueDefect_eq]
  rfl

/-- The full actual corrected XR branch is precisely the data-only SS1-F
query, after source estimates have forced both genuine value gates. -/
theorem algorithm_full_ss1FPoint {n : ℕ} (P : Parameters) (hon : P.valuesEnabled = true)
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (S : State (EuclideanSpace ℝ (Fin n))) (hn : 0 < n)
    (hfull : (algorithmModel P S).pairs.length = n) (hg : S.gradient = G S.point)
    (hW : ∀ a ∈ (algorithmModel P S).pairs, PairFaithful f G S.point a)
    (hgate : ∀ i : Fin (algorithmModel P S).pairs.length,
      |12 * storedSplit (algorithmModel P S).pairs i * ((algorithmModel P S).pairs.get i).valueDefect| ≤
        storedPairing (algorithmModel P S).pairs i i / 2)
    (hpass : correctedWindowPasses P.windowThreshold (algorithmModel P S).pairs) :
    S.point + (algorithmModel P S).direction =
      krylov.Convergence.ss1FPoint f G (storedAnchors (algorithmModel P S).pairs)
        (storedSteps (algorithmModel P S).pairs) (storedSplit (algorithmModel P S).pairs) S.point := by
  classical
  have hu := algorithmModel_direction_decomposition P S (by omega)
  rw [algorithmTrialParameter_full P S hn hfull, zero_smul, add_zero] at hu
  have hselected : selectedModel P (algorithmModel P S).pairs = storedValueModel (algorithmModel P S).pairs :=
    ite_eq_left ⟨hon, hpass⟩
  rw [hselected, storedValueModel_eq_actual f G S.point _ hW hgate, hg] at hu
  rw [hu]
  rfl

end
end krylov.XR
