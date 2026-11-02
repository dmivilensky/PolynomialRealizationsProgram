import krylov.XR.QuadraticModel
import krylov.XR.RealComplexPositive

/-!
Article: main_krylov, thm:XR, exact quadratic refutation/value gates.
Use: derive that every actually observed independent positive-quadratic
window is retained by the real Hermitian test, and XR-F is exactly XR on
quadratics. Source: genuine quadratic endpoint cancellation and real-to-
complex positive-form transport; no gate-success hypothesis is supplied.
-/

namespace krylov.XR
noncomputable section
open Matrix krylov.Methods krylov.Secant
open scoped InnerProductSpace ComplexOrder
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The actual pairing matrix of a faithful independent SPD-quadratic
window is positive; hence its skew defect vanishes exactly. -/
theorem storedPairing_quadratic_posDef (Q : E →L[ℝ] E)
    (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v : E, v ≠ 0 → 0 < inner ℝ v (Q v))
    (g₀ : E) (constant : ℝ) (x : E) (W : List (PairObservation E))
    (hW : ∀ P ∈ W, PairFaithful (quadraticObjective Q g₀ constant) (quadraticGradient Q g₀) x P)
    (hs : LinearIndependent ℝ (storedSteps W)) : (storedPairing W).PosDef := by
  rw [storedPairing_quadratic Q hQ g₀ constant x W hW]
  exact operatorGram_posDef Q hQ hpos hs

/-- A genuine independent positive-quadratic window passes the actual
complex Hermitian test for every threshold. -/
theorem quadratic_windowUnrefuted (theta : ℝ) (Q : E →L[ℝ] E)
    (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v : E, v ≠ 0 → 0 < inner ℝ v (Q v))
    (g₀ : E) (constant : ℝ) (x : E) (W : List (PairObservation E))
    (hW : ∀ P ∈ W, PairFaithful (quadraticObjective Q g₀ constant) (quadraticGradient Q g₀) x P)
    (hs : LinearIndependent ℝ (storedSteps W)) :
    windowUnrefuted theta (storedPairing W) := by
  have hp := storedPairing_quadratic_posDef Q hQ hpos g₀ constant x W hW hs
  have hd : defect (storedPairing W) = 0 := by
    rw [defect, hp.isHermitian.isSymm.eq, sub_self]
  have he : hermitianWindowMatrix theta (storedPairing W) =
      (storedPairing W).map Complex.ofReal := by
    rw [hermitianWindowMatrix, latest_eq_of_isSymm hp.isHermitian.isSymm, hd]
    simp
  rw [windowUnrefuted, he]
  exact ofReal_posDef _ hp

/-- Every faithful quadratic value model is the ordinary observed model,
so the enabled/disabled value switch has exactly the same selected matrix. -/
theorem selectedModel_quadratic (P : Parameters) (Q : E →L[ℝ] E)
    (hQ : Q.toLinearMap.IsSymmetric) (g₀ : E) (constant : ℝ) (x : E)
    (W : List (PairObservation E))
    (hW : ∀ a ∈ W, PairFaithful (quadraticObjective Q g₀ constant) (quadraticGradient Q g₀) x a) :
    selectedModel P W = storedModel W := by
  classical
  unfold selectedModel
  rw [storedValueModel_quadratic Q hQ g₀ constant x W hW]
  split <;> rfl

/-- Actual quadratic independent windows incur no refutation deletions. -/
theorem quadratic_modelDeletion_zero (P : Parameters) (Q : E →L[ℝ] E)
    (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v : E, v ≠ 0 → 0 < inner ℝ v (Q v))
    (g₀ : E) (constant : ℝ) (x : E) (W : List (PairObservation E))
    (hW : ∀ a ∈ W, PairFaithful (quadraticObjective Q g₀ constant) (quadraticGradient Q g₀) x a)
    (hs : LinearIndependent ℝ (storedSteps W)) : modelDeletion P W = 0 :=
  modelDeletion_eq_zero P W (quadratic_windowUnrefuted P.windowThreshold Q hQ hpos g₀ constant x W hW hs)

end
end krylov.XR
