import krylov.XR.MemoryObservations
import krylov.XR.MemoryRank
import krylov.Functions.QuadraticHiddenFamily
import krylov.Methods.VirtualReference

/-!
Article: main_krylov, thm:XR, exact quadratic observation/model dictionary.
Use: prove the literal endpoint-value correction vanishes on every actual
stored quadratic pair, and identify the observed model with the true
positive quadratic Gram matrix. No compatible-data flag is assumed.
Source: exact scalar quadratic differentiation and trapezoid cancellation.
-/

namespace krylov.XR
noncomputable section
open Matrix krylov.Methods krylov.Secant krylov.Functions
open scoped InnerProductSpace BigOperators
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- An arbitrary affine scalar quadratic, with true symmetric Hessian Q. -/
def quadraticObjective (Q : E →L[ℝ] E) (g₀ : E) (constant : ℝ) (x : E) : ℝ :=
  quadraticPotential ((innerSL ℝ).comp Q) (-(innerSL ℝ g₀)) x + constant

/-- Its actual affine gradient. -/
def quadraticGradient (Q : E →L[ℝ] E) (g₀ x : E) : E := g₀ + Q x

/-- The gradient supplied to the quadratic execution is the real first
derivative of the scalar objective. -/
theorem quadraticObjective_hasFDerivAt (Q : E →L[ℝ] E)
    (hQ : Q.toLinearMap.IsSymmetric) (g₀ : E) (constant : ℝ) (x : E) :
    HasFDerivAt (quadraticObjective Q g₀ constant)
      (innerSL ℝ (quadraticGradient Q g₀ x)) x := by
  have hA : ∀ u v : E, ((innerSL ℝ).comp Q) u v = ((innerSL ℝ).comp Q) v u := by
    intro u v
    change inner ℝ (Q u) v = inner ℝ (Q v) u
    exact (hQ u v).trans (real_inner_comm _ _)
  have hf := (quadraticPotential_hasFDerivAt ((innerSL ℝ).comp Q)
    (-(innerSL ℝ g₀)) hA x).add_const constant
  convert hf using 1
  · rfl
  · ext v
    simp only [quadraticGradient, map_add, ContinuousLinearMap.comp_apply,
      _root_.sub_apply, _root_.neg_apply, _root_.add_apply, innerSL_apply_apply]
    ring

/-- Actual quadratic secants are true Q-images, with no unknown operator
supplied to the algorithm. -/
theorem faithful_quadratic_image (Q : E →L[ℝ] E) (g₀ : E) (constant : ℝ)
    (x : E) (P : PairObservation E)
    (hP : PairFaithful (quadraticObjective Q g₀ constant) (quadraticGradient Q g₀) x P) :
    P.image = Q P.step := by
  have h := hP.1
  simpa only [quadraticGradient, map_add, add_sub_add_left_eq_sub, add_sub_cancel_left] using h

/-- Every faithful actual quadratic pair has exactly zero trapezoid defect. -/
theorem faithful_quadratic_defect (Q : E →L[ℝ] E)
    (hQ : Q.toLinearMap.IsSymmetric) (g₀ : E) (constant : ℝ)
    (x : E) (P : PairObservation E)
    (hP : PairFaithful (quadraticObjective Q g₀ constant) (quadraticGradient Q g₀) x P) :
    P.valueDefect = 0 := by
  have hA : ∀ u v : E, ((innerSL ℝ).comp Q) u v = ((innerSL ℝ).comp Q) v u := by
    intro u v
    change inner ℝ (Q u) v = inner ℝ (Q v) u
    exact (hQ u v).trans (real_inner_comm _ _)
  have ht := quadraticPotential_trapezoid ((innerSL ℝ).comp Q)
    (-(innerSL ℝ g₀)) hA P.anchor P.step
  have hd := hP.2.1
  rw [hP.1] at hd
  dsimp only [quadraticObjective, quadraticGradient] at hd
  simp only [ContinuousLinearMap.comp_apply, _root_.sub_apply, _root_.neg_apply,
    innerSL_apply_apply] at ht
  simp only [inner_add_left, inner_sub_right, inner_add_right] at hd
  have hcomm (z : E) : inner ℝ P.step z = inner ℝ z P.step := real_inner_comm _ _
  simp only [hcomm] at hd
  linarith

/-- The complete observed corrected model reduces to the uncorrected
latest-information model on actual quadratic data, regardless of its split. -/
theorem storedValueModel_quadratic (Q : E →L[ℝ] E)
    (hQ : Q.toLinearMap.IsSymmetric) (g₀ : E) (constant : ℝ) (x : E)
    (W : List (PairObservation E))
    (hW : ∀ P ∈ W, PairFaithful (quadraticObjective Q g₀ constant) (quadraticGradient Q g₀) x P) :
    storedValueModel W = storedModel W := by
  have hd (i : Fin W.length) : (W.get i).valueDefect = 0 :=
    faithful_quadratic_defect Q hQ g₀ constant x _ (hW _ (List.get_mem W i))
  have he : storedValueTerm W = 0 := by
    funext i
    dsimp only [storedValueTerm]
    rw [hd i]
    simp
  simp only [storedValueModel, he, Matrix.diagonal_zero', sub_zero]

/-- Actual quadratic observed pairings are the genuine symmetric Gram
matrix of Q, in chronological order. -/
theorem storedPairing_quadratic (Q : E →L[ℝ] E)
    (hQ : Q.toLinearMap.IsSymmetric) (g₀ : E) (constant : ℝ) (x : E)
    (W : List (PairObservation E))
    (hW : ∀ P ∈ W, PairFaithful (quadraticObjective Q g₀ constant) (quadraticGradient Q g₀) x P) :
    storedPairing W = crossGram (fun i => Q (storedSteps W i)) (storedSteps W) := by
  ext i j
  have hy := faithful_quadratic_image Q g₀ constant x _ (hW _ (List.get_mem W j))
  change inner ℝ (storedSteps W i) (W.get j).image = _
  rw [hy]
  exact (hQ _ _).symm

/-- Every actual independent positive-quadratic window has its genuine
positive observed model; the algorithm does not receive this as a field. -/
theorem storedModel_quadratic_posDef (Q : E →L[ℝ] E)
    (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v : E, v ≠ 0 → 0 < inner ℝ v (Q v))
    (g₀ : E) (constant : ℝ) (x : E) (W : List (PairObservation E))
    (hW : ∀ P ∈ W, PairFaithful (quadraticObjective Q g₀ constant) (quadraticGradient Q g₀) x P)
    (hs : LinearIndependent ℝ (storedSteps W)) : (storedModel W).PosDef := by
  have hg := operatorGram_posDef Q hQ hpos hs
  rw [storedModel, storedPairing_quadratic Q hQ g₀ constant x W hW,
    latest_eq_of_isSymm hg.isHermitian.isSymm]
  exact hg

end
end krylov.XR
