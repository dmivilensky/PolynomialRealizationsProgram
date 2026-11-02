import krylov.Functions.LocalExactSearch
import krylov.Nonlinear.MetricCoordinates

/-!
Article: main_krylov, lem:cycle-transfer and apG:E, actual scalar metric transport.
Use: transport the real objective and its genuine Riesz gradient through the
constructed positive-root coordinates while retaining the physical algorithm.
The coordinate direction is transported as a primal vector; it is not silently
replaced by the negative canonical gradient.
Source: the actual Frechet chain rule and symmetry of the inverse metric root.
-/

namespace krylov.Functions
noncomputable section
open Set Metric krylov.Nonlinear
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The actual scalar objective in inverse linear metric coordinates.
Article: main_krylov, lem:cycle-transfer. -/
def coordinateObjective (T : E ≃L[ℝ] E) (f : E → ℝ) (z : E) : ℝ := f (T.symm z)

/-- A true scalar derivative transports to the genuine inverse-congruence gradient.
Article: main_krylov, lem:cycle-transfer and apG:E.
Proof: apply the actual scalar chain rule and move the self-adjoint inverse
coordinate map across the real inner product. -/
theorem coordinateObjective_hasFDerivAt (T : E ≃L[ℝ] E)
    (hT : T.symm.toContinuousLinearMap.IsSymmetric) (f : E → ℝ) (G : E → E) (z : E)
    (hf : HasFDerivAt f (innerSL ℝ (G (T.symm z))) (T.symm z)) :
    HasFDerivAt (coordinateObjective T f) (innerSL ℝ (coordinateGradient T G z)) z := by
  convert! hf.comp z T.symm.toContinuousLinearMap.hasFDerivAt using 1
  ext v
  exact hT (G (T.symm z)) v

/-- Actual objective values are exactly preserved at transported physical points.
Article: main_krylov, lem:cycle-transfer. Proof: cancel the true linear equivalence. -/
theorem coordinateObjective_apply (T : E ≃L[ℝ] E) (f : E → ℝ) (x : E) :
    coordinateObjective T f (T x) = f x := by simp [coordinateObjective]

/-- The entire physical search line maps to the corresponding canonical line.
Article: main_krylov, apG:E.
Proof: exact linear transport of the actual direction and displacement. -/
theorem coordinateObjective_line (T : E ≃L[ℝ] E) (f : E → ℝ) (x d : E) (t : ℝ) :
    coordinateObjective T f (T x + t • T d) = f (x + t • d) := by
  simp [coordinateObjective]

/-- A genuine physical chord minimum in the metric ball is exactly a canonical chord minimum.
Article: main_krylov, apG:E and lem:cycle-transfer.
Proof: the actual objective and every actual line parameter agree after the
linear equivalence, including the zero direction and both chord endpoints. -/
theorem isChordMinimum_coordinate_iff (T : E ≃L[ℝ] E) (f : E → ℝ) (x d y : E) (r : ℝ) :
    IsChordMinimum (coordinateObjective T f) (T x) (T d) r (T y) ↔
      ‖T y‖ ≤ r ∧ (∃ t : ℝ, y = x + t • d) ∧
        ∀ t : ℝ, ‖T (x + t • d)‖ ≤ r → f y ≤ f (x + t • d) := by
  simp only [IsChordMinimum, chordParameters, mem_ofPred_eq, mem_closedBall,
    dist_zero_right, coordinateObjective_apply, coordinateObjective_line]
  constructor
  · rintro ⟨hy, ⟨t, ht⟩, hmin⟩
    refine ⟨hy, ⟨t, ?_⟩, ?_⟩
    · apply T.injective
      simpa only [map_add, map_smul] using ht
    · intro t ht
      exact hmin t (by simpa only [map_add, map_smul] using ht)
  · rintro ⟨hy, ⟨t, ht⟩, hmin⟩
    refine ⟨hy, ⟨t, ?_⟩, ?_⟩
    · rw [ht, map_add, map_smul]
    · intro t ht
      exact hmin t (by simpa only [map_add, map_smul] using ht)

variable [CompleteSpace E]

/-- The mathematical Riesz gradient of the actual coordinate objective is the true inverse-congruence gradient.
Article: main_krylov, lem:cycle-transfer.
Proof: identify both genuine scalar derivatives by the chain rule, then use
the uniqueness of the actual Riesz gradient. -/
theorem gradient_coordinateObjective (T : E ≃L[ℝ] E)
    (hT : T.symm.toContinuousLinearMap.IsSymmetric) (f : E → ℝ) (z : E)
    (hf : DifferentiableAt ℝ f (T.symm z)) :
    gradient (coordinateObjective T f) z = coordinateGradient T (gradient f) z := by
  have hd := coordinateObjective_hasFDerivAt T hT f (gradient f) z hf.hasGradientAt.hasFDerivAt
  have hg : HasGradientAt (coordinateObjective T f) (coordinateGradient T (gradient f) z) z := hd
  exact hg.gradient

end
end krylov.Functions
