import krylov.Functions.AnchoredTrapezoid
import Mathlib.Analysis.InnerProductSpace.LinearMap
import krylov.Secant.Model
import Mathlib.Data.Matrix.Diagonal

/-!
Article: main_krylov, thm:Fexact, invariance of the function-value model.
Use: prove that the actual observed scalar quantities and the model-metric
split commute with affine coordinate changes. The Euclidean split commutes
with isometric coordinate changes.
Source: Appendix G; the actual Frechet chain rule and dual-vector pairing.
-/

namespace krylov.Functions
noncomputable section
section Normed
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The trapezoid defect computed from actual values and first differentials.
Article: main_krylov, equation (function-value-model). -/
def segmentValueDefect (f : E → ℝ) (D : E → E →L[ℝ] ℝ) (a s : E) : ℝ :=
  f (a + s) - f a - (D a s + D (a + s) s) / 2

/-- The observed corrected diagonal, for any chosen split.
Article: main_krylov, equation (function-value-model). -/
def correctedValueDiagonal (f : E → ℝ) (D : E → E →L[ℝ] ℝ)
    (a s : E) (l : ℝ) : ℝ :=
  (D (a + s) - D a) s - 12 * l * segmentValueDefect f D a s

/-- The model-metric split uses a genuine covector, hence its coordinate-free pairing.
Article: main_krylov, Section 4, lambda^Y. -/
def covectorSplit (y : E →L[ℝ] ℝ) (a s x : E) : ℝ :=
  y (x - (a + (1 / 2 : ℝ) • s)) / y s

/-- Pulling back the differential gives the actual derivative of the pulled-back function.
Article: main_krylov, thm:Fexact, linear-change invariance.
Proof: the genuine Frechet chain rule, also valid for affine maps. -/
theorem affine_pullback_hasFDerivAt (f : E → ℝ) (D : E → E →L[ℝ] ℝ)
    (A : F →L[ℝ] E) (p : E) (x : F)
    (hD : HasFDerivAt f (D (p + A x)) (p + A x)) :
    HasFDerivAt (fun x => f (p + A x)) ((D (p + A x)).comp A) x := by
  exact hD.comp x (A.hasFDerivAt.const_add p)

/-- Actual value defects are invariant under affine pullback.
Article: main_krylov, thm:Fexact, function-value and gradient-step invariance. -/
theorem segmentValueDefect_affine (f : E → ℝ) (D : E → E →L[ℝ] ℝ)
    (A : F →L[ℝ] E) (p : E) (a s : F) :
    segmentValueDefect (fun x => f (p + A x))
      (fun x => (D (p + A x)).comp A) a s =
      segmentValueDefect f D (p + A a) (A s) := by
  simp only [segmentValueDefect, map_add, ContinuousLinearMap.comp_apply, ← add_assoc]

/-- The entire function-value diagonal commutes with affine pullback.
Article: main_krylov, thm:Fexact, corrected-model invariance. -/
theorem correctedValueDiagonal_affine (f : E → ℝ) (D : E → E →L[ℝ] ℝ)
    (A : F →L[ℝ] E) (p : E) (a s : F) (l : ℝ) :
    correctedValueDiagonal (fun x => f (p + A x))
      (fun x => (D (p + A x)).comp A) a s l =
      correctedValueDiagonal f D (p + A a) (A s) l := by
  rw [correctedValueDiagonal, correctedValueDiagonal, segmentValueDefect_affine]
  simp only [sub_apply, ContinuousLinearMap.comp_apply, map_add, ← add_assoc]

/-- The model-metric split is invariant under every affine coordinate pullback.
Article: main_krylov, thm:Fexact, lambda^Y invariance.
Proof: both numerator and denominator are the same dual-vector pairings. -/
theorem covectorSplit_affine (y : E →L[ℝ] ℝ) (A : F →L[ℝ] E)
    (p : E) (a s x : F) :
    covectorSplit (y.comp A) a s x = covectorSplit y (p + A a) (A s) (p + A x) := by
  have he : (p + A x) - (p + A a + (1 / 2 : ℝ) • A s) =
      A (x - (a + (1 / 2 : ℝ) • s)) := by
    simp only [map_sub, map_add, map_smul]
    module
  simp only [covectorSplit, ContinuousLinearMap.comp_apply, he]

/-- The model-metric split removes the observed covector component exactly.
Article: main_krylov, Section 4, w_i perpendicular to y_i. -/
theorem covectorSplit_annihilates (y : E →L[ℝ] ℝ) (a s x : E) (hy : y s ≠ 0) :
    y (x - (a + (1 / 2 : ℝ) • s) - covectorSplit y a s x • s) = 0 := by
  rw [map_sub, map_smul]
  simp only [covectorSplit, smul_eq_mul]
  field_simp
  ring

/-- The complete observed latest-information model with its value correction.
Article: main_krylov, equation (function-value-model), not merely its diagonal. -/
def valueCorrectedModel {ι : Type*} [LinearOrder ι] [Fintype ι] [DecidableEq ι]
    (f : E → ℝ) (D : E → E →L[ℝ] ℝ) (a s : ι → E) (l : ι → ℝ) : Matrix ι ι ℝ :=
  Secant.latest (fun i j => (D (a j + s j) - D (a j)) (s i)) -
    Matrix.diagonal (fun i => 12 * l i * segmentValueDefect f D (a i) (s i))

/-- The entire corrected model matrix is invariant under affine pullback.
Article: main_krylov, thm:Fexact, corrected-model invariance.
Proof: every raw cross pairing and every observed value defect is invariant. -/
theorem valueCorrectedModel_affine {ι : Type*} [LinearOrder ι] [Fintype ι] [DecidableEq ι]
    (f : E → ℝ) (D : E → E →L[ℝ] ℝ) (A : F →L[ℝ] E) (p : E)
    (a s : ι → F) (l : ι → ℝ) :
    valueCorrectedModel (fun x => f (p + A x)) (fun x => (D (p + A x)).comp A) a s l =
      valueCorrectedModel f D (fun i => p + A (a i)) (fun i => A (s i)) l := by
  have hM : (fun i j => ((D (p + A (a j + s j))).comp A - (D (p + A (a j))).comp A) (s i)) =
      (fun i j => (D (p + A (a j) + A (s j)) - D (p + A (a j))) (A (s i))) := by
    ext i j
    simp only [sub_apply, ContinuousLinearMap.comp_apply, map_add, ← add_assoc]
  rw [valueCorrectedModel, valueCorrectedModel, hM]
  congr 1
  apply congrArg Matrix.diagonal
  funext i
  rw [segmentValueDefect_affine]

end Normed

section InnerProduct
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- The Euclidean split at the actual segment midpoint.
Article: main_krylov, Section 4, lambda^E. -/
def innerSplit (a s x : E) : ℝ :=
  inner ℝ s (x - (a + (1 / 2 : ℝ) • s)) / ‖s‖ ^ 2

/-- Euclidean splits commute with isometries, including orthogonal coordinate changes.
Article: main_krylov, thm:Fexact, lambda^E invariance. -/
theorem innerSplit_isometry (A : F →ₗᵢ[ℝ] E) (p : E) (a s x : F) :
    innerSplit a s x = innerSplit (p + A a) (A s) (p + A x) := by
  have he : (p + A x) - (p + A a + (1 / 2 : ℝ) • A s) =
      A (x - (a + (1 / 2 : ℝ) • s)) := by
    simp only [map_sub, map_add, map_smul]
    module
  rw [innerSplit, innerSplit, he, A.inner_map_map, A.norm_map]

/-- The Euclidean split removes the actual step component exactly.
Article: main_krylov, Section 4, w_i perpendicular to s_i. -/
theorem innerSplit_orthogonal (a s x : E) (hs : s ≠ 0) :
    inner ℝ s (x - (a + (1 / 2 : ℝ) • s) - innerSplit a s x • s) = 0 := by
  rw [inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq]
  simp only [innerSplit]
  have hn : ‖s‖ ≠ 0 := norm_ne_zero_iff.mpr hs
  field_simp
  ring

end InnerProduct
end
end krylov.Functions
