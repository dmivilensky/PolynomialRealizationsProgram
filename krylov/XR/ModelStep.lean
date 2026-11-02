import krylov.Methods.SecantSolve
import krylov.Methods.ProjectedModel
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Tactic

/-!
Article: main_krylov, lem:mm, genuine observed model steps.
Use: construct the trial entirely from retained step/secant arrays and the
observed gradient, then derive its slope and block-model energy identity.
Source: the existing actual secant solves and elementary positive quadratic
minimization. No descent or output identity is an execution assumption.
-/

/-!
Article: krylov, Lemma F.6 [lem:mm].

Raw model normal solves give a unique physical block-quadratic minimizer and the exact
slope/energy and quadratic directional identities. The actual Taylor quotient is at unit trial.
The physical minimizer and gᵀd=ĝᵀd need nonsingular conjugacy and an independent augmented
frame. The scalar slope identity alone is more general. Safeguarded replacement is excluded
from the model-minimizer interpretation.
-/
namespace krylov.XR
noncomputable section
open Matrix Finset krylov.Methods
open scoped InnerProductSpace BigOperators
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {p : ℕ}

/-- Actual stored-window model correction. Article: lem:mm. -/
def modelVirtualCorrection (s : Fin p → E) (T : Matrix (Fin p) (Fin p) ℝ) (g : E) : E :=
  combine s (modelCoefficients s T g)

/-- Actual observed extrapolated gradient, without a hidden operator query.
Article: main_krylov, lem:mm. -/
def modelVirtualGradient (s y : Fin p → E) (T : Matrix (Fin p) (Fin p) ℝ) (g : E) : E :=
  g+combine y (modelCoefficients s T g)

/-- The genuine image-conjugate direction at the extrapolated gradient.
Article: main_krylov, lem:mm and alg:xr. -/
def modelDirection (s y : Fin p → E) (T : Matrix (Fin p) (Fin p) ℝ) (g : E) : E :=
  conjugacyDirection s y (modelVirtualGradient s y T g)

/-- The actual trial length computed from the observed slope and the
positive supplied new curvature. Article: main_krylov, lem:mm. -/
def modelTrialLength (s y : Fin p → E) (T : Matrix (Fin p) (Fin p) ℝ) (g : E) (c : ℝ) : ℝ :=
  -inner ℝ g (modelDirection s y T g)/c

/-- The literal original model step, including the virtual window move.
The zero-direction branch has zero trial movement automatically.
Article: main_krylov, lem:mm and alg:xr. -/
def modelTrialStep (s y : Fin p → E) (T : Matrix (Fin p) (Fin p) ℝ) (g : E) (c : ℝ) : E :=
  modelVirtualCorrection s T g+modelTrialLength s y T g c • modelDirection s y T g

/-- Exact finite observed normal equation of the actual inverse solve.
Article: main_krylov, lem:mm. -/
theorem modelCoefficients_normal (s : Fin p → E) (T : Matrix (Fin p) (Fin p) ℝ)
    (hT : IsUnit T.det) (g : E) : T*ᵥ modelCoefficients s T g= -coordinates s g := by
  rw [modelCoefficients,mulVec_neg,mulVec_mulVec,mul_nonsing_inv T hT,one_mulVec]

/-- Pairing with a real finite synthesized window is its actual scalar
coordinate dot product. Article: main_krylov, lem:mm. -/
theorem inner_combine_coordinates (g : E) (s : Fin p → E) (w : Fin p → ℝ) :
    inner ℝ g (combine s w)=w ⬝ᵥ coordinates s g := by
  simp only [combine,inner_sum,real_inner_smul_right,dotProduct,coordinates,real_inner_comm]

/-- The actual window correction's negative slope is exactly its model
energy. Article: main_krylov, lem:mm. -/
theorem modelVirtualCorrection_slope (s : Fin p → E) (T : Matrix (Fin p) (Fin p) ℝ)
    (hT : IsUnit T.det) (g : E) :
    inner ℝ g (modelVirtualCorrection s T g)=
      -(modelCoefficients s T g ⬝ᵥ (T*ᵥ modelCoefficients s T g)) := by
  rw [modelVirtualCorrection,inner_combine_coordinates,modelCoefficients_normal s T hT g,dotProduct_neg,neg_neg]

/-- The true computed direction is conjugate to every actual retained
image, on the genuine observed inverse domain. Article: lem:mm. -/
theorem modelDirection_conjugate (s y : Fin p → E) (T : Matrix (Fin p) (Fin p) ℝ)
    (hinv : IsUnit (crossGram y s).det) (g : E) :
    coordinates y (modelDirection s y T g)=0 :=
  conjugacyDirection_conjugate s y _ hinv

/-- The slope at the anchor equals the slope at the genuine extrapolated
gradient; this follows from observed image conjugacy. Article: lem:mm. -/
theorem modelDirection_slope (s y : Fin p → E) (T : Matrix (Fin p) (Fin p) ℝ)
    (hinv : IsUnit (crossGram y s).det) (g : E) :
    inner ℝ g (modelDirection s y T g)=
      inner ℝ (modelVirtualGradient s y T g) (modelDirection s y T g) := by
  have hc := modelDirection_conjugate s y T hinv g
  have hz : inner ℝ (combine y (modelCoefficients s T g)) (modelDirection s y T g)=0 := by
    rw [real_inner_comm,inner_combine_coordinates,hc,dotProduct_zero]
  rw [modelVirtualGradient,inner_add_left,hz,add_zero]

/-- The actual observed model step has exactly the original negative
block-model energy as its directional derivative. Article: lem:mm. -/
theorem modelTrialStep_slope (s y : Fin p → E) (T : Matrix (Fin p) (Fin p) ℝ)
    (hT : IsUnit T.det) (g : E) (c : ℝ) (hc : 0<c) :
    inner ℝ g (modelTrialStep s y T g c)=
      -(modelCoefficients s T g ⬝ᵥ (T*ᵥ modelCoefficients s T g)+
        (modelTrialLength s y T g c)^2*c) := by
  rw [modelTrialStep,inner_add_right,real_inner_smul_right,modelVirtualCorrection_slope s T hT g]
  dsimp only [modelTrialLength]
  field_simp
  ring

/-- A zero genuine direction gives exactly the window-only correction,
including every full-window branch that derives zero direction.
Article: main_krylov, lem:mm. -/
theorem modelTrialStep_zero_direction (s y : Fin p → E) (T : Matrix (Fin p) (Fin p) ℝ)
    (g : E) (c : ℝ) (hd : modelDirection s y T g=0) :
    modelTrialStep s y T g c=modelVirtualCorrection s T g := by
  simp only [modelTrialStep,hd,smul_zero,add_zero]

end
end krylov.XR
