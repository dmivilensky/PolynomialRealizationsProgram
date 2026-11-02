import krylov.Functions.TrapezoidAffine
import krylov.Methods.NormalizedCorrection
import krylov.Secant.ModelConvergence
import krylov.Secant.NormalizedModel

/-!
Article: main_krylov, thm:Ip, thm:ss1F and apG:mss.
Use: the sliding methods below use actual successive points, observed gradient
differences, and function values. Their square-window Newton representation is
proved from those observations; it is not an input to the method.
Source: the symmetric multipoint secant model (Burdakov83), with the already
proved nonsingular coordinate-change identities.
-/

namespace krylov.Convergence
noncomputable section
open Matrix krylov.Methods krylov.Secant krylov.Reference krylov.Functions
open scoped InnerProductSpace BigOperators Matrix.Norms.L2Operator
variable {n : ℕ}

/-- The physical matrix whose columns are precisely the observed steps. -/
def windowMatrix (s : Fin n → EuclideanSpace ℝ (Fin n)) : Matrix (Fin n) (Fin n) ℝ :=
  fun a i => s i a

/-- Chronological anchors of a genuine sliding window. -/
def windowAnchor {E : Type*} (x : ℕ → E) (o : ℕ) (i : Fin n) : E := x (o+i.val)

/-- Actual successive displacements, with no independent pair-data field. -/
def windowStep {E : Type*} [AddCommGroup E] (x : ℕ → E) (o : ℕ) (i : Fin n) : E :=
  x (o+i.val+1)-x (o+i.val)

/-- Actual observed differences of the gradient. -/
def windowImage {E : Type*} [AddCommGroup E] (G : E → E) (x : ℕ → E)
    (o : ℕ) (i : Fin n) : E := G (x (o+i.val+1))-G (x (o+i.val))

/-- The SS1 model formed from the chronologically ordered observed pairs. -/
def ss1Model {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (s y : Fin n → E) : Matrix (Fin n) (Fin n) ℝ := latest (crossGram s y)

/-- The actual SS1 query. Only stored steps, their observed images and the
current gradient enter this one-gradient rule. -/
def ss1Point {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (s y : Fin n → E) (g x : E) : E :=
  x+combine s (modelCoefficients s (ss1Model s y) g)

/-- The actual value-corrected SS1 query, for the specified observable split. -/
def ss1FPoint {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (f : E → ℝ) (G : E → E) (a s : Fin n → E) (l : Fin n → ℝ) (x : E) : E :=
  x+combine s (modelCoefficients s
    (valueCorrectedModel f (fun z=>innerSL ℝ (G z)) a s l) (G x))

theorem window_anchor_add_step {E : Type*} [AddCommGroup E]
    (x : ℕ → E) (o : ℕ) (i : Fin n) :
    windowAnchor x o i+windowStep x o i=x (o+i.val+1) := by
  simp only [windowAnchor,windowStep,add_sub_cancel]

/-- Physical window synthesis is the true Euclidean matrix action. -/
theorem combine_windowMatrix (s : Fin n → EuclideanSpace ℝ (Fin n)) (c : Fin n → ℝ) :
    combine s c=WithLp.toLp 2 (windowMatrix s*ᵥc) := by
  ext a
  simp only [combine,WithLp.ofLp_sum,WithLp.ofLp_smul,Finset.sum_apply,Pi.smul_apply,
    smul_eq_mul,windowMatrix,Matrix.mulVec,dotProduct]
  exact Finset.sum_congr rfl fun i _=>mul_comm _ _

/-- The projected right-hand side is exactly the physical transpose action. -/
theorem coordinates_windowMatrix (s : Fin n → EuclideanSpace ℝ (Fin n))
    (g : EuclideanSpace ℝ (Fin n)) :
    coordinates s g=(windowMatrix s)ᵀ*ᵥWithLp.ofLp g := by
  ext i
  simp only [coordinates,PiLp.inner_apply,RCLike.inner_apply,conj_trivial,
    windowMatrix,Matrix.mulVec,dotProduct,transpose_apply]
  exact Finset.sum_congr rfl fun a _=>mul_comm _ _

/-- Every square observed-model correction equals the genuine inverse ambient
model action, including on the singular-model branch of matrix inversion. -/
theorem square_model_correction (s : Fin n → EuclideanSpace ℝ (Fin n))
    (H : Matrix (Fin n) (Fin n) ℝ) (g : EuclideanSpace ℝ (Fin n))
    (hs : IsUnit (windowMatrix s).det) :
    combine s (modelCoefficients s H g)=
      -(cgOperator (inverseCongruence (windowMatrix s) H)⁻¹ g) := by
  rw [modelCoefficients,combine_windowMatrix,coordinates_windowMatrix,
    Matrix.mulVec_neg,Matrix.mulVec_mulVec,Matrix.mulVec_mulVec,
    inverseCongruence_inv _ _ hs]
  rfl

/-- The data-only SS1 query has the claimed ambient inverse-model formula. -/
theorem ss1Point_eq_model_step (s y : Fin n → EuclideanSpace ℝ (Fin n))
    (g x : EuclideanSpace ℝ (Fin n)) (hs : IsUnit (windowMatrix s).det) :
    ss1Point s y g x=x-cgOperator
      (inverseCongruence (windowMatrix s) (ss1Model s y))⁻¹ g := by
  rw [ss1Point,square_model_correction _ _ _ hs,sub_eq_add_neg]

/-- The value-corrected data-only query has the same genuine square-model
formula. Function values remain in the actually computed model. -/
theorem ss1FPoint_eq_model_step (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (a s : Fin n → EuclideanSpace ℝ (Fin n)) (l : Fin n → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) (hs : IsUnit (windowMatrix s).det) :
    ss1FPoint f G a s l x=x-cgOperator (inverseCongruence (windowMatrix s)
      (valueCorrectedModel f (fun z=>innerSL ℝ (G z)) a s l))⁻¹ (G x) := by
  rw [ss1FPoint,square_model_correction _ _ _ hs,sub_eq_add_neg]

/-- The true observed raw matrix equals its physical compressed operator
matrix as soon as the genuine secant identities have been proved. -/
theorem crossGram_eq_pairImages (s y : Fin n → EuclideanSpace ℝ (Fin n))
    (A : ℕ → Matrix (Fin n) (Fin n) ℝ)
    (hy : ∀ i, y i=cgOperator (A i.val) (s i)) :
    crossGram s y=(windowMatrix s)ᵀ*pairImages (windowMatrix s) A := by
  ext i j
  rw [crossGram,hy j]
  simp only [cgOperator,Matrix.inner_toEuclideanCLM,windowMatrix,Matrix.mul_apply,
    transpose_apply,pairImages,Matrix.mulVec,dotProduct]

end
end krylov.Convergence
