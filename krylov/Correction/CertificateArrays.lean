import krylov.Correction.CertificateMatrix
import krylov.Methods.ProjectedModel
import krylov.Methods.RFCPhase


/-!
Article: main_krylov, prop:deep, actual checked source-array execution.
Use: interpret the unchanged earlier integer checker expressions as true
physical source vectors, observed pair arrays, conjugacy and model solves,
line searches, genuine correction queries and returned RFC phase results.
Source: exact finite matrix certificate semantics and the existing original
RFC array executor, with the actual empty and accepted gate branches.
-/

namespace krylov.Correction.Certificate
noncomputable section
open Matrix Finset chebyshev2.Numerics.IntegerCertificate krylov.Methods
open scoped BigOperators InnerProductSpace Matrix.Norms.L2Operator

/-- The genuine Euclidean interpretation of a finite certificate-expression vector.
Use: Identify actual physical vectors, inner products and operator actions in the existing checked language.
Article: main_krylov, prop:deep, actual checked RFC array execution. -/
def euclideanValue {n : ℕ} (v : Fin n → Term) (x : ℕ → ℝ) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (vectorValue v x)

/-- The exact coordinatewise vector-negation expression.
Use: Compile the actual negative-gradient direction and measured gradient differences.
Article: main_krylov, prop:deep, actual checked RFC array execution. -/
def termNeg {n : ℕ} (v : Fin n → Term) : Fin n → Term := fun i => .neg (v i)

/-- The exact coordinatewise vector-addition expression.
Use: Compile genuine search and correction gradient updates.
Article: main_krylov, prop:deep, actual checked RFC array execution. -/
def termAdd {n : ℕ} (u v : Fin n → Term) : Fin n → Term := fun i => .add (u i) (v i)

/-- The exact scalar-vector multiplication expression.
Use: Retain real line lengths and correction coefficient scales.
Article: main_krylov, prop:deep, actual checked RFC array execution. -/
def termScale {n : ℕ} (a : Term) (v : Fin n → Term) : Fin n → Term := fun i => .mul a (v i)

/-- Certificate vector negation has its genuine real Euclidean semantics.
Use: Preserve the actual negative-gradient physical direction.
Article: main_krylov, prop:deep, actual checked RFC array execution.
Proof: Both genuine interpretations have the same real coordinatewise negation. -/
theorem euclideanValue_neg {n : ℕ} (v : Fin n → Term) (x : ℕ → ℝ) :
    euclideanValue (termNeg v) x=-(euclideanValue v x) := rfl

/-- Certificate vector addition has exactly its genuine real Euclidean semantics.
Use: Preserve the actual physical sum of line and correction movements.
Article: main_krylov, prop:deep, actual checked RFC array execution.
Proof: Both interpreted vector families have the same real coordinate sums. -/
theorem euclideanValue_add {n : ℕ} (u v : Fin n → Term) (x : ℕ → ℝ) :
    euclideanValue (termAdd u v) x=euclideanValue u x+euclideanValue v x := rfl

/-- Certificate scalar-vector multiplication equals its genuine real Euclidean action.
Use: Retain true physical line-length scaling in the checked source program.
Article: main_krylov, prop:deep, actual checked RFC array execution.
Proof: Each interpreted real coordinate is the same scalar product. -/
theorem euclideanValue_scale {n : ℕ} (a : Term) (v : Fin n → Term) (x : ℕ → ℝ) :
    euclideanValue (termScale a v) x=a.value x • euclideanValue v x := rfl

/-- Every compiled finite scalar pairing equals the genuine Euclidean inner product of the actual interpreted vectors.
Use: Tie certificate pairing entries to actual physical source data.
Article: main_krylov, prop:deep, actual checked RFC array execution.
Proof: The proved finite real dot-product semantics and the standard Euclidean star-dot-product identity agree by real commutativity. -/
theorem termDot_inner {n : ℕ} (u v : Fin n → Term) (x : ℕ → ℝ) :
    (termDot u v).value x=inner ℝ (euclideanValue u x) (euclideanValue v x) := by
  rw [EuclideanSpace.inner_eq_star_dotProduct,termDot_value]
  simp only [euclideanValue,star_trivial]
  exact dotProduct_comm _ _

/-- The exact finite expression for synthesis from an actual vector family and its scalar coefficients.
Use: Compile the genuine stored-span physical correction query.
Article: main_krylov, prop:deep, actual checked RFC array execution. -/
def termCombine {n p : ℕ} (s : Fin p → Fin n → Term) (c : Fin p → Term) : Fin n → Term :=
  fun i => termSum (fun j => .mul (c j) (s j i))

/-- Certificate finite synthesis is exactly the real stored-vector combination used by the method.
Use: Preserve the actual physical correction and conjugacy displacements.
Article: main_krylov, prop:deep, actual checked RFC array execution.
Proof: Evaluate each real coordinate of the genuine finite scalar-vector sum. -/
theorem termCombine_value {n p : ℕ} (s : Fin p → Fin n → Term) (c : Fin p → Term) (x : ℕ → ℝ) :
    euclideanValue (termCombine s c) x=combine (fun i => euclideanValue (s i) x) (vectorValue c x) := by
  ext i
  simp only [euclideanValue,vectorValue,termCombine,termSum_value,Expr.value,
    combine,WithLp.ofLp_sum,Finset.sum_apply,PiLp.smul_apply,smul_eq_mul]

/-- The actual projected-gradient pairing family compiled in the existing integer certificate language.
Use: Encode genuine coefficient-system right-hand sides.
Article: main_krylov, prop:deep, actual checked RFC array execution. -/
def termCoordinates {n p : ℕ} (s : Fin p → Fin n → Term) (g : Fin n → Term) : Fin p → Term :=
  fun i => termDot (s i) g

/-- The compiled pairing family is exactly the actual method coordinate vector.
Use: Keep numerical solve inputs tied to the genuine observed gradient.
Article: main_krylov, prop:deep, actual checked RFC array execution.
Proof: Each interpreted entry has the independently proved true Euclidean inner-product semantics. -/
theorem termCoordinates_value {n p : ℕ} (s : Fin p → Fin n → Term) (g : Fin n → Term) (x : ℕ → ℝ) :
    vectorValue (termCoordinates s g) x=coordinates (fun i => euclideanValue (s i) x) (euclideanValue g x) := by
  ext i
  exact termDot_inner (s i) g x

/-- The genuine observed cross-Gram expression of two finite vector families.
Use: Compile the actual RFC direction coefficient matrix.
Article: main_krylov, prop:deep, actual checked RFC array execution. -/
def termCross {n p : ℕ} (y s : Fin p → Fin n → Term) : Matrix (Fin p) (Fin p) Term :=
  fun i j => termDot (y i) (s j)

/-- The compiled observed cross Gram equals the actual real cross-Gram matrix of the interpreted observations.
Use: Certify the genuine conjugacy solve matrix rather than a surrogate.
Article: main_krylov, prop:deep, actual checked RFC array execution.
Proof: Each actual entry is precisely the proved interpreted Euclidean pairing. -/
theorem termCross_value {n p : ℕ} (y s : Fin p → Fin n → Term) (x : ℕ → ℝ) :
    matrixValue (termCross y s) x=crossGram (fun i => euclideanValue (y i) x) (fun i => euclideanValue (s i) x) := by
  ext i j
  exact termDot_inner (y i) (s j) x

/-- The actual finite totalized inverse expression in all dimensions, including the empty coefficient space.
Use: Handle the original empty retained window and every genuine later solve uniformly.
Article: main_krylov, prop:deep, actual checked RFC array execution. -/
def termInverse : {n : ℕ} → Matrix (Fin n) (Fin n) Term → Matrix (Fin n) (Fin n) Term
  | 0, _ => fun i => Fin.elim0 i
  | _+1, H => termInv H

/-- The compiled finite inverse equals the actual totalized real matrix inverse in every dimension.
Use: Keep empty-window and singular-domain behavior consistent with the true method implementation.
Article: main_krylov, prop:deep, actual checked RFC array execution.
Proof: The empty coefficient matrix is unique; every positive-size case is the already proved true adjugate inverse. -/
theorem termInverse_value {n : ℕ} (H : Matrix (Fin n) (Fin n) Term) (x : ℕ → ℝ) :
    matrixValue (termInverse H) x=(matrixValue H x)⁻¹ := by
  cases n with
  | zero => exact Subsingleton.elim _ _
  | succ n => exact termInv_value H x

/-- The actual finite data-only conjugacy-direction expression.
Use: Compile the true RFC direction from original stored steps, measured secants and gradient.
Article: main_krylov, prop:deep, actual checked RFC array execution. -/
def termDirection {n p : ℕ} (s y : Fin p → Fin n → Term) (g : Fin n → Term) : Fin n → Term :=
  termAdd (termNeg g) (termCombine s (termMatVec (termInverse (termCross y s)) (termCoordinates y g)))

/-- The compiled finite direction is exactly the actual method conjugacy solve on the interpreted observed arrays.
Use: Prove source direction semantics independently of all numerical enclosures.
Article: main_krylov, prop:deep, actual checked RFC array execution.
Proof: The true finite synthesis, cross Gram, inverse and projected-gradient semantics identify precisely the original implemented direction formula. -/
theorem termDirection_value {n p : ℕ} (s y : Fin p → Fin n → Term) (g : Fin n → Term) (x : ℕ → ℝ) :
    euclideanValue (termDirection s y g) x=
      conjugacyDirection (fun i => euclideanValue (s i) x) (fun i => euclideanValue (y i) x) (euclideanValue g x) := by
  simp only [termDirection,euclideanValue_add,euclideanValue_neg,termCombine_value,
    termMatVec_value,termInverse_value,termCross_value,termCoordinates_value,
    conjugacyDirection,conjugacyCoefficients]

/-- The exact original newest-first latest-information coefficient-model expression.
Use: Retain the actual measured-pair storage order in the singular-model certificate.
Article: main_krylov, prop:deep, actual checked RFC array execution. -/
def termPairModel {n p : ℕ} (s y : Fin p → Fin n → Term) : Matrix (Fin p) (Fin p) Term :=
  fun i j => termDot (s (max i j)) (y (min i j))

/-- The compiled newest-first coefficient matrix is exactly the actual latest-information pair model.
Use: Certify the genuine executed correction model.
Article: main_krylov, prop:deep, actual checked RFC array execution.
Proof: Each ordered index pair uses the same older step and newer measured image as the real method. -/
theorem termPairModel_value {n p : ℕ} (s y : Fin p → Fin n → Term) (x : ℕ → ℝ) :
    matrixValue (termPairModel s y) x=pairModel (fun i => euclideanValue (s i) x) (fun i => euclideanValue (y i) x) := by
  ext i j
  exact termDot_inner _ _ x


/-- The compiled square matrix action is exactly the genuine physical Euclidean operator action.
Use: Connect actual source Hessian actions to the checked finite arithmetic.
Article: main_krylov, prop:deep, actual checked RFC array execution.
Proof: Lift the proved real finite matrix-vector identity through the genuine Euclidean coordinate equivalence. -/
theorem euclideanValue_matVec {n : ℕ} (H : Matrix (Fin n) (Fin n) Term) (v : Fin n → Term) (x : ℕ → ℝ) :
    euclideanValue (termMatVec H v) x=Matrix.toEuclideanCLM (𝕜 := ℝ) (matrixValue H x) (euclideanValue v x) := by
  change WithLp.toLp 2 (vectorValue (termMatVec H v) x)=WithLp.toLp 2 (matrixValue H x*ᵥvectorValue v x)
  exact congrArg (WithLp.toLp 2) (termMatVec_value H v x)

/-- The actual exact-search line-length expression in the unchanged certificate language.
Use: Compile the true physical line search with its original numerator and curvature.
Article: main_krylov, prop:deep, actual checked RFC array execution. -/
def termLineLength {n : ℕ} (g d z : Fin n → Term) : Term :=
  .mul (.neg (termDot g d)) (.inv (termDot d z))

/-- The compiled line coefficient equals the actual exact-search scalar used by the original method.
Use: Preserve the genuine physical search step before checking its denominator and sign.
Article: main_krylov, prop:deep, actual checked RFC array execution.
Proof: Use the actual Euclidean pairing semantics, real inner-product symmetry and the original line-length definition. -/
theorem termLineLength_value {n : ℕ} (g d z : Fin n → Term) (x : ℕ → ℝ) :
    (termLineLength g d z).value x=Reference.lineLength (euclideanValue g x) (euclideanValue d x) (euclideanValue z x) := by
  simp only [termLineLength,Expr.value,termDot_inner,Reference.lineLength,div_eq_mul_inv]
  rw [real_inner_comm (euclideanValue g x) (euclideanValue d x)]

/-- The exact expression for the real post-search gradient.
Use: Compile the genuine incoming gradient of the final model correction.
Article: main_krylov, prop:deep, actual checked RFC array execution. -/
def termPostSearch {n : ℕ} (g d z : Fin n → Term) : Fin n → Term :=
  termAdd g (termScale (termLineLength g d z) z)

/-- The compiled post-search vector is exactly the actual original searched gradient.
Use: Tie the terminal certificate numerator to the true incoming physical gradient.
Article: main_krylov, prop:deep, actual checked RFC array execution.
Proof: The proved real line-length and scalar-vector semantics give the implemented search update. -/
theorem termPostSearch_value {n : ℕ} (g d z : Fin n → Term) (x : ℕ → ℝ) :
    euclideanValue (termPostSearch g d z) x=Reference.searchedGradient (euclideanValue g x) (euclideanValue d x) (euclideanValue z x) := by
  simp only [termPostSearch,euclideanValue_add,euclideanValue_scale,termLineLength_value,Reference.searchedGradient]

/-- The exact expression for the genuine full observed-model correction query.
Use: Compile the actual correction displacement before the real independent operator answer.
Article: main_krylov, prop:deep, actual checked RFC array execution. -/
def termModelQuery {n p : ℕ} (s : Fin p → Fin n → Term) (H : Matrix (Fin p) (Fin p) Term)
    (g : Fin n → Term) : Fin n → Term :=
  termCombine s (termNeg (termMatVec (termInverse H) (termCoordinates s g)))

/-- The compiled model query equals the real finite coefficient-model correction used by the actual policy.
Use: Remove any assumed correction-vector formula from the numerical source certificate.
Article: main_krylov, prop:deep, actual checked RFC array execution.
Proof: Apply the genuine synthesis, totalized inverse and projected-coordinate semantics to the original negative coefficient solve. -/
theorem termModelQuery_value {n p : ℕ} (s : Fin p → Fin n → Term) (H : Matrix (Fin p) (Fin p) Term)
    (g : Fin n → Term) (x : ℕ → ℝ) :
    euclideanValue (termModelQuery s H g) x=combine (fun i => euclideanValue (s i) x)
      (modelCoefficients (fun i => euclideanValue (s i) x) (matrixValue H x) (euclideanValue g x)) := by
  rw [termModelQuery,termCombine_value]
  have hn (v : Fin p → Term) : vectorValue (termNeg v) x=-(vectorValue v x) := rfl
  rw [hn,termMatVec_value,termInverse_value,termCoordinates_value]
  rfl


end
end krylov.Correction.Certificate
