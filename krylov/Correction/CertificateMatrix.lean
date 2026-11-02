import chebyshev2.Numerics.IntegerExpression
import krylov.LinearAlgebra.MatrixNormBounds

/-!
Article: main_krylov, prop:deep, kernel-certified finite matrix arithmetic.
Use: reuse the existing checked integer expression/program language for
actual finite matrix sums, determinants, adjugates and totalized inverses.
Source: chebyshev2 Numerics.IntegerExpression and IntegerProgram; the
standard Laplace and adjugate formulas use mathlib det_succ_row_zero and
adjugate_fin_succ_eq_det_submatrix. No native verification is introduced.
-/

namespace krylov.Correction.Certificate
noncomputable section
open Matrix Finset chebyshev2.Numerics.IntegerCertificate
open scoped BigOperators

/-- The existing earlier-package integer-checker expression type used unchanged for finite source matrix arithmetic.
Use: Reuse the original certified arithmetic language and its independent real semantics.
Article: main_krylov, prop:deep, actual checked finite matrix semantics. -/
abbrev Term := Expr

/-- A true finite sum in the existing certificate expression language, with an explicit empty sum.
Use: Compile actual finite source inner products without an assumed algebraic expression.
Article: main_krylov, prop:deep, actual checked finite matrix semantics. -/
def termSum : {n : ℕ} → (Fin n → Term) → Term
  | 0, _ => .literal 0 1
  | n+1, f => .add (f 0) (termSum (fun i : Fin n => f i.succ))

/-- The compiled finite expression sum has exactly its actual finite real-sum semantics.
Use: Connect generated arithmetic graphs to genuine source matrix entries.
Article: main_krylov, prop:deep, actual checked finite matrix semantics.
Proof: Induct on the actual finite dimension and split the genuine finite sum into its first coordinate and remaining coordinates. -/
theorem termSum_value {n : ℕ} (f : Fin n → Term) (x : ℕ → ℝ) :
    (termSum f).value x=∑ i, (f i).value x := by
  induction n with
  | zero => simp only [termSum,Expr.value,Int.cast_zero,Nat.cast_one,zero_div,Fin.sum_univ_zero]
  | succ n ih => simp only [termSum,Expr.value,ih,Fin.sum_univ_succ]

/-- The genuine real finite-vector interpretation of an original checker-expression family.
Use: Keep every certificate vector tied to its actual real values.
Article: main_krylov, prop:deep, actual checked finite matrix semantics. -/
def vectorValue {n : ℕ} (v : Fin n → Term) (x : ℕ → ℝ) : Fin n → ℝ := fun i => (v i).value x

/-- The genuine real finite-matrix interpretation of an original checker-expression array.
Use: Compare exact source matrix formulas with the same checked literal arithmetic.
Article: main_krylov, prop:deep, actual checked finite matrix semantics. -/
def matrixValue {n m : ℕ} (H : Matrix (Fin n) (Fin m) Term) (x : ℕ → ℝ) : Matrix (Fin n) (Fin m) ℝ :=
  fun i j => (H i j).value x

/-- The exact finite dot-product expression in the unchanged earlier checker language.
Use: Encode original real pairings of the actual RFC source arrays.
Article: main_krylov, prop:deep, actual checked finite matrix semantics. -/
def termDot {n : ℕ} (u v : Fin n → Term) : Term := termSum (fun i => .mul (u i) (v i))

/-- The actual compiled finite pairing is exactly the genuine real vector dot product.
Use: Discharge physical scalar pairing semantics before accepting numerical bounds.
Article: main_krylov, prop:deep, actual checked finite matrix semantics.
Proof: Use the proved finite real-sum semantics and the literal multiplication value rule. -/
theorem termDot_value {n : ℕ} (u v : Fin n → Term) (x : ℕ → ℝ) :
    (termDot u v).value x=vectorValue u x ⬝ᵥ vectorValue v x := by
  simp only [termDot,termSum_value,Expr.value,vectorValue,dotProduct]

/-- The exact finite matrix-vector multiplication expression.
Use: Compile actual source operator actions in the shared certified arithmetic graph.
Article: main_krylov, prop:deep, actual checked finite matrix semantics. -/
def termMatVec {n m : ℕ} (H : Matrix (Fin n) (Fin m) Term) (v : Fin m → Term) : Fin n → Term :=
  fun i => termDot (H i) v

/-- The compiled finite matrix action is exactly its actual real matrix-vector action.
Use: Preserve real source vector semantics through every certificate operator action.
Article: main_krylov, prop:deep, actual checked finite matrix semantics.
Proof: Each genuine row pairing has the independently proved actual dot-product semantics. -/
theorem termMatVec_value {n m : ℕ} (H : Matrix (Fin n) (Fin m) Term) (v : Fin m → Term) (x : ℕ → ℝ) :
    vectorValue (termMatVec H v) x=matrixValue H x*ᵥvectorValue v x := by
  ext i
  exact termDot_value (H i) v x

/-- The true finite Laplace determinant expression, including the empty determinant one.
Use: Certify actual source coefficient-model and query-basis determinants.
Article: main_krylov, prop:deep, actual checked finite matrix semantics. -/
def termDet : {n : ℕ} → Matrix (Fin n) (Fin n) Term → Term
  | 0, _ => .literal 1 1
  | n+1, H => termSum (fun j : Fin (n+1) => .mul (.mul (.literal ((-1 : ℤ)^j.val) 1) (H 0 j))
      (termDet (H.submatrix Fin.succ j.succAbove)))

/-- The actual compiled Laplace expression equals the genuine real matrix determinant in every finite dimension.
Use: Keep the singular-model certificate about the actual source determinant.
Article: main_krylov, prop:deep, actual checked finite matrix semantics.
Proof: Induct on the true finite matrix size and apply the standard first-row Laplace expansion with precisely the same signed real minors. -/
theorem termDet_value {n : ℕ} (H : Matrix (Fin n) (Fin n) Term) (x : ℕ → ℝ) :
    (termDet H).value x=(matrixValue H x).det := by
  -- The true Laplace expansion uses the same finite signed minors as the original certificate expression.
  induction n with
  | zero => simp only [termDet,Expr.value,Int.cast_one,Nat.cast_one,div_one,Matrix.det_isEmpty]
  | succ n ih =>
    rw [termDet,termSum_value,Matrix.det_succ_row_zero]
    apply sum_congr rfl
    intro j _
    simp only [Expr.value,Int.cast_pow,Int.cast_neg,Int.cast_one,Nat.cast_one,div_one,ih]
    rfl

/-- The exact signed-minor adjugate expression for a genuine positive-size square source matrix.
Use: Compile the actual terminal adjugate numerator used in the unboundedness certificate.
Article: main_krylov, prop:deep, actual checked finite matrix semantics. -/
def termAdj {n : ℕ} (H : Matrix (Fin (n+1)) (Fin (n+1)) Term) : Matrix (Fin (n+1)) (Fin (n+1)) Term :=
  fun i j => .mul (.literal ((-1 : ℤ)^(j.val+i.val)) 1) (termDet (H.submatrix j.succAbove i.succAbove))

/-- Every actual signed-minor certificate entry equals the corresponding genuine real adjugate entry.
Use: Tie the checked terminal numerator to the actual source adjugate.
Article: main_krylov, prop:deep, actual checked finite matrix semantics.
Proof: Apply the standard finite adjugate signed-minor formula and the proved actual determinant semantics. -/
theorem termAdj_value {n : ℕ} (H : Matrix (Fin (n+1)) (Fin (n+1)) Term) (x : ℕ → ℝ) :
    matrixValue (termAdj H) x=(matrixValue H x).adjugate := by
  ext i j
  rw [Matrix.adjugate_fin_succ_eq_det_submatrix]
  simp only [matrixValue,termAdj,Expr.value,Int.cast_pow,Int.cast_neg,Int.cast_one,Nat.cast_one,div_one,termDet_value]
  rfl

/-- The genuine totalized matrix-inverse expression obtained from its true determinant reciprocal and adjugate.
Use: Compile real source conjugacy and correction coefficient solves without supplying their desired answers.
Article: main_krylov, prop:deep, actual checked finite matrix semantics. -/
def termInv {n : ℕ} (H : Matrix (Fin (n+1)) (Fin (n+1)) Term) : Matrix (Fin (n+1)) (Fin (n+1)) Term :=
  fun i j => .mul (.inv (termDet H)) (termAdj H i j)

/-- The actual compiled inverse expression equals the genuine real totalized nonsingular matrix inverse, including singular matrices.
Use: Separate exact real inverse semantics from the independently checked denominator domains.
Article: main_krylov, prop:deep, actual checked finite matrix semantics.
Proof: The genuine matrix inverse is determinant reciprocal times adjugate. The proved actual determinant and adjugate semantics identify the same expression exactly. -/
theorem termInv_value {n : ℕ} (H : Matrix (Fin (n+1)) (Fin (n+1)) Term) (x : ℕ → ℝ) :
    matrixValue (termInv H) x=(matrixValue H x)⁻¹ := by
  -- Retain the genuine totalized determinant reciprocal rather than assuming a nonsingular model.
  rw [Matrix.inv_def,Ring.inverse_eq_inv]
  ext i j
  change (termInv H i j).value x=(matrixValue H x).det⁻¹*(matrixValue H x).adjugate i j
  simp only [termInv,Expr.value,termDet_value,← termAdj_value]
  rfl

end
end krylov.Correction.Certificate
