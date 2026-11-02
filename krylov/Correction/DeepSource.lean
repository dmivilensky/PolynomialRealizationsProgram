import krylov.Correction.DeepFamily
import krylov.Correction.CertificatePhase

/-!
Article: main_krylov, prop:deep, independent actual source expressions.
Use: Independent rational source expressions with proved exact original physical oracle semantics.
Source: the original seven rational rows and positive diagonal root,
exact existing physical congruence and real RFC array semantics.
-/

namespace krylov.Correction.Certificate
noncomputable section
open Matrix Finset chebyshev2.Numerics.IntegerCertificate krylov.Methods krylov.Reference krylov.Information krylov.Secant
open scoped BigOperators InnerProductSpace Matrix.Norms.L2Operator

/-- An exact rational literal in the unchanged earlier integer certificate language.
Use: Compile the true original rational source constants with their canonical numerators and denominators.
Article: main_krylov, prop:deep, genuine original numerical source. -/
def termRational (q : ℚ) : Term := .literal q.num q.den

/-- The original certificate rational literal has precisely its genuine real rational value.
Use: Preserve every actual source coefficient exactly.
Article: main_krylov, prop:deep, genuine original numerical source.
Proof: Use the standard exact rational-cast numerator/denominator formula. -/
theorem termRational_value (q : ℚ) (x : ℕ → ℝ) : (termRational q).value x=(q : ℝ) := by
  simp only [termRational,Expr.value,Rat.cast_def]

/-- The exact pointwise matrix-addition expression.
Use: Compile original physical probe accumulation.
Article: main_krylov, prop:deep, genuine original numerical source. -/
def termMatrixAdd {n m : ℕ} (A B : Matrix (Fin n) (Fin m) Term) : Matrix (Fin n) (Fin m) Term :=
  fun i j => .add (A i j) (B i j)

/-- The exact real scalar-matrix multiplication expression.
Use: Compile the original affine first physical increment.
Article: main_krylov, prop:deep, genuine original numerical source. -/
def termMatrixScale {n m : ℕ} (c : Term) (A : Matrix (Fin n) (Fin m) Term) : Matrix (Fin n) (Fin m) Term :=
  fun i j => .mul c (A i j)

/-- The actual zero matrix in the existing integer expression language.
Use: Represent zero original correction defects and absent later increments.
Article: main_krylov, prop:deep, genuine original numerical source. -/
def termMatrixZero (n m : ℕ) : Matrix (Fin n) (Fin m) Term := fun _ _ => .literal 0 1

/-- Compiled matrix addition has exactly its genuine real matrix semantics.
Use: Retain original physical operator sums.
Article: main_krylov, prop:deep, genuine original numerical source.
Proof: Both interpreted entries have the same real sum. -/
theorem termMatrixAdd_value {n m : ℕ} (A B : Matrix (Fin n) (Fin m) Term) (x : ℕ → ℝ) :
    matrixValue (termMatrixAdd A B) x=matrixValue A x+matrixValue B x := rfl

/-- Compiled scalar-matrix multiplication has precisely its actual real form semantics.
Use: Keep the true original affine source coefficients.
Article: main_krylov, prop:deep, genuine original numerical source.
Proof: Every real interpreted entry is the same scalar product. -/
theorem termMatrixScale_value {n m : ℕ} (c : Term) (A : Matrix (Fin n) (Fin m) Term) (x : ℕ → ℝ) :
    matrixValue (termMatrixScale c A) x=c.value x • matrixValue A x := rfl

/-- The compiled zero matrix equals the genuine real zero form.
Use: Preserve the exact original zero perturbation branches.
Article: main_krylov, prop:deep, genuine original numerical source.
Proof: Every interpreted real entry is the exact rational zero. -/
theorem termMatrixZero_value (n m : ℕ) (x : ℕ → ℝ) : matrixValue (termMatrixZero n m) x=0 := by
  ext i j
  simp [matrixValue,termMatrixZero,Expr.value]

/-- The exact rational expression array for the original physical scaled two-block source form.
Use: Compile the actual positive-root physical source coefficients, rather than arbitrary generated numbers.
Article: main_krylov, prop:deep, genuine original numerical source. -/
def sourceBlock (a b c d e f : ℚ) : Matrix (Fin 4) (Fin 4) Term :=
  fun i j => termRational
    ((!![a,b,0,0; b,c,0,0; 0,0,d,e; 0,0,e,f] i j)*((i.val+1 : ℕ) : ℚ)*((j.val+1 : ℕ) : ℚ)/32000)

/-- The independently compiled rational block is exactly the true positive-root transport of the original scaled canonical block.
Use: Prove the original physical source coefficients independently of all interval annotations.
Article: main_krylov, prop:deep, genuine original numerical source.
Proof: Evaluate the true diagonal-root congruence entrywise. Its exact one-thousandth and one-thirty-second scales give the same original rational physical coefficients. -/
theorem sourceBlock_value (a b c d e f : ℚ) (x : ℕ → ℝ) :
    matrixValue (sourceBlock a b c d e f) x=
      deepRoot*(deepBudget • deepBlock (a : ℝ) b c d e f)*deepRoot := by
  ext i j
  simp only [matrixValue,sourceBlock,termRational_value,deepRoot,Matrix.diagonal_mul,Matrix.mul_diagonal,
    deepBlock,Matrix.smul_apply,smul_eq_mul]
  fin_cases i <;> fin_cases j <;> norm_num [deepBudget] <;> ring

/-- The seven independently compiled exact original physical source seed arrays.
Use: Define source arithmetic before inspecting any generated certificate.
Article: main_krylov, prop:deep, genuine original numerical source. -/
def sourceSeed : Fin 7 → Matrix (Fin 4) (Fin 4) Term :=
  ![sourceBlock (-1) 6 (-5) (-7) 2 (-2),sourceBlock 0 (-2) 8 (-7) 2 6,
    sourceBlock (-8) (-7) (-6) 4 6 (-8),sourceBlock (-6) (-7) 5 7 2 (-4),
    sourceBlock 7 (-1) 6 1 2 2,sourceBlock (-8) 2 2 (-4) 6 2,sourceBlock (-3) 0 (-6) 3 (-1) (-1)]

/-- Every compiled literal physical seed equals the genuine positive-root form of the same original canonical seed.
Use: Prevent numerical graph data from choosing a different physical family.
Article: main_krylov, prop:deep, genuine original numerical source.
Proof: Each actual literal row is a specialization of the proved exact original rational block identity. -/
theorem sourceSeed_value (i : Fin 7) (x : ℕ → ℝ) :
    matrixValue (sourceSeed i) x=deepRoot*(deepBudget • deepSeed i)*deepRoot := by
  fin_cases i
  all_goals
    change matrixValue (sourceBlock _ _ _ _ _ _) x=deepRoot*(deepBudget • deepBlock _ _ _ _ _ _)*deepRoot
    rw [sourceBlock_value]
    norm_num

/-- The independently compiled exact original diagonal physical reference.
Use: Keep the real checked source base fixed at the printed matrix.
Article: main_krylov, prop:deep, genuine original numerical source. -/
def sourceBase : Matrix (Fin 4) (Fin 4) Term :=
  fun i j => termRational ((diagonal ![1,4,9,16] : Matrix (Fin 4) (Fin 4) ℚ) i j)

/-- The compiled reference array equals the actual original positive physical base.
Use: Identify the certificate operator source independently of its proposed bounds.
Article: main_krylov, prop:deep, genuine original numerical source.
Proof: Verify the sixteen true rational diagonal matrix entries. -/
theorem sourceBase_value (x : ℕ → ℝ) : matrixValue sourceBase x=deepReference := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [matrixValue,sourceBase,termRational_value,deepReference]

/-- The exact independently compiled physical initial-gradient coordinate array.
Use: Keep the source execution input equal to the original printed gradient.
Article: main_krylov, prop:deep, genuine original numerical source. -/
def sourceInitial : Fin 4 → Term := fun i => termRational (![1,2,3/(10^12),4/(10^12)] i : ℚ)

/-- The actual original positive-root initial gradient has the exact four printed physical rational coordinates.
Use: Connect the genuine mathematical input to the fixed numerical literal source.
Article: main_krylov, prop:deep, genuine original numerical source.
Proof: Apply the true explicit diagonal root to the original canonical coordinates and evaluate the four exact rational products. -/
theorem deepInitial_coordinates : deepInitial=WithLp.toLp 2 ![1,2,(3 : ℝ)/(10^12),4/(10^12)] := by
  ext i
  change (deepRoot*ᵥ![1,1,deepBudget^4,deepBudget^4]) i=_
  simp only [deepRoot,Matrix.mulVec_diagonal]
  fin_cases i <;> norm_num [deepBudget]

/-- The independently compiled initial-gradient literals equal the genuine original physical initial gradient.
Use: Initialize the source execution without an assumed trajectory or generated starting vector.
Article: main_krylov, prop:deep, genuine original numerical source.
Proof: The proved true initial-gradient coordinate formula and exact rational literal semantics identify all four actual coordinates. -/
theorem sourceInitial_value (x : ℕ → ℝ) : euclideanValue sourceInitial x=deepInitial := by
  rw [deepInitial_coordinates]
  ext i
  fin_cases i <;> norm_num [euclideanValue,vectorValue,sourceInitial,termRational_value]

/-- The independently compiled original affine first physical increment and two fixed later physical increments.
Use: Compile the real physical source family in the unchanged integer language.
Article: main_krylov, prop:deep, genuine original numerical source. -/
def sourceIncrement (k : ℕ) : Matrix (Fin 4) (Fin 4) Term :=
  if k=0 then termMatrixAdd (termMatrixScale (.add (.literal 1 1) (.neg (.input 0))) (sourceSeed 0))
    (termMatrixScale (.input 0) (sourceSeed 1))
  else if k=1 then sourceSeed 2 else if k=2 then sourceSeed 3 else termMatrixZero 4 4

/-- Every independently compiled increment equals the actual original physical scenario increment for the true parameter input.
Use: Tie arithmetic certificate perturbations to the original admissible family.
Article: main_krylov, prop:deep, genuine original numerical source.
Proof: Exact relative-form reconstruction identifies the true physical increment. The compiled literal seeds and scalar matrix semantics give the same genuine affine or fixed source branch. -/
theorem sourceIncrement_value (k : ℕ) (x : ℕ → ℝ) :
    matrixValue (sourceIncrement k) x=(deepScenario (x 0)).increment k := by
  -- Recover the genuine physical source increment before comparing any compiled affine branch.
  have he : (deepScenario (x 0)).increment k=deepRoot*deepIncrement (x 0) k*deepRoot := by
    have hh := relativeOperator_reconstruct deepReference ((deepScenario (x 0)).increment k) deepReference_posDef
    rw [deepScenario_increment_relative,deepReference_root] at hh
    exact hh.symm
  rw [he]
  unfold sourceIncrement deepIncrement
  split_ifs
  · rw [termMatrixAdd_value,termMatrixScale_value,termMatrixScale_value,sourceSeed_value,sourceSeed_value]
    simp only [Expr.value,Int.cast_one,Nat.cast_one,div_one,sub_eq_add_neg,
      Matrix.mul_add,Matrix.add_mul,Matrix.mul_smul,Matrix.smul_mul,smul_smul]
    module
  · exact sourceSeed_value 2 x
  · exact sourceSeed_value 3 x
  · simp only [termMatrixZero_value,Matrix.mul_zero,Matrix.zero_mul]

/-- The independently compiled chronological probe operator sequence of the genuine original affine family.
Use: Accumulate the actual source increments in precisely their original order.
Article: main_krylov, prop:deep, genuine original numerical source. -/
def sourceProbe : ℕ → Matrix (Fin 4) (Fin 4) Term
  | 0 => sourceBase
  | k+1 => termMatrixAdd (sourceProbe k) (sourceIncrement k)

/-- Every compiled chronological probe is exactly the actual original physical scenario probe.
Use: Execute the checked source against the genuine original oracle sequence.
Article: main_krylov, prop:deep, genuine original numerical source.
Proof: Induct over the original probe recurrence using the actual base and independently proved true increment semantics. -/
theorem sourceProbe_value (k : ℕ) (x : ℕ → ℝ) :
    matrixValue (sourceProbe k) x=(deepScenario (x 0)).probe k := by
  induction k with
  | zero => simpa only [sourceProbe,Scenario.probe,Finset.sum_range_zero,add_zero,deepScenario_base] using sourceBase_value x
  | succ k ih => rw [sourceProbe,termMatrixAdd_value,ih,sourceIncrement_value,Scenario.probe_succ]

/-- The independently compiled true original independent correction-defect sequence.
Use: Retain the actual physical correction operators rather than idealized secants.
Article: main_krylov, prop:deep, genuine original numerical source. -/
def sourceDefect (k : ℕ) : Matrix (Fin 4) (Fin 4) Term :=
  if k=1 then sourceSeed 4 else if k=2 then sourceSeed 5 else termMatrixZero 4 4

/-- Each compiled correction defect equals the actual independent physical source perturbation.
Use: Keep actual correction queries tied to the printed admissible source matrices.
Article: main_krylov, prop:deep, genuine original numerical source.
Proof: Exact relative reconstruction and the genuine literal-seed semantics identify both original nonzero branches and every true zero branch. -/
theorem sourceDefect_value (k : ℕ) (x : ℕ → ℝ) :
    matrixValue (sourceDefect k) x=(deepScenario (x 0)).correction k := by
  -- Recover the actual physical correction defect from its original canonical source coefficient.
  have he : (deepScenario (x 0)).correction k=deepRoot*deepCorrection k*deepRoot := by
    have hh := relativeOperator_reconstruct deepReference ((deepScenario (x 0)).correction k) deepReference_posDef
    rw [deepScenario_correction_relative,deepReference_root] at hh
    exact hh.symm
  rw [he]
  unfold sourceDefect deepCorrection
  split_ifs
  · exact sourceSeed_value 4 x
  · exact sourceSeed_value 5 x
  · simp only [termMatrixZero_value,Matrix.mul_zero,Matrix.zero_mul]

/-- The independently compiled original physical correction-oracle sequence with its true distinct final operator.
Use: Use the real prescribed preterminal and terminal query operators in source verification.
Article: main_krylov, prop:deep, genuine original numerical source. -/
def sourceCorrection (k : ℕ) : Matrix (Fin 4) (Fin 4) Term :=
  if k<3 then termMatrixAdd (sourceProbe k) (sourceDefect k)
  else termMatrixAdd (sourceProbe 3) (sourceSeed 6)

/-- Every compiled physical correction operator is exactly the actual original scenario correction oracle at the full source horizon.
Use: Prevent the singular-model certificate from replacing the true independent physical query operator.
Article: main_krylov, prop:deep, genuine original numerical source.
Proof: The genuine preterminal probe-plus-defect formula uses the proved actual source components. Beyond the original horizon, exact terminal relative reconstruction identifies the same fixed original last operator. -/
theorem sourceCorrection_value (k : ℕ) (x : ℕ → ℝ) :
    cgOperator (matrixValue (sourceCorrection k) x)=(deepScenario (x 0)).correctionOracle 3 k := by
  -- Keep the genuine finite-horizon terminal query operator distinct from the preterminal correction defects.
  unfold sourceCorrection Scenario.correctionOracle
  split_ifs
  · rw [termMatrixAdd_value,sourceProbe_value,sourceDefect_value]
    rfl
  · rw [termMatrixAdd_value,sourceProbe_value,sourceSeed_value]
    have he : (deepScenario (x 0)).terminal=deepRoot*deepTerminal*deepRoot := by
      have hh := relativeOperator_reconstruct deepReference (deepScenario (x 0)).terminal deepReference_posDef
      rw [deepScenario_terminal_relative,deepReference_root] at hh
      exact hh.symm
    rw [show deepRoot*(deepBudget • deepSeed 6)*deepRoot=(deepScenario (x 0)).terminal from he.symm]
    rfl

end
end krylov.Correction.Certificate
