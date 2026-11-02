import krylov.Realization.FixedBridge
import krylov.Realization.AffineUnrolling

/-!
Article: main_krylov, s6:kernel and prop:dict(i), general polynomial insertion dictionary.
Use: construct actual query and injection polynomials for every existing fixed-memory
realization and prove their exact factorization of the true two-variable kernel.
Source: the existing ordered affine realization calculus of PasechnyukTakac26;
only the scalar query and readout contractions are repackaged here.
-/
namespace krylov.Realization
noncomputable section
open chebyshev1 Polynomial Matrix
open scoped BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
/-- The actual polynomial of the scalar query selected from the true fixed-memory prefix.
Use: identifies the reference vector on which an error-model drift acts.
Article: main_krylov, s6:kernel, r_s. -/
def queryPolynomial (R : chebyshev1.Realization ι) (s : ℕ) : ℝ[X] :=
  (fun i=>C (R.q s i)) ⬝ᵥ (orderedProduct R.polynomialStep s *ᵥ fun j=>C (R.b j))
/-- The actual terminal response polynomial of an independent additive oracle injection.
Use: its sign follows the real negative gradient-query insertion convention.
Article: main_krylov, s6:kernel, R_s. -/
def injectionPolynomial (R : chebyshev1.Realization ι) (N s : ℕ) : ℝ[X] :=
  -((fun i=>C (R.readout i)) ⬝ᵥ (orderedProduct (fun t=>R.polynomialStep (s+1+t)) (N-(s+1)) *ᵥ fun j=>C (R.g s j)))
/-- The same fixed realization with its real query schedule shifted to the start of a tail.
Use: reuses the proved polynomial transfer theorem for every actual injection tail.
Article: main_krylov, prop:dict(i), chronological tail transfer. -/
def shiftedRealization (R : chebyshev1.Realization ι) (a : ℕ) : chebyshev1.Realization ι :=
  {R with P := fun j=>R.P (a+j),g := fun j=>R.g (a+j),q := fun j=>R.q (a+j)}
/-- The actual query polynomial evaluates to the true unperturbed query selected from fixed memory.
Use: connects the constructed polynomial with the real scalar affine trajectory.
Article: main_krylov, s6:kernel.
Proof: evaluate the actual finite contractions and apply the existing ordered polynomial-transfer identity. -/
theorem queryPolynomial_eval (R : chebyshev1.Realization ι) (s : ℕ) (nu : ℝ) :
    (queryPolynomial R s).eval nu=R.q s ⬝ᵥ (orderedProduct (fun i=>R.scalarStep i nu) s *ᵥ R.b) := by
  simp only [queryPolynomial,dotProduct,Matrix.mulVec,eval_finsetSum,eval_mul,eval_C,
    ← R.orderedProduct_polynomialStep_eval,Matrix.map_apply]

/-- The actual injection polynomial evaluates to the genuine terminal readout of its true remaining tail.
Use: no tail response is assumed in the realization dictionary.
Article: main_krylov, s6:kernel.
Proof: apply the existing polynomial-transfer theorem to the actual shifted realization and evaluate its real contraction. -/
theorem injectionPolynomial_eval (R : chebyshev1.Realization ι) (N s : ℕ) (lam : ℝ) :
    (injectionPolynomial R N s).eval lam=
      -(R.readout ⬝ᵥ (orderedProduct (fun i=>R.scalarStep (s+1+i) lam) (N-(s+1)) *ᵥ R.g s)) := by
  have ht : (orderedProduct (fun i=>R.polynomialStep (s+1+i)) (N-(s+1))).map (eval lam)=
      orderedProduct (fun i=>R.scalarStep (s+1+i) lam) (N-(s+1)) :=
    (shiftedRealization R (s+1)).orderedProduct_polynomialStep_eval _ lam
  simp only [injectionPolynomial,dotProduct,Matrix.mulVec,eval_neg,eval_finsetSum,eval_mul,eval_C,
    ← ht,Matrix.map_apply]

/-- The true fixed-memory kernel factors into actual scalar terminal-tail and scalar reference-query transfers.
Use: factorization follows from the actual rank-one query insertion at every memory size.
Article: main_krylov, s6:kernel and prop:dict(i).
Proof: move the scalar readout through the true memory operator product;
the actual rank-one insertion separates its two scalar contractions. -/
theorem fixed_kernel_scalar_factorization (R : chebyshev1.Realization ι) (N s : ℕ) (lam nu : ℝ) :
    R.kernel N s lam nu=
      -(R.readout ⬝ᵥ (orderedProduct (fun i=>R.scalarStep (s+1+i) lam) (N-(s+1)) *ᵥ R.g s)) *
        (R.q s ⬝ᵥ (orderedProduct (fun i=>R.scalarStep i nu) s *ᵥ R.b)) := by
  -- Separate the actual tail/readout and prefix/query contractions at the genuine rank-one insertion.
  have hc (M : Matrix ι ι ℝ) : R.scalarContract M=R.readout ⬝ᵥ (M *ᵥ R.b) := by
    simp only [chebyshev1.Realization.scalarContract,dotProduct,Matrix.mulVec,Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _=>Finset.sum_congr rfl fun j _=>by ring
  rw [chebyshev1.Realization.kernel,hc,← Matrix.mulVec_mulVec,← Matrix.mulVec_mulVec,
    chebyshev1.Realization.queryFactor,Matrix.vecMulVec_mulVec,Matrix.mulVec_smul, dotProduct_smul]
  simp only [op_smul_eq_smul,smul_eq_mul]
  ring
/-- Every fixed realization has the printed polynomial kernel factorization with its actual query and injection polynomials.
Use: the arbitrary-memory insertion dictionary is an identity of the actual existing realization kernel.
Article: main_krylov, s6:kernel and prop:dict(i).
Proof: substitute the two proved actual polynomial evaluations into the genuine rank-one kernel factorization. -/
theorem fixed_kernel_polynomial_factorization (R : chebyshev1.Realization ι)
    (N s : ℕ) (lam nu : ℝ) :
    R.kernel N s lam nu=(injectionPolynomial R N s).eval lam*(queryPolynomial R s).eval nu := by
  rw [injectionPolynomial_eval,queryPolynomial_eval,fixed_kernel_scalar_factorization]

end
end krylov.Realization
