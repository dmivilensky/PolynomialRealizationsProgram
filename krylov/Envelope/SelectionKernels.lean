import krylov.Envelope.DaleckiiKreinLastBlock
import krylov.Envelope.PolynomialCoverage
import krylov.Envelope.RFCSelectionValue
import krylov.Envelope.ScenarioAbsorption

set_option autoImplicit false
/-!
Article: main_krylov, thm:select, nuclear selection kernels and actual sign scenarios.
Use: define the printed compressed sensitivity kernels, their nuclear
support and concrete feasible spectral-sign increment arrays.
Source: DaleckiiKrein65 for the polynomial sensitivity; reuse actual
finite spectral/nuclear duality and the proved common-tilt Frobenius formula.
-/

namespace krylov.Envelope
noncomputable section
open krylov.Reference krylov.Methods krylov.LinearAlgebra chebyshev1 Polynomial Matrix Finset
open scoped BigOperators Matrix.Norms.L2Operator NNReal
variable {n : ℕ}

/-- The printed complementary canonical flag compression of the actual Daleckii--Krein sensitivity matrix.
Use: The printed complementary canonical flag compression of the actual Daleckii--Krein sensitivity matrix.
Article: main_krylov, thm:select, nuclear selection kernels and actual sign scenarios.
Proof: Compress the true polynomial matrix by its actual complementary projector on both sides. -/
def selectionKernel (base : Matrix (Fin n) (Fin n) ℝ) (g : EuclideanSpace ℝ (Fin n))
    (N : ℕ) (p : ℝ[X]) (l : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  canonicalComplementMatrix base g l*daleckiiKreinMatrix base g N p*canonicalComplementMatrix base g l

/-- Every actual compressed selection kernel is symmetric.
Use: Every actual compressed selection kernel is symmetric.
Article: main_krylov, thm:select, nuclear selection kernels and actual sign scenarios.
Proof: Transpose the actual product and use the genuine projector and sensitivity symmetries. -/
theorem selectionKernel_symm (base : Matrix (Fin n) (Fin n) ℝ) (g : EuclideanSpace ℝ (Fin n))
    (N : ℕ) (p : ℝ[X]) (l : ℕ) : (selectionKernel base g N p l).IsSymm := by
  simp only [selectionKernel,Matrix.IsSymm,transpose_mul,(canonicalComplementMatrix_symm base g l).eq,
    (daleckiiKreinMatrix_symm base g N p).eq,mul_assoc]

/-- The actual budget-weighted nuclear support of a genuine polynomial direction.
Use: The actual budget-weighted nuclear support of a genuine polynomial direction.
Article: main_krylov, thm:select, nuclear selection kernels and actual sign scenarios.
Proof: Sum the true compressed nuclear norms against the real nonnegative increment budgets. -/
def selectionSupport (base : Matrix (Fin n) (Fin n) ℝ) (g : EuclideanSpace ℝ (Fin n))
    (N : ℕ) (ω : Fin (N-1) → ℝ≥0) (p : ℝ[X]) : ℝ :=
  ∑ l : Fin (N-1), (ω l : ℝ)*matrixNuclearNorm (selectionKernel base g N p l.val)

/-- The concrete actual spectral-sign increment array for a given genuine polynomial direction.
Use: The concrete actual spectral-sign increment array for a given genuine polynomial direction.
Article: main_krylov, thm:select, nuclear selection kernels and actual sign scenarios.
Proof: Scale each actual finite spectral sign by its true increment budget, retaining zero eigenmodes. -/
def selectionSignIncrements (base : Matrix (Fin n) (Fin n) ℝ) (g : EuclideanSpace ℝ (Fin n))
    (N : ℕ) (ω : Fin (N-1) → ℝ≥0) (p : ℝ[X]) : Fin (N-1) → Matrix (Fin n) (Fin n) ℝ :=
  fun l => (ω l : ℝ) • signInBasis (SpectralBasis.ofHermitian (selectionKernel base g N p l.val)
    (Matrix.isHermitian_iff_isSymm.mpr (selectionKernel_symm base g N p l.val)))

/-- Every concrete actual sign increment array satisfies all true symmetric spectral budgets, including zero budgets.
Use: Every concrete actual sign increment array satisfies all true symmetric spectral budgets, including zero budgets.
Article: main_krylov, thm:select, nuclear selection kernels and actual sign scenarios.
Proof: Use the actual spectral sign symmetry and its proved spectral norm bound, then scale by the real nonnegative budget. -/
theorem selectionSignIncrements_budget (base : Matrix (Fin n) (Fin n) ℝ)
    (g : EuclideanSpace ℝ (Fin n)) (N : ℕ) (ω : Fin (N-1) → ℝ≥0) (p : ℝ[X]) :
    selectionSignIncrements base g N ω p∈incrementBudget N ω := by
  intro l
  refine ⟨(signInBasis_isSymm _).smul _,?_⟩
  change ‖(ω l : ℝ) • signInBasis _‖≤(ω l : ℝ)
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (ω l).coe_nonneg]
  exact (mul_le_mul_of_nonneg_left (signInBasis_norm_le _) (ω l).coe_nonneg).trans_eq (mul_one _)

/-- The actual continuous common-tilt polynomial functional equals the finite sum of genuine increment/selection-kernel product traces.
Use: The actual continuous common-tilt polynomial functional equals the finite sum of genuine increment/selection-kernel product traces.
Article: main_krylov, thm:select, nuclear selection kernels and actual sign scenarios.
Proof: Use the proved true Daleckii--Krein Frobenius pairing, restrict the actual finite extension to its real coordinates, and identify symmetric Frobenius products with genuine traces. -/
theorem canonicalTiltLinear_polynomial_pairing (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (N : ℕ) (hN : 2≤N) (hcount : N≤referenceAtomCount base hb g)
    (E : Fin (N-1) → Matrix (Fin n) (Fin n) ℝ) (hE : ∀ l, (E l).IsSymm)
    (p : ℝ[X]) (hdegree : p.natDegree<N) :
    inner ℝ (canonicalPolynomialVector base g p) (canonicalTiltLinear base g N E)=
      ∑ l : Fin (N-1), Matrix.trace (E l*selectionKernel base g N p l.val) := by
  -- Restrict the true infinite increment formula to its actual finite coordinates before using genuine symmetric trace pairing.
  rw [canonicalTiltLinear_apply base hb g N hN hcount E,
    actual_tilt_daleckiiKrein_pairing base hb g N hN hcount (matrixSequenceExtension (N-1) E)
      (fun l hl => by rw [matrixSequenceExtension_fin E ⟨l,hl⟩];exact hE ⟨l,hl⟩) p hdegree]
  rw [← Fin.sum_univ_eq_sum_range]
  apply sum_congr rfl
  intro l _
  rw [matrixSequenceExtension_fin E l,symmetric_frobenius_trace _ _ (hE l)]
  rfl

/-- The concrete genuine sign scenario attains exactly the actual budget-weighted nuclear support in its true polynomial direction.
Use: The concrete genuine sign scenario attains exactly the actual budget-weighted nuclear support in its true polynomial direction.
Article: main_krylov, thm:select, nuclear selection kernels and actual sign scenarios.
Proof: Apply the genuine common-tilt trace formula to the actual feasible sign increments, and use the proved true spectral sign/nuclear trace equality in every real block. -/
theorem selectionSignIncrements_pairing (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (N : ℕ) (hN : 2≤N) (hcount : N≤referenceAtomCount base hb g)
    (ω : Fin (N-1) → ℝ≥0) (p : ℝ[X]) (hdegree : p.natDegree<N) :
    inner ℝ (canonicalPolynomialVector base g p) (canonicalTiltLinear base g N (selectionSignIncrements base g N ω p))=
      selectionSupport base g N ω p := by
  rw [canonicalTiltLinear_polynomial_pairing base hb g N hN hcount _
    (fun l => (selectionSignIncrements_budget base g N ω p l).1) p hdegree]
  apply sum_congr rfl
  intro l _
  change Matrix.trace (((ω l : ℝ) • signInBasis _) * selectionKernel base g N p l.val)=_
  rw [Matrix.smul_mul,Matrix.trace_smul,trace_sign_eq_nuclear,smul_eq_mul]
end
end krylov.Envelope
