import krylov.Envelope.SelectionKernels
import chebyshev2.Continuum.NuclearAlgebra

set_option autoImplicit false
/-!
Article: main_krylov, thm:select, nuclear support dependence on budgets.
Use: establish the exact positive linearity and monotonicity of the
printed nuclear support in its nonnegative budget profile.
Source: the existing finite nuclear norm and elementary finite sums.
-/

namespace krylov.Envelope
noncomputable section
open krylov.Reference krylov.LinearAlgebra Polynomial Matrix Finset
open scoped BigOperators Matrix.Norms.L2Operator NNReal
variable {n N : ℕ}

/-- The reused finite matrix nuclear norm is nonnegative.
Use: The reused finite matrix nuclear norm is nonnegative.
Article: main_krylov, thm:select, nuclear support dependence on budgets.
Proof: Its value is the real value of an extended nonnegative norm. -/
theorem matrixNuclearNorm_nonneg (K : Matrix (Fin n) (Fin n) ℝ) : 0≤matrixNuclearNorm K :=
  ENNReal.toReal_nonneg

/-- The reused finite matrix nuclear norm of zero is zero.
Use: The reused finite matrix nuclear norm of zero is zero.
Article: main_krylov, thm:select, nuclear support dependence on budgets.
Proof: Reuse the earlier proved nuclear norm zero identity through the actual matrix/operator map. -/
theorem matrixNuclearNorm_zero : matrixNuclearNorm (0 : Matrix (Fin n) (Fin n) ℝ)=0 := by
  simp only [matrixNuclearNorm,map_zero,chebyshev2.Continuum.nuclearNorm_zero,ENNReal.toReal_zero]

/-- The polynomial nuclear selection support is additive in the budget profile.
Use: The polynomial nuclear selection support is additive in the budget profile.
Article: main_krylov, thm:select, nuclear support dependence on budgets.
Proof: Distribute each nonnegative budget sum in the finite weighted nuclear sum. -/
theorem selectionSupport_add (base : Matrix (Fin n) (Fin n) ℝ) (g : EuclideanSpace ℝ (Fin n))
    (ω η : Fin (N-1) → ℝ≥0) (p : ℝ[X]) :
    selectionSupport base g N (ω+η) p=selectionSupport base g N ω p+selectionSupport base g N η p := by
  simp only [selectionSupport,Pi.add_apply,NNReal.coe_add,add_mul,sum_add_distrib]

/-- The polynomial nuclear selection support is positively homogeneous in the budget profile.
Use: The polynomial nuclear selection support is positively homogeneous in the budget profile.
Article: main_krylov, thm:select, nuclear support dependence on budgets.
Proof: Factor the real nonnegative budget multiplier out of its finite sum. -/
theorem selectionSupport_smul (base : Matrix (Fin n) (Fin n) ℝ) (g : EuclideanSpace ℝ (Fin n))
    (r : ℝ≥0) (ω : Fin (N-1) → ℝ≥0) (p : ℝ[X]) :
    selectionSupport base g N (r • ω) p=(r : ℝ)*selectionSupport base g N ω p := by
  simp only [selectionSupport,Pi.smul_apply,smul_eq_mul,NNReal.coe_mul,mul_assoc,mul_sum]

/-- A zero budget profile has zero polynomial nuclear selection support.
Use: A zero budget profile has zero polynomial nuclear selection support.
Article: main_krylov, thm:select, nuclear support dependence on budgets.
Proof: Every term of its finite weighted sum is zero. -/
theorem selectionSupport_zero (base : Matrix (Fin n) (Fin n) ℝ) (g : EuclideanSpace ℝ (Fin n)) (p : ℝ[X]) :
    selectionSupport base g N 0 p=0 := by simp only [selectionSupport,Pi.zero_apply,NNReal.coe_zero,zero_mul,sum_const_zero]

/-- The polynomial nuclear selection support increases with every nonnegative budget.
Use: The polynomial nuclear selection support increases with every nonnegative budget.
Article: main_krylov, thm:select, nuclear support dependence on budgets.
Proof: Every actual nuclear coefficient is nonnegative, so the finite weighted sum preserves the pointwise budget order. -/
theorem selectionSupport_mono (base : Matrix (Fin n) (Fin n) ℝ) (g : EuclideanSpace ℝ (Fin n))
    (ω η : Fin (N-1) → ℝ≥0) (h : ω≤η) (p : ℝ[X]) :
    selectionSupport base g N ω p≤selectionSupport base g N η p :=
  sum_le_sum (fun l _ => mul_le_mul_of_nonneg_right (show (ω l : ℝ)≤(η l : ℝ) from h l) (matrixNuclearNorm_nonneg _))

/-- The unit singleton budget polynomial support equals its actual individual compressed nuclear norm.
Use: The unit singleton budget polynomial support equals its actual individual compressed nuclear norm.
Article: main_krylov, thm:select, nuclear support dependence on budgets.
Proof: All other real budget coordinates vanish; evaluate the remaining finite summand. -/
theorem selectionSupport_single (base : Matrix (Fin n) (Fin n) ℝ) (g : EuclideanSpace ℝ (Fin n))
    (l : Fin (N-1)) (p : ℝ[X]) :
    selectionSupport base g N (Pi.single l 1) p=matrixNuclearNorm (selectionKernel base g N p l.val) := by
  classical
  rw [selectionSupport,sum_eq_single l]
  · simp
  · intro i _ hne
    simp [hne]
  · simp
end
end krylov.Envelope
