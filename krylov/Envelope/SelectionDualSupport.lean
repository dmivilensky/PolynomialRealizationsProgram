import krylov.Envelope.SelectionKernels
import krylov.Envelope.UnitPolynomial
import krylov.LinearAlgebra.BudgetSupport

set_option autoImplicit false
/-!
Article: main_krylov, thm:select, attained directional nuclear selection support.
Use: prove the exact actual polynomial-direction support over all true
symmetric spectral-budget increments, with a concrete genuine sign witness.
Source: actual Daleckii--Krein trace kernels and previously proved
finite spectral/nuclear duality, including real zero-budget cases.
-/

namespace krylov.Envelope
noncomputable section
open krylov.Reference krylov.Methods krylov.LinearAlgebra chebyshev1 Polynomial Matrix Finset
open scoped BigOperators Matrix.Norms.L2Operator NNReal
variable {n : ℕ}

/-- The genuine actual polynomial-direction common-tilt support is exactly the printed budget-weighted nuclear sum and is attained by the concrete true sign scenario.
Use: The genuine actual polynomial-direction common-tilt support is exactly the printed budget-weighted nuclear sum and is attained by the concrete true sign scenario.
Article: main_krylov, thm:select, attained directional nuclear selection support.
Proof: The constructed actual sign increments attain every true block trace simultaneously. Every other real symmetric budget increment obeys the proved actual spectral/nuclear trace bound. -/
theorem selection_polynomial_support (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (N : ℕ) (hN : 2≤N) (hcount : N≤referenceAtomCount base hb g)
    (ω : Fin (N-1) → ℝ≥0) (p : ℝ[X]) (hdegree : p.natDegree<N) :
    IsGreatest ((fun E => inner ℝ (canonicalPolynomialVector base g p) (canonicalTiltLinear base g N E)) '' incrementBudget N ω)
      (selectionSupport base g N ω p) := by
  -- The actual spectral sign scenario attains every real block at once; genuine trace duality bounds all other feasible increments.
  refine ⟨⟨selectionSignIncrements base g N ω p,selectionSignIncrements_budget base g N ω p,
    selectionSignIncrements_pairing base hb g N hN hcount ω p hdegree⟩,?_⟩
  rintro r ⟨E,hE,rfl⟩
  dsimp only
  rw [canonicalTiltLinear_polynomial_pairing base hb g N hN hcount E (fun l => (hE l).1) p hdegree]
  exact sum_le_sum (fun l _ => trace_spectral_bound (E l) (selectionKernel base g N p l.val)
    (hE l).1 (Matrix.isHermitian_iff_isSymm.mpr (selectionKernel_symm base g N p l.val))
    (ω l).coe_nonneg (hE l).2)

/-- Every genuine unit polynomial nuclear support is bounded by the actual common-tilt selection value.
Use: Every genuine unit polynomial nuclear support is bounded by the actual common-tilt selection value.
Article: main_krylov, thm:select, attained directional nuclear selection support.
Proof: Evaluate the actual feasible sign scenario, apply true Cauchy--Schwarz with its genuine unit polynomial vector, and use the real attained common-tilt norm upper bound. -/
theorem selectionSupport_le_value (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (N : ℕ) (hN : 2≤N) (hcount : N≤referenceAtomCount base hb g)
    (ω : Fin (N-1) → ℝ≥0) (p : ℝ[X]) (hp : p∈unitPolynomialSet base g N) :
    selectionSupport base g N ω p≤selectionValue base g N ω := by
  rw [← selectionSignIncrements_pairing base hb g N hN hcount ω p hp.1]
  calc
    _ ≤ ‖canonicalPolynomialVector base g p‖*‖canonicalTiltLinear base g N (selectionSignIncrements base g N ω p)‖ := real_inner_le_norm _ _
    _ = ‖canonicalTiltLinear base g N (selectionSignIncrements base g N ω p)‖ := by rw [hp.2,one_mul]
    _ ≤ _ := (selectionValue_attained base g N ω).2 ⟨_,selectionSignIncrements_budget base g N ω p,rfl⟩

/-- Every degree-admissible genuine polynomial nuclear selection support is nonnegative, including all actual zero budgets.
Use: Every degree-admissible genuine polynomial nuclear selection support is nonnegative, including all actual zero budgets.
Article: main_krylov, thm:select, attained directional nuclear selection support.
Proof: The true zero increment scenario is feasible and gives actual zero directional support. -/
theorem selectionSupport_nonneg (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (N : ℕ) (hN : 2≤N) (hcount : N≤referenceAtomCount base hb g)
    (ω : Fin (N-1) → ℝ≥0) (p : ℝ[X]) (hdegree : p.natDegree<N) :
    0≤selectionSupport base g N ω p := by
  apply (selection_polynomial_support base hb g N hN hcount ω p hdegree).2
  refine ⟨0,(scenarioBudget_zero_mem (n := n) ω).1,?_⟩
  dsimp only
  rw [map_zero,inner_zero_right]
end
end krylov.Envelope
