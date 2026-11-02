import krylov.Envelope.SelectionNuclearDual
import krylov.Envelope.SelectionBoundary

set_option autoImplicit false
/-!
Article: main_krylov, thm:select, printed nuclear selection sum without the final budget.
Use: express the actual attained nuclear maximum with exactly the source
early increment indices, excluding the genuinely zero last sensitivity block.
Source: the actual nuclear-dual theorem and the proved true zero final
complementary Daleckii--Krein compression.
-/

namespace krylov.Envelope
noncomputable section
open krylov.Reference krylov.LinearAlgebra Polynomial Matrix Finset
open scoped BigOperators Matrix.Norms.L2Operator NNReal
variable {n : ℕ}

/-- The printed weighted nuclear selection sum over exactly the increment indices zero through horizon minus three.
Use: The printed weighted nuclear selection sum over exactly the increment indices zero through horizon minus three.
Article: main_krylov, thm:select, printed nuclear selection sum without the final budget.
Proof: Filter the actual finite increment indices by their genuine early-index bound. -/
def selectionEarlySupport (base : Matrix (Fin n) (Fin n) ℝ) (g : EuclideanSpace ℝ (Fin n))
    (N : ℕ) (ω : Fin (N-1) → ℝ≥0) (p : ℝ[X]) : ℝ :=
  ∑ l∈(univ : Finset (Fin (N-1))).filter (fun l => l.val<N-2),
    (ω l : ℝ)*matrixNuclearNorm (selectionKernel base g N p l.val)

/-- The actual full nuclear selection support equals exactly its printed early-budget sum.
Use: The actual full nuclear selection support equals exactly its printed early-budget sum.
Article: main_krylov, thm:select, printed nuclear selection sum without the final budget.
Proof: The only omitted true increment is the actual final one; its genuine compressed sensitivity and nuclear norm are zero. -/
theorem selectionSupport_eq_early (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (N : ℕ) (hN : 2≤N) (hcount : N≤referenceAtomCount base hb g)
    (ω : Fin (N-1) → ℝ≥0) (p : ℝ[X]) (hdegree : p.natDegree<N) :
    selectionSupport base g N ω p=selectionEarlySupport base g N ω p := by
  -- The only omitted actual index is the genuine final increment, whose true compressed sensitivity vanishes.
  unfold selectionEarlySupport
  rw [sum_filter]
  apply sum_congr rfl
  intro l _
  by_cases hl : l.val<N-2
  · rw [ite_eq_left hl]
  · rw [ite_eq_right hl]
    have he : l.val=N-2 := by have := l.isLt;omega
    have hz : selectionKernel base g N p l.val=0 := by
      rw [selectionKernel,he]
      exact daleckiiKrein_last_compression_zero base hb g N hN hcount p hdegree
    rw [hz,matrixNuclearNorm_zero,mul_zero]

/-- The actual selection value is the attained maximum of exactly the printed early-budget nuclear sum over the true source unit polynomial set.
Use: The actual selection value is the attained maximum of exactly the printed early-budget nuclear sum over the true source unit polynomial set.
Article: main_krylov, thm:select, printed nuclear selection sum without the final budget.
Proof: Identify the actual support images using the genuine zero final-block theorem and apply the proved attained full nuclear duality. -/
theorem selection_nuclear_early_dual (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (N : ℕ) (hN : 2≤N) (hcount : N≤referenceAtomCount base hb g)
    (ω : Fin (N-1) → ℝ≥0) :
    IsGreatest (selectionEarlySupport base g N ω '' unitPolynomialSet base g N) (selectionValue base g N ω) := by
  have he : selectionEarlySupport base g N ω '' unitPolynomialSet base g N=
      selectionSupport base g N ω '' unitPolynomialSet base g N := by
    apply Set.image_congr
    intro p hp
    exact (selectionSupport_eq_early base hb g N hN hcount ω p hp.1).symm
  rw [he]
  exact selection_nuclear_dual base hb g N hN hcount ω
end
end krylov.Envelope
