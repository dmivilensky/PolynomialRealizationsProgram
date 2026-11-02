import krylov.Cancellation.ResidualPropagation
set_option autoImplicit false
/-!
Article: main_krylov, thm:dcs(c), chronological stale-defect geometric damping.
Use: turn the actual finite residual-product identity and a common bound on
its real multipliers into the printed age-dependent geometric defect estimate.
Source: finite variation of constants, finite product monotonicity and the
real triangle inequality; no residual response is postulated.
-/

namespace krylov.Cancellation
noncomputable section
open scoped BigOperators

/-- Uniformly bounded actual damping multipliers give the original geometric
age weight on each finite old-defect contribution.
Use: insert the real arithmetic Gauss--Radau multiplier bounds into native
DC residual products, or into their proved reference linearization.
Article: main_krylov, thm:dcs(c), geometric forgetting.
Proof: absolute values factor through each real finite product, whose factors
are bounded by rho; its actual chronological cardinality is N-1-j. -/
theorem residual_product_geometric (e d : ℕ → ℝ) (N : ℕ) (rho : ℝ)
    (he : ∀ l<N,|e l|≤rho) :
    |∑ j∈Finset.range N,(∏ l∈Finset.Ico (j+1) N,e l)*d j|≤
      ∑ j∈Finset.range N,rho^(N-1-j)*|d j| := by
  calc
    _≤∑ j∈Finset.range N,|(∏ l∈Finset.Ico (j+1) N,e l)*d j| := Finset.abs_sum_le_sum_abs _ _
    _≤_ := by
      apply Finset.sum_le_sum
      intro j hj
      rw [abs_mul,Finset.abs_prod]
      apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
      calc
        _≤∏ _l∈Finset.Ico (j+1) N,rho := by
          apply Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _)
          intro l hl
          exact he l (Finset.mem_Ico.mp hl).2
        _=rho^(N-1-j) := by
          rw [Finset.prod_const,Nat.card_Ico]
          congr 1
          omega

/-- An actual zero-initialized residual recursion with bounded real
multipliers has the full finite geometric fresh-defect bound.
Use: arithmetic damping yields geometric forgetting, while rho=1 recovers
FC-style accumulation and rho=0 leaves only the newest defect.
Article: main_krylov, thm:dcs(c).
Proof: unroll the true recursion with the proved exact finite identity and
apply the genuine chronological geometric product estimate. -/
theorem residual_recursion_geometric (r e d : ℕ → ℝ) (hzero : r 0=0)
    (N : ℕ) (rho : ℝ) (hrec : ∀ k<N,r (k+1)=e k*r k+d k)
    (he : ∀ l<N,|e l|≤rho) :
    |r N|≤∑ j∈Finset.range N,rho^(N-1-j)*|d j| := by
  rw [residual_recursion_unroll r e d hzero N hrec]
  exact residual_product_geometric e d N rho he

end
end krylov.Cancellation
