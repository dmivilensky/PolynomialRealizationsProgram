import nesterov.Momentum.Queries
import nesterov.Momentum.Execution

/-!
Article: Remark `rem:twostep`, Appendix A query inversion formula.
Use: the exact finite causal filter recovering physical iterates from queries,
including the residual initial coordinate and the horizon-zero case.
-/
namespace nesterov.Momentum
noncomputable section
open scoped BigOperators
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem iterate_inverse_query_succ (g : E → E) (β τ h : ℝ)
    (hτ : 1+τ≠0) (x₀ : E) (n : ℕ) :
    iterate g β τ h x₀ (n+1)=(1/(1+τ)) • queryIterate g β τ h x₀ (n+1)+
      queryPole τ • iterate g β τ h x₀ n := by
  rw [queryIterate_succ]
  exact inverse_query τ hτ _ _

/-- Forward-index version of the exact geometric query filter. -/
theorem iterate_query_convolution (g : E → E) (β τ h : ℝ)
    (hτ : 1+τ≠0) (x₀ : E) (n : ℕ) :
    iterate g β τ h x₀ n=(1/(1+τ)) •
      (∑ j ∈ Finset.range (n+1),(queryPole τ)^(n-j) • queryIterate g β τ h x₀ j)+
      (queryPole τ)^(n+1) • x₀ := by
  induction n with
  | zero =>
    simpa [Finset.sum_range_succ] using inverse_query τ hτ x₀ x₀
  | succ n ih =>
    have hsum : (∑ j ∈ Finset.range (n+1),
        (queryPole τ)^(n+1-j) • queryIterate g β τ h x₀ j)=
        queryPole τ • (∑ j ∈ Finset.range (n+1),
          (queryPole τ)^(n-j) • queryIterate g β τ h x₀ j) := by
      rw [Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      have hj' : j≤n := by have := Finset.mem_range.mp hj; omega
      rw [show n+1-j=(n-j)+1 by omega,pow_succ,smul_smul]
      congr 1
      ring
    rw [iterate_inverse_query_succ g β τ h hτ,ih]
    rw [Finset.sum_range_succ (fun j =>
      (queryPole τ)^(n+1-j) • queryIterate g β τ h x₀ j) (n+1),hsum]
    simp only [Nat.sub_self,pow_zero,one_smul,pow_succ]
    module

/-- The source's reverse-index formula, with its exact initial residual. -/
theorem iterate_query_inverse_formula (g : E → E) (β τ h : ℝ)
    (hτ : 1+τ≠0) (x₀ : E) (n : ℕ) :
    iterate g β τ h x₀ n=(1/(1+τ)) •
      (∑ j ∈ Finset.range (n+1),(queryPole τ)^j • queryIterate g β τ h x₀ (n-j))+
      (queryPole τ)^(n+1) • x₀ := by
  rw [iterate_query_convolution g β τ h hτ]
  congr 2
  have he := Finset.sum_range_reflect
    (fun j => (queryPole τ)^(n-j) • queryIterate g β τ h x₀ j) (n+1)
  rw [← he]
  apply Finset.sum_congr rfl
  intro j hj
  have hj' : j≤n := by have := Finset.mem_range.mp hj; omega
  simp only [show n+1-1-j=n-j by omega,show n-(n-j)=j by omega]

end
end nesterov.Momentum
