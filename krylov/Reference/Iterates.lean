import krylov.Reference.CGGeometry

/-!
Article: main_krylov, s2:eq:cg and prop:dict(i), reference iterates and frozen recurrence.
Use: construct the actual reference displacement from the executed CG steps
and prove its gradient/momentum form with the actual measured coefficients.
Source: elimination of the actual Fletcher--Reeves direction (Meurant06).
-/

namespace krylov.Reference.CG
noncomputable section
open scoped BigOperators InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The accumulated physical CG displacement from the initial point.
Use: actual reference iterates are initial point plus this computed finite sum.
Article: main_krylov, s2:eq:cg, x_k⁰−x₀. -/
def displacement (Q : E →L[ℝ] E) (g : E) (k : ℕ) : E :=
  ∑ i∈Finset.range k, length Q g i • direction Q g i

/-- The actual reference displacement advances by its actual computed step.
Use: connects the trajectory to the executed line and direction coefficients.
Article: main_krylov, s2:eq:cg, x_(k+1)−x_k=α_k d_k.
Proof: split the last term of the actual finite step sum. -/
theorem displacement_succ (Q : E →L[ℝ] E) (g : E) (k : ℕ) :
    displacement Q g (k+1)=displacement Q g k+length Q g k • direction Q g k := by
  exact Finset.sum_range_succ _ k

/-- The actual computed gradient equals its initial gradient plus the operator applied to the actual displacement.
Use: the constructed reference iterates solve the original fixed quadratic.
Article: main_krylov, s2:eq:cg, g_k=g₀+A(x_k−x₀).
Proof: induction uses the two already established genuine state and displacement updates. -/
theorem gradient_displacement (Q : E →L[ℝ] E) (g : E) (k : ℕ) :
    gradient Q g k=g+Q (displacement Q g k) := by
  induction k with
  | zero => simp only [displacement, Finset.range_zero, Finset.sum_empty, map_zero, add_zero]; rfl
  | succ k ih =>
    rw [gradient_succ, displacement_succ, map_add, map_smul, ih, add_assoc]

/-- The actual reference iterates obey the source's frozen gradient/momentum recurrence with their actual CG coefficients.
Use: later fixed-realization arguments can freeze the measured trajectory rather than choose an unrelated Jacobi chain.
Article: main_krylov, prop:dict(i), equation s6:frozen.
Proof: substitute the actual direction recurrence and recover its predecessor from the actual nonzero line step. -/
theorem displacement_frozen (Q : E →L[ℝ] E) (g : E) (k : ℕ) (hk : length Q g k≠0) :
    displacement Q g (k+2)=displacement Q g (k+1)-length Q g (k+1) • gradient Q g (k+1)+
      (length Q g (k+1)*beta Q g k/length Q g k) • (displacement Q g (k+1)-displacement Q g k) := by
  rw [displacement_succ Q g (k+1), direction_succ]
  have hs : displacement Q g (k+1)-displacement Q g k=length Q g k • direction Q g k := by
    rw [displacement_succ]
    abel
  rw [hs, smul_smul, div_mul_cancel₀ _ hk, smul_add, smul_neg, smul_smul]
  abel

end
end krylov.Reference.CG
