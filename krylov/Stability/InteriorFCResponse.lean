import krylov.Stability.UniformResponseScale

/-!
Article: Theorem 3.1 [thm:A] of krylov.tex.
Use: state the genuine global response remainder with precisely one fewer
independent canonical increments than cycle steps, as printed in the paper.
The one-atom cycle has the empty increment family and zero remainder.
Source: zero extension of the actual finite interior family, finite sum
identities and the proved arbitrary-spectral-scale actual FC response theorem.
-/

namespace krylov.Stability
noncomputable section
open Matrix Finset krylov.Methods krylov.Reference krylov.Secant krylov.Variation
open scoped Matrix.Norms.L2Operator
variable {n N : ℕ}

/-- Extend a genuine finite family of meaningful interior canonical increments by zero.
Use: Extend a genuine finite family of meaningful interior canonical increments by zero.
Article: main_krylov, thm:A, exactly the meaningful interior FC budgets.
Proof: There is no extra independent terminal increment or terminal budget. -/
def interiorIncrements (E : Fin n → Matrix (Fin N) (Fin N) ℝ) (l : ℕ) : Matrix (Fin N) (Fin N) ℝ :=
  if hl : l < n then E ⟨l,hl⟩ else 0

/-- Zero extension preserves the genuine symmetry of every assigned canonical increment.
Use: Zero extension preserves the genuine symmetry of every assigned canonical increment.
Article: main_krylov, thm:A, exactly the meaningful interior FC budgets.
Proof: Each actual entry is either the supplied symmetric matrix or zero. -/
theorem interiorIncrements_symmetric (E : Fin n → Matrix (Fin N) (Fin N) ℝ)
    (hE : ∀ l, (E l).IsSymm) (l : ℕ) : (interiorIncrements E l).IsSymm := by
  unfold interiorIncrements
  split_ifs with hl
  · exact hE ⟨l,hl⟩
  · exact Matrix.isSymm_zero

/-- The actual cycle budget of the extended family is exactly the sum of the meaningful interior component norms.
Use: The actual cycle budget of the extended family is exactly the sum of the meaningful interior component norms.
Article: main_krylov, thm:A, exactly the meaningful interior FC budgets.
Proof: The final entry is zero; identify the genuine finite-index sum with its natural-number prefix. -/
theorem interiorIncrements_budget (E : Fin n → Matrix (Fin N) (Fin N) ℝ) :
    (∑ l∈range (n+1), ‖interiorIncrements E l‖)=∑ l : Fin n, ‖E l‖ := by
  have hz : interiorIncrements E n=0 := by simp [interiorIncrements]
  rw [sum_range_succ,hz,norm_zero,add_zero,← Fin.sum_univ_eq_sum_range]
  apply sum_congr rfl
  intro i _
  simp only [interiorIncrements,i.isLt,dite_true]

/-- The genuine response of the zero-extended family is exactly the printed finite sum over the meaningful interior increments.
Use: The genuine response of the zero-extended family is exactly the printed finite sum over the meaningful interior increments.
Article: main_krylov, thm:A, exactly the meaningful interior FC budgets.
Proof: The zero terminal increment contributes zero to the actual response, and the remaining finite prefix is precisely the supplied family. -/
theorem interiorIncrements_response (base : Matrix (Fin N) (Fin N) ℝ)
    (g : EuclideanSpace ℝ (Fin N)) (E : Fin n → Matrix (Fin N) (Fin N) ℝ) :
    fullCycleResponse base g (range (n+1)) (interiorIncrements E)=
      ∑ l : Fin n, (oldFlag base g l.val).starProjection
        (Matrix.toEuclideanCLM (𝕜 := ℝ) (E l) (remainingTail base g l.val)) := by
  have hz : interiorIncrements E n=0 := by simp [interiorIncrements]
  -- Remove the unused terminal slot from the actual response itself, as well as from its budget.
  unfold fullCycleResponse
  rw [sum_range_succ]
  simp only [hz,map_zero,_root_.zero_apply,add_zero]
  rw [← Fin.sum_univ_eq_sum_range]
  apply sum_congr rfl
  intro i _
  simp only [interiorIncrements,i.isLt,dite_true]

/-- The actual defined FC cycle has the true uniform quadratic first-response remainder under exactly the printed interior component budgets at every positive spectral scale.
Use: The actual defined FC cycle has the true uniform quadratic first-response remainder under exactly the printed interior component budgets at every positive spectral scale.
Article: main_krylov, thm:A, exactly the meaningful interior FC budgets.
Proof: Reuse the completed arbitrary-scale theorem on the zero-extended real increment family. The proved budget and response identities eliminate the unused terminal slot without an additional smallness assumption. -/
theorem fullFC_interior_quadratic_response (base : Matrix (Fin (n+1)) (Fin (n+1)) ℝ)
    (hb : base.PosDef) (E : Fin n → Matrix (Fin (n+1)) (Fin (n+1)) ℝ)
    (hE : ∀ l, (E l).IsSymm) (g : EuclideanSpace ℝ (Fin (n+1))) {μ κ : ℝ}
    (hμ : 0 < μ) (hκ : 1 ≤ κ)
    (hspec : ∀ i, μ ≤ hb.1.eigenvalues i ∧ hb.1.eigenvalues i ≤ μ*κ)
    (hcount : referenceAtomCount base hb g=n+1)
    (hsolve : ∀ i < n+1, IsUnit (crossGram
      (windowImages (selectedWindow fullMemory (fcHistory fullMemory (canonicalFCPath base (interiorIncrements E) 1) g i)))
      (windowSteps (selectedWindow fullMemory (fcHistory fullMemory (canonicalFCPath base (interiorIncrements E) 1) g i)))).det)
    (hcurv : ∀ i < n+1, inner ℝ (fcDirection fullMemory (canonicalFCPath base (interiorIncrements E) 1) g i)
      (canonicalFCPath base (interiorIncrements E) 1 i (fcDirection fullMemory (canonicalFCPath base (interiorIncrements E) 1) g i))≠0)
    (hsmall : 8*(((n+1 : ℕ) : ℝ)+1)*(∑ l : Fin n, ‖E l‖) ≤ 1) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base)⁻¹
        (fcGradient fullMemory (canonicalFCPath base (interiorIncrements E) 1) g (n+1))-
      (∑ l : Fin n, (oldFlag base g l.val).starProjection
        (Matrix.toEuclideanCLM (𝕜 := ℝ) (E l) (remainingTail base g l.val)))‖ ≤
      fcResponseConstant (n+1) κ*(∑ l : Fin n, ‖E l‖)^2*‖cgCanonicalError base g 0‖ := by
  have h := fullFC_uniform_quadratic_response_scale base hb (interiorIncrements E)
    (interiorIncrements_symmetric E hE) g hμ hκ hspec hcount hsolve hcurv
    (by simpa only [interiorIncrements_budget] using hsmall)
  simpa only [interiorIncrements_budget,interiorIncrements_response] using h
end
end krylov.Stability
