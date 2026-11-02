import krylov.Methods.CorrectionFreeOracles
import krylov.Methods.ProjectedSearch

set_option autoImplicit false
/-!
Article: main_krylov, apB:lem:mu(d), actual final correction-free residual orthogonality.
Use: prove genuine last recorded-step residual cancellation on arbitrary
true oracle data, including actual zero-curvature totalized searches.
Source: real exact-search quotient and the proved actual searched-gradient
orthogonality on its genuine nonzero curvature domain.
-/

namespace krylov.Methods
noncomputable section
open krylov.Reference
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Every genuine totalized exact-search recorded line step is orthogonal to its actual searched gradient, including true zero curvature.
Use: Every genuine totalized exact-search recorded line step is orthogonal to its actual searched gradient, including true zero curvature.
Article: main_krylov, apB:lem:mu(d), actual final correction-free residual orthogonality.
Proof: A real zero curvature gives a genuine zero totalized line step; otherwise actual searched-gradient orthogonality gives the true pairing. -/
theorem searchedStep_inner_zero (g d z : E) :
    inner ℝ (lineLength g d z • d) (searchedGradient g d z)=0 := by
  by_cases hc : inner ℝ d z=0
  · simp only [lineLength,hc,div_zero,zero_smul,inner_zero_left]
  · rw [real_inner_smul_left,searchedGradient_inner_zero g d z hc,mul_zero]

/-- Every actual correction-free method has identically zero genuine final own-step/returned-gradient residual.
Use: Every actual correction-free method has identically zero genuine final own-step/returned-gradient residual.
Article: main_krylov, apB:lem:mu(d), actual final correction-free residual orthogonality.
Proof: Use its true recorded line step and actual empty-correction returned searched gradient. -/
theorem correctionFree_last_residual (m : ProbedMethod E) (hm : CorrectionFree m)
    (A B : ℕ → E →L[ℝ] E) (g : E) (k : ℕ) :
    inner ℝ (probedStep m A B g k) (probedGradient m A B g (k+1))=0 := by
  rw [correctionFree_step m hm A B g k,correctionFree_gradient_succ m hm A B g k]
  exact searchedStep_inner_zero _ _ _
end
end krylov.Methods
