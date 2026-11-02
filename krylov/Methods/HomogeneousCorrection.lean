import krylov.Methods.HomogeneousSolve
import krylov.Methods.WindowCoordinates

/-!
Article: main_krylov, lem:U(c,d), actual repeated correction and gate scaling.
Use: propagate positive homogeneity through real repeated model queries and
the true normalized observed-defect gate, including zero or indefinite pair data.
Source: real bilinearity, square-root scalar covariance and the existing finite
query executor; no assumed trajectory scaling or minimum step length is used.
-/

namespace krylov.Methods
noncomputable section
open Matrix
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Every actual repeated-model gradient and accumulated correction scales with its initial data.
Use: genuine intermediate RFC queries and their output preserve degree-one homogeneity.
Article: main_krylov, lem:U(c,d), repeated RFC corrections.
Proof: the actual inverse coefficients stay fixed while the query vector
scales; its true linear-operator image therefore scales, and induction follows
the genuinely observed next gradient through all remaining queries. -/
theorem repeatedModel_execution_scalar (s : ι → E) (H : Matrix ι ι ℝ)
    (B : E →L[ℝ] E) (count : ℕ) (g : E) (c : ℝ) (hc : c≠0) :
    (runCorrections (repeatedModelTree (fun i => c • s i) ((c*c) • H) count (c • g)) B (c • g)).movement=
      c • (runCorrections (repeatedModelTree s H count g) B g).movement ∧
    (runCorrections (repeatedModelTree (fun i => c • s i) ((c*c) • H) count (c • g)) B (c • g)).gradient=
      c • (runCorrections (repeatedModelTree s H count g) B g).gradient := by
  -- Every successor right-hand side is the actual returned gradient, not a hypothetical prescribed residual.
  induction count generalizing g with
  | zero => exact ⟨(smul_zero c).symm,rfl⟩
  | succ count ih =>
    simp only [repeatedModelTree,runCorrections,modelCoefficients_scalar s H g c hc,
      combine_scalar,map_smul,← smul_add]
    exact ⟨by rw [(ih _).1,← smul_add],(ih _).2⟩

omit [Fintype ι] [DecidableEq ι] in
/-- The true normalized observed skew-defect gate is unchanged under common nonzero data scaling.
Use: gated RFC takes the same actual branch at every positive scale, including singular observed pair data.
Article: main_krylov, alg:fc and lem:U(c,d).
Proof: both skew pairings scale by c²; the true diagonal product scales by
c⁴ and its actual square root by c². Cancel this nonzero common scalar in
every actual defect entry, without requiring positive diagonal products. -/
theorem pairDefect_scalar {p : ℕ} (s y : Fin p → E) (c : ℝ) (hc : c≠0) :
    pairDefect (fun i => c • s i) (fun i => c • y i)=pairDefect s y := by
  -- Square-root covariance remains valid if a diagonal product is zero or negative.
  have hs (a b : ℝ) : Real.sqrt ((c*(c*a))*(c*(c*b)))=(c*c)*Real.sqrt (a*b) := by
    rw [show (c*(c*a))*(c*(c*b))=(c*c)^2*(a*b) by ring,
      Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq (mul_self_nonneg c)]
  ext i j
  simp only [pairDefect,real_inner_smul_left,real_inner_smul_right,hs]
  rw [show c*(c*inner ℝ (s i) (y j))-c*(c*inner ℝ (s j) (y i))=
    (c*c)*(inner ℝ (s i) (y j)-inner ℝ (s j) (y i)) by ring,
    mul_div_mul_left _ _ (mul_ne_zero hc hc)]

end
end krylov.Methods
