import krylov.Methods.ProjectedSearch

set_option autoImplicit false
/-!
Article: main_krylov, s3:thm:cf, genuine exact last-probe response.
Use: identify actual correction-free final-search changes for true probe
perturbations orthogonal to the genuine chosen direction.
Source: actual exact-search scalar quotient and true linear oracle update;
no asymptotic output response is assumed.
-/

namespace krylov.Methods
noncomputable section
open krylov.Reference
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- An actual probe perturbation orthogonal to the true chosen direction leaves the genuine totalized exact-search length unchanged.
Use: An actual probe perturbation orthogonal to the true chosen direction leaves the genuine totalized exact-search length unchanged.
Article: main_krylov, s3:thm:cf, genuine exact last-probe response.
Proof: The actual curvature pairing has a genuine zero perturbation. -/
theorem lineLength_orthogonal_probe (g d z w : E) (hw : inner ℝ d w=0) (t : ℝ) :
    lineLength g d (z+t • w)=lineLength g d z := by
  simp only [lineLength,inner_add_right,real_inner_smul_right,hw,mul_zero,add_zero]

/-- The actual searched gradient has an exact affine response to every real probe perturbation orthogonal to its true direction.
Use: The actual searched gradient has an exact affine response to every real probe perturbation orthogonal to its true direction.
Article: main_krylov, s3:thm:cf, genuine exact last-probe response.
Proof: Its genuine line length is unchanged; expand the actual line-gradient update. -/
theorem searchedGradient_orthogonal_probe (g d z w : E) (hw : inner ℝ d w=0) (t : ℝ) :
    searchedGradient g d (z+t • w)=searchedGradient g d z+t • (lineLength g d z • w) := by
  simp only [searchedGradient,lineLength_orthogonal_probe g d z w hw t,smul_add,smul_smul]
  module
end
end krylov.Methods
