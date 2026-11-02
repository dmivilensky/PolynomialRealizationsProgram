import krylov.Methods.ProjectedModel

/-!
Article: main_krylov, def:classes and lem:U(c,d), actual coefficient homogeneity.
Use: prove degree-zero homogeneity of the computed finite inverse coefficients
and degree-one homogeneity of actual directions, corrections and exact searches.
Source: scalar covariance of finite nonsingular inverses and real inner products.
The identities include totalized singular solves; no inverse domain is assumed.
-/

namespace krylov.Methods
noncomputable section
open Matrix krylov.Reference
open scoped BigOperators InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
/-- A scalar factors out of the actual totalized real matrix inverse with its reciprocal.
Use: scale actual finite coefficient solves without assuming their homogeneity.
Article: main_krylov, lem:U(c), degree-zero coefficients.
Proof: zero scalars give the zero matrix; otherwise invert the scalar identity
matrix and reverse its product with the supplied matrix. -/
theorem matrix_inv_scalar (H : Matrix ι ι ℝ) (c : ℝ) : (c • H)⁻¹=c⁻¹ • H⁻¹ := by
  -- Product reversal also covers singular H, so this covariance needs no hidden solve premise.
  by_cases hc : c=0
  · simp [hc]
  have hi : (c • (1 : Matrix ι ι ℝ))⁻¹=c⁻¹ • 1 := by
    apply Matrix.inv_eq_left_inv
    simp [smul_smul,hc]
  have he : c • H=(c • (1 : Matrix ι ι ℝ))*H := by simp
  rw [he,Matrix.mul_inv_rev,hi]
  simp

omit [Fintype ι] [DecidableEq ι] in
/-- Scaling both observed families scales their actual cross Gram matrix quadratically.
Use: the real conjugacy matrix transforms with the same weight as its right-hand side.
Article: main_krylov, lem:U(c).
Proof: apply real bilinearity to each actual observed entry. -/
theorem crossGram_scalar (s y : ι → E) (c : ℝ) :
    crossGram (fun i => c • y i) (fun i => c • s i)=(c*c) • crossGram y s := by
  ext i j
  simp only [crossGram,real_inner_smul_left,real_inner_smul_right,Matrix.smul_apply,smul_eq_mul]
  ring

omit [Fintype ι] [DecidableEq ι] in
/-- Scaling the window and gradient scales their actual paired right-hand side quadratically.
Use: both actual inverse solves have degree-zero coefficients.
Article: main_krylov, lem:U(c).
Proof: real bilinearity applies independently in every observed coordinate. -/
theorem coordinates_scalar (s : ι → E) (g : E) (c : ℝ) :
    coordinates (fun i => c • s i) (c • g)=(c*c) • coordinates s g := by
  ext i
  simp only [coordinates,real_inner_smul_left,real_inner_smul_right,Pi.smul_apply,smul_eq_mul]
  ring

/-- The actual FC conjugacy coefficients are homogeneous of degree zero in the observed data.
Use: source homogeneity is a proved property of the implemented coefficients.
Article: main_krylov, def:classes and lem:U(c,d).
Proof: the quadratic Gram and paired right-hand side factors cancel around the actual inverse. -/
theorem conjugacyCoefficients_scalar (s y : ι → E) (g : E) (c : ℝ) (hc : c≠0) :
    conjugacyCoefficients (fun i => c • s i) (fun i => c • y i) (c • g)=
      conjugacyCoefficients s y g := by
  rw [conjugacyCoefficients,crossGram_scalar,coordinates_scalar,matrix_inv_scalar,
    smul_mulVec,mulVec_smul,smul_smul,inv_mul_cancel₀ (mul_ne_zero hc hc),one_smul]
  rfl

/-- The actual latest-model coefficients are homogeneous of degree zero in observed data.
Use: RFC and XRFC correction coefficients obey the source scaling convention.
Article: main_krylov, def:classes and lem:U(c,d).
Proof: cancel the common nonzero quadratic scaling of the real model and right-hand side. -/
theorem modelCoefficients_scalar (s : ι → E) (H : Matrix ι ι ℝ) (g : E) (c : ℝ) (hc : c≠0) :
    modelCoefficients (fun i => c • s i) ((c*c) • H) (c • g)=modelCoefficients s H g := by
  rw [modelCoefficients,coordinates_scalar,matrix_inv_scalar,
    smul_mulVec,mulVec_smul,smul_smul,inv_mul_cancel₀ (mul_ne_zero hc hc),one_smul]
  rfl

omit [DecidableEq ι] in
/-- A genuine physical observed combination is homogeneous of degree one when its coefficients are fixed.
Use: transfer degree-zero coefficient identities to actual vector outputs.
Article: main_krylov, lem:U(c).
Proof: commute real scalar multiplication in each summand and collect the finite sum. -/
theorem combine_scalar (s : ι → E) (b : ι → ℝ) (c : ℝ) :
    combine (fun i => c • s i) b=c • combine s b := by
  simp only [combine,Finset.smul_sum,smul_comm (b _) c]

/-- The computed physical FC direction is homogeneous of degree one in all observed data.
Use: actual vector outputs inherit the proved coefficient scaling.
Article: main_krylov, lem:U(c,d).
Proof: substitute actual degree-zero coefficients and collect the two scaled physical terms. -/
theorem conjugacyDirection_scalar (s y : ι → E) (g : E) (c : ℝ) (hc : c≠0) :
    conjugacyDirection (fun i => c • s i) (fun i => c • y i) (c • g)=c • conjugacyDirection s y g := by
  rw [conjugacyDirection,conjugacyCoefficients_scalar s y g c hc,combine_scalar,
    ← smul_neg,← smul_add]
  rfl

omit [Fintype ι] [DecidableEq ι] in
/-- The genuine newest-information pair model scales quadratically in all stored observations.
Use: actual RFC and XRFC models have precisely the scaling used by the coefficient theorem.
Article: main_krylov, lem:U(c,d).
Proof: each true latest pairing is bilinear in the two observed vectors. -/
theorem pairModel_scalar {p : ℕ} (s y : Fin p → E) (c : ℝ) :
    pairModel (fun i => c • s i) (fun i => c • y i)=(c*c) • pairModel s y := by
  ext i j
  simp only [pairModel,real_inner_smul_left,real_inner_smul_right,Matrix.smul_apply,smul_eq_mul]
  ring

omit [Fintype ι] [DecidableEq ι] in
/-- The actual exact-search scalar is unchanged when all observed vectors scale by a common nonzero number.
Use: no lower bound on the actual search curvature is needed for the scaling identity.
Article: main_krylov, lem:U(c,d).
Proof: cancel the common nonzero quadratic factor in the numerator and denominator, including a zero denominator. -/
theorem lineLength_scalar (g d z : E) (c : ℝ) (hc : c≠0) :
    lineLength (c • g) (c • d) (c • z)=lineLength g d z := by
  simp only [lineLength,real_inner_smul_left,real_inner_smul_right]
  have he (a : ℝ) : -(c*(c*a))=(c*c)*(-a) := by ring
  rw [he,← mul_assoc,mul_div_mul_left _ _ (mul_ne_zero hc hc)]

omit [Fintype ι] [DecidableEq ι] in
/-- The actual post-search gradient scales by the same factor as the observed initial data.
Use: the exact search preserves positive homogeneity of every subsequent real correction query.
Article: main_krylov, lem:U(c,d).
Proof: use the proved invariant real line scalar and collect its actual gradient update. -/
theorem searchedGradient_scalar (g d z : E) (c : ℝ) (hc : c≠0) :
    searchedGradient (c • g) (c • d) (c • z)=c • searchedGradient g d z := by
  rw [searchedGradient,lineLength_scalar g d z c hc,smul_comm (lineLength g d z) c,← smul_add]
  rfl

end
end krylov.Methods
