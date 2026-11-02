import krylov.OneGradient.PlanarCompletion
set_option autoImplicit false
/-!
Article: main_krylov, thm:local(c), actual closed-disc hidden-entry fibre.
Use: construct genuine original spectral-budget endpoint/centre matrices
with exactly one shared observed column, including singular disc corners.
Source: true planar Schur completion, exact rational interval midpoint and
half-width, with explicit direct proofs at the singular corners.
-/

namespace krylov.OneGradient
noncomputable section
open Matrix krylov.LinearAlgebra
open scoped Matrix.Norms.L2Operator InnerProductSpace
variable {n : ℕ}

/-- The actual missing scalar interval centre, with the source zero corner
convention supplied by real zero division.
Use: the observed-column centring method never uses the unknown entry.
Article: main_krylov, thm:local(c), y_c. -/
def hiddenPlaneCentre (a g : ℝ) : ℝ := -a^2*g/(1-g^2)

/-- The true missing scalar interval half-width on the entire closed disc.
Use: the two actual hidden endpoint adversaries and centred output rule.
Article: main_krylov, thm:local(c), h. -/
def hiddenPlaneHalfWidth (a g : ℝ) : ℝ := 1-a^2/(1-g^2)

/-- Every point of the true closed missing-entry interval gives an actual
symmetric spectral-contraction matrix on the real physical plane, including
both endpoints, its genuine centre and the two singular disc corners.
Use: physical hidden-model adversaries and centring use original matrix
budgets, without a strict-interior or continuous-centre hypothesis.
Article: main_krylov, thm:local(c), actual missing-entry completion fibre.
Proof: away from the singular corner, the exact rational midpoint and
half-width reproduce the two genuine Schur endpoints. At a singular
corner the cross coordinate is zero and both true shifted diagonal forms
are nonnegative directly. The actual planar whole-matrix test applies. -/
theorem hiddenPlane_completion_bound (e h : EuclideanSpace ℝ (Fin n))
    (he : ‖e‖=1) (hh : ‖h‖=1) (heh : inner ℝ e h=0) (a g sigma : ℝ)
    (hdisc : a^2+g^2≤1) (hsigma : sigma∈Set.Icc (-1 : ℝ) 1) :
    ‖planarMatrix e h (hiddenPlaneCentre a g+sigma*hiddenPlaneHalfWidth a g) a g‖≤1 := by
  have hd : 0≤1-g^2 := by nlinarith [sq_nonneg a]
  by_cases hdz : 1-g^2=0
  · have haz : a=0 := by nlinarith [sq_nonneg a]
    have hgl : -1≤ g := by nlinarith
    have hgu : g≤1 := by nlinarith
    rw [haz]
    simp only [hiddenPlaneCentre,hiddenPlaneHalfWidth,zero_pow (by decide : 2≠0),neg_zero,
      zero_mul,zero_div,zero_add,sub_zero,mul_one]
    apply planarCompletion_norm_le e h he hh heh sigma 0 g
    · intro x z
      have hx := mul_nonneg (sub_nonneg.mpr hsigma.2) (sq_nonneg x)
      have hz := mul_nonneg (sub_nonneg.mpr hgu) (sq_nonneg z)
      nlinarith
    · intro x z
      have hx := mul_nonneg (by linarith [hsigma.1] : 0≤1+sigma) (sq_nonneg x)
      have hz := mul_nonneg (by linarith : 0≤1+g) (sq_nonneg z)
      nlinarith
  have hdp : 0<1-g^2 := lt_of_le_of_ne hd (Ne.symm hdz)
  have hg : |g|<1 := abs_lt.mpr ⟨by nlinarith,by nlinarith⟩
  have hgp : 0<1+g := by linarith [(abs_lt.mp hg).1]
  have hgm : 0<1-g := by linarith [(abs_lt.mp hg).2]
  have hhalf : 0≤ hiddenPlaneHalfWidth a g := by
    unfold hiddenPlaneHalfWidth
    exact sub_nonneg.mpr ((div_le_one hdp).mpr (by linarith))
  have hlo : hiddenPlaneCentre a g-hiddenPlaneHalfWidth a g= -1+a^2/(1+g) := by
    unfold hiddenPlaneCentre hiddenPlaneHalfWidth
    field_simp
    ring
  have hhi : hiddenPlaneCentre a g+hiddenPlaneHalfWidth a g=1-a^2/(1-g) := by
    unfold hiddenPlaneCentre hiddenPlaneHalfWidth
    field_simp
    ring
  apply planarCompletion_schur_bound e h he hh heh _ a g hg
  · rw [← hlo]
    nlinarith [mul_nonneg (by linarith [hsigma.1] : 0≤ sigma+1) hhalf]
  · rw [← hhi]
    nlinarith [mul_nonneg (sub_nonneg.mpr hsigma.2) hhalf]

/-- All actual hidden completions have exactly the same genuine observed
column in the real terminal query direction, independent of the hidden entry.
Use: the source indistinguishability applies to entire true histories.
Article: main_krylov, thm:local(c), shared physical observed column.
Proof: the true planar action pairs the terminal unit vector with itself
and its real orthogonal old unit vector; the hidden diagonal disappears. -/
theorem hiddenPlane_observed_column (e h : EuclideanSpace ℝ (Fin n))
    (hh : ‖h‖=1) (heh : inner ℝ e h=0) (a g y : ℝ) :
    Matrix.toEuclideanCLM (𝕜 := ℝ) (planarMatrix e h y a g) h=a • e+g • h := by
  have hhh : inner ℝ h h=1 := by rw [real_inner_self_eq_norm_sq,hh,one_pow]
  rw [planarMatrix_action]
  simp only [heh,hhh,mul_zero,mul_one,zero_add]

end
end krylov.OneGradient
