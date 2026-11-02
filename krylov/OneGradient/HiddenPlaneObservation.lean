import krylov.OneGradient.HiddenPlaneFibre
set_option autoImplicit false
/-!
Article: main_krylov, thm:local(c), true observed-column hidden interval.
Use: derive the original scalar missing-entry constraints from an actual
contractive symmetric physical operator and its genuine observed column.
Source: exact physical pairings, true quadratic contraction bounds and
the real two-unit-vector Bessel inequality.
-/

namespace krylov.OneGradient
noncomputable section
open Matrix krylov.LinearAlgebra
open scoped InnerProductSpace Matrix.Norms.L2Operator
variable {n : ℕ}

/-- The actual symmetric operator has its exact scalar quadratic form
on every real two-vector combination, without a planar-support premise.
Use: the original observed hidden-entry constraints concern the genuine
operator, rather than a postulated compressed two-dimensional model.
Article: main_krylov, thm:local(c), observed physical quadratic forms.
Proof: expand actual linearity and real pairings; the genuine symmetry
identifies both actual cross entries. -/
theorem hiddenPlane_operator_pairing (T : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hT : T.toLinearMap.IsSymmetric) (e h : EuclideanSpace ℝ (Fin n)) (x z : ℝ) :
    inner ℝ (x • e+z • h) (T (x • e+z • h))=
      x^2*inner ℝ e (T e)+2*x*z*inner ℝ e (T h)+z^2*inner ℝ h (T h) := by
  simp only [map_add,map_smul,inner_add_left,inner_add_right,real_inner_smul_left,real_inner_smul_right]
  have he : inner ℝ h (T e)=inner ℝ e (T h) := (real_inner_comm (T e) h).trans (hT e h)
  rw [he]
  ring

/-- An actual physical symmetric contraction's true observed column
belongs to the original closed unit disc, and its genuine hidden entry
lies in the exact Schur interval whenever the measured diagonal is interior.
Use: derive the true feasible hidden centre/radius from real returned
observations, rather than assuming feasibility of a scalar model.
Article: main_krylov, thm:local(c), original observed missing-entry interval.
Proof: the genuine unit-vector image and two-vector Bessel bound give the
disc. Test the actual two shifted quadratic forms on the true Schur
minimizing physical vectors e±a/(1±g) h; the exact physical pairings and
norms yield precisely the printed two scalar endpoint inequalities. -/
theorem hiddenPlane_observed_interval
    (T : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hT : T.toLinearMap.IsSymmetric) (hbound : ‖T‖≤1)
    (e h : EuclideanSpace ℝ (Fin n)) (he : ‖e‖=1) (hh : ‖h‖=1) (heh : inner ℝ e h=0) :
    let y := inner ℝ e (T e)
    let a := inner ℝ e (T h)
    let g := inner ℝ h (T h)
    a^2+g^2≤1 ∧ (|g|<1 → -1+a^2/(1+g)≤ y ∧ y≤1-a^2/(1-g)) := by
  let y := inner ℝ e (T e)
  let a := inner ℝ e (T h)
  let g := inner ℝ h (T h)
  have himg : ‖T h‖≤1 := by
    simpa only [hh,mul_one] using (T.le_opNorm h).trans (mul_le_mul_of_nonneg_right hbound (norm_nonneg h))
  have hbessel := two_unit_bessel e h (T h) he hh heh
  constructor
  · nlinarith [sq_le_sq₀ (norm_nonneg (T h)) (by norm_num : (0 : ℝ)≤1) |>.mpr himg]
  · intro hg
    have hgp : 0<1+g := by linarith [(abs_lt.mp hg).1]
    have hgm : 0<1-g := by linarith [(abs_lt.mp hg).2]
    have hform (t : ℝ) : |y+2*a*t+g*t^2|≤1+t^2 := by
      have hb := contraction_quadratic_bound T hbound ((1 : ℝ) • e+t • h)
      rw [hiddenPlane_operator_pairing T hT e h 1 t,planar_coordinates_norm_sq e h he hh heh] at hb
      have heq : y+2*a*t+g*t^2=inner ℝ e (T e)+2*t*inner ℝ e (T h)+t^2*inner ℝ h (T h) := by
        dsimp only [y,a,g]
        ring
      rw [heq]
      simpa only [one_pow,one_mul,mul_one] using hb
    constructor
    · have h := (abs_le.mp (hform (-a/(1+g)))).1
      have heq : 1+(-a/(1+g))^2+(y+2*a*(-a/(1+g))+g*(-a/(1+g))^2)=1+y-a^2/(1+g) := by
        field_simp
        ring
      linarith
    · have h := (abs_le.mp (hform (a/(1-g)))).2
      have heq : 1+(a/(1-g))^2-(y+2*a*(a/(1-g))+g*(a/(1-g))^2)=1-y-a^2/(1-g) := by
        field_simp
        ring
      linarith

end
end krylov.OneGradient
