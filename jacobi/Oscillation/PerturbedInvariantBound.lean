import jacobi.Oscillation.PhaseInvariantLipschitz

/-!
Article: jacobi, Proposition B.1.
The genuine corrected finite phase derivative differs from the true
Bessel invariant derivative by an explicitly integrable inverse-square
majorant plus a constant of order 1/N. This bound uses the proved actual
linear phase stability and literal bounded perturbation e,e'.
Use: controls the literal finite Jacobi perturbation terms uniformly in its true phase.
-/
namespace jacobi.Oscillation
noncomputable section
open Real Set
set_option backward.isDefEq.respectTransparency false

/-- The actual oscillatory factors in both corrected derivative remainders have absolute value at most one.
Use: controls the literal finite Jacobi perturbation terms uniformly in its true phase.
Article: jacobi, Proposition B.1.
Proof: each double-angle coordinate is unit bounded and the actual sine square lies in [0,1]. -/
theorem phase_products_bound (u : ℝ) :
    |cos (2*u)*sin u^2|≤1 ∧ |sin (2*u)*sin u^2|≤1 := by
  have hs : |sin u^2|≤1 := by
    rw [abs_of_nonneg (sq_nonneg _)]
    nlinarith [Real.sin_sq_add_cos_sq u,sq_nonneg (cos u)]
  constructor
  · rw [abs_mul]
    exact (mul_le_mul (Real.abs_cos_le_one _) hs (abs_nonneg _) (by norm_num)).trans_eq (one_mul _)
  · rw [abs_mul]
    exact (mul_le_mul (Real.abs_sin_le_one _) hs (abs_nonneg _) (by norm_num)).trans_eq (one_mul _)

/-- The exact finite corrected-phase derivative has a quantitative perturbation remainder relative to the genuine Bessel invariant.
Use: after actual linear phase control, its bound is integrable uniformly over the entire growing finite comparison interval.
Article: jacobi, Proposition B.1.
Proof: compare the two original Bessel derivative terms using their
proved fourth-order phase Lipschitz constant. Bound each of the four
literal finite perturbation terms by its original unit-bounded
trigonometric factors, and compare x^(-3)/2 with x^(-2) for x>=1. -/
theorem perturbedInvariantSlope_remainder (c : ℝ) (f g e e' : ℝ → ℝ) {x : ℝ} (hx : 1≤x) :
    |perturbedInvariantSlope c f e e' x-phaseInvariantSlope c g x|≤
      (4*c^2+2*|c|)*|f x-g x|/x^4+2*|c| *|e x|/x^2+(e x)^2/2+|e' x|/4 := by
  -- All oscillatory terms here occur in the already proved exact derivative identity for the original constructed phases.
  have hxp : 0<x := by linarith
  have hp := phase_products_bound (f x)
  let a := phaseInvariantSlope c f x-phaseInvariantSlope c g x
  let b := c*e x*cos (2*f x)*sin (f x)^2/x^2
  let d := c*e x*sin (2*f x)*sin (f x)^2/(2*x^3)
  let v := (e x)^2*cos (2*f x)*sin (f x)^2/2
  let w := e' x*sin (2*f x)/4
  have hb : |b|≤ |c| *|e x|/x^2 := by
    have he : b=(c*e x/x^2)*(cos (2*f x)*sin (f x)^2) := by dsimp [b]; ring
    rw [he,abs_mul,abs_div,abs_mul,abs_of_pos (by positivity : 0<x^2)]
    exact (mul_le_mul_of_nonneg_left hp.1 (by positivity)).trans_eq (mul_one _)
  have hd : |d|≤ |c| *|e x|/x^2 := by
    have he : d=(c*e x/(2*x^3))*(sin (2*f x)*sin (f x)^2) := by dsimp [d]; ring
    rw [he,abs_mul,abs_div,abs_mul,abs_of_pos (by positivity : 0<2*x^3)]
    have hh : |c| *|e x|/(2*x^3)≤ |c| *|e x|/x^2 :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) (by nlinarith [mul_le_mul_of_nonneg_left hx (show 0≤x^2 by positivity)])
    exact ((mul_le_mul_of_nonneg_left hp.2 (by positivity)).trans_eq (mul_one _)).trans hh
  have hv : |v|≤(e x)^2/2 := by
    have he : v=((e x)^2/2)*(cos (2*f x)*sin (f x)^2) := by dsimp [v]; ring
    rw [he,abs_mul,abs_of_nonneg (by positivity : 0≤(e x)^2/2)]
    exact (mul_le_mul_of_nonneg_left hp.1 (by positivity)).trans_eq (mul_one _)
  have hw : |w|≤ |e' x|/4 := by
    dsimp [w]
    rw [abs_div,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<4)]
    exact div_le_div_of_nonneg_right ((mul_le_mul_of_nonneg_left (Real.abs_sin_le_one _) (abs_nonneg _)).trans_eq (mul_one _)) (by norm_num)
  have ha := phaseInvariantSlope_lipschitz c f g hx
  have he : perturbedInvariantSlope c f e e' x-phaseInvariantSlope c g x=a+b+d+v+w := by
    dsimp [perturbedInvariantSlope,a,b,d,v,w]
    ring
  rw [he]
  have h1 := abs_add_le a b
  have h2 := abs_add_le (a+b) d
  have h3 := abs_add_le (a+b+d) v
  have h4 := abs_add_le (a+b+d+v) w
  dsimp [a] at h1 h2 h3 h4 ⊢
  rw [show 2*|c| * |e x|/x^2=|c| * |e x|/x^2+|c| * |e x|/x^2 by ring]
  linarith

end
end jacobi.Oscillation
