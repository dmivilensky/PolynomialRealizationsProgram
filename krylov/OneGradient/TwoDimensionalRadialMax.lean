import krylov.OneGradient.TwoDimensionalEnvelope
set_option autoImplicit false
/-!
Article: main_krylov, thm:local(c), exact two-dimensional radial maximum.
Use: compute the two original known-base minimax branches by algebraic
global bounds, retaining the branch boundary and all endpoint radii.
Source: a nonnegative cubic gap, planar Cauchy--Schwarz and exact boundary
comparisons; no differentiation of a singular endpoint is required.
-/

namespace krylov.OneGradient
noncomputable section

/-- The original two-branch known-base value, with its small-budget term
written as its exact stationary-radius expression.
Use: exact algebraic maximization precedes physical minimax realization.
Article: main_krylov, thm:local(c), V_2. -/
def twoDimensionalValue (W w : ℝ) : ℝ :=
  if w≤ W/2 then (2/3)*W*(W+w)*Real.sqrt ((W+w)/(3*W))
  else W*Real.sqrt (w^2+W^2/4)

/-- The original small-radius cubic has its exact global stationary bound.
Use: prove the first minimax branch by a genuine nonnegative gap.
Article: main_krylov, thm:local(c), cubic branch.
Proof: the actual objective gap is W²(r-a)²(r+2a) at 3Wa²=W+w. -/
theorem twoDimensional_cubic_bound (W w a r : ℝ) (ha : 0≤ a) (hr : 0≤ r)
    (hstation : 3*W*a^2=W+w) :
    W^2*r*(1-r^2)+w*W*r≤(2/3)*W*(W+w)*a := by
  have he : (2/3)*W*(W+w)*a-(W^2*r*(1-r^2)+w*W*r)=W^2*(r-a)^2*(r+2*a) := by
    linear_combination (W*r-(2/3)*W*a)*hstation
  have hp := mul_nonneg (mul_nonneg (sq_nonneg W) (sq_nonneg (r-a))) (by linarith : 0≤ r+2*a)
  linarith

/-- The original large-radius expression has its exact planar support bound.
Use: derive the second minimax branch and its shared boundary comparison.
Article: main_krylov, thm:local(c), large-radius branch.
Proof: the two planar squared pairings sum to the squared budget radius;
the actual nonnegative pairing is therefore bounded by its positive root. -/
theorem twoDimensional_circle_bound (W w r s : ℝ) (hW : 0≤ W) (hcircle : r^2+s^2=1) :
    W^2/2*s+w*W*r≤ W*Real.sqrt (w^2+W^2/4) := by
  have he : (W/2*s+w*r)^2+(w*s-W/2*r)^2=(w^2+W^2/4)*(r^2+s^2) := by ring
  rw [hcircle,mul_one] at he
  have hsq := Real.sq_sqrt (by positivity : 0≤ w^2+W^2/4)
  have hdot : W/2*s+w*r≤ Real.sqrt (w^2+W^2/4) := by
    nlinarith [sq_nonneg (w*s-W/2*r),Real.sqrt_nonneg (w^2+W^2/4)]
  nlinarith [mul_le_mul_of_nonneg_left hdot hW]

/-- The genuine closed-interval radial objective is bounded by the exact
original two-branch value for all nonnegative budgets and positive W.
Use: the full two-dimensional hidden-entry coefficient has the printed
global scalar upper bound, including the shared branch threshold.
Article: main_krylov, thm:local(c), exact radial optimization.
Proof: the cubic stationary gap gives its global bound. The other branch
has the exact planar support bound. When the corresponding stationary
radius is outside its interval, factor the boundary gap or use r+s≤ sqrt2;
both branches then meet at the same true half-radius boundary. -/
theorem twoDimensional_radial_bound (W w r : ℝ) (hW : 0< W) (hw : 0≤ w)
    (hr : 0≤ r) (hr1 : r≤1) : twoDimensionalRadialValue W w r≤ twoDimensionalValue W w := by
  let b := Real.sqrt (1/2 : ℝ)
  have hb : 0≤ b := Real.sqrt_nonneg _
  have hb2 : b^2=(1/2 : ℝ) := Real.sq_sqrt (by norm_num)
  let s := Real.sqrt (1-r^2)
  have hs : 0≤ s := Real.sqrt_nonneg _
  have hs2 : s^2=1-r^2 := Real.sq_sqrt (by nlinarith)
  have hcircle : r^2+s^2=1 := by linarith
  unfold twoDimensionalRadialValue twoDimensionalValue
  split_ifs with hhalf hbudget hbudget
  · let a := Real.sqrt ((W+w)/(3*W))
    have ha : 0≤ a := Real.sqrt_nonneg _
    have ha2 : a^2=(W+w)/(3*W) := Real.sq_sqrt (by positivity)
    have hstation : 3*W*a^2=W+w := by rw [ha2];field_simp
    exact twoDimensional_cubic_bound W w a r ha hr hstation
  · have hbr : r≤ b := by nlinarith
    have hprod := mul_nonneg hb (sub_nonneg.mpr hbr)
    have hsum : b^2+b*r+r^2≤3/2 := by nlinarith
    have hfactor : 0≤ W+w-W*(b^2+b*r+r^2) := by
      nlinarith [mul_le_mul_of_nonneg_left hsum hW.le]
    have hgap := mul_nonneg (mul_nonneg hW.le (sub_nonneg.mpr hbr)) hfactor
    have he : (W^2*b*(1-b^2)+w*W*b)-(W^2*r*(1-r^2)+w*W*r)=
        W*(b-r)*(W+w-W*(b^2+b*r+r^2)) := by ring
    have hbound := twoDimensional_circle_bound W w b b hW.le (by linarith)
    rw [hb2] at he hgap
    nlinarith
  · have hbr : b≤ r := by nlinarith
    have hrs : r+s≤2*b := by nlinarith [sq_nonneg (r-s)]
    have hcoeff : 0≤ W^2/2-w*W := by nlinarith
    have hmono := mul_nonneg hcoeff (sub_nonneg.mpr hbr)
    have hsum := mul_le_mul_of_nonneg_left hrs (by positivity : 0≤ W^2/2)
    have hbound : W^2/2*s+w*W*r≤ W^2*b*(1-b^2)+w*W*b := by rw [hb2];nlinarith
    let a := Real.sqrt ((W+w)/(3*W))
    have ha : 0≤ a := Real.sqrt_nonneg _
    have ha2 : a^2=(W+w)/(3*W) := Real.sq_sqrt (by positivity)
    have hstation : 3*W*a^2=W+w := by rw [ha2];field_simp
    exact hbound.trans (twoDimensional_cubic_bound W w a b ha hb hstation)
  · exact twoDimensional_circle_bound W w r s hW.le hcircle

end
end krylov.OneGradient
