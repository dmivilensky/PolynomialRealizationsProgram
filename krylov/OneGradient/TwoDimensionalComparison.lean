import krylov.OneGradient.TwoDimensionalAttainment
set_option autoImplicit false
/-!
Article: main_krylov, thm:local(c), strict two-dimensional RFC comparison.
Use: the exact known-base scalar value is strictly smaller than the true
RFC constant on both original branches, including their shared boundary.
Source: explicit admissible RFC test directions and the existing genuine
RFC variational maximum; no numerical comparison or endpoint approximation.
-/

namespace krylov.OneGradient
noncomputable section
open krylov.Correction

/-- The exact original two-dimensional known-base value is strictly
smaller than the genuine RFC sharp constant for every positive total
budget and nonnegative output budget, on both original branches.
Use: closes the scalar strict comparison in the original known-base
minimax theorem, with the actual RFC variational value.
Article: main_krylov, thm:local(c), V_2< K(W,w').
Proof: in the first branch the actual cubic maximizer has a strict gap
between its complementary square and positive complementary root. In
the second branch the exact planar maximizer r=w/q has r>one half;
the same admissible RFC test gains W²s(r-one half)>0. -/
theorem twoDimensionalValue_lt_rfc (W w : ℝ) (hW : 0< W) (hw : 0≤ w) :
    twoDimensionalValue W w< sharpConstant W w := by
  by_cases hb : w≤ W/2
  · let r := Real.sqrt ((W+w)/(3*W))
    have hr : 0< r := Real.sqrt_pos.mpr (by positivity)
    have hr2 : r^2=(W+w)/(3*W) := Real.sq_sqrt (by positivity)
    have hstation : 3*W*r^2=W+w := by rw [hr2];field_simp
    have hrHalf : r^2≤1/2 := by nlinarith
    have hr1 : r<1 := by nlinarith
    let s := Real.sqrt (1-r^2)
    have hs : 0< s := Real.sqrt_pos.mpr (by nlinarith)
    have hs2 : s^2=1-r^2 := Real.sq_sqrt (by nlinarith)
    have hs1 : s<1 := by nlinarith [sq_pos_of_pos hr]
    have hgap : 0< s-(1-r^2) := by nlinarith
    have hstrict := mul_pos (mul_pos (sq_pos_of_pos hW) hr) hgap
    have hvalue : twoDimensionalValue W w=W^2*r*(1-r^2)+w*W*r := by
      rw [twoDimensionalValue,ite_eq_left hb]
      change (2/3)*W*(W+w)*r=W^2*r*(1-r^2)+w*W*r
      nlinarith [congrArg (fun x : ℝ => W*r*x) hstation]
    have hbound := (sharpConstant_variational hW.le hw).2.2 r ⟨hr.le,hr1.le⟩
    change W*r*(W*s+w)≤ sharpConstant W w at hbound
    rw [hvalue]
    nlinarith
  · let q := Real.sqrt (w^2+W^2/4)
    have hq : 0< q := Real.sqrt_pos.mpr (by positivity)
    have hq2 : q^2=w^2+W^2/4 := Real.sq_sqrt (by positivity)
    have hwp : 0< w := by linarith
    let r := w/q
    let s := W/(2*q)
    have hr : 0< r := div_pos hwp hq
    have hs : 0< s := div_pos hW (by positivity)
    have hcircle : r^2+s^2=1 := by dsimp only [r,s];field_simp;nlinarith
    have hr1 : r≤1 := by nlinarith [sq_nonneg s]
    have hcomp : Real.sqrt (1-r^2)=s := by rw [show 1-r^2=s^2 by linarith];exact Real.sqrt_sq hs.le
    have hrhalf : 1/2< r := by
      change 1/2< w/q
      apply (lt_div_iff₀ hq).mpr
      nlinarith
    have hvalue : twoDimensionalValue W w=W^2/2*s+w*W*r := by
      rw [twoDimensionalValue,ite_eq_right hb]
      change W*q=W^2/2*(W/(2*q))+w*W*(w/q)
      field_simp
      nlinarith
    have hbound := (sharpConstant_variational hW.le hw).2.2 r ⟨hr.le,hr1⟩
    rw [hcomp] at hbound
    have hstrict := mul_pos (mul_pos (sq_pos_of_pos hW) hs) (sub_pos.mpr hrhalf)
    rw [hvalue]
    nlinarith

end
end krylov.OneGradient
