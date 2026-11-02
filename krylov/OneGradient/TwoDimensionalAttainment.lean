import krylov.OneGradient.TwoDimensionalRadialMax
import krylov.Correction.ConstantBounds
set_option autoImplicit false
/-!
Article: main_krylov, thm:local(c), exact attained hidden-entry scalar value.
Use: identify the genuine closed-disc maximum and its strict comparison
with the RFC constant before the physical arbitrary-method minimax proof.
Source: explicit admissible stationary points, genuine radial bounds and
the existing attained RFC variational constant.
-/

namespace krylov.OneGradient
noncomputable section
open krylov.Correction

/-- The full original hidden-entry coefficient attains the exact two-branch
value on the actual closed spectral disc, at an interior cross coordinate.
Use: the complete scalar maximum is a genuine attained value, including
the shared budget threshold; the cross coordinate is nonzero.
Article: main_krylov, thm:local(c), attaining two-dimensional coefficient.
Proof: below the threshold use g=0 and the true cubic stationary radius.
Above it choose a=W/(2q), r=w/q and g=sqrt(r²-a²), q²=w²+W²/4.
Then the true hidden half-width is exactly one half and both the planar
support inequality and the original scalar value are equalities. -/
theorem twoDimensional_hidden_attained (W w : ℝ) (hW : 0< W) (hw : 0≤ w) :
    ∃ a g : ℝ,0< a ∧ 0≤ g ∧ a^2+g^2≤1 ∧
      twoDimensionalHiddenValue W w a g=twoDimensionalValue W w := by
  by_cases hbudget : w≤ W/2
  · let a := Real.sqrt ((W+w)/(3*W))
    have ha : 0< a := Real.sqrt_pos.mpr (by positivity)
    have ha2 : a^2=(W+w)/(3*W) := Real.sq_sqrt (by positivity)
    have hstation : 3*W*a^2=W+w := by rw [ha2];field_simp
    have haHalf : a^2≤1/2 := by nlinarith
    refine ⟨a,0,ha,le_refl 0,by nlinarith,?_⟩
    rw [twoDimensionalHiddenValue,twoDimensionalValue,ite_eq_left hbudget]
    simp only [zero_pow (by decide : 2≠0),sub_zero,div_one,add_zero,Real.sqrt_sq ha.le]
    change W^2*a*(1-a^2)+w*W*a=(2/3)*W*(W+w)*a
    nlinarith [congrArg (fun x : ℝ => W*a*x) hstation]
  · let q := Real.sqrt (w^2+W^2/4)
    have hq : 0< q := Real.sqrt_pos.mpr (by positivity)
    have hq2 : q^2=w^2+W^2/4 := Real.sq_sqrt (by positivity)
    let a := W/(2*q)
    let r := w/q
    have ha : 0< a := div_pos hW (by positivity)
    have hr : 0≤ r := div_nonneg hw hq.le
    have hcircle : a^2+r^2=1 := by
      dsimp only [a,r]
      field_simp
      nlinarith
    have hgap : 0≤ r^2-a^2 := by
      dsimp only [a,r]
      have hnum : 0≤ w^2-W^2/4 := by nlinarith
      have he : (w/q)^2-(W/(2*q))^2=(w^2-W^2/4)/q^2 := by ring
      rw [he]
      exact div_nonneg hnum (sq_nonneg q)
    let g := Real.sqrt (r^2-a^2)
    have hg : 0≤ g := Real.sqrt_nonneg _
    have hg2 : g^2=r^2-a^2 := Real.sq_sqrt hgap
    have hdisc : a^2+g^2≤1 := by nlinarith [sq_nonneg a]
    have hd : 1-g^2=2*a^2 := by nlinarith
    have hrad : Real.sqrt (a^2+g^2)=r := by rw [hg2,add_sub_cancel];exact Real.sqrt_sq hr
    have hfrac : a^2/(1-g^2)=1/2 := by rw [hd];field_simp
    refine ⟨a,g,ha,hg,hdisc,?_⟩
    rw [twoDimensionalHiddenValue,hfrac,hrad,twoDimensionalValue,ite_eq_right hbudget]
    change W^2*a*(1-1/2)+w*W*r=W*q
    dsimp only [a,r]
    field_simp
    nlinarith

/-- The original genuine closed-disc hidden-entry maximum is exactly the
two-branch value; the full scalar upper bound and a real attaining point
hold for all positive total budgets and nonnegative output budgets.
Use: no abstract radius or postulated scalar maximization remains in the
two-dimensional known-base coefficient.
Article: main_krylov, thm:local(c), exact scalar V_2.
Proof: the proved closed-disc radial reduction followed by the genuine
global two-branch bound gives the upper estimate; use the explicit point. -/
theorem twoDimensional_hidden_maximum (W w : ℝ) (hW : 0< W) (hw : 0≤ w) :
    (∀ a g : ℝ,0≤ a → 0≤ g → a^2+g^2≤1 →
      twoDimensionalHiddenValue W w a g≤ twoDimensionalValue W w) ∧
    ∃ a g : ℝ,0< a ∧ 0≤ g ∧ a^2+g^2≤1 ∧
      twoDimensionalHiddenValue W w a g=twoDimensionalValue W w := by
  refine ⟨?_,twoDimensional_hidden_attained W w hW hw⟩
  intro a g ha hg hd
  exact (twoDimensional_hidden_radial_bound W w a g ha hg hd).trans
    (twoDimensional_radial_bound W w (Real.sqrt (a^2+g^2)) hW hw (Real.sqrt_nonneg _)
      ((Real.sqrt_le_one).mpr hd))

end
end krylov.OneGradient
