import polyak.Boundary.SpiralArc
import polyak.Boundary.Tail

/-!
Article: the exact spiral branch and its derivative in the exponent coordinate.
Use: branch derivatives are quantitative before joining adjacent analytic regimes.
-/

namespace polyak.Boundary
noncomputable section

/-- Article: the spiral twist boundary as an explicit function of t. -/
def spiralBoundary (t : ℝ) : ℝ := Real.arsinh (1-1/(2*Real.cosh t))

/-- Article: exact derivative of the explicit spiral boundary. -/
def spiralBoundaryDerivative (t : ℝ) : ℝ :=
  Real.sinh t/(2*Real.cosh t^2*Real.sqrt (1+(1-1/(2*Real.cosh t))^2))

/-- Article: actual differentiability of the explicit spiral branch. -/
theorem hasDerivAt_spiralBoundary (t : ℝ) :
    HasDerivAt spiralBoundary (spiralBoundaryDerivative t) t := by
  have hc := Real.cosh_pos t
  have hs : 0 < Real.sqrt (1+(1-1/(2*Real.cosh t))^2) := Real.sqrt_pos.mpr (by positivity)
  have hd := ((hasDerivAt_const t (1 : ℝ)).sub
    ((hasDerivAt_const t (1 : ℝ)).div ((Real.hasDerivAt_cosh t).const_mul 2)
      (show 2*Real.cosh t≠0 by positivity))).arsinh
  dsimp only [Pi.sub_apply,Pi.div_apply] at hd
  convert hd using 1
  · rfl
  · simp only [spiralBoundaryDerivative,smul_eq_mul]
    field_simp
    ring

/-- Article: the spiral branch has absolute derivative strictly below one. -/
theorem abs_spiralBoundaryDerivative_lt_one (t : ℝ) : |spiralBoundaryDerivative t|<1 := by
  have hc := Real.one_le_cosh t
  have hcp := Real.cosh_pos t
  have hs : 1 ≤ Real.sqrt (1+(1-1/(2*Real.cosh t))^2) := by
    have h : Real.sqrt (1 : ℝ)=1 := Real.sqrt_one
    rw [←h]
    exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg (1-1/(2*Real.cosh t))])
  have hd : 0 < 2*Real.cosh t^2*Real.sqrt (1+(1-1/(2*Real.cosh t))^2) := by positivity
  have hmul := mul_le_mul_of_nonneg_left hs (show 0 ≤ 2*Real.cosh t^2 by positivity)
  have hcoshsq : Real.cosh t ≤ Real.cosh t^2 := by nlinarith
  have ha := abs_sinh_le_cosh t
  unfold spiralBoundaryDerivative
  rw [abs_div,abs_of_pos hd]
  apply (div_lt_one hd).mpr
  nlinarith

end
end polyak.Boundary
