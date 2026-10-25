import polyak.Boundary.P2.Physical
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv

/-! Article: Theorem p2arc(vii), differential bounds in exact rational coordinates. -/
namespace polyak.Boundary.P2
noncomputable section
open Spectral Filter
open scoped Topology

/-- Article: the physical parameter map has a strict, nonzero derivative. -/
theorem hasStrictDerivAt_G {z : ℝ} (hz : z∈parameterInterval) :
    HasStrictDerivAt G (GDerivative z) z := by
  have h0 := (parameter_pos hz).ne'
  have hr := (rMinus_pos hz).ne'
  have hd := (((hasStrictDerivAt_id z).pow 4).add_const 4).div
    (((hasStrictDerivAt_id z).const_mul 8).mul (((hasStrictDerivAt_id z).pow 2).sub_const 2))
      (show 8*z*(z^2-2)≠0 by exact mul_ne_zero (mul_ne_zero (by norm_num) h0) hr)
  convert hd using 1
  · rfl
  · dsimp [GDerivative,rPlus,eMinus,ePlus,rMinus]
    norm_num
    field_simp
    ring

/-- Article: exponent coordinates belonging to the closed rational P₂ arc. -/
def exponentArc : Set ℝ := {t | Ga ≤ Real.cosh t ∧ Real.cosh t ≤ Boundary.G1}

/-- Article: the exact derivative dV/dt expressed in the rational parameter. -/
def boundaryDerivative (z t : ℝ) : ℝ := slope z*Real.sinh t/Real.sqrt (1+u z^2)

/-- Article: every closed-arc parameter is strictly inside the common sign interval. -/
theorem arc_mem_interior {z : ℝ} (hz : z∈Set.Icc zeta1 zetaA) :
    z∈Set.Ioo (3391/2000) (1699/1000) := by
  constructor <;> linarith [hz.1,hz.2,zeta1_bounds.1,zetaA_bounds.2]

/-- Article: the absolute derivative is strictly below one on both exponent copies. -/
theorem abs_boundaryDerivative_lt_one {z t : ℝ} (hz : z∈parameterInterval)
    (ht : Real.cosh t=G z) : |boundaryDerivative z t|<1 := by
  have hsl:=slope_bounds hz
  have hg:=G_upper_positive z hz
  have hs : |Real.sinh t|<1 := by
    have he:=Real.sinh_sq t
    rw [ht] at he
    have hp:=one_lt_G hz
    nlinarith [sq_abs (Real.sinh t),sq_nonneg (G z-1),abs_nonneg (Real.sinh t)]
  have hroot : 1 ≤ Real.sqrt (1+u z^2) := by
    calc
      (1 : ℝ)=Real.sqrt 1 := Real.sqrt_one.symm
      _ ≤ Real.sqrt (1+u z^2) := Real.sqrt_le_sqrt (by nlinarith [sq_nonneg (u z)])
  have hr : 0<Real.sqrt (1+u z^2) := by linarith
  unfold boundaryDerivative
  rw [abs_div,abs_mul,abs_of_pos hsl.1,abs_of_pos hr]
  apply (div_lt_one hr).mpr
  have hm:=mul_lt_mul_of_pos_left hs hsl.1
  nlinarith


end
end polyak.Boundary.P2
