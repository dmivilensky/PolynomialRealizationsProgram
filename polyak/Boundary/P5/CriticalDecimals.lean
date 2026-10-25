import polyak.Boundary.P5.CriticalDecimalsRoot
import polyak.Certificates.P5Critical
import polyak.Numerics.KernelDecide

/-! Exact enclosures justifying every printed critical coefficient in Appendix B.
The article uses decimal prefixes for some entries and rounded values for others;
the rational intervals below state the precise meaning for each entry. -/
noncomputable section
namespace polyak.Boundary.P5
open Polynomial Numerics Certificates.P5 LeanCert.Core LeanCert.Engine

private theorem source_bounds {p : ℚ[X]} (P : PolynomialCode p) (lo hi : ℚ)
    (hl : QPoly.bernsteinCheck .strictLower P.code lo criticalFineInterval 0=true)
    (hu : QPoly.bernsteinCheck .strictUpper P.code hi criticalFineInterval 0=true) :
    (lo : ℝ)<Polynomial.aeval y₀ p ∧ Polynomial.aeval y₀ p<hi := by
  have hL:=QPoly.lt_aeval_of_bernsteinCheck hl y₀ y₀_fine_mem
  have hU:=QPoly.aeval_lt_of_bernsteinCheck hu y₀ y₀_fine_mem
  simpa only [P.exact] using And.intro hL hU

/-- The displayed y₀=0.2318891… is a certified decimal prefix. -/
theorem y₀_displayed_bounds : (2318891/10000000 : ℝ)<y₀ ∧ y₀<2318892/10000000 := by
  constructor <;> linarith [y₀_decimal_bounds.1,y₀_decimal_bounds.2]

/-- The displayed A₀=0.5146605… is a certified decimal prefix. -/
theorem A₀_displayed_bounds : (5146605/10000000 : ℝ)<A₀ ∧ A₀<5146606/10000000 := by
  have h:=source_bounds ACode (5146605/10000000) (5146606/10000000) (by kernel_decide) (by kernel_decide)
  norm_num at h ⊢
  exact h

/-- The displayed B₀=−0.2585419… is a certified signed decimal prefix. -/
theorem B₀_displayed_bounds : (-2585420/10000000 : ℝ)<B₀ ∧ B₀< -2585419/10000000 := by
  have h:=source_bounds BCode (-2585420/10000000) (-2585419/10000000) (by kernel_decide) (by kernel_decide)
  norm_num at h ⊢
  exact h

/-- The displayed D₀=2.1051110 is correctly rounded to seven decimal places. -/
theorem D₀_displayed_bounds : (42102219/20000000 : ℝ)<D₀ ∧ D₀<42102221/20000000 := by
  have h:=source_bounds DCode (42102219/20000000) (42102221/20000000) (by kernel_decide) (by kernel_decide)
  norm_num at h ⊢
  exact h

/-- The displayed P₀=2.5790145… is a certified decimal prefix. -/
theorem P₀_displayed_bounds : (25790145/10000000 : ℝ)<P₀ ∧ P₀<25790146/10000000 := by
  have h:=source_bounds PCode (25790145/10000000) (25790146/10000000) (by kernel_decide) (by kernel_decide)
  norm_num at h ⊢
  exact h

/-- The displayed w₂⁽⁰⁾=0.3743478… is a certified decimal prefix. -/
theorem w2₀_displayed_bounds : (3743478/10000000 : ℝ)<w2₀ ∧ w2₀<3743479/10000000 := by
  have h:=source_bounds w2Code (3743478/10000000) (3743479/10000000) (by kernel_decide) (by kernel_decide)
  norm_num at h ⊢
  exact h

/-- The displayed w₃⁽⁰⁾=0.5965020 is correctly rounded to seven decimal places. -/
theorem w3₀_displayed_bounds : (11930039/20000000 : ℝ)<w3₀ ∧ w3₀<11930041/20000000 := by
  have h:=source_bounds w3Code (11930039/20000000) (11930041/20000000) (by kernel_decide) (by kernel_decide)
  norm_num at h ⊢
  exact h

/-- The displayed w₅⁽⁰⁾=0.0291502 is correctly rounded to seven decimal places. -/
theorem w5₀_displayed_bounds : (583003/20000000 : ℝ)<w5₀ ∧ w5₀<583005/20000000 := by
  have h:=source_bounds w5Code (583003/20000000) (583005/20000000) (by kernel_decide) (by kernel_decide)
  norm_num at h ⊢
  exact h

/-- The displayed critical quadratic coefficient q₀=0.65052… is a decimal prefix. -/
theorem q0₀_displayed_bounds : (65052/100000 : ℝ)<q0₀ ∧ q0₀<65053/100000 := by
  have h:=source_bounds q0Code (65052/100000) (65053/100000) (by kernel_decide) (by kernel_decide)
  norm_num at h ⊢
  exact h

/-- The displayed critical quadratic coefficient q₁=−0.05001… is a signed decimal prefix. -/
theorem q1₀_displayed_bounds : (-5002/100000 : ℝ)<q1₀ ∧ q1₀< -5001/100000 := by
  have h:=source_bounds q1Code (-5002/100000) (-5001/100000) (by kernel_decide) (by kernel_decide)
  norm_num at h ⊢
  exact h

/-- The displayed critical quadratic coefficient q₂=0.09328… is a decimal prefix. -/
theorem q2₀_displayed_bounds : (9328/100000 : ℝ)<q2₀ ∧ q2₀<9329/100000 := by
  have h:=source_bounds q2Code (9328/100000) (9329/100000) (by kernel_decide) (by kernel_decide)
  norm_num at h ⊢
  exact h

end polyak.Boundary.P5
