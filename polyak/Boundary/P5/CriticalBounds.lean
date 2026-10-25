import polyak.Certificates.P5Critical

/-!
Article: Appendix B, strict signs of the critical P₅ data in ℚ(y₀).
Use: exact Bernstein checks on the rational root interval give uniform signs;
all conclusions refer to the independently defined source polynomials.
-/
noncomputable section
namespace polyak.Boundary.P5
open Polynomial Numerics Certificates.P5 LeanCert.Core LeanCert.Engine

private theorem source_lower {p : ℚ[X]} (P : PolynomialCode p) (a : ℚ)
    (hc : QPoly.bernsteinCheck .strictLower P.code a criticalInterval 0 = true) :
    (a : ℝ) < Polynomial.aeval y₀ p := by
  have h := QPoly.lt_aeval_of_bernsteinCheck hc y₀ criticalRoot.mem
  simpa only [P.exact] using h

private theorem source_upper {p : ℚ[X]} (P : PolynomialCode p) (a : ℚ)
    (hc : QPoly.bernsteinCheck .strictUpper P.code a criticalInterval 0 = true) :
    Polynomial.aeval y₀ p < (a : ℝ) := by
  have h := QPoly.aeval_lt_of_bernsteinCheck hc y₀ criticalRoot.mem
  simpa only [P.exact] using h

/-- Article: strict exact bounds for the critical A coefficient. -/
theorem A₀_bounds : (0 : ℝ) < A₀ ∧ A₀ < 55/100 := by
  have hl := source_lower ACode (0) (by decide +kernel)
  have hu := source_upper ACode (55/100) (by decide +kernel)
  norm_num at hl hu ⊢
  exact ⟨hl,hu⟩

/-- Article: strict exact bounds for the critical B coefficient. -/
theorem B₀_bounds : (-27/100 : ℝ) < B₀ ∧ B₀ < 0 := by
  have hl := source_lower BCode (-27/100) (by decide +kernel)
  have hu := source_upper BCode (0) (by decide +kernel)
  norm_num at hl hu ⊢
  exact ⟨hl,hu⟩

/-- Article: strict exact bounds for the critical D coefficient. -/
theorem D₀_bounds : (0 : ℝ) < D₀ ∧ D₀ < 22/10 := by
  have hl := source_lower DCode (0) (by decide +kernel)
  have hu := source_upper DCode (22/10) (by decide +kernel)
  norm_num at hl hu ⊢
  exact ⟨hl,hu⟩

/-- Article: strict exact bounds for the critical P coefficient. -/
theorem P₀_bounds : (0 : ℝ) < P₀ ∧ P₀ < 258/100 := by
  have hl := source_lower PCode (0) (by decide +kernel)
  have hu := source_upper PCode (258/100) (by decide +kernel)
  norm_num at hl hu ⊢
  exact ⟨hl,hu⟩

/-- Article: strict exact bounds for the critical w2 coefficient. -/
theorem w2₀_bounds : (0 : ℝ) < w2₀ ∧ w2₀ < 1 := by
  have hl := source_lower w2Code (0) (by decide +kernel)
  have hu := source_upper w2Code (1) (by decide +kernel)
  norm_num at hl hu ⊢
  exact ⟨hl,hu⟩

/-- Article: strict exact bounds for the critical w3 coefficient. -/
theorem w3₀_bounds : (0 : ℝ) < w3₀ ∧ w3₀ < 1 := by
  have hl := source_lower w3Code (0) (by decide +kernel)
  have hu := source_upper w3Code (1) (by decide +kernel)
  norm_num at hl hu ⊢
  exact ⟨hl,hu⟩

/-- Article: strict exact bounds for the critical w5 coefficient. -/
theorem w5₀_bounds : (0 : ℝ) < w5₀ ∧ w5₀ < 1 := by
  have hl := source_lower w5Code (0) (by decide +kernel)
  have hu := source_upper w5Code (1) (by decide +kernel)
  norm_num at hl hu ⊢
  exact ⟨hl,hu⟩

/-- Article: strict exact bounds for the critical q0 coefficient. -/
theorem q0₀_bounds : (3/5 : ℝ) < q0₀ ∧ q0₀ < 7/10 := by
  have hl := source_lower q0Code (3/5) (by decide +kernel)
  have hu := source_upper q0Code (7/10) (by decide +kernel)
  norm_num at hl hu ⊢
  exact ⟨hl,hu⟩

/-- Article: strict exact bounds for the critical q1 coefficient. -/
theorem q1₀_bounds : (-1/10 : ℝ) < q1₀ ∧ q1₀ < 0 := by
  have hl := source_lower q1Code (-1/10) (by decide +kernel)
  have hu := source_upper q1Code (0) (by decide +kernel)
  norm_num at hl hu ⊢
  exact ⟨hl,hu⟩

/-- Article: strict exact bounds for the critical q2 coefficient. -/
theorem q2₀_bounds : (0 : ℝ) < q2₀ ∧ q2₀ < 1/10 := by
  have hl := source_lower q2Code (0) (by decide +kernel)
  have hu := source_upper q2Code (1/10) (by decide +kernel)
  norm_num at hl hu ⊢
  exact ⟨hl,hu⟩

/-- Article: strict exact bounds for the critical dualDet coefficient. -/
theorem dualDet₀_bounds : (-4000 : ℝ) < dualDet₀ ∧ dualDet₀ < -3000 := by
  have hl := source_lower dualDetCode (-4000) (by decide +kernel)
  have hu := source_upper dualDetCode (-3000) (by decide +kernel)
  norm_num at hl hu ⊢
  exact ⟨hl,hu⟩

/-- Article: strict exact bounds for the critical primalDet coefficient. -/
theorem primalDet₀_bounds : (-7000 : ℝ) < primalDet₀ ∧ primalDet₀ < -5000 := by
  have hl := source_lower primalDetCode (-7000) (by decide +kernel)
  have hu := source_upper primalDetCode (-5000) (by decide +kernel)
  norm_num at hl hu ⊢
  exact ⟨hl,hu⟩

/-- Article: finer exact bounds used in the all-lag and local-limit estimates. -/
theorem A₀_fine_bounds : (514/1000 : ℝ) < A₀ ∧ A₀ < 515/1000 := by
  have hl := source_lower ACode (514/1000) (by decide +kernel)
  have hu := source_upper ACode (515/1000) (by decide +kernel)
  norm_num at hl hu ⊢
  exact ⟨hl,hu⟩

/-- Article: finer exact bounds used in the all-lag and local-limit estimates. -/
theorem B₀_fine_bounds : (-259/1000 : ℝ) < B₀ ∧ B₀ < -258/1000 := by
  have hl := source_lower BCode (-259/1000) (by decide +kernel)
  have hu := source_upper BCode (-258/1000) (by decide +kernel)
  norm_num at hl hu ⊢
  exact ⟨hl,hu⟩

/-- Article: finer exact bounds used in the all-lag and local-limit estimates. -/
theorem D₀_fine_bounds : (2105/1000 : ℝ) < D₀ ∧ D₀ < 2106/1000 := by
  have hl := source_lower DCode (2105/1000) (by decide +kernel)
  have hu := source_upper DCode (2106/1000) (by decide +kernel)
  norm_num at hl hu ⊢
  exact ⟨hl,hu⟩

/-- Article: both exact critical Jacobian block determinants are nonzero. -/
theorem critical_block_determinants_ne_zero : dualDet₀ ≠ 0 ∧ primalDet₀ ≠ 0 := by
  have hd := dualDet₀_bounds.2
  have hp := primalDet₀_bounds.2
  constructor <;> linarith

/-- Article: a positive uniform residual gap for the critical quadratic dual quotient. -/
theorem critical_dual_residual_gap : 0 < q0₀ - |q1₀| - |q2₀| := by
  rw [abs_of_neg q1₀_bounds.2,abs_of_pos q2₀_bounds.1]
  linarith [q0₀_bounds.1,q1₀_bounds.1,q2₀_bounds.2]

/-- Article: the two source constants controlling all first-order lags. -/
theorem critical_first_order_constants :
    |B₀|+D₀ < (237/100 : ℝ) ∧ |B₀-3*A₀| < (181/100 : ℝ) ∧ P₀ < (258/100 : ℝ) := by
  rw [abs_of_neg B₀_bounds.2,abs_of_neg (by linarith [B₀_bounds.2,A₀_bounds.1] : B₀-3*A₀<0)]
  exact ⟨by linarith [B₀_fine_bounds.1,D₀_fine_bounds.2],
    by linarith [B₀_fine_bounds.1,A₀_fine_bounds.2],P₀_bounds.2⟩

/-- Article: strict phase and amplitude limits needed for uniform central-family tail bounds. -/
theorem critical_local_limits :
    |B₀-A₀| < 1 ∧ 4*B₀^2 < (1/3 : ℝ) ∧ (3*A₀+B₀)^2 < 12 := by
  have hA := A₀_fine_bounds
  have hB := B₀_fine_bounds
  have hBA : B₀-A₀ < 0 := by linarith
  rw [abs_of_neg hBA]
  refine ⟨by linarith,?_,?_⟩
  · have hsq := mul_pos (by linarith : 0 < B₀+(259/1000 : ℝ))
      (by linarith : 0 < (259/1000 : ℝ)-B₀)
    nlinarith
  · have hsq := mul_pos (by linarith : 0 < 3*A₀+B₀+2)
      (by linarith : 0 < 2-(3*A₀+B₀))
    nlinarith

end polyak.Boundary.P5
