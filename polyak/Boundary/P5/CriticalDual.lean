import polyak.Boundary.P5.DualExpansion
import polyak.Boundary.P5.CriticalSolution
import polyak.Boundary.P5.Hermite

/-!
Article: Proposition p5h0dual, positivity of the actual critical dual.
Use: the displayed exact quadratic residual is extracted from the actual source,
whose two double contacts have been proved from the critical equations.
-/
noncomputable section
namespace polyak.Boundary.P5
open Polynomial Spectral

/-- Article: the central source is the generic dual with its six exact scalar parameters. -/
theorem dualClosed_generic (u G w₂ w₃ : ℝ) :
    dualClosed u G w₂ w₃=dualGeneric G u
      (G*(4*G^2-1)*(16*G^4-12*G^2+1))
      (w₂*((4*G^2-1)*(16*G^4-12*G^2+1)*(1/2)))
      (w₃*(G*(16*G^4-12*G^2+1))) ((1-w₂-w₃)*(G*(4*G^2-1))) := rfl

/-- Article: exact critical sextic coefficients before the double-root division. -/
theorem dualReal_critical_coefficients :
    (dualReal 0 criticalPoint).coeff 6=48*(1-w2₀-w3₀) ∧
    (dualReal 0 criticalPoint).coeff 5=0 ∧
    (dualReal 0 criticalPoint).coeff 4=96*w2₀+116*w3₀-96 := by
  rw [dualReal_closed]
  norm_num only [zero_mul,add_zero,criticalPoint_5,criticalPoint_6]
  rw [dualClosed_generic]
  rw [dualGeneric_coeff6,dualGeneric_coeff5,dualGeneric_coeff4]
  refine ⟨?_,?_,?_⟩ <;> norm_num [genericCoefficient6,genericCoefficient5,genericCoefficient4] <;> ring

/-- Article: the critical residual's coefficients are exactly the source algebraic qᵢ. -/
theorem critical_residual_coefficients :
    48*(1-w2₀-w3₀)=15*q2₀ ∧
    (2*y₀-1)*48*(1-w2₀-w3₀)=15*q1₀ ∧
    96*w2₀+116*w3₀-96+(3/4-2*y₀+3*y₀^2)*48*(1-w2₀-w3₀)=15*q0₀ := by
  refine ⟨?_,?_,?_⟩
  · norm_num [w2₀,w3₀,q2₀,w2Polynomial,w3Polynomial,q2Polynomial]
    ring
  · norm_num [w2₀,w3₀,q1₀,w2Polynomial,w3Polynomial,q1Polynomial]
    linear_combination (-124675200/43243231 : ℝ)*y₀_equation
  · norm_num [w2₀,w3₀,q0₀,w2Polynomial,w3Polynomial,q0Polynomial]
    linear_combination (-187012800*y₀/43243231-188910000/43243231)*y₀_equation

/-- Article: the three-cycle contact is an exact root of the actual critical dual. -/
theorem dualReal_critical_main_root : (dualReal 0 criticalPoint).eval (-1/2)=0 := by
  rw [dualReal_closed]
  norm_num [dualClosed]
  ring

/-- Article: Proposition p5h0dual, full exact critical double-square factorization. -/
theorem critical_dual_factor (c : ℝ) :
    (dualReal 0 criticalPoint).eval c=
      15*(c+1/2)^2*(c-y₀)^2*(q2₀*c^2+q1₀*c+q0₀) := by
  obtain ⟨hy,hdx,hdy⟩ := regularSystem_dual_exact 0 criticalPoint
  rw [regularSystem_criticalPoint] at hy hdx hdy
  norm_num at hy hdx hdy
  have hxy : (-1/2 : ℝ)≠y₀ := by linarith [y₀_bounds.1]
  have hdx' : (dualReal 0 criticalPoint).derivative.eval (-1/2)=0 := by
    convert hdx.symm using 2
    norm_num
  have hf := hermite_sextic_eval (dualReal_natDegree 0 criticalPoint) hxy
    dualReal_critical_main_root hdx' hy.symm hdy.symm c
  obtain ⟨h6,h5,h4⟩ := dualReal_critical_coefficients
  obtain ⟨hq2,hq1,hq0⟩ := critical_residual_coefficients
  rw [h6,h5,h4] at hf
  rw [hf]
  linear_combination (c+1/2)^2*(c-y₀)^2*(c^2*hq2+c*hq1+hq0)

/-- Article: a strict coefficient reserve makes a real quadratic positive on the whole interval. -/
theorem quadratic_pos_on_frequency {a b d : ℝ} (h : 0<d-|b|-|a|) (c : Frequency) :
    0<a*(c : ℝ)^2+b*c+d := by
  have hc : |(c : ℝ)|≤1 := abs_le.mpr c.property
  have hc2 : |(c : ℝ)^2|≤1 := by
    rw [abs_of_nonneg (sq_nonneg _)]
    exact (sq_le_one_iff_abs_le_one _).mpr hc
  have h1 : |b*(c : ℝ)|≤|b| := by
    rw [abs_mul]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hc (abs_nonneg b)
  have h2 : |a*(c : ℝ)^2|≤|a| := by
    rw [abs_mul]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hc2 (abs_nonneg a)
  linarith [neg_abs_le (b*(c : ℝ)),neg_abs_le (a*(c : ℝ)^2)]

/-- Article: the exact critical residual is strictly positive at every frequency. -/
theorem critical_dual_residual_pos (c : Frequency) : 0<q2₀*(c : ℝ)^2+q1₀*c+q0₀ :=
  quadratic_pos_on_frequency critical_dual_residual_gap c

/-- Article: Proposition p5h0dual, genuine critical dual nonnegativity on all frequencies. -/
theorem critical_dual_nonneg (c : Frequency) : 0≤(dualReal 0 criticalPoint).eval (c : ℝ) := by
  rw [critical_dual_factor]
  exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) (sq_nonneg _))
    (critical_dual_residual_pos c).le

/-- Article: the exact zero set consists precisely of the two critical contacts. -/
theorem critical_dual_zero_iff (c : Frequency) :
    (dualReal 0 criticalPoint).eval (c : ℝ)=0 ↔ (c : ℝ)= -1/2 ∨ (c : ℝ)=y₀ := by
  rw [critical_dual_factor,mul_eq_zero,or_iff_left (ne_of_gt (critical_dual_residual_pos c)),
    mul_eq_zero,mul_eq_zero,or_iff_right (by norm_num : (15 : ℝ)≠0),sq_eq_zero_iff,
    sq_eq_zero_iff,sub_eq_zero]
  constructor <;> intro hc
  · rcases hc with hc | hc
    · left; linarith
    · exact Or.inr hc
  · rcases hc with hc | hc
    · left; linarith
    · exact Or.inr hc

end polyak.Boundary.P5
