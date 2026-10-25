import polyak.Levels.Chart.Coefficients
import Mathlib.Algebra.Polynomial.Eval.Defs

/-! The source Laurent expression and its genuine quartic polynomial. -/
noncomputable section
namespace polyak.Levels.Chart
open General Polynomial

def Coefficients.evalComplex (C : Coefficients) (z : ℂ) : ℂ :=
  (C.c0:ℂ)+(C.c1:ℂ)*z+(C.c2:ℂ)*z^2

def E (C : Coefficients) (z : ℂ) : ℂ :=
  C.evalComplex ((z+z⁻¹)/2)-(z-z⁻¹)/2

def quartic (C : Coefficients) : Polynomial ℂ :=
  Polynomial.C ((C.c2:ℂ)/4)*X^4+
    Polynomial.C (((C.c1:ℂ)-1)/2)*X^3+
    Polynomial.C ((C.c0:ℂ)+(C.c2:ℂ)/2)*X^2+
    Polynomial.C (((C.c1:ℂ)+1)/2)*X+Polynomial.C ((C.c2:ℂ)/4)

theorem quartic_eval (C : Coefficients) {z : ℂ} (hz : z≠0) :
    (quartic C).eval z=z^2*E C z := by
  simp only [quartic,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,
    Polynomial.eval_pow,Polynomial.eval_X,E,Coefficients.evalComplex]
  field_simp
  ring

theorem quartic_at_zero (C : Coefficients) : (quartic C).eval 0=(C.c2:ℂ)/4 := by
  simp [quartic]

/-- Appendix E, Lemma Efactor, for the actual characteristic polynomials. -/
theorem E_factor (q : Tuning) {z : ℂ} (hz : z≠0) :
    (2*q.B*(1-q.beta):ℝ)*E (coefficients q) z= -q.a z*q.b z⁻¹ := by
  have hB : (q.B:ℂ)≠0 := by exact_mod_cast q.B_ne_zero
  have hβ : (1-q.beta:ℂ)≠0 := by exact_mod_cast ne_of_gt (sub_pos.mpr q.beta_lt_one)
  have hxy : (q.y:ℂ)-(q.x:ℂ)≠0 := by exact_mod_cast ne_of_gt (sub_pos.mpr q.x_lt_y)
  dsimp [E,Coefficients.evalComplex,coefficients,Tuning.a,Tuning.b,Tuning.A,Tuning.B]
  push_cast
  field_simp [hxy]
  ring

theorem quartic_factor (q : Tuning) {z : ℂ} (hz : z≠0) :
    (2*q.B*(1-q.beta):ℝ)*(quartic (coefficients q)).eval z=
      -q.a z*(q.beta*z^2-(1+q.beta-q.y:ℝ)*z+1) := by
  rw [quartic_eval _ hz]
  have he := E_factor q hz
  have hreverse : z^2*q.b z⁻¹=q.beta*z^2-(1+q.beta-q.y:ℝ)*z+1 := by
    unfold Tuning.b
    push_cast
    field_simp
    ring
  calc
    _=z^2*(-q.a z*q.b z⁻¹) := by rw [← he]; ring
    _= -q.a z*(z^2*q.b z⁻¹) := by ring
    _=_ := by rw [hreverse]

theorem E_wave (C : Coefficients) (ω : ℝ) :
    E C (Waves.z 0 ω)=(C.eval (Real.cos ω):ℝ)-(Real.sin ω:ℂ)*Complex.I := by
  have he : Waves.z 0 ω=(Real.cos ω:ℂ)+(Real.sin ω:ℂ)*Complex.I := by
    simp only [Waves.z,Complex.ofReal_zero,zero_add,Complex.exp_ofReal_mul_I]
  have hnorm : Complex.normSq (Waves.z 0 ω)=1 := by
    simpa only [pow_one,mul_zero,Real.exp_zero] using Waves.normSq_z_pow 0 ω 1
  have hinv : (Waves.z 0 ω)⁻¹=(Real.cos ω:ℂ)-(Real.sin ω:ℂ)*Complex.I := by
    rw [Complex.inv_def,hnorm,he]
    simp only [inv_one,Complex.ofReal_one,mul_one,map_add,map_mul,
      Complex.conj_ofReal,Complex.conj_I,mul_neg,← sub_eq_add_neg]
  unfold E Coefficients.evalComplex Coefficients.eval
  rw [hinv,he]
  push_cast
  ring

end polyak.Levels.Chart
