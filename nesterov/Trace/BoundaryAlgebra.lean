import nesterov.Trace.Model
import Mathlib.Analysis.RCLike.Lemmas

/-! Exact polynomial identities for the source weighted lag-one symbol. -/
namespace nesterov.Trace
noncomputable section
open Complex Polynomial

theorem eval_conj (p : Polynomial ℝ) (z : ℂ) : eval p (star z)=star (eval p z) := by
  have he : algebraMap ℝ ℂ=Complex.ofRealHom := by ext x;rfl
  simpa only [eval,Polynomial.aeval_def,Polynomial.eval₂_eq_eval_map,Complex.star_def,he] using Polynomial.aeval_conj p z

@[simp] theorem eval_ofReal (p : Polynomial ℝ) (x : ℝ) : eval p (x:ℂ)=((p.eval x:ℝ):ℂ) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [eval_add,Polynomial.eval_add,hp,hq,Complex.ofReal_add]
  | monomial n a =>
    simp only [eval,Polynomial.map_monomial,Polynomial.eval_monomial,
      Complex.ofReal_mul,Complex.ofReal_pow]
    rfl

@[simp] theorem eval_neg_one (p : Polynomial ℝ) : eval p (-1)=((p.eval (-1):ℝ):ℂ) := by
  simpa only [Complex.ofReal_neg,Complex.ofReal_one] using eval_ofReal p (-1)

/-- The unit-circle identity before division by the characteristic polynomial.
It includes both real endpoints, where both sides vanish. -/
theorem weighted_product_identity {z : ℂ} (hz : Complex.normSq z=1) (k : ℂ) :
    (1+z.re)*((z-1)^3*k).re=
      -2*(1-z.re)*z.im*((-z*(z+1)*k).im) := by
  simp only [Complex.normSq_apply] at hz
  simp only [pow_succ,pow_zero,Complex.mul_re,Complex.mul_im,Complex.sub_re,
    Complex.sub_im,Complex.add_re,Complex.add_im,Complex.neg_re,Complex.neg_im,
    Complex.one_re,Complex.one_im,sub_zero,add_zero]
  linear_combination (k.re*(z.re-1)^2+k.im*z.im*(3-z.re))*hz

/-- This is the weighted trace integrand on the circle. -/
theorem weighted_quotient_identity {z : ℂ} (hz : Complex.normSq z=1)
    (hz1 : z≠1) (q d : ℂ) (hd : d≠0) :
    -(z.im/(1-z.re))*((-z*(z+1)*q)/d).im=
      (1+z.re)*((1-z)*(-(z-1)^2*q)*star d).re/
        (2*(1-z.re)^2*Complex.normSq d) := by
  have hden : 1-z.re≠0 := by
    intro hh
    have hr : z.re=1 := by linarith
    have hi : z.im=0 := by simp only [Complex.normSq_apply,hr] at hz;nlinarith
    exact hz1 (Complex.ext hr hi)
  have hd0 := (Complex.normSq_pos.mpr hd).ne'
  have hs : ((1-z)*(-(z-1)^2*q)*star d)=((z-1)^3*(q*star d)) := by ring
  have hh := weighted_product_identity hz (q*star d)
  have hq : ((-z*(z+1)*q)/d).im=
      (-z*(z+1)*(q*star d)).im/Complex.normSq d := by
    simp only [Complex.div_im,Complex.mul_im,Complex.mul_re,Complex.star_def,Complex.conj_re,Complex.conj_im]
    ring
  rw [hs,hq]
  calc
    _ = (-2*(1-z.re)*z.im*(-z*(z+1)*(q*star d)).im)/
        (2*(1-z.re)^2*Complex.normSq d) := by
      generalize (-z*(z+1)*(q*star d)).im=T
      field_simp [hden,hd0]
    _ = _ := by rw [←hh]

end
end nesterov.Trace
