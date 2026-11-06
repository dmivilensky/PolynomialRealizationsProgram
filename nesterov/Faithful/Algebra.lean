import nesterov.Phase.Defect
import nesterov.Phase.LagOne
import Mathlib.Algebra.Polynomial.Taylor

/-!
Article: Section 5, the effective spectral phase lead and half-step multiplier.
Use: literal polynomial dictionaries, including invariance under a common
normalized factor; no coprimality or stability hypothesis is imposed.
-/
namespace nesterov.Faithful
noncomputable section
open Polynomial

def effectiveLead (u q : Polynomial ℝ) (y : ℝ) : ℝ :=
  u.derivative.eval 1-1+y*q.derivative.eval 1

theorem effectiveLead_common_factor (u q r : Polynomial ℝ) {y : ℝ}
    (hu : u.eval 1=1) (hq : y*q.eval 1= -1) (hr : r.eval 1=1) :
    effectiveLead (u*r) (q*r) y=effectiveLead u q y := by
  simp only [effectiveLead,derivative_mul,eval_add,eval_mul,hu,hr,one_mul,mul_one]
  linear_combination r.derivative.eval 1*hq

theorem effectiveLead_momentum (τ y : ℝ) :
    effectiveLead (C (1+τ)*X-C τ) (C (-1/y)) y=τ := by
  simp [effectiveLead]

/-- The exact discrete-difference/continuous-derivative multiplier identity. -/
theorem half_step_multiplier {ω : ℝ} (hω : ω≠0) :
    1-Complex.exp ((ω:ℂ)*Complex.I)=
      ((2*Real.sin (ω/2)/ω:ℝ):ℂ)*Complex.exp (((ω/2:ℝ):ℂ)*Complex.I)*
        (-(ω:ℂ)*Complex.I) := by
  have hcos := Real.cos_two_mul (ω/2)
  have hsin := Real.sin_two_mul (ω/2)
  rw [show 2*(ω/2)=ω by ring] at hcos hsin
  have hh := Real.sin_sq_add_cos_sq (ω/2)
  simp only [Complex.exp_mul_I]
  rw [←Complex.ofReal_cos,←Complex.ofReal_sin,←Complex.ofReal_cos,←Complex.ofReal_sin]
  apply Complex.ext
  · norm_num only [Complex.mul_re,Complex.mul_im,Complex.add_re,Complex.add_im,
      Complex.sub_re,Complex.sub_im,Complex.ofReal_re,Complex.ofReal_im,
      Complex.I_re,Complex.I_im,Complex.one_re,Complex.one_im,Complex.neg_re,Complex.neg_im,
      mul_zero,zero_mul,mul_one,one_mul,add_zero,zero_add,sub_zero,zero_sub,neg_zero]
    field_simp [hω]
    nlinarith
  · norm_num only [Complex.mul_re,Complex.mul_im,Complex.add_re,Complex.add_im,
      Complex.sub_re,Complex.sub_im,Complex.ofReal_re,Complex.ofReal_im,
      Complex.I_re,Complex.I_im,Complex.one_re,Complex.one_im,Complex.neg_re,Complex.neg_im,
      mul_zero,zero_mul,mul_one,one_mul,add_zero,zero_add,sub_zero,zero_sub,neg_zero]
    field_simp [hω]
    nlinarith

theorem half_step_magnitude_pos {ω : ℝ} (hω : ω∈Set.Ioc (0:ℝ) Real.pi) :
    0<2*Real.sin (ω/2)/ω :=
  div_pos (mul_pos (by norm_num) (Real.sin_pos_of_pos_of_lt_pi
    (by linarith [hω.1]) (by linarith [hω.2,Real.pi_pos]))) hω.1

/-- The stationary lag-one criterion used in the finite-memory theorem.
The radius is exp(t), so the zero middle-radius case needs no logarithm. -/
theorem rate_lt_of_lagOne (M : StationaryMethod) {μ L t : ℝ}
    (hμ : 0<μ) (hμL : μ<L) (ht : t≤0)
    (hr : IQC.middleRadius M μ L<Real.exp t)
    (hpos : ∀ z : ℂ,‖z‖=Real.exp t →
      0<((1-z)*M.characteristic μ z*star (M.characteristic L z)).re) :
    Rates.rate M μ L<Real.exp t := by
  obtain ⟨cert⟩ := Phase.lagOne_certificate ht (a:=M.symbolPair μ L t) (fun c=>by
    unfold Phase.lagOne
    rw [Phase.stationary_factor M hμL]
    have he :
        (-((4/(L-μ)^2:ℝ):ℂ)*M.characteristic μ (polyak.Waves.z t (Real.arccos c))*
          star (M.characteristic L (polyak.Waves.z t (Real.arccos c))))*
          (1-polyak.Waves.z t (Real.arccos c))=
        -((4/(L-μ)^2:ℝ):ℂ)*
          ((1-polyak.Waves.z t (Real.arccos c))*M.characteristic μ (polyak.Waves.z t (Real.arccos c))*
          star (M.characteristic L (polyak.Waves.z t (Real.arccos c)))) := by ring
    rw [he]
    simp only [Complex.mul_re,Complex.neg_re,Complex.ofReal_re,Complex.neg_im,
      Complex.ofReal_im,neg_zero,zero_mul,sub_zero]
    exact mul_neg_of_neg_of_pos (neg_neg_of_pos (div_pos (by norm_num) (sq_pos_of_pos (sub_pos.mpr hμL))))
      (hpos _ (by simpa using polyak.Waves.norm_z_pow t (Real.arccos c) 1)))
  exact IQC.one_exponent hμ hμL hr cert

end
end nesterov.Faithful
