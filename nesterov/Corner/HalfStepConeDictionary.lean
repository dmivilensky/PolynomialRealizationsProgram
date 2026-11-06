import nesterov.Corner.HalfStepCone
import nesterov.Phase.Algebra
import nesterov.TwoStep.AsymptoticsBridge
import nesterov.Spectral.Coordinates

/-! Exact zero-exponent slacks of the limiting TMM method.  The sine cone uses
the radial-weighted latent spectrum; the radial weight vanishes at both
endpoints, so no inverse-weight assertion is made there. -/
namespace nesterov.Corner
noncomputable section
open Spectral MeasureTheory

def halfStepLimitPair : SymbolPair :=
  (Momentum.method 1 (1/2) 2 (by norm_num)).symbolPair 0 1 0

def halfStepRadial (ω : ℝ) : ℝ :=
  8*Real.cos (ω/2)*Real.sin (ω/2)^2

theorem halfStepLimitPair_u (c : Frequency) :
    halfStepLimitPair.u c=(3/2:ℂ)*polyak.Waves.z 0 (Real.arccos c)-1/2 := by
  simp only [halfStepLimitPair,StationaryMethod.symbolPair_u,
    TwoStep.method_queryPolynomial,Polynomial.map_add,Polynomial.map_mul,
    Polynomial.map_C,Polynomial.map_one,Polynomial.map_X,Polynomial.eval_add,
    Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_one,Polynomial.eval_X]
  norm_num
  ring

theorem halfStepLimitPair_p (c : Frequency) :
    halfStepLimitPair.p c=(polyak.Waves.z 0 (Real.arccos c))^2-
      (1/2:ℂ)*polyak.Waves.z 0 (Real.arccos c)+1/2 := by
  simp only [halfStepLimitPair,StationaryMethod.symbolPair_p,
    StationaryMethod.normalizedPolynomial,TwoStep.method_queryPolynomial,
    TwoStep.method_recurrencePolynomial]
  norm_num
  ring

theorem halfStepLimitPair_g (c : Frequency) :
    g halfStepLimitPair c=2*Real.sin (Real.arccos c)^2 := by
  unfold g
  rw [halfStepLimitPair_u,halfStepLimitPair_p]
  simp only [pow_two,Complex.normSq_apply,Complex.sub_re,Complex.sub_im,
    Complex.add_re,Complex.add_im,Complex.mul_re,Complex.mul_im]
  norm_num [polyak.Waves.z]
  have hs := Real.sin_sq_add_cos_sq (Real.arccos (c:ℝ))
  nlinarith [sq_nonneg (Real.sin (Real.arccos (c:ℝ))^2+Real.cos (Real.arccos (c:ℝ))^2-1)]

theorem halfStepLimitPair_skew (c : Frequency) :
    skew halfStepLimitPair c=Real.sin (Real.arccos c)*(1-Real.cos (Real.arccos c)) := by
  unfold skew
  rw [halfStepLimitPair_u,halfStepLimitPair_p]
  simp only [pow_two,Complex.star_def,Complex.sub_re,Complex.sub_im,
    Complex.add_re,Complex.add_im,Complex.mul_re,Complex.mul_im,
    Complex.conj_re,Complex.conj_im]
  norm_num [polyak.Waves.z]
  linear_combination (3/2:ℝ)*Real.sin (Real.arccos (c:ℝ))*
    (Real.sin_sq_add_cos_sq (Real.arccos (c:ℝ)))

theorem halfStepRadial_nonneg {ω : ℝ} (hω : ω∈Set.Icc (0:ℝ) Real.pi) :
    0≤halfStepRadial ω := by
  unfold halfStepRadial
  apply mul_nonneg
  · exact mul_nonneg (by norm_num) (Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos,hω.1],by linarith [hω.2]⟩)
  · positivity

theorem halfStepRadial_pos {ω : ℝ} (hω : ω∈Set.Ioo (0:ℝ) Real.pi) :
    0<halfStepRadial ω := by
  unfold halfStepRadial
  apply mul_pos
  · exact mul_pos (by norm_num) (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos,hω.1],by linarith [hω.2]⟩)
  · exact sq_pos_of_pos (Real.sin_pos_of_pos_of_lt_pi (by linarith [hω.1]) (by linarith [hω.2,Real.pi_pos]))

theorem halfStepRadial_zero : halfStepRadial 0=0 := by simp [halfStepRadial]

theorem halfStepRadial_pi : halfStepRadial Real.pi=0 := by
  simp [halfStepRadial,Real.cos_pi_div_two]

theorem halfStepLimitPair_g_radial (c : Frequency) :
    g halfStepLimitPair c=halfStepRadial (Real.arccos c)*Real.cos (Real.arccos c/2) := by
  rw [halfStepLimitPair_g]
  have hs := Real.sin_two_mul (Real.arccos (c:ℝ)/2)
  rw [show 2*(Real.arccos (c:ℝ)/2)=Real.arccos c by ring] at hs
  rw [hs]
  unfold halfStepRadial
  ring

theorem halfStepLimitPair_skew_radial (c : Frequency) :
    2*skew halfStepLimitPair c=halfStepRadial (Real.arccos c)*Real.sin (Real.arccos c/2) := by
  rw [halfStepLimitPair_skew]
  have hs := Real.sin_two_mul (Real.arccos (c:ℝ)/2)
  have hc := Real.cos_two_mul' (Real.arccos (c:ℝ)/2)
  rw [show 2*(Real.arccos (c:ℝ)/2)=Real.arccos c by ring] at hs hc
  rw [hs,hc]
  unfold halfStepRadial
  linear_combination -4*Real.sin (Real.arccos (c:ℝ)/2)*Real.cos (Real.arccos (c:ℝ)/2)*
    (Real.sin_sq_add_cos_sq (Real.arccos (c:ℝ)/2))

theorem halfStep_lag_lower (n : ℕ) (c : Frequency) :
    lagA halfStepLimitPair 0 n c-lagB halfStepLimitPair n c=
      2*halfStepRadial (Real.arccos c)*halfStepLower (Real.arccos c) n := by
  unfold lagA lagB
  rw [halfStepLimitPair_g_radial,halfStepLimitPair_skew_radial]
  simp only [mul_zero,Real.cosh_zero]
  have hh := Real.cos_sub (n*Real.arccos (c:ℝ)) (Real.arccos (c:ℝ)/2)
  have hc := Real.cos_sub_cos (Real.arccos (c:ℝ)/2)
    (n*Real.arccos (c:ℝ)-Real.arccos (c:ℝ)/2)
  have h1 : (Real.arccos (c:ℝ)/2+(n*Real.arccos (c:ℝ)-Real.arccos (c:ℝ)/2))/2=
      n*Real.arccos (c:ℝ)/2 := by ring
  have h2 : (Real.arccos (c:ℝ)/2-(n*Real.arccos (c:ℝ)-Real.arccos (c:ℝ)/2))/2=
      -(((n:ℝ)-1)*Real.arccos (c:ℝ)/2) := by ring
  rw [h1,h2,Real.sin_neg,hh] at hc
  unfold halfStepLower
  linear_combination halfStepRadial (Real.arccos (c:ℝ))*hc

theorem halfStep_lag_upper (n : ℕ) (c : Frequency) :
    lagA halfStepLimitPair 0 n c+lagB halfStepLimitPair n c=
      2*halfStepRadial (Real.arccos c)*halfStepUpper (Real.arccos c) n := by
  unfold lagA lagB
  rw [halfStepLimitPair_g_radial,halfStepLimitPair_skew_radial]
  simp only [mul_zero,Real.cosh_zero]
  have hh := Real.cos_add (n*Real.arccos (c:ℝ)) (Real.arccos (c:ℝ)/2)
  have hc := halfStep_cos_gap (Real.arccos (c:ℝ)) n
  have he : ((n:ℝ)+1/2)*Real.arccos (c:ℝ)=
      n*Real.arccos (c:ℝ)+Real.arccos (c:ℝ)/2 := by ring
  rw [he,hh] at hc
  linear_combination halfStepRadial (Real.arccos (c:ℝ))*hc

end
end nesterov.Corner
