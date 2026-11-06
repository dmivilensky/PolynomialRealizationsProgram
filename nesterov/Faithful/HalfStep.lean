import nesterov.Faithful.LowLimits
import nesterov.TwoStep.LimitSymbol
import nesterov.Flow.LevelSets
import nesterov.Faithful.TraceLimit

/-! Exact finite-frequency identities behind the half-step mechanism. -/
namespace nesterov.Faithful
noncomputable section
open Polynomial Set

def momentumQuery (τ : ℝ) : Polynomial ℝ := C (1+τ)*X-C τ

theorem circle_arg {ω : ℝ} (hω : ω∈Ioc (-Real.pi) Real.pi) : (circle ω).arg=ω := by
  rw [circle,Complex.arg_exp_mul_I,toIocMod_eq_self]
  simpa only [two_mul,neg_add_cancel_left] using hω

theorem momentum_phase_factor (τ y ω : ℝ) (hy : y≠0) :
    -star (limitProduct (momentumQuery τ) (C (-1/y)) ω)=
      ((2*(1-Real.cos ω)/y^2:ℝ):ℂ)*
        (((y-(2-y*τ)*(1-Real.cos ω):ℝ):ℂ)+Complex.I*(y*τ*Real.sin ω:ℝ)) := by
  unfold limitProduct evalComplex momentumQuery circle
  simp only [Polynomial.map_sub,Polynomial.map_mul,Polynomial.map_C,Polynomial.map_X,
    Polynomial.eval_sub,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X]
  have hc (a : ℝ) : Complex.ofRealHom a=(a:ℂ) := rfl
  simp only [hc,Complex.exp_mul_I,←Complex.ofReal_cos,←Complex.ofReal_sin]
  simp only [star_mul,star_sub,star_pow,star_neg,star_add,star_one,
    Complex.star_def,Complex.conj_ofReal,Complex.conj_I]
  simp only [pow_two]
  apply Complex.ext <;> simp only [Complex.mul_re,Complex.mul_im,Complex.sub_re,Complex.sub_im,
    Complex.add_re,Complex.add_im,Complex.neg_re,Complex.neg_im,
    Complex.ofReal_re,Complex.ofReal_im,Complex.one_re,Complex.one_im,Complex.I_re,Complex.I_im]
  all_goals field_simp [hy]
  all_goals ring_nf
  · have hs : Real.sin ω^2=1-Real.cos ω^2 := by nlinarith [Real.sin_sq_add_cos_sq ω]
    rw [show Real.sin ω^4=(Real.sin ω^2)^2 by ring,hs]
    ring
  · have hs : Real.sin ω^2=1-Real.cos ω^2 := by nlinarith [Real.sin_sq_add_cos_sq ω]
    rw [show Real.sin ω^3=Real.sin ω^2*Real.sin ω by ring,hs]
    ring

theorem momentum_angle (τ y : ℝ) (hy : 0<y) {ω : ℝ} (hω : ω∈Ioc (0:ℝ) Real.pi) :
    limitAngle (momentumQuery τ) (C (-1/y)) ω=
      Complex.arg (((y-(2-y*τ)*(1-Real.cos ω):ℝ):ℂ)+Complex.I*(y*τ*Real.sin ω:ℝ)) := by
  rw [limitAngle,momentum_phase_factor τ y ω hy.ne',Complex.arg_real_mul]
  have hcos : Real.cos ω<1 := by
    simpa only [Real.cos_zero] using Real.cos_lt_cos_of_nonneg_of_le_pi (by norm_num : (0:ℝ)≤0) hω.2 hω.1
  exact div_pos (by linarith) (sq_pos_of_ne_zero hy.ne')

theorem nesterov_angle {ω : ℝ} (hω : ω∈Ioc (0:ℝ) Real.pi) :
    limitAngle (momentumQuery 1) (C (-1)) ω=ω := by
  have hh := momentum_angle 1 1 (by norm_num) hω
  have he : (((1-(2-1*1)*(1-Real.cos ω):ℝ):ℂ)+Complex.I*(1*1*Real.sin ω:ℝ))=circle ω := by
    rw [circle,Complex.exp_mul_I]
    rw [←Complex.ofReal_cos,←Complex.ofReal_sin]
    push_cast
    ring
  rw [he] at hh
  convert! hh.trans (circle_arg ⟨by linarith [Real.pi_pos,hω.1],hω.2⟩) using 1
  norm_num

theorem tmm_angle {ω : ℝ} (hω : ω∈Ioo (0:ℝ) Real.pi) :
    limitAngle (momentumQuery (1/2)) (C (-1/2)) ω=ω/2 := by
  have hh := momentum_angle (1/2) 2 (by norm_num) ⟨hω.1,hω.2.le⟩
  have he : (((2-(2-2*(1/2))*(1-Real.cos ω):ℝ):ℂ)+Complex.I*(2*(1/2)*Real.sin ω:ℝ))=
      ((2*Real.cos (ω/2):ℝ):ℂ)*circle (ω/2) := by
    have hcos := Real.cos_two_mul (ω/2)
    have hsin := Real.sin_two_mul (ω/2)
    rw [show 2*(ω/2)=ω by ring] at hcos hsin
    simp only [circle,Complex.exp_mul_I,←Complex.ofReal_cos,←Complex.ofReal_sin]
    apply Complex.ext <;> simp only [Complex.mul_re,Complex.mul_im,Complex.add_re,Complex.add_im,
      Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,Complex.I_im,mul_zero,zero_mul,zero_add,
      add_zero,mul_one,one_mul,sub_zero]
    · norm_num;linarith
    · norm_num;linarith
  rw [he,Complex.arg_real_mul] at hh
  · convert! hh.trans (circle_arg ⟨by linarith [Real.pi_pos,hω.1],by linarith [hω.2,Real.pi_pos]⟩) using 1
  · exact mul_pos (by norm_num) (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos,hω.1],by linarith [hω.2]⟩)

theorem momentum_symbol (τ y ω : ℝ) (hy : 0<y) :
    limitSymbol (momentumQuery τ) (C (-1/y)) ω=TwoStep.limitSymbol τ y (1-Real.cos ω) := by
  have hh := trace_symbol_eq (TwoStep.limitData τ y hy) ω
  rw [TwoStep.limitData_query] at hh
  change (TwoStep.limitData τ y hy).symbol ω=limitSymbol (momentumQuery τ) (C (-1/y)) ω at hh
  rw [←hh,TwoStep.limitData_symbol]

theorem tmm_symbol_zero (ω : ℝ) : limitSymbol (momentumQuery (1/2)) (C (-1/2)) ω=0 := by
  have hh := momentum_symbol (1/2) 2 ω (by norm_num)
  convert! hh using 1
  norm_num [TwoStep.limitSymbol]

/-- The slow cubic is precisely the negative minimizer slack. -/
theorem slow_symbol_opposite_slack (θ y c γ : ℝ) :
    c*Flow.delta θ y c+(θ-3*c)*γ^2= -((3*c-θ)*γ^2-c*Flow.delta θ y c) := by ring

theorem slow_symbol_positive_iff {θ y c : ℝ} (hc : 0<c) (hcQ : c<Flow.cQ θ y) :
    (∀ γ : ℝ,0<c*Flow.delta θ y c+(θ-3*c)*γ^2) ↔ c≤θ/3 := by
  have hd := (Flow.lt_cQ_iff θ y c).mp hcQ |>.2
  constructor
  · intro h
    by_contra hn
    have he : 0<3*c-θ := by linarith [lt_of_not_ge hn]
    let γ := Real.sqrt ((c*Flow.delta θ y c+1)/(3*c-θ))
    have hs : γ^2=(c*Flow.delta θ y c+1)/(3*c-θ) := Real.sq_sqrt (by positivity)
    have hh := h γ
    rw [hs] at hh
    have hi := (div_mul_cancel₀ (c*Flow.delta θ y c+1) he.ne')
    nlinarith
  · intro h γ
    exact add_pos_of_pos_of_nonneg (mul_pos hc hd) (mul_nonneg (by linarith) (sq_nonneg γ))

end
end nesterov.Faithful
