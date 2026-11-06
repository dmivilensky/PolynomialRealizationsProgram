import polyak.Global.Kernels.Fourier
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.Calculus.Deriv.Support

/-! The literal inverse-square Fourier decay of the smooth convolution. -/
namespace nesterov.Spread
noncomputable section
open MeasureTheory Set Filter Complex
open scoped FourierTransform Topology ContDiff
open polyak.Global.Kernels

def complexBump (x : ℝ) : ℂ := (psi x:ℂ)

theorem complexBump_smooth : ContDiff ℝ ∞ complexBump :=
  Complex.ofRealCLM.contDiff.comp psi_smooth

theorem complexBump_compact : HasCompactSupport complexBump := by
  change HasCompactSupport ((fun x : ℝ=>(x:ℂ)) ∘ psi)
  exact psi_compact.comp_left rfl

theorem psi_fourier (ξ : ℝ) : charFun psiMeasure ξ=𝓕 complexBump (-(ξ/(2*Real.pi))) := by
  rw [charFun_apply_real,integral_psiMeasure,Real.fourier_real_eq_integral_exp_smul]
  congr 1
  funext x
  simp only [Complex.real_smul,smul_eq_mul,complexBump]
  rw [mul_comm (psi x:ℂ)]
  congr 1
  have hr : -2*Real.pi*x* -(ξ/(2*Real.pi))=ξ*x := by
    field_simp
  rw [hr]
  push_cast
  rfl

theorem psiHat_decay :
    ∃ C : ℝ,0<C ∧ ∀ ξ : ℝ,ξ≠0 → |psiHat ξ|≤C/|ξ| := by
  let C : ℝ := 1+∫x,‖deriv complexBump x‖
  have hC : 0<C := by dsimp [C];positivity
  have hf : Integrable complexBump := complexBump_smooth.continuous.integrable_of_hasCompactSupport complexBump_compact
  have hdf : Differentiable ℝ complexBump := complexBump_smooth.differentiable (by norm_num)
  have hd : Integrable (deriv complexBump) :=
    (complexBump_smooth.continuous_deriv (by norm_num)).integrable_of_hasCompactSupport complexBump_compact.deriv
  refine ⟨C,hC,?_⟩
  intro ξ hξ
  have hderiv := congrFun (Real.fourier_deriv hf hdf hd) (-(ξ/(2*Real.pi)))
  have hnorm : ‖𝓕 (deriv complexBump) (-(ξ/(2*Real.pi)))‖≤∫x,‖deriv complexBump x‖ :=
    VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ _
  have harg : (2*(Real.pi:ℂ)*Complex.I*(-(ξ/(2*Real.pi):ℝ):ℂ))= -(ξ:ℂ)*Complex.I := by
    push_cast
    field_simp
  have hderivNorm := congrArg norm hderiv
  simp only [Complex.ofReal_neg] at hderivNorm
  rw [harg,norm_smul,norm_mul,norm_neg,Complex.norm_real,Complex.norm_I,mul_one] at hderivNorm
  simp only [Real.norm_eq_abs] at hderivNorm
  have hnorm' : |ξ| * |psiHat ξ|≤∫x,‖deriv complexBump x‖ := by
    have hc : ‖𝓕 complexBump (-(ξ/(2*Real.pi)))‖=|psiHat ξ| := by
      rw [←psi_fourier,psi_characteristic_real,Complex.norm_real]
      exact Real.norm_eq_abs _
    rw [hc] at hderivNorm
    rw [hderivNorm] at hnorm
    exact hnorm
  exact (le_div_iff₀ (abs_pos.mpr hξ)).mpr (by dsimp [C];nlinarith)

theorem phiHat_decay :
    ∃ C : ℝ,0<C ∧ ∀ ξ : ℝ,ξ≠0 → |phiHat ξ|≤C/ξ^2 := by
  obtain ⟨C,hC,hbound⟩ := psiHat_decay
  refine ⟨C^2,sq_pos_of_pos hC,?_⟩
  intro ξ hξ
  have hh := hbound ξ hξ
  have hp := mul_self_le_mul_self (abs_nonneg (psiHat ξ)) hh
  simp only [←pow_two] at hp
  simp only [div_pow,sq_abs] at hp
  simpa only [phiHat,abs_sq] using hp

end
end nesterov.Spread
