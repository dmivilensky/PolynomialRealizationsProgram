import polyak.Global.Kernels.Convolution
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.TaylorExpansion

/-! The source kernel transform is the fourth power of a real characteristic function. -/
noncomputable section
namespace polyak.Global.Kernels
open MeasureTheory Set Function Complex
open scoped Topology ENNReal NNReal

def psiHat (ξ : ℝ) : ℝ := (charFun psiMeasure ξ).re

def phiHat (ξ : ℝ) : ℝ := psiHat ξ^2

def kernelHat (ε ξ : ℝ) : ℝ := phiHat (ε*ξ)^2

theorem psi_characteristic_real (ξ : ℝ) : charFun psiMeasure ξ=(psiHat ξ:ℂ) := by
  have hc : (starRingEnd ℂ) (charFun psiMeasure ξ)=charFun psiMeasure ξ := by
    rw [charFun_apply_real,integral_psiMeasure,←integral_conj]
    have hh := integral_neg_eq_self (fun x:ℝ=>psi x • Complex.exp ((ξ:ℂ)*(x:ℂ)*Complex.I)) (μ:=volume)
    rw [←hh]
    apply integral_congr_ae
    filter_upwards with x
    simp [Complex.real_smul,psi_even,←Complex.exp_conj]

  apply Complex.ext
  · rfl
  · have hi := congrArg Complex.im hc
    simp only [Complex.conj_im] at hi
    simp only [Complex.ofReal_im]
    linarith

theorem psiHat_abs_le_one (ξ : ℝ) : |psiHat ξ|≤1 := by
  exact (Complex.abs_re_le_norm _).trans (norm_charFun_le_one _)

theorem phiHat_mem (ξ : ℝ) : phiHat ξ∈Icc (0:ℝ) 1 := by
  constructor
  · exact sq_nonneg _
  · unfold phiHat
    have hh := psiHat_abs_le_one ξ
    nlinarith [sq_abs (psiHat ξ),abs_nonneg (psiHat ξ)]

theorem kernelHat_mem (ε ξ : ℝ) : kernelHat ε ξ∈Icc (0:ℝ) 1 := by
  constructor
  · exact sq_nonneg _
  · unfold kernelHat
    obtain ⟨hl,hu⟩ := phiHat_mem (ε*ξ)
    nlinarith

@[simp] theorem psiHat_zero : psiHat 0=1 := by simp [psiHat,charFun_zero,measureReal_def]
@[simp] theorem phiHat_zero : phiHat 0=1 := by simp [phiHat]
@[simp] theorem kernelHat_zero (ε:ℝ) : kernelHat ε 0=1 := by simp [kernelHat]

theorem phi_characteristic (ξ : ℝ) : charFun phiMeasure ξ=(phiHat ξ:ℂ) := by
  rw [phiMeasure,charFun_conv,psi_characteristic_real]
  simp [phiHat,pow_two]

theorem kappa_characteristic (ξ : ℝ) : charFun kappaMeasure ξ=(kernelHat 1 ξ:ℂ) := by
  rw [kappaMeasure,charFun_conv,phi_characteristic]
  simp [kernelHat,pow_two]

@[fun_prop] theorem continuous_psiHat : Continuous psiHat :=
  Complex.continuous_re.comp continuous_charFun
@[fun_prop] theorem continuous_phiHat : Continuous phiHat := continuous_psiHat.pow 2
@[fun_prop] theorem continuous_kernelHat (ε:ℝ) : Continuous (kernelHat ε) := by
  unfold kernelHat
  exact ((continuous_phiHat.comp (continuous_const.mul continuous_id)).pow 2)

@[simp] theorem kernelHat_zero_scale (ξ:ℝ) : kernelHat 0 ξ=1 := by simp [kernelHat]

@[fun_prop] theorem continuous_kernelHat_scale (ξ:ℝ) : Continuous (fun ε=>kernelHat ε ξ) := by
  unfold kernelHat
  exact (continuous_phiHat.comp (continuous_id.mul continuous_const)).pow 2

@[fun_prop] theorem continuous_kernelHat_joint : Continuous (fun p:ℝ×ℝ=>kernelHat p.1 p.2) := by
  unfold kernelHat
  exact (continuous_phiHat.comp (continuous_fst.mul continuous_snd)).pow 2

def kernelMeasure (ε : ℝ) : Measure ℝ := kappaMeasure.map (fun x=>ε*x)

instance kernelMeasure_probability (ε:ℝ) : IsProbabilityMeasure (kernelMeasure ε) :=
  inferInstanceAs (IsProbabilityMeasure (kappaMeasure.map (fun x=>ε*x)))

theorem kernel_characteristic (ε ξ : ℝ) : charFun (kernelMeasure ε) ξ=(kernelHat ε ξ:ℂ) := by
  rw [kernelMeasure,charFun_map_mul,kappa_characteristic]
  simp only [kernelHat,one_mul]

end polyak.Global.Kernels
