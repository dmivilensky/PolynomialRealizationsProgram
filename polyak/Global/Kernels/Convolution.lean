import polyak.Global.Kernels.Bump
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic

/-! The source convolutions φ=ψ⋆ψ and κ=φ⋆φ are actual positive smooth densities. -/
noncomputable section
namespace polyak.Global.Kernels
open MeasureTheory Set Function ContinuousLinearMap
open scoped Topology Convolution ContDiff ENNReal NNReal

def phi : ℝ→ℝ := psi ⋆[mul ℝ ℝ] psi

def kappa : ℝ→ℝ := phi ⋆[mul ℝ ℝ] phi

theorem phi_nonneg (x:ℝ) : 0≤phi x :=
  integral_nonneg fun t=>mul_nonneg (psi_nonneg t) (psi_nonneg (x-t))

theorem kappa_nonneg (x:ℝ) : 0≤kappa x :=
  integral_nonneg fun t=>mul_nonneg (phi_nonneg t) (phi_nonneg (x-t))

theorem phi_even (x:ℝ) : phi (-x)=phi x :=
  convolution_neg_of_neg_eq (mul ℝ ℝ) (ae_of_all _ psi_even) (ae_of_all _ psi_even)

theorem kappa_even (x:ℝ) : kappa (-x)=kappa x :=
  convolution_neg_of_neg_eq (mul ℝ ℝ) (ae_of_all _ phi_even) (ae_of_all _ phi_even)

theorem phi_integrable : Integrable phi := psi_integrable.integrable_convolution (mul ℝ ℝ) psi_integrable

theorem kappa_integrable : Integrable kappa := phi_integrable.integrable_convolution (mul ℝ ℝ) phi_integrable

theorem phi_compact : HasCompactSupport phi := psi_compact.convolution (mul ℝ ℝ) psi_compact

theorem kappa_compact : HasCompactSupport kappa := phi_compact.convolution (mul ℝ ℝ) phi_compact

theorem phi_smooth : ContDiff ℝ ∞ phi :=
  psi_compact.contDiff_convolution_right (mul ℝ ℝ) psi_integrable.locallyIntegrable psi_smooth

theorem kappa_smooth : ContDiff ℝ ∞ kappa :=
  phi_compact.contDiff_convolution_right (mul ℝ ℝ) phi_integrable.locallyIntegrable phi_smooth

@[simp] theorem integral_phi : ∫x,phi x=1 := by
  rw [phi,integral_convolution (mul ℝ ℝ) psi_integrable psi_integrable,integral_psi]
  norm_num

@[simp] theorem integral_kappa : ∫x,kappa x=1 := by
  rw [kappa,integral_convolution (mul ℝ ℝ) phi_integrable phi_integrable,integral_phi]
  norm_num

def phiMeasure : Measure ℝ := psiMeasure.conv psiMeasure

def kappaMeasure : Measure ℝ := phiMeasure.conv phiMeasure

instance phiMeasure_probability : IsProbabilityMeasure phiMeasure := inferInstanceAs (IsProbabilityMeasure (psiMeasure.conv psiMeasure))
instance kappaMeasure_probability : IsProbabilityMeasure kappaMeasure := inferInstanceAs (IsProbabilityMeasure (phiMeasure.conv phiMeasure))

end polyak.Global.Kernels
