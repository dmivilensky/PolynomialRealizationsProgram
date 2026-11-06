import nesterov.Spread.KernelGap
import nesterov.Spread.KernelDecay

/-! The source's fixed bump is the actual normalized even Polyak bump.
Its convolution and every quantitative Fourier bound are proved here. -/
namespace nesterov.Spread
noncomputable section
open Set MeasureTheory
open scoped ContDiff
open polyak.Global.Kernels

theorem exists_kernel_data : ∃ D : KernelData,D.hat=phiHat := by
  obtain ⟨a0,ck,ha0,hck,hckhalf,hhalf,hgap⟩ := exists_relative_fourier_gap
  obtain ⟨C,hC,hdecay⟩ := phiHat_decay
  exact ⟨{
    hat := phiHat
    a0 := a0
    ck := ck
    Ck := C
    a0_pos := ha0
    ck_pos := hck
    ck_le_half := hckhalf
    Ck_pos := hC
    hat_mem := phiHat_mem
    hat_even := phiHat_even
    hat_zero := phiHat_zero
    continuous_hat := continuous_phiHat
    hat_half := fun ha haa=>hhalf _ ha haa
    gap := fun ha haa hax=>hgap _ _ ha haa hax
    decay := fun hx=>hdecay _ hx },rfl⟩

def canonicalKernel : KernelData := Classical.choose exists_kernel_data

@[simp] theorem canonicalKernel_hat : canonicalKernel.hat=phiHat :=
  Classical.choose_spec exists_kernel_data

theorem canonicalKernel_strict {ξ : ℝ} (hξ : ξ≠0) : canonicalKernel.hat ξ<1 := by
  rw [canonicalKernel_hat]
  exact phiHat_lt_one hξ

theorem source_bump_properties :
    ContDiff ℝ ∞ psi ∧ HasCompactSupport psi ∧ (∀ x : ℝ,0≤psi x) ∧
      (∀ x : ℝ,psi (-x)=psi x) ∧ (∫x,psi x)=1 ∧
      Function.support psi⊆Ioo (-1/2:ℝ) (1/2) := by
  refine ⟨psi_smooth,psi_compact,psi_nonneg,psi_even,integral_psi,?_⟩
  intro x hx
  rw [psi_support,Metric.mem_ball,Real.dist_eq,sub_zero] at hx
  exact ⟨by linarith [(abs_lt.mp hx).1],by linarith [(abs_lt.mp hx).2]⟩

theorem source_bump_tsupport : tsupport psi⊆Ioo (-1/2:ℝ) (1/2) := by
  intro x hx
  rw [psi_tsupport,Metric.mem_closedBall,Real.dist_eq,sub_zero] at hx
  exact ⟨by linarith [(abs_le.mp hx).1],by linarith [(abs_le.mp hx).2]⟩

theorem source_kernel_properties :
    ContDiff ℝ ∞ phi ∧ HasCompactSupport phi ∧ (∀ x : ℝ,0≤phi x) ∧
      (∀ x : ℝ,phi (-x)=phi x) ∧ (∫x,phi x)=1 ∧
      Function.support phi⊆Icc (-1:ℝ) 1 ∧
      ∀ ξ : ℝ,charFun phiMeasure ξ=(canonicalKernel.hat ξ:ℂ) := by
  refine ⟨phi_smooth,phi_compact,phi_nonneg,phi_even,integral_phi,?_,?_⟩
  · intro x hx
    have hh := phi_support_bound hx
    exact ⟨by linarith [(abs_lt.mp hh).1],by linarith [(abs_lt.mp hh).2]⟩
  · intro ξ
    rw [canonicalKernel_hat]
    exact phi_characteristic ξ

end
end nesterov.Spread
