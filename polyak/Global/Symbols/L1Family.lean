import polyak.Global.Symbols.UniformRiemannLebesgue
import polyak.Global.Symbols.Series
import Mathlib.Topology.Order.ProjIcc

/-! The actual varying-curve modulations of an L¹ test function form a
compact L¹ family. No smoothness or finite Fourier support is assumed. -/
noncomputable section
namespace polyak.Global.Symbols
open Levels MeasureTheory Filter Set Topology

 def realCurve (Θ : Curve) (x : ℝ) : ℝ := Θ (projIcc 0 Real.pi Real.pi_pos.le x)

@[fun_prop] theorem continuous_realCurve (Θ : Curve) : Continuous (realCurve Θ) :=
  Θ.continuous.comp continuous_projIcc

@[simp] theorem realCurve_of_mem (Θ : Curve) {x : ℝ} (hx : x∈Icc (0:ℝ) Real.pi) :
    realCurve Θ x=Θ ⟨x,hx⟩ := by unfold realCurve; rw [projIcc_of_mem]

def phaseSignal (Θ : Curve) (φ : ℝ→ℂ) (x : ℝ) : ℂ :=
  Complex.exp ((-realCurve Θ x:ℝ)*Complex.I)*φ x

theorem phaseSignal_norm (Θ : Curve) (φ : ℝ→ℂ) (x : ℝ) :
    ‖phaseSignal Θ φ x‖=‖φ x‖ := by
  unfold phaseSignal
  rw [norm_mul,Complex.norm_exp_ofReal_mul_I,one_mul]

theorem integrable_phaseSignal (Θ : Curve) {φ : ℝ→ℂ} (hφ : Integrable φ) :
    Integrable (phaseSignal Θ φ) := by
  apply hφ.bdd_mul
  · exact ((Complex.continuous_exp.comp
      ((Complex.continuous_ofReal.comp (continuous_realCurve Θ).neg).mul continuous_const))).aestronglyMeasurable
  · exact Eventually.of_forall (fun x=>(Complex.norm_exp_ofReal_mul_I _).le)

def phaseL1 (Θ : Curve) {φ : ℝ→ℂ} (hφ : Integrable φ) : RealL1 :=
  (integrable_phaseSignal Θ hφ).toL1 (phaseSignal Θ φ)

theorem norm_toL1_sub {f g : ℝ→ℂ} (hf : Integrable f (volume : Measure ℝ)) (hg : Integrable g (volume : Measure ℝ)) :
    ‖hf.toL1 f-hg.toL1 g‖=∫x,‖f x-g x‖ := by
  rw [L1.norm_sub_eq_lintegral]
  change _=∫x,‖(f-g) x‖
  rw [integral_norm_eq_lintegral_enorm (hf.aestronglyMeasurable.sub hg.aestronglyMeasurable)]
  congr 1
  apply lintegral_congr_ae
  filter_upwards [hf.coeFn_toL1,hg.coeFn_toL1] with x hfx hgx
  simp only [hfx,hgx,Pi.sub_apply]

theorem phaseL1_tendsto (Θ : ℕ→Curve) (Ψ : Curve)
    (hΘ : ∀ω,Tendsto (fun j=>Θ j ω) atTop (𝓝 (Ψ ω)))
    {φ : ℝ→ℂ} (hφ : Integrable φ) :
    Tendsto (fun j=>phaseL1 (Θ j) hφ) atTop (𝓝 (phaseL1 Ψ hφ)) := by
  have hp (x : ℝ) : Tendsto (fun j=>phaseSignal (Θ j) φ x) atTop (𝓝 (phaseSignal Ψ φ x)) := by
    apply Tendsto.mul_const
    apply Complex.continuous_exp.continuousAt.tendsto.comp
    exact ((Complex.continuous_ofReal.continuousAt.tendsto).comp
      (hΘ (projIcc 0 Real.pi Real.pi_pos.le x)).neg).mul_const Complex.I
  have hb (j : ℕ) (x : ℝ) : ‖phaseSignal (Θ j) φ x-phaseSignal Ψ φ x‖≤2*‖φ x‖ := by
    have hh := norm_sub_le (phaseSignal (Θ j) φ x) (phaseSignal Ψ φ x)
    rw [phaseSignal_norm,phaseSignal_norm] at hh
    linarith
  have ht : Tendsto (fun j=>∫x,‖phaseSignal (Θ j) φ x-phaseSignal Ψ φ x‖) atTop (𝓝 0) := by
    have hi := tendsto_integral_of_dominated_convergence (fun x=>2*‖φ x‖)
      (fun j=>((integrable_phaseSignal (Θ j) hφ).aestronglyMeasurable.sub
        (integrable_phaseSignal Ψ hφ).aestronglyMeasurable).norm)
      (hφ.norm.const_mul 2) (fun j=>Eventually.of_forall (fun x=>by
        rw [Real.norm_of_nonneg (norm_nonneg _)];exact hb j x))
      (Eventually.of_forall (fun x=>by simpa only [Pi.sub_apply,sub_self,norm_zero] using (hp x).sub_const (phaseSignal Ψ φ x) |>.norm))
    simpa only [Pi.sub_apply,integral_zero] using hi
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simpa only [phaseL1,norm_toL1_sub] using ht

theorem phaseL1_compact (Θ : ℕ→Curve) (Ψ : Curve)
    (hΘ : ∀ω,Tendsto (fun j=>Θ j ω) atTop (𝓝 (Ψ ω)))
    {φ : ℝ→ℂ} (hφ : Integrable φ) :
    IsCompact (insert (phaseL1 Ψ hφ) (range (fun j=>phaseL1 (Θ j) hφ))) :=
  (phaseL1_tendsto Θ Ψ hΘ hφ).isCompact_insert_range

end polyak.Global.Symbols
