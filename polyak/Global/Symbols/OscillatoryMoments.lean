import polyak.Global.Symbols.L1Family
import Mathlib.Topology.Instances.ZMultiples
import Mathlib.Topology.Algebra.Field

/-! Actual source cosine moments and uniform decay for all varying curves
of a convergent sequence, with the limit curve included. -/
noncomputable section
namespace polyak.Global.Symbols
open Levels MeasureTheory Filter Set Topology
open scoped FourierTransform

def scaledFrequency (n : ℤ) : ℝ := -(n:ℝ)/(2*Real.pi)
def oscillatoryMoment (Θ : Curve) (φ : ℝ→ℝ) (n : ℤ) : ℝ :=
  ∫x,Real.cos ((n:ℝ)*x-realCurve Θ x)*φ x

theorem scaledFrequency_tendsto : Tendsto scaledFrequency cofinite (cocompact ℝ) := by
  have hh := (tendsto_cocompact_mul_right₀
    (show -(1/(2*Real.pi))≠(0:ℝ) by
      exact neg_ne_zero.mpr (one_div_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero)))).comp Int.tendsto_coe_cofinite
  convert hh using 1
  ext n
  dsimp [scaledFrequency,Function.comp_def]
  ring

theorem phase_fourier (Θ : Curve) {φ : ℝ→ℂ} (hφ : Integrable φ) (n : ℤ) :
    fourierL1 (phaseL1 Θ hφ) (scaledFrequency n)=
      ∫x,Complex.exp ((((n:ℝ)*x-realCurve Θ x:ℝ):ℂ)*Complex.I)*φ x := by
  unfold fourierL1
  rw [Real.fourier_eq]
  apply integral_congr_ae
  filter_upwards [(integrable_phaseSignal Θ hφ).coeFn_toL1] with x hx
  change 𝐞 (-inner ℝ x (scaledFrequency n)) •
    (phaseL1 Θ hφ : ℝ→ℂ) x=_
  rw [show (phaseL1 Θ hφ : ℝ→ℂ) x=phaseSignal Θ φ x from hx,
    Circle.smul_def,Real.fourierChar_apply]
  unfold phaseSignal
  rw [smul_eq_mul,←mul_assoc,←Complex.exp_add]
  congr 2
  have he : 2*Real.pi*(-inner ℝ x (scaledFrequency n))-realCurve Θ x=
      (n:ℝ)*x-realCurve Θ x := by
    simp only [RCLike.inner_apply,starRingEnd_apply,star_trivial]
    unfold scaledFrequency
    field_simp
  calc
    _=(((2*Real.pi*(-inner ℝ x (scaledFrequency n))-realCurve Θ x):ℝ):ℂ)*Complex.I := by push_cast;ring
    _=_ := by rw [he]

theorem complexOsc_integrable (Θ : Curve) {φ : ℝ→ℝ} (hφ : Integrable φ) (n : ℤ) :
    Integrable (fun x=>Complex.exp ((((n:ℝ)*x-realCurve Θ x:ℝ):ℂ)*Complex.I)*(φ x:ℂ)) := by
  apply hφ.ofReal.bdd_mul
  · exact (Complex.continuous_exp.comp
      ((Complex.continuous_ofReal.comp ((continuous_const.mul continuous_id).sub
        (continuous_realCurve Θ))).mul continuous_const)).aestronglyMeasurable
  · exact Eventually.of_forall (fun x=>(Complex.norm_exp_ofReal_mul_I _).le)

theorem oscillatoryMoment_fourier (Θ : Curve) {φ : ℝ→ℝ} (hφ : Integrable φ) (n : ℤ) :
    oscillatoryMoment Θ φ n=(fourierL1 (phaseL1 Θ hφ.ofReal) (scaledFrequency n)).re := by
  rw [phase_fourier]
  change oscillatoryMoment Θ φ n=RCLike.re (∫x,Complex.exp ((((n:ℝ)*x-realCurve Θ x:ℝ):ℂ)*Complex.I)*(φ x:ℂ))
  rw [←integral_re (complexOsc_integrable Θ hφ n)]
  unfold oscillatoryMoment
  congr 1
  ext x
  change Real.cos ((n:ℝ)*x-realCurve Θ x)*φ x=
    (Complex.exp ((((n:ℝ)*x-realCurve Θ x:ℝ):ℂ)*Complex.I)*(φ x:ℂ)).re
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero,
    Complex.exp_ofReal_mul_I_re]

theorem oscillatoryMoment_norm_bound (Θ : Curve) {φ : ℝ→ℝ} (hφ : Integrable φ) (n : ℤ) :
    ‖oscillatoryMoment Θ φ n‖≤∫x,‖φ x‖ := by
  apply (norm_integral_le_integral_norm _).trans
  apply integral_mono_of_nonneg
  · exact Eventually.of_forall (fun x=>norm_nonneg _)
  · exact hφ.norm
  · apply Eventually.of_forall
    intro x
    change ‖Real.cos ((n:ℝ)*x-realCurve Θ x)*φ x‖≤‖φ x‖
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (by simpa only [Real.norm_eq_abs] using Real.abs_cos_le_one _)

theorem oscillatoryMoment_tendsto (Θ : ℕ→Curve) (Ψ : Curve)
    (hΘ : ∀ω,Tendsto (fun j=>Θ j ω) atTop (𝓝 (Ψ ω)))
    {φ : ℝ→ℝ} (hφ : Integrable φ) (n : ℤ) :
    Tendsto (fun j=>oscillatoryMoment (Θ j) φ n) atTop (𝓝 (oscillatoryMoment Ψ φ n)) := by
  apply tendsto_integral_of_dominated_convergence (fun x=>‖φ x‖)
  · intro j
    exact ((Real.continuous_cos.comp
      ((continuous_const.mul continuous_id).sub (continuous_realCurve (Θ j)))).aestronglyMeasurable).mul hφ.aestronglyMeasurable
  · exact hφ.norm
  · intro j
    apply Eventually.of_forall
    intro x
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (by simpa only [Real.norm_eq_abs] using Real.abs_cos_le_one _)
  · apply Eventually.of_forall
    intro x
    exact (Real.continuous_cos.continuousAt.tendsto.comp
      (tendsto_const_nhds.sub (hΘ (projIcc 0 Real.pi Real.pi_pos.le x)))).mul_const (φ x)

theorem oscillatoryMoment_uniform_tail (Θ : ℕ→Curve) (Ψ : Curve)
    (hΘ : ∀ω,Tendsto (fun j=>Θ j ω) atTop (𝓝 (Ψ ω)))
    {φ : ℝ→ℝ} (hφ : Integrable φ) (ε : ℝ) (hε : 0<ε) :
    ∃F : Finset ℤ,(∀j n,n∉F→‖oscillatoryMoment (Θ j) φ n‖≤ε) ∧
      (∀n,n∉F→‖oscillatoryMoment Ψ φ n‖≤ε) := by
  let K : Set RealL1 := insert (phaseL1 Ψ hφ.ofReal) (range (fun j=>phaseL1 (Θ j) hφ.ofReal))
  have hK : IsCompact K := phaseL1_compact Θ Ψ hΘ hφ.ofReal
  have he := scaledFrequency_tendsto.eventually
    ((Metric.tendstoUniformlyOn_iff.mp (uniform_RiemannLebesgue hK)) ε hε)
  have hfinite : {n : ℤ | ¬∀f∈K,dist (0:ℂ) (fourierL1 f (scaledFrequency n))<ε}.Finite := he
  refine ⟨hfinite.toFinset,?_,?_⟩
  · intro j n hn
    have hp : ∀f∈K,dist (0:ℂ) (fourierL1 f (scaledFrequency n))<ε := by
      by_contra hh
      exact hn (hfinite.mem_toFinset.mpr hh)
    have hh := hp (phaseL1 (Θ j) hφ.ofReal) (Or.inr ⟨j,rfl⟩)
    rw [dist_zero_left] at hh
    rw [oscillatoryMoment_fourier (Θ j) hφ n,Real.norm_eq_abs]
    exact (Complex.abs_re_le_norm _).trans hh.le
  · intro n hn
    have hp : ∀f∈K,dist (0:ℂ) (fourierL1 f (scaledFrequency n))<ε := by
      by_contra hh
      exact hn (hfinite.mem_toFinset.mpr hh)
    have hh := hp (phaseL1 Ψ hφ.ofReal) (Or.inl rfl)
    rw [dist_zero_left] at hh
    rw [oscillatoryMoment_fourier Ψ hφ n,Real.norm_eq_abs]
    exact (Complex.abs_re_le_norm _).trans hh.le

end polyak.Global.Symbols
