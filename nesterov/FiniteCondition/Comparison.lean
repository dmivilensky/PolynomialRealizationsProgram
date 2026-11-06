import nesterov.FiniteCondition.TongueFree
import nesterov.IQC.CertificateTransport
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Cotangent

/-!
Additional library result: the same finite certificate transfers under
cotangent ordering. Its nonnegative diagonal replaces the equivalent primal
change of spectral density in the source proof.
-/
namespace nesterov.FiniteCondition
noncomputable section
open Spectral Duality Phase Set
open scoped BigOperators

def imaginaryCoefficient {a : SymbolPair} (cert : Duality.StrictCertificate a 0) (c : Frequency) : ℝ :=
  ∑ n∈cert.lags,2*(cert.β n-cert.α n)*Real.sin (n*Real.arccos c)

theorem certificate_split {a : SymbolPair} (cert : Duality.StrictCertificate a 0)
    (b : SymbolPair) (c : Frequency) :
    symbol b 0 cert.lags cert.α cert.β cert.γplus cert.γminus c=
      g b c*IQC.diagonal cert c+skew b c*imaginaryCoefficient cert c := by
  calc
    _=(∑ n∈cert.lags,(g b c*((cert.α n+cert.β n)*(1-Real.cos (n*Real.arccos c)))+
      skew b c*(2*(cert.β n-cert.α n)*Real.sin (n*Real.arccos c))))+
        (cert.γplus+cert.γminus)*g b c := by
      unfold symbol
      congr 1
      apply Finset.sum_congr rfl
      intro n _
      simp only [lagA,lagB,mul_zero,Real.cosh_zero]
      ring
    _=_ := by
      rw [Finset.sum_add_distrib,←Finset.mul_sum,←Finset.mul_sum]
      simp only [IQC.diagonal,mul_zero,Real.cosh_zero,imaginaryCoefficient]
      ring

theorem transfer_certificate {a₁ a₂ : SymbolPair} (cert : Duality.StrictCertificate a₂ 0)
    (hend : ∀ c : Frequency,(c:ℝ)=-1 ∨ (c:ℝ)=1 → g a₁ c<0 ∧ skew a₁ c=0)
    (hs₁ : ∀ c : Frequency,(c:ℝ)∈Ioo (-1:ℝ) 1 → 0<skew a₁ c)
    (hs₂ : ∀ c : Frequency,(c:ℝ)∈Ioo (-1:ℝ) 1 → 0<skew a₂ c)
    (hord : ∀ c : Frequency,(c:ℝ)∈Ioo (-1:ℝ) 1 →
      g a₁ c/(2*skew a₁ c)≤g a₂ c/(2*skew a₂ c)) :
    Nonempty (Duality.StrictCertificate a₁ 0) := by
  obtain ⟨d,hd,hdb⟩ := IQC.exists_diagonal_lower cert
  apply certificate_of_negative a₁ 0 cert.lags cert.α cert.β cert.γplus cert.γminus
    cert.positive_lag cert.α_nonneg cert.β_nonneg cert.γplus_nonneg cert.γminus_nonneg cert.cancel
  intro c
  have hA : 0<IQC.diagonal cert c := hd.trans_le (hdb c)
  by_cases he : (c:ℝ)=-1 ∨ (c:ℝ)=1
  · obtain ⟨hg,hs⟩ := hend c he
    rw [certificate_split cert a₁,hs,zero_mul,add_zero]
    exact mul_neg_of_neg_of_pos hg hA
  · have hc : (c:ℝ)∈Ioo (-1:ℝ) 1 := by
      constructor
      · exact lt_of_le_of_ne c.2.1 (fun hh=>he (Or.inl hh.symm))
      · exact lt_of_le_of_ne c.2.2 (fun hh=>he (Or.inr hh))
    have h₁ := hs₁ c hc
    have h₂ := hs₂ c hc
    have hg : g a₁ c*(2*skew a₂ c)≤g a₂ c*(2*skew a₁ c) :=
      (div_le_div_iff₀ (by positivity) (by positivity)).mp (hord c hc)
    have hdiag := mul_le_mul_of_nonneg_right hg hA.le
    have hsigma :
        symbol a₁ 0 cert.lags cert.α cert.β cert.γplus cert.γminus c*skew a₂ c≤
          symbol a₂ 0 cert.lags cert.α cert.β cert.γplus cert.γminus c*skew a₁ c := by
      rw [certificate_split cert a₁,certificate_split cert a₂]
      nlinarith only [hdiag]
    have hneg : symbol a₂ 0 cert.lags cert.α cert.β cert.γplus cert.γminus c<0 :=
      (cert.strict c).trans_lt (neg_neg_of_pos cert.ε_pos)
    have hm := hsigma.trans_lt (mul_neg_of_neg_of_pos hneg h₁)
    exact neg_of_mul_neg_left hm h₂.le

theorem cot_angle {g s : ℝ} (hs : 0<s) : Real.cot (Phase.angle g s)=g/(2*s) := by
  have hM : Phase.magnitude g s≠0 := (Phase.magnitude_pos (Or.inr hs.ne')).ne'
  rw [Real.cot_eq_cos_div_sin]
  calc
    _=(Phase.magnitude g s*Real.cos (Phase.angle g s))/
        (Phase.magnitude g s*Real.sin (Phase.angle g s)) := by
      rw [mul_div_mul_left _ _ hM]
    _=_ := by rw [Phase.magnitude_cos_angle,Phase.magnitude_sin_angle]

theorem momentum_skew_endpoint (q : Momentum.Tuning) {μ L : ℝ} (hμL : μ<L) :
    skew ((Momentum.method q.beta q.tau q.stepSize q.step_pos.ne').symbolPair μ L 0) endpoint=0 := by
  have hf := momentum_factor (β:=q.beta) (τ:=q.tau) hμL q.step_pos.ne' 0 endpoint
  have hz : polyak.Waves.z 0 (Real.arccos (endpoint:Frequency))=1 := by
    simp [endpoint,polyak.Waves.z]
  rw [hz,Quadratic.characteristic_one,Quadratic.characteristic_one] at hf
  have hi := congrArg Complex.im hf
  simp only [Complex.star_def,Complex.conj_ofReal] at hi
  simp only [Complex.sub_im,Complex.ofReal_im,Complex.mul_im,Complex.mul_re,
    Complex.ofReal_re,Complex.neg_im,Complex.neg_re,Complex.I_re,Complex.I_im,
    mul_zero,sub_zero,zero_sub] at hi
  norm_num only [show (2:ℂ).re=(2:ℝ) from rfl] at hi
  linarith

/-- The source comparison principle, with every original stability and curvature hypothesis. -/
theorem rate_comparison (q₁ q₂ : Momentum.Tuning) {μ₁ L₁ μ₂ L₂ : ℝ}
    (hμ₁ : 0<μ₁) (hμL₁ : μ₁<L₁) (hs₁ : q₁.Stable μ₁ L₁)
    (hμ₂ : 0<μ₂) (hμL₂ : μ₂<L₂) (hs₂ : q₂.Stable μ₂ L₂)
    (hord : ∀ ω∈Ioo (0:ℝ) Real.pi,
      Real.cot (momentumAngle q₁ μ₁ L₁ ω)≤Real.cot (momentumAngle q₂ μ₂ L₂ ω))
    (hr₂ : Momentum.momentumRate q₂.beta q₂.tau q₂.stepSize q₂.step_pos.ne' μ₂ L₂<1) :
    Momentum.momentumRate q₁.beta q₁.tau q₁.stepSize q₁.step_pos.ne' μ₁ L₁<1 := by
  let M₁ := Momentum.method q₁.beta q₁.tau q₁.stepSize q₁.step_pos.ne'
  let M₂ := Momentum.method q₂.beta q₂.tau q₂.stepSize q₂.step_pos.ne'
  let a₁ := M₁.symbolPair μ₁ L₁ 0
  let a₂ := M₂.symbolPair μ₂ L₂ 0
  have hc₂ : IQC.middleRadius M₂ μ₂ L₂<Real.exp 0 := by
    simpa using middleRadius_lt_one_of_stable q₂ hμ₂ hμL₂ hs₂
  obtain ⟨cert⟩ := (Closure.certificate_iff_rate_lt M₂ hμ₂ hμL₂ hc₂).mpr (by simpa only [Real.exp_zero,Momentum.momentumRate,M₂] using hr₂)
  have hsk₁ (c : Frequency) (hc : (c:ℝ)∈Ioo (-1:ℝ) 1) : 0<skew a₁ c := by
    have hw : Real.arccos (c:ℝ)∈Ioo (0:ℝ) Real.pi :=
      ⟨Real.arccos_pos.mpr hc.2,Real.arccos_lt_pi.mpr hc.1⟩
    have he : frequency (Real.arccos (c:ℝ))=c := by
      apply Subtype.ext
      exact Real.cos_arccos c.2.1 c.2.2
    simpa only [he] using momentum_skew_pos q₁ hμL₁ hw
  have hsk₂ (c : Frequency) (hc : (c:ℝ)∈Ioo (-1:ℝ) 1) : 0<skew a₂ c := by
    have hw : Real.arccos (c:ℝ)∈Ioo (0:ℝ) Real.pi :=
      ⟨Real.arccos_pos.mpr hc.2,Real.arccos_lt_pi.mpr hc.1⟩
    have he : frequency (Real.arccos (c:ℝ))=c := by
      apply Subtype.ext
      exact Real.cos_arccos c.2.1 c.2.2
    simpa only [he] using momentum_skew_pos q₂ hμL₂ hw
  obtain ⟨cert₁⟩ := transfer_certificate cert (a₁:=a₁) (fun c hc=>by
    rcases hc with hc|hc
    · have he : c=frequency Real.pi := by apply Subtype.ext;simpa [frequency] using hc
      rw [he]
      exact momentum_endpoint_pair q₁ hμ₁ hμL₁ hs₁
    · have he : c=endpoint := Subtype.ext hc
      rw [he]
      exact ⟨stationary_g_endpoint M₁ hμ₁ hμL₁,momentum_skew_endpoint q₁ hμL₁⟩)
    hsk₁ hsk₂ (fun c hc=>by
      have hw : Real.arccos (c:ℝ)∈Ioo (0:ℝ) Real.pi :=
        ⟨Real.arccos_pos.mpr hc.2,Real.arccos_lt_pi.mpr hc.1⟩
      have he : frequency (Real.arccos (c:ℝ))=c := by
        apply Subtype.ext
        exact Real.cos_arccos c.2.1 c.2.2
      have hh := hord (Real.arccos c) hw
      have hh' : Real.cot (angle (g a₁ c) (skew a₁ c))≤Real.cot (angle (g a₂ c) (skew a₂ c)) := by
        simpa only [momentumAngle,he] using hh
      rwa [cot_angle (hsk₁ c hc),cot_angle (hsk₂ c hc)] at hh')
  have hc₁ : IQC.middleRadius M₁ μ₁ L₁<Real.exp 0 := by
    simpa using middleRadius_lt_one_of_stable q₁ hμ₁ hμL₁ hs₁
  simpa only [Real.exp_zero,Momentum.momentumRate,M₁] using (Closure.certificate_iff_rate_lt M₁ hμ₁ hμL₁ hc₁).mp ⟨cert₁⟩

end
end nesterov.FiniteCondition
