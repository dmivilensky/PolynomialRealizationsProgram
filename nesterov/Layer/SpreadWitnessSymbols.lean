import nesterov.Layer.SpreadWitnessGeometry
import nesterov.TwoStep.ScaledCoefficients
import nesterov.TwoStep.MixedCriterion

/-! Exact symbol identities and quantitative phase control on the spread band. -/
namespace nesterov.TwoStep.Spread
noncomputable section
open Set Spectral Phase

def product (q : Momentum.Tuning) (μ L r ω : ℝ) : ℂ :=
  Quadratic.characteristic q.beta q.tau q.stepSize μ (circle r ω)*
    star (Quadratic.characteristic q.beta q.tau q.stepSize L (circle r ω))

def pair (q : Momentum.Tuning) (μ L r : ℝ) : SymbolPair :=
  (Momentum.method q.beta q.tau q.stepSize q.step_pos.ne').symbolPair μ L (Real.log r)

def scale (q : Momentum.Tuning) (μ L : ℝ) : ℝ := 4/(q.stepSize^2*(L-μ)^2)

theorem scale_pos (q : Momentum.Tuning) {μ L : ℝ} (hμL : μ<L) :
    0<scale q μ L := div_pos (by norm_num)
  (mul_pos (sq_pos_of_pos q.step_pos) (sq_pos_of_pos (sub_pos.mpr hμL)))

theorem characteristic_normalized (β τ h lam : ℝ) (z : ℂ) :
    Quadratic.characteristic β τ h lam z=Quadratic.characteristic β τ 1 (h*lam) z := by
  simp only [Quadratic.characteristic]
  push_cast
  ring

theorem product_normalized (q : Momentum.Tuning) (μ L r ω : ℝ) :
    product q μ L r ω=
      Quadratic.characteristic q.beta q.tau 1 (q.stepSize*μ) (circle r ω)*
        star (Quadratic.characteristic q.beta q.tau 1 (q.stepSize*L) (circle r ω)) := by
  unfold product
  rw [characteristic_normalized q.beta q.tau q.stepSize μ,
    characteristic_normalized q.beta q.tau q.stepSize L]

theorem factor (q : Momentum.Tuning) {μ L r ω : ℝ} (hμL : μ<L) (hr : 0<r)
    (hω : ω∈Icc (0:ℝ) Real.pi) :
    (g (pair q μ L r) (frequency ω):ℂ)-2*Complex.I*skew (pair q μ L r) (frequency ω)=
      -(scale q μ L:ℂ)*product q μ L r ω := by
  have hh := momentum_factor (β:=q.beta) (τ:=q.tau) hμL q.step_pos.ne'
    (Real.log r) (frequency ω)
  rw [arccos_frequency hω,wave_log_radius hr] at hh
  simpa only [pair,scale,product,mul_assoc] using hh

theorem coordinates (q : Momentum.Tuning) {μ L r ω : ℝ} (hμL : μ<L) (hr : 0<r)
    (hω : ω∈Icc (0:ℝ) Real.pi) :
    g (pair q μ L r) (frequency ω)= -scale q μ L*(product q μ L r ω).re ∧
      2*skew (pair q μ L r) (frequency ω)=scale q μ L*(product q μ L r ω).im := by
  have hh := factor q hμL hr hω
  have hre := congrArg Complex.re hh
  have him := congrArg Complex.im hh
  constructor
  · simpa using hre
  · norm_num at him
    linarith

theorem product_re_mixed (q : Momentum.Tuning) {μ L r ω : ℝ}
    (hω : ω∈Ioo (0:ℝ) Real.pi) :
    (product q μ L r ω).re=
      mixedPolynomial q.beta q.tau (q.stepSize*μ) (q.stepSize*L) r (1-Real.cos ω)-
      (2-(1-Real.cos ω))*(q.stepSize*L-q.stepSize*μ)*r*
        mixedBracket q.beta q.tau r (1-Real.cos ω) := by
  have hξ : 0<1-Real.cos ω := sub_pos.mpr (by
    simpa only [Real.cos_zero] using
      Real.cos_lt_cos_of_nonneg_of_le_pi (by norm_num : (0:ℝ)≤0) hω.2.le hω.1)
  have hm := mixed_symbol q.beta q.tau (q.stepSize*μ) (q.stepSize*L) r ω
  have hi := cross_im_circle q.beta q.tau (q.stepSize*μ) (q.stepSize*L) r ω
  rw [mul_assoc,←product_normalized] at hm
  rw [←product_normalized] at hi
  have hr : (circle 1 ω).re=Real.cos ω := by simpa using circle_pow_re 1 ω 1
  have him : (circle 1 ω).im=Real.sin ω := by simpa using circle_im 1 ω
  rw [Complex.mul_re,Complex.sub_re,Complex.sub_im,
    Complex.one_re,Complex.one_im,hr,him,hi] at hm
  have heq : (1-Real.cos ω)*((product q μ L r ω).re-
      mixedPolynomial q.beta q.tau (q.stepSize*μ) (q.stepSize*L) r (1-Real.cos ω)+
      (2-(1-Real.cos ω))*(q.stepSize*L-q.stepSize*μ)*r*
        mixedBracket q.beta q.tau r (1-Real.cos ω))=0 := by
    linear_combination hm-
      (q.stepSize*L-q.stepSize*μ)*r*mixedBracket q.beta q.tau r (1-Real.cos ω)*
        (Real.sin_sq_add_cos_sq ω)
  have hz := (mul_eq_zero.mp heq).resolve_left hξ.ne'
  linarith

/-- Small mixed symbol forces the source half-step phase defect to be small.
The common positive characteristic normalization cancels exactly. -/
theorem phase_defect_bound {g₀ s₀ k a ω M : ℝ} {B : ℂ}
    (hω : ω∈Ioo (0:ℝ) Real.pi) (hk : 0<k) (ha : 0<a) (hs : 0<s₀)
    (hg : k*a*(1-Real.cos ω)≤g₀)
    (hf : (g₀:ℂ)-2*Complex.I*s₀= -(k:ℂ)*B)
    (hM : ((1-Complex.exp ((ω:ℂ)*Complex.I))*B).re=(1-Real.cos ω)*M) :
    |ω-2*angle g₀ s₀|≤Real.pi^2*|M|/(2*a*ω) := by
  have hξ : 0<1-Real.cos ω := sub_pos.mpr (by
    simpa only [Real.cos_zero] using
      Real.cos_lt_cos_of_nonneg_of_le_pi (by norm_num : (0:ℝ)≤0) hω.2.le hω.1)
  have hg0 : 0<g₀ := (mul_pos (mul_pos hk ha) hξ).trans_le hg
  have hθ := angle_pos_lt_pi (g:=g₀) hs
  have hθhi : angle g₀ s₀<Real.pi/2 :=
    Complex.arg_lt_pi_div_two_iff.mpr (Or.inl (by simpa only [mode_re] using hg0))
  have hδ : |(ω-2*angle g₀ s₀)/2|≤Real.pi/2 := by
    rw [abs_le]
    constructor <;> linarith [hω.1,hω.2,hθ.1,hθhi]
  have hsin := Real.mul_abs_le_abs_sin hδ
  have hdelta : |ω-2*angle g₀ s₀|≤Real.pi*|Real.sin ((ω-2*angle g₀ s₀)/2)| := by
    rw [abs_div,abs_of_pos (by norm_num : (0:ℝ)<2)] at hsin
    have hh := (div_le_iff₀ Real.pi_pos).mp (show
      |ω-2*angle g₀ s₀|/Real.pi≤|Real.sin ((ω-2*angle g₀ s₀)/2)| by
        convert hsin using 1; ring)
    nlinarith
  have hhalf : 0<Real.sin (ω/2) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hω.1]) (by linarith [hω.2,Real.pi_pos])
  have hωsin : ω≤Real.pi*Real.sin (ω/2) := by
    have hh := Real.mul_le_sin (x:=ω/2) (by linarith [hω.1]) (by linarith [hω.2])
    have he : (2/Real.pi)*(ω/2)=ω/Real.pi := by ring
    rw [he] at hh
    simpa only [mul_comm] using (div_le_iff₀ Real.pi_pos).mp hh
  have hR : k*a*(1-Real.cos ω)≤magnitude g₀ s₀ := hg.trans (by
    simpa only [magnitude,mode_re] using Complex.re_le_norm (mode g₀ s₀))
  have hdef := (complex_defect_phase g₀ s₀ ω).1
  have hscaled : ((1-Complex.exp ((ω:ℂ)*Complex.I))*
      ((g₀:ℂ)-2*Complex.I*s₀)).re= -k*((1-Real.cos ω)*M) := by
    rw [hf]
    rw [show (1-Complex.exp ((ω:ℂ)*Complex.I))*(-(k:ℂ)*B)=
      -(k:ℂ)*((1-Complex.exp ((ω:ℂ)*Complex.I))*B) by ring]
    simp only [Complex.mul_re,Complex.neg_re,Complex.neg_im,Complex.ofReal_re,
      Complex.ofReal_im,neg_zero,zero_mul,sub_zero,hM]
  have habs := congrArg abs (hdef.symm.trans hscaled)
  have hRpos := magnitude_pos (Or.inl hg0.ne' : g₀≠0 ∨ s₀≠0)
  simp only [abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2),abs_of_pos hRpos,
    abs_of_pos hhalf,abs_neg,abs_of_pos hk,abs_of_pos hξ] at habs
  have hterm : 2*a*Real.sin (ω/2)*|Real.sin ((ω-2*angle g₀ s₀)/2)|≤|M| := by
    apply (mul_le_mul_iff_right₀ (mul_pos hk hξ)).mp
    calc
      _=(k*a*(1-Real.cos ω))*(2*Real.sin (ω/2)*|Real.sin ((ω-2*angle g₀ s₀)/2)|) := by ring
      _≤magnitude g₀ s₀*(2*Real.sin (ω/2)*|Real.sin ((ω-2*angle g₀ s₀)/2)|) :=
        mul_le_mul_of_nonneg_right hR (by positivity)
      _=|M| *(k*(1-Real.cos ω)) := by nlinarith only [habs]
      _=k*(1-Real.cos ω)*|M| := by ring
  apply (le_div_iff₀ (mul_pos (mul_pos (by norm_num) ha) hω.1)).mpr
  calc
    _=(2*a*ω)*|ω-2*angle g₀ s₀| := by ring
    _≤(2*a*ω)*(Real.pi*|Real.sin ((ω-2*angle g₀ s₀)/2)|) :=
      mul_le_mul_of_nonneg_left hdelta (by positivity [hω.1])
    _≤Real.pi^2*(2*a*Real.sin (ω/2)*|Real.sin ((ω-2*angle g₀ s₀)/2)|) := by
      have hh := mul_le_mul_of_nonneg_right hωsin
        (show 0≤2*a*Real.pi*|Real.sin ((ω-2*angle g₀ s₀)/2)| by positivity)
      nlinarith only [hh]
    _≤Real.pi^2*|M| := mul_le_mul_of_nonneg_left hterm (sq_nonneg Real.pi)

end
end nesterov.TwoStep.Spread
