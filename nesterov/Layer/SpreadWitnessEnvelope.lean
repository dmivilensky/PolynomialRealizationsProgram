import nesterov.Layer.SpreadWitnessGeometry
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Analysis.Real.Pi.Bounds

/-! The half-step phase stays in a fixed positive-cosine cone; continuous
band functions admit globally continuous clipped extensions. -/
namespace nesterov.Spread
noncomputable section
open Set Spectral

theorem quarter_lt_cos_five_pi_twelve : (1/4:ℝ)<Real.cos (5*Real.pi/12) := by
  have h2 := Real.sq_sqrt (by norm_num : (0:ℝ)≤2)
  have h6 := Real.sq_sqrt (by norm_num : (0:ℝ)≤6)
  have h2lt : Real.sqrt 2<3/2 := by nlinarith [Real.sqrt_nonneg (2:ℝ)]
  have h6gt : 1+Real.sqrt 2<Real.sqrt 6 := by
    apply (sq_lt_sq₀ (show 0≤1+Real.sqrt 2 by positivity) (Real.sqrt_nonneg 6)).mp
    nlinarith
  have hprod : Real.sqrt 2*Real.sqrt 3=Real.sqrt 6 := by
    rw [←Real.sqrt_mul (by norm_num : (0:ℝ)≤2)]
    norm_num
  have hcos : Real.cos (5*Real.pi/12)=(Real.sqrt 6-Real.sqrt 2)/4 := by
    calc
      _=(Real.sqrt 2*Real.sqrt 3-Real.sqrt 2)/4 := by
        rw [show 5*Real.pi/12=Real.pi/4+Real.pi/6 by ring,Real.cos_add,
          Real.cos_pi_div_four,Real.cos_pi_div_six,Real.sin_pi_div_four,Real.sin_pi_div_six]
        ring
      _=_ := by rw [hprod]
  rw [hcos]
  linarith

theorem phase_envelope {s ω₀ ω Θ d : ℝ} (hs : s∈Ioc (0:ℝ) (1/6))
    (hω₀ : ω₀∈Ioc (0:ℝ) (2*Real.pi/3))
    (hω : ω∈TwoStep.Spread.band s ω₀)
    (hd : d≤1/8) (hdω : d≤ω₀^2/12) (hphase : |ω-2*Θ|≤d) :
    Θ∈Ioo (0:ℝ) (5*Real.pi/12) ∧ 1/4<Real.cos Θ := by
  have hφ := abs_le.mp hphase
  have hωfour : ω₀<4 := by linarith [hω₀.2,Real.pi_lt_four]
  have hsq : ω₀^2<4*ω₀ := by nlinarith [mul_pos hω₀.1 (sub_pos.mpr hωfour)]
  have hsω := mul_nonneg (show 0≤1/6-s by linarith [hs.2]) hω₀.1.le
  have hΘ0 : 0<Θ := by nlinarith [hω.1,hdω,hsω,hω₀.1,hφ.2]
  have hωmax : ω≤7*Real.pi/9 := by
    nlinarith [hω.2,hω₀.2,hsω]
  have hΘmax : Θ<5*Real.pi/12 := by linarith [hφ.1,hd,Real.pi_gt_three]
  refine ⟨⟨hΘ0,hΘmax⟩,?_⟩
  have hc := Real.cos_lt_cos_of_nonneg_of_le_pi hΘ0.le
    (by linarith [Real.pi_pos] : 5*Real.pi/12≤Real.pi) hΘmax
  exact quarter_lt_cos_five_pi_twelve.trans hc

theorem polar_cone_bound {g s R Θ : ℝ}
    (hpolar : (g:ℂ)-2*Complex.I*s=(R:ℂ)*Complex.exp (-(Θ:ℂ)*Complex.I))
    (hR : 0<R) (hΘ : 1/4<Real.cos Θ) : 0<g ∧ R<4*g := by
  have hre := congrArg Complex.re hpolar
  rw [Complex.exp_mul_I] at hre
  have hg : g=R*Real.cos Θ := by
    simpa [←Complex.ofReal_cos,←Complex.ofReal_sin] using hre
  rw [hg]
  constructor
  · exact mul_pos hR (by linarith)
  · nlinarith [mul_pos hR (show 0<Real.cos Θ-1/4 by linarith)]

def extendBand {a b : ℝ} (hab : a≤b) (f : ℝ→ℝ) (hf : ContinuousOn f (Icc a b)) :
    C(Frequency,ℝ) where
  toFun c := f (projIcc a b hab (Real.arccos c))
  continuous_toFun := by
    have hc : Continuous (fun c : Frequency=>projIcc a b hab (Real.arccos c)) :=
      continuous_projIcc.comp (Real.continuous_arccos.comp continuous_subtype_val)
    exact hf.domRestrict.comp hc

theorem extendBand_eq {a b : ℝ} (hab : a≤b) (f : ℝ→ℝ)
    (hf : ContinuousOn f (Icc a b)) {c : Frequency} (hc : Real.arccos c∈Icc a b) :
    extendBand hab f hf c=f (Real.arccos c) := by
  change f (projIcc a b hab (Real.arccos c))=f (Real.arccos c)
  rw [projIcc_of_mem hab hc]

theorem extendBand_positive {a b : ℝ} (hab : a≤b) (f : ℝ→ℝ)
    (hf : ContinuousOn f (Icc a b)) (hpos : ∀ ω∈Icc a b,0<f ω) (c : Frequency) :
    0<extendBand hab f hf c :=
  hpos _ (projIcc a b hab (Real.arccos c)).property

end
end nesterov.Spread
