import nesterov.Spread.PhaseLags
import nesterov.Spread.Weighted
import nesterov.Layer.SpreadWitnessEnvelope

/-! The quantitative hypotheses of the source half-step spreading lemma. -/
namespace nesterov.Spread
noncomputable section
open MeasureTheory Spectral Set

def bandCarrier (K : ℕ) (s : ℝ) : Set Frequency :=
  {c | Real.arccos (c:ℝ)∈Icc (centerAngle K-s*centerAngle K) (centerAngle K+s*centerAngle K)}

structure HalfStepData where
  pair : SymbolPair
  t : ℝ
  K : ℕ
  s : ℝ
  eta : ℝ
  defect : ℝ
  radial : C(Frequency,ℝ)
  phase : C(Frequency,ℝ)
  t_neg : t<0
  K_ge : 3≤K
  s_pos : 0<s
  s_le : s≤canonicalKernel.s1
  eta_pos : 0<eta
  eta_lt : eta<1
  defect_nonneg : 0≤defect
  defect_le : defect≤bandMargin canonicalKernel K s/2
  small : canonicalKernel.longConstant*(|t|/(bandMargin canonicalKernel K s*(s*centerAngle K)))^2+
    defect<Real.sqrt eta/8
  radial_pos : ∀ c,0<radial c
  polar : ∀ c∈bandCarrier K s,(g pair c:ℂ)-2*Complex.I*skew pair c=
    (radial c:ℂ)*Complex.exp (-(phase c:ℂ)*Complex.I)
  phase_defect : ∀ c∈bandCarrier K s,|Real.arccos (c:ℝ)-2*phase c|≤defect

namespace HalfStepData
variable (D : HalfStepData)

def base : Spectrum := bandSpectrum (centerAngle D.K) (D.s*centerAngle D.K)

def probability : Spectrum := reciprocalProbability D.radial D.base D.radial_pos

def charge : ℝ := -(1-D.eta)*meanG D.probability D.pair

theorem base_carrier : ∀ᵐ (c : Frequency) ∂(D.base:Measure Frequency),c∈bandCarrier D.K D.s := by
  obtain ⟨hl,hu⟩ := band_endpoints D.K_ge D.s_pos D.s_le
  exact bandSpectrum_ae_angles _ (mul_pos D.s_pos (centerAngle_pos D.K_ge)) hl hu

theorem probability_carrier :
    ∀ᵐ (c : Frequency) ∂(D.probability:Measure Frequency),c∈bandCarrier D.K D.s :=
  reciprocalProbability_ae D.radial D.base D.radial_pos D.base_carrier

theorem base_polar : ∀ᵐ (c : Frequency) ∂(D.base:Measure Frequency),
    (g D.pair c:ℂ)-2*Complex.I*skew D.pair c=
      (D.radial c:ℂ)*Complex.exp (-(D.phase c:ℂ)*Complex.I) :=
  D.base_carrier.mono fun c hc=>D.polar c hc

theorem cone {c : Frequency} (hc : c∈bandCarrier D.K D.s) :
    D.phase c∈Ioo (0:ℝ) (5*Real.pi/12) ∧ 1/4<Real.cos (D.phase c) := by
  have hs6 := D.s_le.trans canonicalKernel.s1_le_one_sixth
  have hdm4 := bandMargin_le_quarter canonicalKernel D.K D.s
  have hdmω := bandMargin_le_angle canonicalKernel D.K D.s
  have hb : Real.arccos (c:ℝ)∈TwoStep.Spread.band D.s (centerAngle D.K) := by
    constructor <;> nlinarith [hc.1,hc.2]
  exact phase_envelope ⟨D.s_pos,hs6⟩ ⟨centerAngle_pos D.K_ge,centerAngle_le D.K_ge⟩ hb
    (by linarith [D.defect_le]) (by linarith [D.defect_le]) (D.phase_defect c hc)

theorem point_g_pos {c : Frequency} (hc : c∈bandCarrier D.K D.s) : 0<g D.pair c :=
  (polar_cone_bound (D.polar c hc) (D.radial_pos c) (D.cone hc).2).1

theorem point_osc_bounds {c : Frequency} (hc : c∈bandCarrier D.K D.s) (n : ℕ) :
    lowerOsc D.pair n c≤4*g D.pair c ∧ upperOsc D.pair n c≤4*g D.pair c := by
  have hcone := (polar_cone_bound (D.polar c hc) (D.radial_pos c) (D.cone hc).2).2
  rw [lowerOsc_polar D.pair D.radial D.phase (D.polar c hc),
    upperOsc_polar D.pair D.radial D.phase (D.polar c hc)]
  constructor
  · have hh := mul_le_mul_of_nonneg_left (Real.cos_le_one ((n:ℝ)*Real.arccos c-D.phase c))
      (D.radial_pos c).le
    nlinarith
  · have hh := mul_le_mul_of_nonneg_left (Real.cos_le_one ((n:ℝ)*Real.arccos c+D.phase c))
      (D.radial_pos c).le
    nlinarith

end HalfStepData
end
end nesterov.Spread
