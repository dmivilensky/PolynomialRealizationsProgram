import nesterov.Layer.SpreadWitnessPhase
import nesterov.Layer.SpreadWitnessContinuous
import nesterov.Layer.SpreadWitnessSmallness
import nesterov.Layer.SpreadWitnessLagOne
import nesterov.Spread.Kernel
import nesterov.Spread.FourierMargin

/-! The original moving-band little-o hypotheses imply all quantitative
inputs of the proved general half-step spreading construction. -/
namespace nesterov.TwoStep
noncomputable section
open Filter Set Spectral Phase
open scoped Topology

namespace Spread

def sourceBand (K : ℕ) (s : ℝ) : Set ℝ :=
  Icc (nesterov.Spread.centerAngle K-s*nesterov.Spread.centerAngle K)
    (nesterov.Spread.centerAngle K+s*nesterov.Spread.centerAngle K)

theorem sourceBand_eq (K : ℕ) (s : ℝ) :
    sourceBand K s=band s (nesterov.Spread.centerAngle K) := by
  unfold sourceBand band
  congr 1 <;> ring

structure PreparedBand (a : SymbolPair) (t : ℝ) (K : ℕ) (s η : ℝ) where
  d : ℝ
  R : C(Frequency,ℝ)
  Θ : C(Frequency,ℝ)
  negative_t : t<0
  period_ge : 3≤K
  eta_pos : 0<η
  eta_lt_one : η<1
  defect_nonneg : 0≤d
  defect_le_margin : d≤nesterov.Spread.bandMargin nesterov.Spread.canonicalKernel K s/2
  small : nesterov.Spread.canonicalKernel.longConstant*
    (|t|/(nesterov.Spread.bandMargin nesterov.Spread.canonicalKernel K s*
      (s*nesterov.Spread.centerAngle K)))^2+d<Real.sqrt η/8
  radius_pos : ∀ c : Frequency,0<R c
  polar : ∀ c : Frequency,Real.arccos c∈sourceBand K s →
    (g a c:ℂ)-2*Complex.I*skew a c=(R c:ℂ)*Complex.exp (-(Θ c:ℂ)*Complex.I)
  defect : ∀ c : Frequency,Real.arccos c∈sourceBand K s → |Real.arccos c-2*Θ c|≤d
  first_lag : ∀ c : Frequency,Real.arccos c∈sourceBand K s →
    η*Real.exp t*Real.sinh |t| *g a c<nesterov.Spread.lagOneSymbol a t c

end Spread

namespace Scaling
variable {A : Type*} {l : Filter A} {θ y τ : ℝ} (F : Scaling A l θ y τ)

theorem prepare_spread_band {c s lam : ℝ} {K : A→ℕ} {M X : A→ℝ}
    (hc0 : 0<c) (hc : c<θ/2) (hτ : 0<τ)
    (hs0 : 0<s) (hs1 : s≤nesterov.Spread.canonicalKernel.s1) (hlam : 0<lam)
    (hK : ∀ᶠ a in l,3≤K a)
    (hM : ∀ᶠ a in l,∀ ω∈Spread.band s (nesterov.Spread.centerAngle (K a)),
      |mixedPolynomial (F.tuning a).beta (F.tuning a).tau
        ((F.tuning a).stepSize*F.epsilon a^2) (F.tuning a).stepSize
        (1-c*F.epsilon a) (1-Real.cos ω)|≤M a)
    (hX : ∀ᶠ a in l,∀ ω∈Spread.band s (nesterov.Spread.centerAngle (K a)),
      ‖Spread.product (F.tuning a) (F.epsilon a^2) 1 (1-c*F.epsilon a) ω‖≤X a)
    (hH : ∀ᶠ a in l,∀ ω∈Spread.band s (nesterov.Spread.centerAngle (K a)),
      ((1-circle (1-c*F.epsilon a) ω)*
        Spread.product (F.tuning a) (F.epsilon a^2) 1 (1-c*F.epsilon a) ω).re≤
          -lam*F.epsilon a*X a)
    (hεscale : Tendsto (fun a=>F.epsilon a/Spread.cubicScale
      (Spread.xiMax s (nesterov.Spread.centerAngle (K a)))) l (𝓝 0))
    (hMscale : Tendsto (fun a=>M a/Spread.cubicScale
      (Spread.xiMax s (nesterov.Spread.centerAngle (K a)))) l (𝓝 0)) :
    ∃ η : ℝ,0<η ∧ η<1 ∧ ∀ᶠ a in l,
      Nonempty (Spread.PreparedBand
        (Spread.pair (F.tuning a) (F.epsilon a^2) 1 (1-c*F.epsilon a))
        (Real.log (1-c*F.epsilon a)) (K a) s η) := by
  let ω₀ : A→ℝ := fun a=>nesterov.Spread.centerAngle (K a)
  have hs : s∈Ioc (0:ℝ) (1/6) := ⟨hs0,hs1.trans nesterov.Spread.canonicalKernel.s1_le_one_sixth⟩
  have hω₀ : ∀ᶠ a in l,ω₀ a∈Ioc (0:ℝ) (2*Real.pi/3) :=
    hK.mono fun _ ha=>⟨nesterov.Spread.centerAngle_pos ha,nesterov.Spread.centerAngle_le ha⟩
  have hMpos : ∀ᶠ a in l,0≤M a := by
    filter_upwards [hM,hω₀] with a hM hω
    have hm : ω₀ a∈Spread.band s (ω₀ a) := by
      constructor <;> nlinarith [mul_pos hs0 hω.1]
    exact (abs_nonneg _).trans (hM _ hm)
  have hxp : ∀ᶠ a in l,0<Spread.xiMax s (ω₀ a) := hω₀.mono fun _ ha=>Spread.xiMax_pos hs ha
  have hx2 : ∀ᶠ a in l,Spread.xiMax s (ω₀ a)≤2 := by
    exact Eventually.of_forall fun a=>by unfold Spread.xiMax;linarith [Real.neg_one_le_cos ((1+s)*ω₀ a)]
  have hMratio := Spread.ratio_xi_of_cubic hMpos hxp hx2 hMscale
  obtain ⟨α,hα,hphase⟩ := F.spread_phase_eventually hc hτ hs hω₀ hM hMratio
  let η : ℝ := min (1/2) (lam/(2*c))
  have hη : 0<η := lt_min (by norm_num) (div_pos hlam (by positivity))
  have hη1 : η<1 := (min_le_left _ _).trans_lt (by norm_num)
  have hηc : η*c≤lam/2 := by
    have hh := (le_div_iff₀ (show 0<2*c by positivity)).mp (min_le_right (1/2:ℝ) (lam/(2*c)))
    change η*(2*c)≤lam at hh
    linarith
  have hsmall := Spread.spread_smallness_of_cubic nesterov.Spread.canonicalKernel.ck_pos hs
    hc0 hα hη F.epsilon_zero F.epsilon_pos hMpos hω₀ hεscale hMscale
      (C:=nesterov.Spread.canonicalKernel.longConstant)
  have hcsmall : ∀ᶠ a in l,c*F.epsilon a<1 := by
    have ht : Tendsto (fun a=>c*F.epsilon a) l (𝓝 0) := by simpa using F.epsilon_zero.const_mul c
    exact ht.eventually (eventually_lt_nhds (by norm_num : (0:ℝ)<1))
  refine ⟨η,hη,hη1,?_⟩
  filter_upwards [hK,hω₀,hphase,hsmall,hX,hH,F.epsilon_pos,
    F.epsilon_zero.eventually (eventually_lt_nhds (by norm_num : (0:ℝ)<1)),hcsmall]
    with a hK hω hphase hsmall hX hH he he1 hcε
  let r := 1-c*F.epsilon a
  let b := Spread.pair (F.tuning a) (F.epsilon a^2) 1 r
  have hr : 0<r := by dsimp [r];linarith
  have hr1 : r<1 := by dsimp [r];nlinarith [mul_pos hc0 he]
  have hμL : F.epsilon a^2<1 := by nlinarith
  have hg : ∀ ω∈Spread.band s (ω₀ a),0<g b (frequency ω) := fun ω hω=>(hphase.2 ω hω).1
  have hlohi : (1-s)*ω₀ a≤(1+s)*ω₀ a := by nlinarith [mul_pos hs0 hω.1]
  obtain ⟨R,Θ,hR,hagree⟩ := Spread.exists_continuous_polar b hlohi hg
  refine ⟨{
    d := Real.pi^2*M a/(α*ω₀ a)
    R := R
    Θ := Θ
    negative_t := Real.log_neg hr hr1
    period_ge := hK
    eta_pos := hη
    eta_lt_one := hη1
    defect_nonneg := div_nonneg (mul_nonneg (sq_nonneg _) hphase.1) (mul_pos hα hω.1).le
    defect_le_margin := by simpa only [nesterov.Spread.bandMargin,Spread.bandMargin,ω₀] using hsmall.1
    small := by simpa only [nesterov.Spread.bandMargin,Spread.bandMargin,ω₀] using hsmall.2
    radius_pos := hR
    polar := ?_
    defect := ?_
    first_lag := ?_ }⟩
  · intro z hz
    have hband : Real.arccos z∈Spread.band s (ω₀ a) := by
      simpa only [Spread.sourceBand_eq] using hz
    exact Spread.continuous_polar_eq hagree hband
  · intro z hz
    have hband : Real.arccos z∈Spread.band s (ω₀ a) := by
      simpa only [Spread.sourceBand_eq] using hz
    rw [(hagree z hband).2]
    have hh := (hphase.2 (Real.arccos z) hband).2.2
    simpa only [Spread.frequency_arccos] using hh
  · intro z hz
    have hband : Real.arccos z∈Spread.band s (ω₀ a) := by
      simpa only [Spread.sourceBand_eq] using hz
    have hmem := Spread.band_mem_Ioo hs hω hband
    have hpos := (hphase.2 (Real.arccos z) hband).1
    rw [Spread.frequency_arccos] at hpos
    have hprod := hX (Real.arccos z) hband
    have hnegative := hH (Real.arccos z) hband
    have hcoord := (Spread.coordinates (F.tuning a) hμL hr ⟨hmem.1.le,hmem.2.le⟩).1
    rw [Spread.frequency_arccos] at hcoord
    have hne : Spread.product (F.tuning a) (F.epsilon a^2) 1 r (Real.arccos z)≠0 := by
      intro hz
      rw [hz] at hcoord
      simp only [Complex.zero_re,mul_zero] at hcoord
      exact hpos.ne' hcoord
    have hXpos : 0<X a := (norm_pos_iff.mpr hne).trans_le hprod
    have hh := Spread.first_lag_pointwise (F.tuning a) hμL he hc0 hr hη hlam hXpos hηc
      ⟨hmem.1.le,hmem.2.le⟩ (by simpa only [Spread.frequency_arccos] using hpos.le) hprod hnegative
    simpa only [Spread.frequency_arccos] using hh

end Scaling
end
end nesterov.TwoStep
