import nesterov.Spread.HalfStepData
import nesterov.Spread.Atomic

/-! The source half-step spread lemma, including every lag and finite atoms. -/
namespace nesterov.Spread
noncomputable section
open MeasureTheory Spectral Set
open scoped BigOperators NNReal

namespace HalfStepData
variable (D : HalfStepData)

theorem noncritical :
    0<meanG D.probability D.pair ∧ |D.charge|<meanG D.probability D.pair ∧
    (∀ n : ℕ,1≤n → 0<upperSlack D.pair D.t D.probability D.charge n) ∧
    (∀ n : ℕ,2≤n → 0<lowerSlack D.pair D.t D.probability D.charge n) := by
  have hdef := D.base_carrier.mono fun c hc=>D.phase_defect c hc
  obtain ⟨hG,hUpper,hLower⟩ := all_phase_lags D.K_ge D.s_pos D.s_le D.t_neg
    D.eta_pos D.eta_lt D.defect_nonneg D.defect_le D.small D.phase hdef
  change 0<phaseMean D.base D.phase at hG
  change ∀ n : ℕ,1≤n → phaseUpper D.base D.phase n<eMinus D.eta (n*|D.t|)*phaseMean D.base D.phase at hUpper
  change ∀ n : ℕ,2≤n → phaseLower D.base D.phase n<ePlus D.eta (n*|D.t|)*phaseMean D.base D.phase at hLower
  have hZ := reciprocalZ_pos D.radial D.base D.radial_pos
  have hmean : reciprocalZ D.radial D.base*meanG D.probability D.pair=phaseMean D.base D.phase :=
    weighted_meanG D.pair D.base D.radial D.phase D.radial_pos D.base_polar
  have hupper (n : ℕ) : reciprocalZ D.radial D.base*(∫ c,upperOsc D.pair n c ∂D.probability)=phaseUpper D.base D.phase n :=
    weighted_upperOsc D.pair D.base D.radial D.phase D.radial_pos D.base_polar n
  have hlower (n : ℕ) : reciprocalZ D.radial D.base*(∫ c,lowerOsc D.pair n c ∂D.probability)=phaseLower D.base D.phase n :=
    weighted_lowerOsc D.pair D.base D.radial D.phase D.radial_pos D.base_polar n
  have hmeanPos : 0<meanG D.probability D.pair := by
    apply (mul_pos_iff_of_pos_left hZ).mp
    rw [hmean]
    exact hG
  refine ⟨hmeanPos,extreme_charge_reserve D.eta_pos D.eta_lt hmeanPos,?_,?_⟩
  · intro n hn
    apply (mul_pos_iff_of_pos_left hZ).mp
    have he : reciprocalZ D.radial D.base*upperSlack D.pair D.t D.probability D.charge n=
        phaseMean D.base D.phase*eMinus D.eta (n*|D.t|)-phaseUpper D.base D.phase n := by
      rw [charge,upperSlack_extreme D.pair D.t_neg]
      calc
        _=(reciprocalZ D.radial D.base*meanG D.probability D.pair)*eMinus D.eta (n*|D.t|)-
          reciprocalZ D.radial D.base*(∫ c,upperOsc D.pair n c ∂D.probability) := by ring
        _=_ := by rw [hmean,hupper]
    rw [he]
    have hh := hUpper n hn
    nlinarith
  · intro n hn
    apply (mul_pos_iff_of_pos_left hZ).mp
    have he : reciprocalZ D.radial D.base*lowerSlack D.pair D.t D.probability D.charge n=
        phaseMean D.base D.phase*ePlus D.eta (n*|D.t|)-phaseLower D.base D.phase n := by
      rw [charge,lowerSlack_extreme D.pair D.t_neg]
      calc
        _=(reciprocalZ D.radial D.base*meanG D.probability D.pair)*ePlus D.eta (n*|D.t|)-
          reciprocalZ D.radial D.base*(∫ c,lowerOsc D.pair n c ∂D.probability) := by ring
        _=_ := by rw [hmean,hlower]
    rw [he]
    have hh := hLower n hn
    nlinarith

theorem feasible_of_first_lag
    (hfirst : D.eta*Real.exp D.t*Real.sinh |D.t| *meanG D.probability D.pair<
      ∫ c,lagOneSymbol D.pair D.t c ∂D.probability) :
    Feasible D.pair D.t D.probability D.charge := by
  obtain ⟨_,hC,hU,hL⟩ := D.noncritical
  refine ⟨hC.le,fun n hn=>⟨?_,(hU n hn).le⟩⟩
  by_cases h1 : n=1
  · subst n
    exact ((lowerSlack_one_pos_iff D.pair D.t_neg D.probability D.eta).mpr hfirst).le
  · exact (hL n (by omega)).le

theorem finite_of_first_lag
    (hfirst : D.eta*Real.exp D.t*Real.sinh |D.t| *meanG D.probability D.pair<
      ∫ c,lagOneSymbol D.pair D.t c ∂D.probability) :
    ∃ (J : Type) (_ : Fintype J) (w : J→ℝ≥0) (c : J→Frequency)
      (hw : ∑ j,w j=1), (∀ j,c j∈bandCarrier D.K D.s) ∧
      ∃ C : ℝ,Feasible D.pair D.t (finiteSpectrum w c hw) C ∧
        |C|<meanG (finiteSpectrum w c hw) D.pair := by
  obtain ⟨hG,_,hU,hL⟩ := D.noncritical
  apply exists_finite_of_strict D.pair D.t_neg D.eta_pos D.eta_lt D.probability
    (bandCarrier D.K D.s) D.probability_carrier
    (fun c hc=>D.point_g_pos hc) (fun c hc n=>D.point_osc_bounds hc n) hG
  intro n hn
  refine ⟨?_,hU n hn⟩
  by_cases h1 : n=1
  · subst n
    exact (lowerSlack_one_pos_iff D.pair D.t_neg D.probability D.eta).mpr hfirst
  · exact hL n (by omega)

theorem first_lag_of_pointwise
    (hfirst : ∀ c∈bandCarrier D.K D.s,
      D.eta*Real.exp D.t*Real.sinh |D.t| *g D.pair c<lagOneSymbol D.pair D.t c) :
    D.eta*Real.exp D.t*Real.sinh |D.t| *meanG D.probability D.pair<
      ∫ c,lagOneSymbol D.pair D.t c ∂D.probability := by
  let f : Frequency→ℝ := fun c=>lagOneSymbol D.pair D.t c-
    D.eta*Real.exp D.t*Real.sinh |D.t| *g D.pair c
  have hf : Continuous f := by
    unfold f lagOneSymbol lowerOsc g skew
    fun_prop
  have hfi := polyak.Spectral.integrable_continuous D.probability hf
  have hp : ∀ᵐ c ∂(D.probability:Measure Frequency),0<f c :=
    D.probability_carrier.mono fun c hc=>sub_pos.mpr (hfirst c hc)
  have hi : 0<∫ c,f c ∂D.probability := by
    apply (integral_pos_iff_support_of_nonneg_ae (hp.mono fun _ h=>h.le) hfi).mpr
    have he : (D.probability:Measure Frequency) (Function.support f)=
        (D.probability:Measure Frequency) univ := by
      apply measure_congr
      filter_upwards [hp] with c hc
      simp [Function.mem_support,hc.ne']
    rw [he,measure_univ]
    norm_num
  have hΦ : Continuous (lagOneSymbol D.pair D.t) := by
    unfold lagOneSymbol lowerOsc g skew
    fun_prop
  dsimp [f] at hi
  rw [integral_sub (polyak.Spectral.integrable_continuous D.probability hΦ)
    ((polyak.Spectral.integrable_continuous D.probability (continuous_g D.pair)).const_mul _),
    integral_const_mul] at hi
  exact sub_pos.mp hi

end HalfStepData

theorem exists_finite_halfstep (a : SymbolPair) {t : ℝ} (ht : t<0)
    {K : ℕ} (hK : 3≤K) {s η d : ℝ} (hs : 0<s) (hs1 : s≤canonicalKernel.s1)
    (hη : 0<η) (hη1 : η<1) (hd : 0≤d) (hdm : d≤bandMargin canonicalKernel K s/2)
    (hsmall : canonicalKernel.longConstant*(|t|/(bandMargin canonicalKernel K s*(s*centerAngle K)))^2+d<
      Real.sqrt η/8)
    (R Θ : C(Frequency,ℝ)) (hR : ∀ q,0<R q)
    (hpolar : ∀ q : Frequency,Real.arccos (q:ℝ)∈Icc (centerAngle K-s*centerAngle K) (centerAngle K+s*centerAngle K) →
      (g a q:ℂ)-2*Complex.I*skew a q=(R q:ℂ)*Complex.exp (-(Θ q:ℂ)*Complex.I))
    (hdef : ∀ q : Frequency,Real.arccos (q:ℝ)∈Icc (centerAngle K-s*centerAngle K) (centerAngle K+s*centerAngle K) →
      |Real.arccos (q:ℝ)-2*Θ q|≤d)
    (hlag : ∀ q : Frequency,Real.arccos (q:ℝ)∈Icc (centerAngle K-s*centerAngle K) (centerAngle K+s*centerAngle K) →
      η*Real.exp t*Real.sinh |t| *g a q<lagOneSymbol a t q) :
    ∃ (J : Type) (_ : Fintype J) (w : J→ℝ≥0) (q : J→Frequency)
      (hw : ∑ j,w j=1),
      (∀ j,Real.arccos (q j:ℝ)∈Icc (centerAngle K-s*centerAngle K) (centerAngle K+s*centerAngle K)) ∧
      ∃ C : ℝ,Feasible a t (finiteSpectrum w q hw) C ∧ |C|<meanG (finiteSpectrum w q hw) a := by
  let D : HalfStepData := {
    pair := a, t := t, K := K, s := s, eta := η, defect := d, radial := R, phase := Θ
    t_neg := ht, K_ge := hK, s_pos := hs, s_le := hs1, eta_pos := hη, eta_lt := hη1
    defect_nonneg := hd, defect_le := hdm, small := hsmall, radial_pos := hR
    polar := hpolar, phase_defect := hdef }
  exact D.finite_of_first_lag (D.first_lag_of_pointwise hlag)

end
end nesterov.Spread
