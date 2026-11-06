import nesterov.Spectral.Feasibility
import Mathlib.MeasureTheory.Measure.WithDensity

/-! Exact normalized reciprocal weighting on the actual cosine carrier.
The underlying measure remains arbitrary, and all carrier properties persist. -/
namespace nesterov.Spread
noncomputable section
open MeasureTheory Set
open scoped Topology
variable {X : Type*} [TopologicalSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X]

def positiveClip (δ : ℝ) (R : C(X,ℝ)) : C(X,ℝ) :=
  ⟨fun q=>max δ (R q),continuous_const.max R.continuous⟩

omit [CompactSpace X] [BorelSpace X] [MeasurableSpace X] in
theorem positiveClip_pos {δ : ℝ} (hδ : 0<δ) (R : C(X,ℝ)) (q : X) :
    0<positiveClip δ R q := hδ.trans_le (le_max_left _ _)

omit [CompactSpace X] [BorelSpace X] [MeasurableSpace X] in
theorem positiveClip_eq {δ : ℝ} (R : C(X,ℝ)) {q : X} (hq : δ≤R q) :
    positiveClip δ R q=R q := max_eq_right hq

omit [CompactSpace X] [BorelSpace X] [MeasurableSpace X] in
theorem exists_positiveClip_on (R : C(X,ℝ)) {S : Set X} (hS : IsCompact S)
    (hne : S.Nonempty) (hR : ∀q∈S,0<R q) :
    ∃ δ : ℝ,0<δ ∧ ∀q∈S,positiveClip δ R q=R q := by
  obtain ⟨q0,hq0,hmin⟩ := hS.exists_isMinOn hne R.continuous.continuousOn
  exact ⟨R q0,hR q0 hq0,fun q hq=>positiveClip_eq R (hmin hq)⟩

def reciprocalZ (R : C(X,ℝ)) (ν : ProbabilityMeasure X) : ℝ := ∫q,(R q)⁻¹∂ν

theorem reciprocal_integrable (R : C(X,ℝ)) (ν : ProbabilityMeasure X)
    (hR : ∀q,0<R q) : Integrable (fun q=>(R q)⁻¹) (ν : Measure X) :=
  (R.continuous.inv₀ fun q=>(hR q).ne').integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

theorem reciprocalZ_pos (R : C(X,ℝ)) (ν : ProbabilityMeasure X)
    (hR : ∀q,0<R q) : 0<reciprocalZ R ν := by
  apply (integral_pos_iff_support_of_nonneg (fun q=>(inv_pos.mpr (hR q)).le)
    (reciprocal_integrable R ν hR)).mpr
  have he : Function.support (fun q : X=>(R q)⁻¹)=univ := by
    ext q
    simp only [Function.mem_support,mem_univ,iff_true]
    exact (inv_pos.mpr (hR q)).ne'
  rw [he]
  simp

def reciprocalWeight (R : C(X,ℝ)) (ν : ProbabilityMeasure X) (q : X) : ℝ :=
  (R q)⁻¹/reciprocalZ R ν

theorem reciprocalWeight_nonneg (R : C(X,ℝ)) (ν : ProbabilityMeasure X)
    (hR : ∀q,0<R q) (q : X) : 0≤reciprocalWeight R ν q :=
  div_nonneg (inv_nonneg.mpr (hR q).le) (reciprocalZ_pos R ν hR).le

omit [CompactSpace X] [BorelSpace X] in
theorem reciprocalWeight_continuous (R : C(X,ℝ)) (ν : ProbabilityMeasure X)
    (hR : ∀q,0<R q) : Continuous (reciprocalWeight R ν) :=
  (R.continuous.inv₀ fun q=>(hR q).ne').div_const _

def reciprocalMeasure (R : C(X,ℝ)) (ν : ProbabilityMeasure X) : Measure X :=
  (ν : Measure X).withDensity (fun q=>ENNReal.ofReal (reciprocalWeight R ν q))

theorem reciprocalMeasure_probability (R : C(X,ℝ)) (ν : ProbabilityMeasure X)
    (hR : ∀q,0<R q) : IsProbabilityMeasure (reciprocalMeasure R ν) := by
  constructor
  have hi : Integrable (reciprocalWeight R ν) (ν : Measure X) :=
    (reciprocalWeight_continuous R ν hR).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hmass : (∫q,reciprocalWeight R ν q∂ν)=1 := by
    unfold reciprocalWeight
    rw [integral_div]
    exact div_self (reciprocalZ_pos R ν hR).ne'
  rw [reciprocalMeasure,withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ,
    ←ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ (reciprocalWeight_nonneg R ν hR)),
    hmass,ENNReal.ofReal_one]

def reciprocalProbability (R : C(X,ℝ)) (ν : ProbabilityMeasure X) (hR : ∀q,0<R q) :
    ProbabilityMeasure X := ⟨reciprocalMeasure R ν,reciprocalMeasure_probability R ν hR⟩

theorem reciprocalProbability_ae (R : C(X,ℝ)) (ν : ProbabilityMeasure X)
    (hR : ∀q,0<R q) {P : X→Prop} (hP : ∀ᵐ q ∂(ν : Measure X),P q) :
    ∀ᵐ q ∂(reciprocalProbability R ν hR : Measure X),P q :=
  (withDensity_absolutelyContinuous _ _).ae_le hP

theorem integral_reciprocalProbability {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (R : C(X,ℝ)) (ν : ProbabilityMeasure X) (hR : ∀q,0<R q) (f : X→E) :
    (∫q,f q∂(reciprocalProbability R ν hR : Measure X))=
      ∫q,reciprocalWeight R ν q • f q∂ν := by
  change (∫q,f q∂(ν : Measure X).withDensity
    (fun q=>ENNReal.ofReal (reciprocalWeight R ν q)))=_
  have h := integral_withDensity_eq_integral_toReal_smul (μ:=(ν : Measure X))
    (f:=fun q=>ENNReal.ofReal (reciprocalWeight R ν q))
    (ENNReal.measurable_ofReal.comp (reciprocalWeight_continuous R ν hR).measurable)
    (ae_of_all _ fun _=>ENNReal.ofReal_lt_top) f
  simpa only [ENNReal.toReal_ofReal (reciprocalWeight_nonneg R ν hR _)] using h

theorem reciprocalProbability_scaled_integral {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (R : C(X,ℝ)) (ν : ProbabilityMeasure X) (hR : ∀q,0<R q) (f : X→E) :
    reciprocalZ R ν • (∫q,f q∂(reciprocalProbability R ν hR : Measure X))=
      ∫q,(R q)⁻¹ • f q∂ν := by
  rw [integral_reciprocalProbability,←integral_smul]
  apply integral_congr_ae
  filter_upwards with q
  rw [smul_smul]
  congr 1
  unfold reciprocalWeight
  field_simp [(reciprocalZ_pos R ν hR).ne']

theorem reciprocalProbability_cancel_integral {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (R : C(X,ℝ)) (ν : ProbabilityMeasure X) (hR : ∀q,0<R q) (f : X→E) :
    reciprocalZ R ν • (∫q,R q • f q∂(reciprocalProbability R ν hR : Measure X))=
      ∫q,f q∂ν := by
  rw [reciprocalProbability_scaled_integral]
  apply integral_congr_ae
  filter_upwards with q
  rw [smul_smul,inv_mul_cancel₀ (hR q).ne',one_smul]

end
end nesterov.Spread
