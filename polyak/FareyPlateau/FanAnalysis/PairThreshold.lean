import polyak.FareyPlateau.FanAnalysis.CarriedPair
import polyak.Levels.Threshold.ShiftThreshold

/-! The exact restricted threshold for a fixed two-point carrier. Its
closed epigraph, attainment and monotonicity are proved for arbitrary
finite measures, so the two fan tests squeeze the actual pair threshold. -/
noncomputable section
set_option maxHeartbeats 800000
namespace polyak.FareyPlateau.FanAnalysis
open General Levels MeasureTheory Set
open scoped Topology

def pairCarrier (a c : Frequency) : Set Frequency := {x | x=a ∨ x=c}
def pairFP (Θ : Curve) (a c : Frequency) : Prop :=
  ∃μ : Measure Frequency,ProgramSolution Θ nonzeroLags μ ∧ (∀ᵐ x ∂μ,x∈pairCarrier a c)
def pairFeasibleShifts (q : Tuning) (a c : Frequency) : Set ℝ :=
  {s | pairFP (Geometry.shiftedCurve q s) a c}
def pairThreshold (q : Tuning) (a c : Frequency) : ℝ := sInf (pairFeasibleShifts q a c)

theorem pairFP_iff_probability (Θ : Curve) (a c : Frequency) :
    pairFP Θ a c ↔ ∃ν : ProbabilityMeasure Frequency,
      ProbabilitySolution Θ nonzeroLags ν ∧ (∀ᵐ x ∂(ν:Measure Frequency),x∈pairCarrier a c) := by
  constructor
  · rintro ⟨μ,hμ,hcar⟩
    exact hμ.normalize_carried hcar
  · rintro ⟨ν,hν,hcar⟩
    exact ⟨ν,hν.toProgramSolution,hcar⟩

theorem pairFeasibleShifts_isClosed (q : Tuning) (a c : Frequency) :
    IsClosed (pairFeasibleShifts q a c) := by
  have hc : Continuous (fun p:ℝ×Frequency=>Geometry.shiftedCurve q p.1 p.2) := by
    have hg : Continuous (fun p:ℝ×Frequency=>((q,p.1),p.2)) :=
      (continuous_const.prodMk continuous_fst).prodMk continuous_snd
    have ht := Threshold.shiftedCurve_jointContinuous.comp hg
    exact ht.congr (fun _=>rfl)
  have hclosed : IsClosed (pairCarrier a c) := by
    change IsClosed (({a}:Set Frequency)∪{c})
    exact isClosed_singleton.union isClosed_singleton
  have hs := Threshold.isClosed_supported_family (A := pairCarrier a c) (fun s=>Geometry.shiftedCurve q s) hc
    nonzeroLags hclosed ⟨a,Or.inl rfl⟩
  have he : pairFeasibleShifts q a c={s | ∃ν : ProbabilityMeasure Frequency,
      ProbabilitySolution (Geometry.shiftedCurve q s) nonzeroLags ν ∧
        (∀ᵐ x ∂(ν:Measure Frequency),x∈pairCarrier a c)} := by
    ext s
    exact pairFP_iff_probability _ _ _
  rw [he]
  exact hs

theorem pairFeasibleShifts_bddBelow (q : Tuning) (a c : Frequency) :
    BddBelow (pairFeasibleShifts q a c) := by
  refine ⟨-Geometry.cotangentUpper q,fun s hs=>?_⟩
  exact Threshold.shifted_fpOn_lower_bound q nonzeroLags ⟨hs.choose,hs.choose_spec.1⟩

theorem pairFP_mono (q : Tuning) (a c : Frequency) {s t : ℝ} (hst : s≤t)
    (hs : pairFP (Geometry.shiftedCurve q s) a c) : pairFP (Geometry.shiftedCurve q t) a c := by
  obtain ⟨ν,hν,hcar⟩ := (Threshold.shifted_monoform_carried_iff q s (pairCarrier a c)).mp hs
  have hh : Measurable (Threshold.shiftedCotangent q t) := by
    unfold Threshold.shiftedCotangent Geometry.cotangent General.Tuning.Xi
    fun_prop
  have hle : ∀ᵐω∂ν,Threshold.shiftedCotangent q s ω≤Threshold.shiftedCotangent q t ω :=
    Filter.Eventually.of_forall (fun ω=>by dsimp [Threshold.shiftedCotangent]; linarith)
  have hbound : ∀ᵐω∂ν,Threshold.shiftedCotangent q t ω≤Geometry.cotangentUpper q+t :=
    hν.2.2.1.mono (fun ω hω=>by
      dsimp [Threshold.shiftedCotangent]
      linarith [Geometry.cotangent_le_upper q hω])
  exact (Threshold.shifted_monoform_carried_iff q t (pairCarrier a c)).mpr
    ⟨ν,(hν.mono_ae hh.aestronglyMeasurable hle hbound).1,hcar⟩

theorem pairThreshold_attained (q : Tuning) (a c : Frequency)
    (hne : (pairFeasibleShifts q a c).Nonempty) :
    pairFP (Geometry.shiftedCurve q (pairThreshold q a c)) a c :=
  (pairFeasibleShifts_isClosed q a c).csInf_mem hne (pairFeasibleShifts_bddBelow q a c)

theorem pair_feasible_iff (q : Tuning) (a c : Frequency)
    (hne : (pairFeasibleShifts q a c).Nonempty) (s : ℝ) :
    pairFP (Geometry.shiftedCurve q s) a c ↔ pairThreshold q a c≤s := by
  constructor
  · exact fun hs=>csInf_le (pairFeasibleShifts_bddBelow q a c) hs
  · exact fun hs=>pairFP_mono q a c hs (pairThreshold_attained q a c hne)

theorem pairThreshold_squeeze (q : Tuning) (a c : Frequency) {s e η δ : ℝ}
    (hδ : δ≠0)
    (hupper : pairFP (Geometry.shiftedCurve q (s-(e-η)*δ^2)) a c)
    (hlower : ¬pairFP (Geometry.shiftedCurve q (s-(e+η)*δ^2)) a c) :
    |(pairThreshold q a c-s)/δ^2+e|≤η := by
  have hne : (pairFeasibleShifts q a c).Nonempty := ⟨_,hupper⟩
  have hu := (pair_feasible_iff q a c hne _).mp hupper
  have hl : s-(e+η)*δ^2<pairThreshold q a c :=
    lt_of_not_ge (fun h=>hlower ((pair_feasible_iff q a c hne _).mpr h))
  have hpos : 0<δ^2 := sq_pos_of_ne_zero hδ
  apply abs_le.mpr
  constructor
  · have hh : -η-e≤(pairThreshold q a c-s)/δ^2 :=
      (le_div_iff₀ hpos).mpr (by nlinarith only [hl])
    linarith
  · have hh : (pairThreshold q a c-s)/δ^2≤η-e :=
      (div_le_iff₀ hpos).mpr (by nlinarith only [hu])
    linarith

end polyak.FareyPlateau.FanAnalysis
