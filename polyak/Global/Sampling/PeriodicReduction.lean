import polyak.Global.Sampling.DiscreteMeasure
import polyak.Global.Sampling.AliasingRepresentatives

/-! Exact residue reduction and transfer of one uniform margin to an
actual finite periodic witness, after removing endpoint atoms. -/
noncomputable section
namespace polyak.Global.Sampling
open polyak.General polyak.Levels MeasureTheory

def densityPhase (q:Tuning) (s:ℝ) (f:C(Circle,ℝ)) : C(Circle,ℂ) where
  toFun x:=(f x:ℂ)*Kernels.cis (-Circle.phaseLift (phase q s) (phase_periodic q s) x)
  continuous_toFun := (Complex.continuous_ofReal.comp f.continuous).mul
    (Kernels.continuous_cis.comp ((Circle.phaseLift_continuous (phase_periodic q s)
      (continuous_phase q s)).neg))

theorem phaseMoment_sampleMeasure (q:Tuning) (s:ℝ) (f:C(Circle,ℝ)) (hf:∀x,0≤f x)
    {L:ℕ} (hL:0<L) (n:ℤ) :
    Circle.phaseMoment (phase q s) (phase_periodic q s) (sampleMeasure f L) n=
      sampleAverage (densityPhase q s f) L n := by
  rw [Circle.phaseMoment,integral_sampleMeasure f hf hL _
    (Circle.wave_continuous _ (continuous_phase q s) n)]
  simp only [sampleAverage,Complex.real_smul,Complex.ofReal_inv,Complex.ofReal_natCast,
    Circle.wave,densityPhase,ContinuousMap.coe_mk]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem phaseMoment_density (q:Tuning) (s:ℝ) (f:C(Circle,ℝ)) (hf:∀x,0≤f x) (n:ℤ) :
    Circle.phaseMoment (phase q s) (phase_periodic q s)
      (Circle.haar.withDensity (fun x=>ENNReal.ofReal (f x))) n=
        fourierCoeff (densityPhase q s f) (-n) := by
  have hh:=integral_withDensity_eq_integral_toReal_smul (μ:=Circle.haar)
    (f:=fun x=>ENNReal.ofReal (f x)) (ENNReal.measurable_ofReal.comp f.continuous.measurable)
    (Filter.Eventually.of_forall fun _=>ENNReal.ofReal_lt_top)
    (Circle.wave (phase q s) (phase_periodic q s) n)
  simp only [ENNReal.toReal_ofReal (hf _),Complex.real_smul] at hh
  rw [Circle.phaseMoment,hh,fourierCoeff]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro x
  simp only [neg_neg,smul_eq_mul,densityPhase,ContinuousMap.coe_mk,Circle.wave]
  ring

theorem phaseMoment_sample_mod (q:Tuning) (s:ℝ) (f:C(Circle,ℝ)) (hf:∀x,0≤f x)
    {L:ℕ} (hL:0<L) (n:ℤ) :
    Circle.phaseMoment (phase q s) (phase_periodic q s) (sampleMeasure f L) n=
      Circle.phaseMoment (phase q s) (phase_periodic q s) (sampleMeasure f L) (n%(L:ℤ)) := by
  rw [phaseMoment_sampleMeasure q s f hf hL,phaseMoment_sampleMeasure q s f hf hL]
  conv_lhs => rw [←Int.emod_add_ediv_mul n (L:ℤ)]
  exact sampleAverage_periodic _ hL _ _

theorem periodicFP_of_uniform_aliasing (q:Tuning) (s:ℝ) (f:C(Circle,ℝ))
    (hf:∀x,0≤f x) {L:ℕ} (hL:0<L) (μ:Measure Circle) [IsFiniteMeasure μ]
    {δ e:ℝ} (he:2*e<δ)
    (hmin : e<∫x,Circle.minimizer (Geometry.shiftedCurve q s) x∂μ)
    (hmargin : ∀n:ℤ,n≠0→δ≤∫x,Circle.lag (Geometry.shiftedCurve q s) n x∂μ)
    (herror : ∀n:ℤ,2*|n|≤(L:ℤ)→
      ‖Circle.phaseMoment (phase q s) (phase_periodic q s) (sampleMeasure f L) n-
        Circle.phaseMoment (phase q s) (phase_periodic q s) μ n‖≤e) :
    PeriodicFP (Geometry.shiftedCurve q s) L := by
  have h0:=herror 0 (by simp)
  have hr0:=(Complex.abs_re_le_norm _).trans h0
  simp only [Complex.sub_re] at hr0
  apply periodicFP_of_sampled_moments (Geometry.shiftedCurve q s) f hL
  · rw [←phaseMinimizer_actual, Circle.phaseMinimizer]
    rw [←phaseMinimizer_actual, Circle.phaseMinimizer] at hmin
    linarith [(abs_le.mp hr0).1]
  · intro r _
    obtain ⟨n,hn,hbalanced,_hzero⟩:=balanced_representative hL r
    have hsame : Circle.phaseMoment (phase q s) (phase_periodic q s) (sampleMeasure f L) r=
        Circle.phaseMoment (phase q s) (phase_periodic q s) (sampleMeasure f L) n := by
      rw [phaseMoment_sample_mod q s f hf hL r,phaseMoment_sample_mod q s f hf hL n,hn]
    rw [←phaseConstraint_actual,Circle.phaseConstraint,hsame]
    by_cases hn0:n=0
    · simp only [hn0,sub_self,Complex.zero_re,le_refl]
    · have hnerr:=herror n hbalanced
      have hrn:=(Complex.abs_re_le_norm _).trans hnerr
      simp only [Complex.sub_re] at hrn
      have hmn:=hmargin n hn0
      rw [←phaseConstraint_actual,Circle.phaseConstraint,Complex.sub_re] at hmn
      rw [Complex.sub_re]
      linarith [(abs_le.mp hr0).1,(abs_le.mp hrn).2]

end polyak.Global.Sampling
