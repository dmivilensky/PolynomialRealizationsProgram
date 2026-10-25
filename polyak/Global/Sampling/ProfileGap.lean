import polyak.Global.Sampling.ReciprocalMeasure
import polyak.Levels.Threshold.PeriodicThreshold
import polyak.Levels.Threshold.Kappa

/-! The source shift and condition-number gaps yield actual strict
finite-measure solutions, while every existing period is preserved. -/
noncomputable section
namespace polyak.Global.Sampling
open General Levels Levels.Threshold MeasureTheory Set Filter

 theorem strict_measure_of_profile_gap (q p : Tuning) (s t : ℝ)
    {ν : Measure Frequency} (hν : MonotoneSolution (shiftedCotangent q s) ν)
    (hNP : Nonperiodic ν) {e : ℝ} (he : 0<e)
    (hgap : ∀ω∈Ioo (0:ℝ) Real.pi,Geometry.cotangent q ω+s+e≤Geometry.cotangent p ω+t) :
    ∃w : Measure Frequency,ProgramSolution (Geometry.shiftedCurve p t) nonzeroLags w ∧
      (∀ᵐω∂w,ω∈interiorCarrier) ∧
      (0<∫ω,(Geometry.shiftedCurve p t).minimizer ω∂w) ∧
      ∀n : ℤ,n≠0→0<∫ω,(Geometry.shiftedCurve p t).lag n ω∂w := by
  have hm : Measurable (shiftedCotangent p t) := by
    unfold shiftedCotangent Geometry.cotangent Tuning.Xi
    fun_prop
  have horder : ∀ᵐω∂ν,shiftedCotangent q s ω+e≤shiftedCotangent p t ω :=
    hν.2.2.1.mono (fun ω hω=>hgap ω hω)
  have hupper : ∀ᵐω∂ν,shiftedCotangent p t ω≤Geometry.cotangentUpper p+t :=
    hν.2.2.1.mono (fun ω hω=>by unfold shiftedCotangent;linarith [Geometry.cotangent_le_upper p hω])
  obtain ⟨hν',hmin,hlag⟩ := strict_monoform_increase hν hNP hm.aestronglyMeasurable he horder hupper
  exact strict_measure_of_monotone p t hν' hmin hlag

 theorem strict_measure_after_shift (q : Tuning) (s : ℝ) {ν : Measure Frequency}
    (hν : MonotoneSolution (shiftedCotangent q s) ν) (hNP : Nonperiodic ν)
    {e : ℝ} (he : 0<e) :
    ∃w : Measure Frequency,ProgramSolution (Geometry.shiftedCurve q (s+e)) nonzeroLags w ∧
      (∀ᵐω∂w,ω∈interiorCarrier) ∧
      (0<∫ω,(Geometry.shiftedCurve q (s+e)).minimizer ω∂w) ∧
      ∀n : ℤ,n≠0→0<∫ω,(Geometry.shiftedCurve q (s+e)).lag n ω∂w :=
  strict_measure_of_profile_gap q q s (s+e) hν hNP he (fun _ _=>by ring_nf;exact le_rfl)

 theorem strict_measure_after_kappa (q p : Tuning) (hy : p.y=q.y) (hb : p.beta=q.beta)
    (hκ : q.kappa<p.kappa) (s : ℝ) {ν : Measure Frequency}
    (hν : MonotoneSolution (shiftedCotangent q s) ν) (hNP : Nonperiodic ν) :
    ∃w : Measure Frequency,ProgramSolution (Geometry.shiftedCurve p s) nonzeroLags w ∧
      (∀ᵐω∂w,ω∈interiorCarrier) ∧
      (0<∫ω,(Geometry.shiftedCurve p s).minimizer ω∂w) ∧
      ∀n : ℤ,n≠0→0<∫ω,(Geometry.shiftedCurve p s).lag n ω∂w := by
  obtain ⟨e,he,hgap⟩ := exists_uniform_cotangent_kappa_gap q p hy hb hκ
  apply strict_measure_of_profile_gap q p s s hν hNP he
  intro ω hω
  unfold Geometry.cotangent
  linarith [hgap ω hω]

private theorem tuning_eq_of_coordinates {q p : Tuning} (hκ : q.kappa=p.kappa)
    (hy : q.y=p.y) (hb : q.beta=p.beta) : q=p := by
  cases q;cases p;dsimp at hκ hy hb
  subst_vars
  rfl

 theorem periodic_kappa_mono (q p : Tuning) (hy : p.y=q.y) (hb : p.beta=q.beta)
    (hκ : q.kappa≤p.kappa) {k : ℕ} (s : ℝ)
    (hs : PeriodicFP (Geometry.shiftedCurve q s) k) :
    PeriodicFP (Geometry.shiftedCurve p s) k := by
  rcases eq_or_lt_of_le hκ with hκ|hκ
  · have he : q=p := tuning_eq_of_coordinates hκ hy.symm hb.symm
    simpa only [←he] using hs
  · obtain ⟨e,he,hgap⟩ := exists_uniform_cotangent_kappa_gap q p hy hb hκ
    apply shifted_periodic_compare k (hs:=hs)
    intro ω hω
    unfold Geometry.cotangent
    linarith [hgap ω hω]

end polyak.Global.Sampling
