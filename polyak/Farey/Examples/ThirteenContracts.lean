import polyak.Farey.Examples.Formulas
import polyak.Farey.FanDivergence.Orbit
import polyak.Farey.Examples.SingleHarmonic
import polyak.Levels.Program.SourceIdentities
import polyak.Levels.Realization.AtomicOrbit
import polyak.Levels.Realization.ExactThreshold
import polyak.Levels.Chart.GapOpen

/-! Exact input and finite acceptance contracts for Proposition 3.13.
The probability weights belong to nu; the full-program weights are density times nu.
`CertifiedExamples.Rational` proves the numerical signs. -/
noncomputable section
namespace polyak.Farey.Examples
open Levels MeasureTheory Set Filter
open scoped Topology

def thirteenFrequency (b:Bool) : Levels.Frequency :=
  ⟨2*Real.pi*(if b then (2:ℝ) else 3)/13,by
    cases b <;> norm_num <;> constructor <;> nlinarith [Real.pi_pos]⟩

def thirteenNuWeight (b:Bool) : NNReal:=if b then 149/797 else 648/797

def thirteenNu : Measure Levels.Frequency:=atomicMeasure thirteenNuWeight thirteenFrequency

theorem thirteen_nu_weights_sum : ∑b,thirteenNuWeight b=1 := by
  norm_num [thirteenNuWeight,Fintype.sum_bool]

instance thirteenNu_probability : IsProbabilityMeasure thirteenNu := by
  constructor
  change atomicMeasure thirteenNuWeight thirteenFrequency Set.univ=1
  simp only [atomicMeasure,Measure.coe_finsetSum,Finset.sum_apply,Measure.smul_apply,
    Measure.dirac_apply_of_mem (Set.mem_univ _),smul_eq_mul,mul_one]
  rw [←ENNReal.ofNNReal_finsetSum,thirteen_nu_weights_sum]
  rfl

def thirteenDensity (b:Bool) : NNReal:=
  ⟨sourceDensity thirteenTuning (thirteenFrequency b),(sourceDensity_pos _ _).le⟩

def thirteenWWeight (b:Bool) : NNReal:=thirteenNuWeight b*thirteenDensity b

def thirteenW : Measure Levels.Frequency:=atomicMeasure thirteenWWeight thirteenFrequency

theorem thirteen_w_weight_pos (b:Bool) : 0<thirteenWWeight b := by
  apply mul_pos
  · cases b <;> norm_num [thirteenNuWeight]
  · exact sourceDensity_pos _ _

theorem thirteen_w_weights_sum_pos : 0<∑b,thirteenWWeight b :=
  lt_of_lt_of_le (thirteen_w_weight_pos false)
    (Finset.single_le_sum (fun _ _=>zero_le) (Finset.mem_univ false))

theorem thirteen_w_is_density_times_nu :
    thirteenW=reweight (sourceDensity thirteenTuning) thirteenNu := by
  have hd (b:Bool) : ENNReal.ofReal (sourceDensity thirteenTuning (thirteenFrequency b))=
      (thirteenDensity b:ENNReal) := by
    change ENNReal.ofReal ((thirteenDensity b:NNReal):ℝ)=(thirteenDensity b:ENNReal)
    simp
  simp only [thirteenW,thirteenNu,atomicMeasure,Fintype.sum_bool,reweight,
    withDensity_add_measure,withDensity_smul_measure,dirac_withDensity,hd,smul_smul,
    thirteenWWeight,ENNReal.coe_mul]

theorem thirteen_source_weight_norm (b:Bool) : (thirteenWWeight b:ℝ)=
    (thirteenNuWeight b:ℝ)*
      ‖((sourceG thirteenTuning (thirteenFrequency b):ℝ):ℂ)-
        2*Complex.I*((angleMultiplier thirteenTuning (thirteenFrequency b)).im:ℂ)‖ := by
  rw [←sourceDensity_eq_norm_g_minus_2is]
  rfl

theorem thirteen_frequency_on_grid (b:Bool) : thirteenFrequency b∈periodicGrid 13 := by
  constructor
  · cases b <;> change 0<2*Real.pi*_/13 <;> positivity
  · refine ⟨if b then 2 else 3,?_⟩
    cases b <;> norm_num [thirteenFrequency] <;> ring

def thirteenRawMin : ℝ:=∑b,(thirteenNuWeight b:ℝ)*sourceG thirteenTuning (thirteenFrequency b)
def thirteenRawLag (n:ℤ) : ℝ:=
  ∑b,(thirteenNuWeight b:ℝ)*sourceLag thirteenTuning n (thirteenFrequency b)

theorem thirteen_raw_min_weighted : thirteenRawMin=
    ∑b,(thirteenWWeight b:ℝ)*(tuningCurve thirteenTuning).minimizer (thirteenFrequency b) := by
  unfold thirteenRawMin
  simp_rw [sourceG_polar]
  apply Finset.sum_congr rfl
  intro b _
  change (thirteenNuWeight b:ℝ)*(sourceDensity _ _*_)=
    ((thirteenNuWeight b:ℝ)*sourceDensity _ _)*_
  ring

theorem thirteen_raw_lag_weighted (n:ℤ) : thirteenRawLag n=
    ∑b,(thirteenWWeight b:ℝ)*(tuningCurve thirteenTuning).lag n (thirteenFrequency b) := by
  unfold thirteenRawLag
  simp_rw [sourceLag_polar]
  apply Finset.sum_congr rfl
  intro b _
  change (thirteenNuWeight b:ℝ)*(sourceDensity _ _*_)=
    ((thirteenNuWeight b:ℝ)*sourceDensity _ _)*_
  ring

/-- Exactly one minimizer sign and twelve residue signs suffice for ALL signed
integer lags. Raw signs are computed in the original probability weights. -/
theorem thirteen_full_program_iff_finite :
    ProgramSolution (tuningCurve thirteenTuning) nonzeroLags thirteenW ↔
      0≤thirteenRawMin ∧ ∀n:ℕ,0<n→n<13→0≤thirteenRawLag n := by
  rw [thirteenW,atomic_program_iff _ (by norm_num : 0<13) thirteenWWeight
    thirteenFrequency thirteen_w_weights_sum_pos thirteen_frequency_on_grid]
  simp only [thirteen_raw_min_weighted,thirteen_raw_lag_weighted]

theorem thirteen_raw_spectrum_iff_finite :
    RawSpectrumSolution thirteenTuning thirteenNu ↔
      0≤thirteenRawMin ∧ ∀n:ℕ,0<n→n<13→0≤thirteenRawLag n := by
  rw [rawSpectrumSolution_iff_reweight,←thirteen_w_is_density_times_nu,
    thirteen_full_program_iff_finite]

theorem thirteen_raw_lag_residue (n:ℤ) : thirteenRawLag n=thirteenRawLag (n%13) := by
  rw [thirteen_raw_lag_weighted,thirteen_raw_lag_weighted]
  apply Finset.sum_congr rfl
  intro b _
  rw [lag_mod_grid _ (thirteen_frequency_on_grid b) n]
  norm_num

theorem thirteen_raw_lag_multiple (m:ℤ) : thirteenRawLag (13*m)=0 := by
  rw [thirteen_raw_lag_residue]
  simp [thirteenRawLag,sourceLag_polar,Curve.lag_zero]

/-- Four finite algebraic comparisons encode the actual source gap, via the
proved root reconstruction. This contract contains no grid approximation. -/
def GapFourChecks (q:General.Tuning) : Prop:=
  (Chart.coefficients q).c2<0 ∧ 0<Chart.gapDiscriminant (Chart.coefficients q) ∧
    Chart.boundaryCosine 4<Chart.leftRoot (Chart.coefficients q) ∧
    Chart.rightRoot (Chart.coefficients q)<Chart.boundaryCosine 5

theorem gap_four_of_checks {q:General.Tuning} (h:GapFourChecks q) : Geometry.Gap 4 q :=
  (Chart.gap_iff_discriminant (by norm_num) q).mpr h

/-- Finite source-sign conditions for the period-thirteen example. -/
def ThirteenFiniteSigns : Prop:=
  0≤thirteenRawMin ∧ ∀n:Fin 12,0≤thirteenRawLag (n.val+1)

theorem thirteen_from_finite_signs (h:ThirteenFiniteSigns) :
    RawSpectrumSolution thirteenTuning thirteenNu ∧
      ProgramSolution (tuningCurve thirteenTuning) nonzeroLags thirteenW ∧
      1≤thirteenTuning.rate := by
  have hf : 0≤thirteenRawMin ∧ ∀n:ℕ,0<n→n<13→0≤thirteenRawLag n := by
    refine ⟨h.1,?_⟩
    intro n hn hk
    have he:((n-1:ℕ):ℤ)+1=(n:ℤ):=by omega
    simpa only [he] using h.2 ⟨n-1,by omega⟩
  have hw:=thirteen_full_program_iff_finite.mpr hf
  exact ⟨thirteen_raw_spectrum_iff_finite.mpr hf,hw,
    fp_one_le_rate thirteenTuning ⟨thirteenW,hw⟩⟩

/-- Once the finite raw signs have been certified, the actual from-rest
trajectory is realized in R^5. -/
theorem thirteen_orbit_of_finite_signs (h:ThirteenFiniteSigns) :
    FanPeriodicOrbit thirteenTuning 13 2 := by
  have hw:ProgramSolution (tuningCurve thirteenTuning) nonzeroLags
      (atomicMeasure thirteenWWeight thirteenFrequency):=(thirteen_from_finite_signs h).2.1
  have hr:FanPeriodicOrbit thirteenTuning 13 (Fintype.card Bool):=
    atomic_periodic_actual_orbit thirteenTuning thirteenWWeight thirteenFrequency
      thirteen_w_weights_sum_pos thirteen_frequency_on_grid hw
  rw [Fintype.card_bool] at hr
  exact hr

end polyak.Farey.Examples
