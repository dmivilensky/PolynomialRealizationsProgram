import polyak.Levels.Program.EndpointRemoval
import polyak.Levels.Threshold.MeasureTools
import polyak.General.AngleComparison

/-! The explicit sine-ratio transformation in the arbitrary-curve monotonicity proof. -/
noncomputable section
open MeasureTheory
namespace polyak.Levels

def monotoneDensity (Θ Ψ : Curve) (ω : Frequency) : ℝ := Real.sin (Θ ω)/Real.sin (Ψ ω)

theorem monotoneDensity_nonneg (Θ Ψ : Curve) (ω : Frequency) : 0≤monotoneDensity Θ Ψ ω :=
  div_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi (Θ.pos ω).le (Θ.le_pi ω))
    (Real.sin_nonneg_of_nonneg_of_le_pi (Ψ.pos ω).le (Ψ.le_pi ω))

theorem monotoneDensity_measurable (Θ Ψ : Curve) : Measurable (monotoneDensity Θ Ψ) :=
  (Real.continuous_sin.comp Θ.continuous).measurable.div (Real.continuous_sin.comp Ψ.continuous).measurable

theorem monotoneDensity_bounded (Θ Ψ : Curve) (horder : ∀ω,Ψ ω≤Θ ω) :
    ∃C:ℝ,∀ω,monotoneDensity Θ Ψ ω≤C := by
  obtain ⟨ω₀,_,hmin⟩ := isCompact_univ.exists_isMinOn Set.univ_nonempty Ψ.continuous.continuousOn
  let δ := min (Ψ ω₀) (Real.pi/2)
  have hδ : 0<δ := lt_min (Ψ.pos ω₀) (by positivity)
  have hδπ : δ<Real.pi := lt_of_le_of_lt (min_le_right _ _) (by linarith [Real.pi_pos])
  have hsδ := Real.sin_pos_of_pos_of_lt_pi hδ hδπ
  refine ⟨max 1 (1/Real.sin δ),fun ω=>?_⟩
  by_cases hp : Ψ ω=Real.pi
  · simp only [monotoneDensity,hp,Real.sin_pi,div_zero]
    exact (zero_le_one.trans (le_max_left _ _))
  have hp' : Ψ ω<Real.pi := lt_of_le_of_ne (Ψ.le_pi ω) hp
  have hsΨ := Real.sin_pos_of_pos_of_lt_pi (Ψ.pos ω) hp'
  by_cases hhalf : Ψ ω≤Real.pi/2
  · have hδω : δ≤Ψ ω := (min_le_left _ _).trans (hmin (Set.mem_univ ω))
    have hsin : Real.sin δ≤Real.sin (Ψ ω) :=
      Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [hδ]) hhalf hδω
    apply le_trans _ (le_max_right _ _)
    apply (div_le_div_iff₀ hsΨ hsδ).mpr
    have hmul := mul_le_mul_of_nonneg_right (Real.sin_le_one (Θ ω)) hsδ.le
    nlinarith
  · have hsin : Real.sin (Θ ω)≤Real.sin (Ψ ω) := by
      have hh := Real.sin_le_sin_of_le_of_le_pi_div_two
        (show -(Real.pi/2)≤Real.pi-Θ ω by linarith [Θ.le_pi ω,Real.pi_pos])
        (show Real.pi-Ψ ω≤Real.pi/2 by linarith)
        (show Real.pi-Θ ω≤Real.pi-Ψ ω by linarith [horder ω])
      simpa only [Real.sin_pi_sub] using hh
    exact ((div_le_one hsΨ).mpr hsin).trans (le_max_left _ _)

theorem monotoneDensity_minimizer {Θ Ψ : Curve} (horder : ∀ω,Ψ ω≤Θ ω)
    (ω : Frequency) (hω : Θ ω≠Real.pi) :
    Θ.minimizer ω≤monotoneDensity Θ Ψ ω*Ψ.minimizer ω := by
  have hΘ : Θ ω<Real.pi := lt_of_le_of_ne (Θ.le_pi ω) hω
  have hΨ : Ψ ω<Real.pi := (horder ω).trans_lt hΘ
  have hsΘ := Real.sin_pos_of_pos_of_lt_pi (Θ.pos ω) hΘ
  have hsΨ := Real.sin_pos_of_pos_of_lt_pi (Ψ.pos ω) hΨ
  have hcot : Real.cos (Θ ω)/Real.sin (Θ ω)≤Real.cos (Ψ ω)/Real.sin (Ψ ω) := by
    rcases eq_or_lt_of_le (horder ω) with he|he
    · rw [he]
    · exact ((General.cot_strictAnti ⟨Θ.pos ω,hΘ⟩ ⟨Ψ.pos ω,hΨ⟩).mpr he).le
  rw [div_le_div_iff₀ hsΘ hsΨ] at hcot
  dsimp [Curve.minimizer,monotoneDensity]
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hsΨ).mpr
  convert hcot using 1; ring

theorem monotoneDensity_lag {Θ Ψ : Curve} (horder : ∀ω,Ψ ω≤Θ ω)
    (n : ℤ) (ω : Frequency) (hω : Θ ω≠Real.pi) :
    Θ.lag n ω≤monotoneDensity Θ Ψ ω*Ψ.lag n ω := by
  have hmin := monotoneDensity_minimizer horder ω hω
  have hsΨ : Real.sin (Ψ ω)≠0 := (Real.sin_pos_of_pos_of_lt_pi (Ψ.pos ω)
    ((horder ω).trans_lt (lt_of_le_of_ne (Θ.le_pi ω) hω))).ne'
  have he : monotoneDensity Θ Ψ ω*Real.sin (Ψ ω)=Real.sin (Θ ω) := div_mul_cancel₀ _ hsΨ
  rw [Θ.lag_expand,Ψ.lag_expand]
  dsimp [Curve.minimizer] at hmin
  have hmul := mul_le_mul_of_nonneg_right hmin (sub_nonneg.mpr (Real.cos_le_one ((n:ℝ)*(ω:ℝ))))
  calc
    _≤(monotoneDensity Θ Ψ ω*Real.cos (Ψ ω))*(1-Real.cos ((n:ℝ)*(ω:ℝ)))-
        Real.sin (Θ ω)*Real.sin ((n:ℝ)*(ω:ℝ)) := sub_le_sub_right hmul _
    _=_ := by rw [← he]; ring

theorem ProgramSolution.mono_weight {Θ Ψ : Curve} {𝒩 : Set ℤ} {w : Measure Frequency}
    (h : ProgramSolution Θ 𝒩 w) (horder : ∀ω,Ψ ω≤Θ ω) :
    ProgramSolution Ψ 𝒩 (Threshold.realWeight (monotoneDensity Θ Ψ)
      (w.restrict {ω | Θ ω≠Real.pi})) := by
  let u := w.restrict {ω | Θ ω≠Real.pi}
  have hu : ProgramSolution Θ 𝒩 u := h.remove_pi_phase
  have : IsFiniteMeasure u := hu.1
  have hucar : ∀ᵐω∂u,Θ ω≠Real.pi := ae_restrict_mem
    (isOpen_ne_fun Θ.continuous continuous_const).measurableSet
  let d := monotoneDensity Θ Ψ
  have hd := monotoneDensity_measurable Θ Ψ
  have hdnonneg := monotoneDensity_nonneg Θ Ψ
  obtain ⟨C,hC⟩ := monotoneDensity_bounded Θ Ψ horder
  have hdi : Integrable d u := (integrable_const C).mono' hd.aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω=>by rw [Real.norm_eq_abs,abs_of_nonneg (hdnonneg ω)]; exact hC ω)
  have hwfinite : IsFiniteMeasure (Threshold.realWeight d u) := isFiniteMeasure_withDensity_ofReal hdi.2
  have hdpos : ∀ᵐω∂u,0<d ω := hucar.mono fun ω hω => div_pos
    (Real.sin_pos_of_pos_of_lt_pi (Θ.pos ω) (lt_of_le_of_ne (Θ.le_pi ω) hω))
    (Real.sin_pos_of_pos_of_lt_pi (Ψ.pos ω) ((horder ω).trans_lt (lt_of_le_of_ne (Θ.le_pi ω) hω)))
  have hwne := Threshold.realWeight_ne_zero hd hdpos hu.2.1
  have hprod (f:C(Frequency,ℝ)) : Integrable (fun ω=>d ω*f ω) u := by
    exact (Threshold.integrable_realWeight_iff hd hdnonneg u f).mp
      (f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
  refine ⟨hwfinite,hwne,?_,fun n hn=>?_⟩
  · rw [Threshold.integral_realWeight hd hdnonneg]
    exact hu.2.2.1.trans (integral_mono_ae (integrable_curve_minimizer Θ u)
      (hprod ⟨Ψ.minimizer,Ψ.continuous_minimizer⟩) (hucar.mono fun ω hω => monotoneDensity_minimizer horder ω hω))
  · rw [Threshold.integral_realWeight hd hdnonneg]
    exact (hu.2.2.2 n hn).trans (integral_mono_ae (integrable_curve_lag Θ n u)
      (hprod ⟨Ψ.lag n,Ψ.continuous_lag n⟩) (hucar.mono fun ω hω => monotoneDensity_lag horder n ω hω))

theorem ProgramSolution.mono_weight_of_interior_order {Θ Ψ : Curve} {𝒩 : Set ℤ} {w : Measure Frequency}
    (h : ProgramSolution Θ 𝒩 w)
    (horder : ∀ω:Frequency,0<(ω:ℝ)→(ω:ℝ)<Real.pi→Ψ ω≤Θ ω) :
    ProgramSolution Ψ 𝒩 (Threshold.realWeight (monotoneDensity Θ Ψ)
      (w.restrict {ω | Θ ω≠Real.pi})) := by
  apply h.mono_weight
  intro ω
  rcases eq_or_lt_of_le ω.property.1 with h0|h0
  · have he : ω=frequencyZero := Subtype.ext h0.symm
    rw [he,Θ.at_zero,Ψ.at_zero]
  rcases eq_or_lt_of_le ω.property.2 with hp|hp
  · have he : ω=frequencyPi := Subtype.ext hp
    rw [he,Θ.at_pi,Ψ.at_pi]
  exact horder ω h0 hp

end polyak.Levels
