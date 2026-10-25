import polyak.ModeLocking.Localization.OscillationJets
import polyak.ModeLocking.Regular.Endpoints

/-! The regular locking potential diverges at both frequency endpoints. -/
noncomputable section
namespace polyak.ModeLocking.Localization
open Levels Filter Set
open scoped Topology BigOperators

private theorem quotient_atTop {l : Filter ℝ} {f g : ℝ → ℝ} {c : ℝ}
    (hf : Tendsto f l (𝓝 c)) (hc : 0 < c) (hg : Tendsto g l (𝓝[>] 0)) :
    Tendsto (fun x => f x/g x) l atTop := by
  simpa only [div_eq_mul_inv,Function.comp_def] using hf.pos_mul_atTop hc (tendsto_inv_nhdsGT_zero.comp hg)

variable {q : General.Tuning} {t : ℝ} {L : ℕ}

theorem continuousAt_extendedPhase (q : General.Tuning) (t : ℝ) (z : ℝ)
    (hz : z ∈ Icc 0 Real.pi) :
    ContinuousAt (fun x : ℝ => Geometry.jointAngle ![q.kappa,q.y,q.beta,t,x]) z := by
  have hp : AnalyticAt ℝ (fun x : ℝ => ![q.kappa,q.y,q.beta,t,x]) z := by
    apply AnalyticAt.pi
    intro i
    fin_cases i
    all_goals first | exact analyticAt_const | exact analyticAt_id
  exact ((Geometry.analyticAt_jointAngle_actual q t hz).comp
    (f := fun x : ℝ => ![q.kappa,q.y,q.beta,t,x]) hp).continuousAt

private theorem phaseSine_tendsto_zero_right (q : General.Tuning) (t : ℝ) :
    Tendsto (fun x : ℝ => Real.sin (Geometry.jointAngle ![q.kappa,q.y,q.beta,t,x]))
      (𝓝[>] 0) (𝓝[>] 0) := by
  rw [tendsto_nhdsWithin_iff]
  constructor
  · have hh := (Real.continuous_sin.continuousAt.comp (continuousAt_extendedPhase q t 0
      ⟨le_rfl,Real.pi_pos.le⟩)).tendsto.mono_left
        (show 𝓝[>] (0:ℝ) ≤ 𝓝 0 from nhdsWithin_le_nhds)
    simpa only [Function.comp_def,Geometry.jointAngle_actual q t ⟨le_rfl,Real.pi_pos.le⟩,
      Geometry.shiftedAngle_zero,Real.sin_pi] using hh
  · have hb : ∀ᶠ x : ℝ in 𝓝 0, x < Real.pi := Iio_mem_nhds Real.pi_pos
    filter_upwards [self_mem_nhdsWithin, hb.filter_mono nhdsWithin_le_nhds] with x hx hπ
    rw [Geometry.jointAngle_actual q t ⟨hx.le,hπ.le⟩]
    exact Real.sin_pos_of_pos_of_lt_pi (Geometry.shiftedAngle_mem q t ⟨hx,hπ⟩).1
      (Geometry.shiftedAngle_mem q t ⟨hx,hπ⟩).2

private theorem phaseSine_tendsto_zero_left (q : General.Tuning) (t : ℝ) :
    Tendsto (fun x : ℝ => Real.sin (Geometry.jointAngle ![q.kappa,q.y,q.beta,t,x]))
      (𝓝[<] Real.pi) (𝓝[>] 0) := by
  rw [tendsto_nhdsWithin_iff]
  constructor
  · have hh := (Real.continuous_sin.continuousAt.comp (continuousAt_extendedPhase q t Real.pi
      ⟨Real.pi_pos.le,le_rfl⟩)).tendsto.mono_left
        (show 𝓝[<] Real.pi ≤ 𝓝 Real.pi from nhdsWithin_le_nhds)
    simpa only [Function.comp_def,Geometry.jointAngle_actual q t ⟨Real.pi_pos.le,le_rfl⟩,
      Geometry.shiftedAngle_pi,Real.sin_pi] using hh
  · have hb : ∀ᶠ x : ℝ in 𝓝 Real.pi, 0 < x := Ioi_mem_nhds Real.pi_pos
    filter_upwards [self_mem_nhdsWithin, hb.filter_mono nhdsWithin_le_nhds] with x hx h0
    rw [Geometry.jointAngle_actual q t ⟨h0.le,hx.le⟩]
    exact Real.sin_pos_of_pos_of_lt_pi (Geometry.shiftedAngle_mem q t ⟨h0,hx⟩).1
      (Geometry.shiftedAngle_mem q t ⟨h0,hx⟩).2

theorem regularPotential_tendsto_at_zero (D : RegularData q t L) :
    Tendsto (extendedPotential D) (𝓝[>] 0) atTop := by
  have hsub : 𝓝[>] (0:ℝ) ≤ 𝓝[≠] 0 := nhdsWithin_mono _ (fun x hx => ne_of_gt hx)
  have hS := (analytic_quadratic_limit
    (analyticAt_finiteSymbol q t D.lags D.dual ⟨le_rfl,Real.pi_pos.le⟩)
    D.symbol_zero_endpoint D.symbol_slope_zero).neg.mono_left hsub
  have hp : AnalyticAt ℝ (pinningPolynomial D.lags D.dual) 0 := by
    unfold pinningPolynomial
    apply Finset.analyticAt_fun_sum
    intro n _
    fun_prop
  have hP := (analytic_quadratic_limit hp (by simp [pinningPolynomial])
    (pinning_deriv_zero D.lags D.dual)).mono_left hsub
  have hPpos := regular_pinning_second_pos D
  have hSpos : 0 < -deriv (deriv (finiteSymbol q t D.lags D.dual)) 0 := by
    exact neg_pos.mpr D.symbol_curvature_zero
  have hc : 0 < (-(deriv (deriv (finiteSymbol q t D.lags D.dual)) 0 / 2)) /
      (deriv (deriv (pinningPolynomial D.lags D.dual)) 0 / 2) := by
    apply div_pos
    · rw [← neg_div]
      exact div_pos hSpos (by norm_num)
    · exact div_pos hPpos (by norm_num)
  have hpne : deriv (deriv (pinningPolynomial D.lags D.dual)) 0 / 2 ≠ 0 :=
    (div_pos hPpos (by norm_num)).ne'
  have hr := hS.div hP hpne
  have htop := quotient_atTop hr hc (phaseSine_tendsto_zero_right q t)
  apply htop.congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  unfold extendedPotential
  have hx0 : x ≠ (0:ℝ) := ne_of_gt hx
  dsimp only [Pi.div_apply]
  simp only [sub_zero]
  field_simp [hx0]

theorem regularPotential_tendsto_at_pi (D : RegularData q t L) :
    Tendsto (extendedPotential D) (𝓝[<] Real.pi) atTop := by
  have hS : ContinuousAt (finiteSymbol q t D.lags D.dual) Real.pi :=
    (analyticAt_finiteSymbol q t D.lags D.dual ⟨Real.pi_pos.le,le_rfl⟩).continuousAt
  have hP : Continuous (pinningPolynomial D.lags D.dual) := by
    unfold pinningPolynomial
    fun_prop
  have hPpos : 0 < pinningPolynomial D.lags D.dual Real.pi :=
    regular_pinning_pos D frequencyPi Real.pi_pos
  have hSneg : finiteSymbol q t D.lags D.dual Real.pi < 0 :=
    D.dual_strict Real.pi Real.pi_pos le_rfl (fun i hi => (D.atoms_lt_pi i).ne hi.symm)
  have hr := (hS.neg.div hP.continuousAt hPpos.ne').tendsto.mono_left
    (show 𝓝[<] Real.pi ≤ 𝓝 Real.pi from nhdsWithin_le_nhds)
  have htop := quotient_atTop hr (div_pos (neg_pos.mpr hSneg) hPpos)
    (phaseSine_tendsto_zero_left q t)
  apply htop.congr'
  exact Filter.Eventually.of_forall fun x => by
    unfold extendedPotential
    dsimp only [Pi.div_apply,Pi.neg_apply]
    ring

end polyak.ModeLocking.Localization
