import krylov.Strings.OptimizerQuadratures
import krylov.LotkaVolterra.GlobalLogisticShooting
import krylov.LotkaVolterra.GlobalBoundedODE
import krylov.LotkaVolterra.GlobalLowerIdentity

/-!
Article: main_krylov, thm:value, actual subcritical optimizer data.
Use: turn the constructed whole logistic stable branch into a genuine global
forward LV orbit by solving its positive bounded scalar time change.
Source: compact shooting, the proved bounded-field continuation theorem,
and the logistic parametrization of the lower saddle branch.
-/

namespace krylov.Strings.OptimizerQuadratures
noncomputable section
open Set Filter MeasureTheory
open scoped Topology NNReal
open krylov.LotkaVolterra

/-- The logistic graph parameter satisfies its exact scalar derivative equation. -/
theorem logisticParameter_derivative (t : ℝ) :
    HasDerivAt logisticParameter (-logisticParameter t * (1 - logisticParameter t)) t := by
  have hd := (hasDerivAt_const t (1 : ℝ)).div
    ((Real.hasDerivAt_exp t).const_add 1) (by linarith [Real.exp_pos t] : 1 + Real.exp t ≠ 0)
  convert hd using 1
  · rfl
  · dsimp [logisticParameter]
    field_simp
    ring

/-- The logistic graph parameter tends to zero at the saddle end. -/
theorem logisticParameter_tendsto_zero : Tendsto logisticParameter atTop (𝓝 0) := by
  have h := tendsto_inv_atTop_zero.comp
    (tendsto_atTop_add_const_left atTop 1 Real.tendsto_exp_atTop)
  change Tendsto (fun t : ℝ ↦ 1 / (1 + Real.exp t)) atTop (𝓝 0)
  simpa only [Function.comp_def, one_div] using h

/-- A bounded positive speed creates a genuine global increasing time change
which reaches arbitrarily large branch parameters. -/
theorem exists_positive_timechange {γ B : ℝ} {v : ℝ → ℝ} {L : ℝ≥0}
    (hγ₁ : γ < 1) (hB : 0 < B) (hv : ∀ t, v t ∈ Ioo 0 γ)
    (hLip : LipschitzWith L v) (a : ℝ) :
    ∃ T : ℝ → ℝ, T 0 = a ∧
      (∀ t, HasDerivAt T (B * (1 - v (T t))) t) ∧
      (∀ t ≥ 0, a + B * (1 - γ) * t ≤ T t) ∧ Tendsto T atTop atTop := by
  let b : ℝ≥0 := ⟨B, hB.le⟩
  have hfLip : ∀ t : ℝ, LipschitzWith (b * L) (fun u ↦ B * (1 - v u)) := by
    intro _
    apply LipschitzWith.of_dist_le_mul
    intro x y
    have he : B * (1 - v x) - B * (1 - v y) = -B * (v x - v y) := by ring
    rw [Real.dist_eq, he, abs_mul, abs_neg, abs_of_pos hB]
    have hh := mul_le_mul_of_nonneg_left (hLip.dist_le_mul x y) hB.le
    change B * |v x - v y| ≤ (B * L) * |x - y|
    simpa only [Real.dist_eq, mul_assoc] using hh
  have hfbound : ∀ t u : ℝ, ‖B * (1 - v u)‖ ≤ b := by
    intro _ u
    rw [Real.norm_eq_abs, abs_of_pos (mul_pos hB (by linarith [(hv u).2]))]
    change B * (1 - v u) ≤ B
    nlinarith [(hv u).1]
  obtain ⟨T, hT₀, hT⟩ := exists_global_solution_of_bounded_lipschitz
    (f := fun _ u ↦ B * (1 - v u)) hfLip (fun _ ↦ continuous_const) hfbound a
  have hdiff (t : ℝ) : HasDerivAt (fun t ↦ T t - B * (1 - γ) * t)
      (B * (γ - v (T t))) t := by
    convert (hT t).sub ((hasDerivAt_id t).const_mul (B * (1 - γ))) using 1
    · rfl
    · ring
  have hmono : Monotone (fun t ↦ T t - B * (1 - γ) * t) :=
    monotone_of_hasDerivAt_nonneg hdiff
      (fun t ↦ mul_nonneg hB.le (by linarith [(hv (T t)).2]))
  have hlinear (t : ℝ) (ht : 0 ≤ t) : a + B * (1 - γ) * t ≤ T t := by
    have hh := hmono ht
    dsimp only at hh
    rw [hT₀] at hh
    linarith
  refine ⟨T, hT₀, hT, hlinear, ?_⟩
  have hl : Tendsto (fun t : ℝ ↦ a + B * (1 - γ) * t) atTop atTop := by
    exact tendsto_atTop_add_const_left atTop a
      (tendsto_id.const_mul_atTop (mul_pos hB (by linarith)))
  apply tendsto_atTop_mono' atTop (f₁ := fun t : ℝ ↦ a + B * (1 - γ) * t) _ hl
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
  exact hlinear t ht

/-- The actual bounded lower-branch logistic slope is globally Lipschitz. -/
theorem logistic_slope_lipschitz {γ : ℝ} (hγ₁ : γ < 1) {v : ℝ → ℝ}
    (hv : ∀ t, v t ∈ Ioo 0 γ ∧
      HasDerivAt v (logisticSlopeRate γ true (logisticParameter t) (v t)) t) :
    ∃ L : ℝ≥0, LipschitzWith L v := by
  obtain ⟨L, _, hbound, _⟩ := logisticSlopeRate_uniform_bounds hγ₁ true
  refine ⟨L, lipschitzWith_of_nnnorm_deriv_le (fun t ↦ (hv t).2.differentiableAt) ?_⟩
  intro t
  rw [(hv t).2.deriv]
  exact_mod_cast hbound _ ⟨(logisticParameter_mem t).1.le, (logisticParameter_mem t).2.le⟩
    _ ⟨(hv t).1.1.le, (hv t).1.2.le⟩

/-- The lower-branch control state reconstructed from its bounded logistic slope. -/
def lowerOrbitS (γ : ℝ) (v : ℝ → ℝ) (t : ℝ) : ℝ :=
  saddleS γ - saddleU γ * logisticParameter t * v t

/-- The lower-branch ratio coordinate ranges between zero and the saddle ratio. -/
def lowerOrbitU (γ t : ℝ) : ℝ := saddleU γ * (1 - logisticParameter t)

/-- The bounded positive lower-branch clock recovers both original LV derivatives. -/
theorem lowerOrbit_derivatives {γ : ℝ} (hγ₁ : γ < 1) {v T : ℝ → ℝ}
    (hv : ∀ t, v t ∈ Ioo 0 γ ∧
      HasDerivAt v (logisticSlopeRate γ true (logisticParameter t) (v t)) t)
    (hT : ∀ t, HasDerivAt T (saddleU γ * (1 - v (T t))) t) (t : ℝ) :
    HasDerivAt (fun u ↦ lowerOrbitS γ v (T u))
        (sRate γ (lowerOrbitS γ v (T t)) (lowerOrbitU γ (T t))) t ∧
      HasDerivAt (fun u ↦ lowerOrbitU γ (T u))
        (uRate (lowerOrbitS γ v (T t)) (lowerOrbitU γ (T t))) t := by
  have hs := (((logisticParameter_derivative (T t)).const_mul (saddleU γ)).mul
    (hv (T t)).2).const_sub (saddleS γ)
  have hU := ((logisticParameter_derivative (T t)).const_sub 1).const_mul (saddleU γ)
  have hn : 1 - v (T t) ≠ 0 := by linarith [(hv (T t)).1.2]
  have hg : 1 - γ ≠ 0 := by linarith
  constructor
  · convert hs.comp t (hT t) using 1
    · rfl
    · dsimp [lowerOrbitS, lowerOrbitU, sRate, logisticSlopeRate, logisticP,
        logisticQ, logisticR, saddleS, saddleU]
      field_simp
      ring
  · convert hU.comp t (hT t) using 1
    · rfl
    · dsimp [lowerOrbitS, lowerOrbitU, uRate, saddleS, saddleU]
      field_simp
      ring

/-- The lower stable branch generates an actual global forward LV orbit,
initialized at U=1 and converging to the interior saddle. -/
theorem exists_subcritical_data {γ : ℝ} (hγ : 0 < γ) (hγ₁ : γ < 1) :
    ∃ s U : ℝ → ℝ, Continuous s ∧ Continuous U ∧ U 0 = 1 ∧
      (∀ t, 1 < s t ∧ 0 < U t) ∧
      (∀ t ≥ 0, 1 ≤ U t) ∧
      (∀ t, 1 + γ * U t < s t ∧ s t < saddleS γ) ∧
      (∀ t, HasDerivAt s (2 * s t * (s t - 1 - γ * U t)) t ∧
        HasDerivAt U (U t * (s t + 1 - U t)) t) ∧
      Tendsto s atTop (𝓝 (saddleS γ)) ∧ Tendsto U atTop (𝓝 (saddleU γ)) ∧
      (∃ C : ℝ, 0 < C ∧ ∀ t ≥ 0,
        |s t - saddleS γ| + |U t - saddleU γ| ≤ C * Real.exp (-2 * t)) ∧
      (∀ G : SubcriticalGraph γ, s 0 = G.σ 1) ∧
      ∀ G : SubcriticalGraph γ, ∀ t, s t = G.σ (U t) := by
  obtain ⟨v, hv⟩ := exists_whole_logistic_slope hγ hγ₁ true
  obtain ⟨L, hLip⟩ := logistic_slope_lipschitz hγ₁ hv
  let B := saddleU γ
  have hB : 0 < B := saddleU_pos hγ₁
  have hB₁ : 1 < B := by
    dsimp [B, saddleU]
    exact (one_lt_div (by linarith : 0 < 1 - γ)).mpr (by linarith)
  let a := Real.log (1 / (B - 1))
  obtain ⟨T, hT₀, hT, hlinear, hTinf⟩ :=
    exists_positive_timechange hγ₁ hB (fun t ↦ (hv t).1) hLip a
  let s : ℝ → ℝ := fun t ↦ lowerOrbitS γ v (T t)
  let U : ℝ → ℝ := fun t ↦ lowerOrbitU γ (T t)
  have hd (t : ℝ) := lowerOrbit_derivatives hγ₁ hv hT t
  have hs : Continuous s := continuous_iff_continuousAt.mpr (fun t ↦ (hd t).1.continuousAt)
  have hU : Continuous U := continuous_iff_continuousAt.mpr (fun t ↦ (hd t).2.continuousAt)
  have hq : logisticParameter a = (B - 1) / B := by
    dsimp [a, logisticParameter]
    rw [Real.exp_log (div_pos (by norm_num) (by linarith : 0 < B - 1))]
    field_simp [hB.ne', (by linarith : B - 1 ≠ 0)]
    ring
  have hU₀ : U 0 = 1 := by
    dsimp [U, lowerOrbitU]
    rw [hT₀, hq]
    change B * (1 - (B - 1) / B) = 1
    field_simp
    ring
  have hpos (t : ℝ) : 1 < s t ∧ 0 < U t := by
    have hqt := logisticParameter_mem (T t)
    have hvn := (hv (T t)).1
    have hUp : 0 < U t := mul_pos hB (by linarith [hqt.2])
    have hrel := saddleS_eq_one_add_mul_saddleU (ne_of_lt hγ₁)
    have hprod : 0 < B * logisticParameter (T t) * (γ - v (T t)) :=
      mul_pos (mul_pos hB hqt.1) (sub_pos.mpr hvn.2)
    constructor
    · dsimp [s, U, lowerOrbitS, lowerOrbitU] at *
      rw [hrel]
      nlinarith [mul_pos hγ hUp]
    · exact hUp
  have hTmono : StrictMono T := strictMono_of_hasDerivAt_pos hT
    (fun t ↦ mul_pos hB (by linarith [(hv (T t)).1.2]))
  have hUbranch : StrictMono (lowerOrbitU γ) := by
    apply strictMono_of_hasDerivAt_pos
      (fun t ↦ ((logisticParameter_derivative t).const_sub 1).const_mul (saddleU γ))
    intro t
    have hqpos := logisticParameter_mem t
    nlinarith [mul_pos (mul_pos hB hqpos.1) (sub_pos.mpr hqpos.2)]
  have hUone : ∀ t ≥ 0, 1 ≤ U t := by
    intro t ht
    have hh := (hUbranch.comp hTmono).monotone ht
    change U 0 ≤ U t at hh
    simpa only [hU₀] using hh
  have hcorr (t : ℝ) : 1 + γ * U t < s t ∧ s t < saddleS γ := by
    have hqt := logisticParameter_mem (T t)
    have hvn := (hv (T t)).1
    have hrel := saddleS_eq_one_add_mul_saddleU (ne_of_lt hγ₁)
    have hprod : 0 < B * logisticParameter (T t) * (γ - v (T t)) :=
      mul_pos (mul_pos hB hqt.1) (sub_pos.mpr hvn.2)
    have hprod' : 0 < B * logisticParameter (T t) * v (T t) :=
      mul_pos (mul_pos hB hqt.1) hvn.1
    dsimp [s, U, lowerOrbitS, lowerOrbitU]
    constructor
    · rw [hrel]
      dsimp [B] at hprod
      nlinarith
    · linarith
  have hqinf := logisticParameter_tendsto_zero.comp hTinf
  have hqvinf : Tendsto (fun t ↦ logisticParameter (T t) * v (T t)) atTop (𝓝 0) := by
    apply squeeze_zero_norm' (Eventually.of_forall (fun t ↦ ?_))
      (by simpa using hqinf.norm.const_mul γ)
    simp only [norm_mul, Real.norm_eq_abs, abs_of_pos (hv (T t)).1.1]
    nlinarith [abs_nonneg (logisticParameter (T t)), (hv (T t)).1.2]
  refine ⟨s, U, hs, hU, hU₀, hpos, hUone, hcorr, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t
    simpa only [sRate, uRate] using hd t
  · have hh := (tendsto_const_nhds (x := saddleS γ)).sub (hqvinf.const_mul B)
    simpa only [s, lowerOrbitS, mul_zero, sub_zero, mul_assoc] using hh
  · have hh := ((tendsto_const_nhds (x := (1 : ℝ))).sub hqinf).const_mul B
    simpa only [U, lowerOrbitU, sub_zero, mul_one, Function.comp_def, B] using hh
  · refine ⟨(1 + γ) * B * Real.exp (-a), by positivity, ?_⟩
    intro t ht
    have hBcancel : B * (1 - γ) = 2 := by
      dsimp [B, saddleU]
      field_simp [(by linarith : 1 - γ ≠ 0)]
    have hTlow : a + 2 * t ≤ T t := by simpa only [hBcancel] using hlinear t ht
    have hqexp : logisticParameter (T t) ≤ Real.exp (-a) * Real.exp (-2 * t) := by
      calc
        logisticParameter (T t) ≤ 1 / Real.exp (T t) :=
          one_div_le_one_div_of_le (Real.exp_pos _) (by linarith)
        _ = Real.exp (-T t) := by rw [Real.exp_neg, one_div]
        _ ≤ Real.exp (-a + (-2 * t)) := Real.exp_le_exp.mpr (by linarith)
        _ = _ := Real.exp_add _ _
    have hqt := logisticParameter_mem (T t)
    have hvn := (hv (T t)).1
    have hsabs : |s t - saddleS γ| = B * logisticParameter (T t) * v (T t) := by
      dsimp [s, lowerOrbitS]
      rw [sub_sub_cancel_left, abs_neg, abs_of_pos (mul_pos (mul_pos hB hqt.1) hvn.1)]
    have hUabs : |U t - saddleU γ| = B * logisticParameter (T t) := by
      have heq : U t - saddleU γ = -(B * logisticParameter (T t)) := by
        dsimp [U, lowerOrbitU, B]
        ring
      rw [heq, abs_neg, abs_of_pos (mul_pos hB hqt.1)]
    rw [hsabs, hUabs]
    calc
      _ ≤ B * logisticParameter (T t) * γ + B * logisticParameter (T t) :=
        add_le_add (mul_le_mul_of_nonneg_left hvn.2.le (mul_pos hB hqt.1).le) le_rfl
      _ = ((1 + γ) * B) * logisticParameter (T t) := by ring
      _ ≤ ((1 + γ) * B) * (Real.exp (-a) * Real.exp (-2 * t)) :=
        mul_le_mul_of_nonneg_left hqexp (mul_pos (by linarith) hB).le
      _ = _ := by ring
  · intro G
    have hg := G.graph_eq_lower_logistic hγ hγ₁
      (fun t ↦ ⟨⟨(hv t).1.1.le, (hv t).1.2.le⟩, (hv t).2⟩)
      (show (1 : ℝ) ∈ Ioo 0 (saddleU γ) from ⟨by norm_num, hB₁⟩)
    have ha : lowerGraphTime γ 1 = a := rfl
    rw [hg, ha]
    dsimp [s, lowerOrbitS]
    rw [hT₀, hq]
    change saddleS γ - B * ((B - 1) / B) * v a = saddleS γ - v a * (B - 1)
    field_simp [hB.ne']
  · intro G t
    have he := congrFun (G.lowerLogisticSlope_eq hγ hγ₁
      (fun t ↦ ⟨⟨(hv t).1.1.le, (hv t).1.2.le⟩, (hv t).2⟩)) (T t)
    change (saddleS γ - G.σ (B - B / 2 * (2 * logisticParameter (T t)))) /
      (B / 2 * (2 * logisticParameter (T t))) = v (T t) at he
    have hden : B / 2 * (2 * logisticParameter (T t)) = B * logisticParameter (T t) := by ring
    have harg : B - B * logisticParameter (T t) = U t := by
      dsimp [U, lowerOrbitU, B]
      ring
    rw [hden, harg] at he
    have hm := (div_eq_iff (mul_pos hB (logisticParameter_mem (T t)).1).ne').mp he
    change saddleS γ - B * logisticParameter (T t) * v (T t) = G.σ (U t)
    linarith

end
end krylov.Strings.OptimizerQuadratures
