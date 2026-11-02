import krylov.Strings.OptimizerSubcriticalData
import krylov.LotkaVolterra.GlobalUpperIdentity

/-!
Article: main_krylov, apC:prop:LV, actual forward stable orbits.
Use: every positive point of either branch of the separating graph has a
global forward solution in the original LV time, converging to the saddle.
The logarithmic graph parameter is converted to LV time by a positive
bounded scalar ODE; the upper clock is clipped only below its initial value.
Source: the proved graph shooting construction and Picard continuation for
bounded Lipschitz fields. A graph parametrization alone is not used as a
substitute for an original-time solution.
-/

namespace krylov.Strings.OptimizerQuadratures
noncomputable section
open Set Filter
open krylov.LotkaVolterra
open scoped Topology NNReal

/-- A reusable positive-speed time change, with no constant-speed factor
assumed. Its linear lower bound ensures that the whole forward graph is
traversed in unbounded original time. -/
theorem exists_bounded_positive_timechange {F : ℝ → ℝ} {L B : ℝ≥0} {c : ℝ}
    (hc : 0 < c) (hLip : LipschitzWith L F) (hlower : ∀ x, c ≤ F x)
    (hbound : ∀ x, ‖F x‖ ≤ B) (a : ℝ) :
    ∃ T : ℝ → ℝ, T 0 = a ∧ (∀ t, HasDerivAt T (F (T t)) t) ∧
      (∀ t ≥ 0, a + c * t ≤ T t) ∧ Tendsto T atTop atTop := by
  obtain ⟨T, hT₀, hT⟩ := exists_global_solution_of_bounded_lipschitz
    (f := fun _ ↦ F) (fun _ ↦ hLip) (fun _ ↦ continuous_const)
    (fun _ x ↦ hbound x) a
  have hd (t : ℝ) : HasDerivAt (fun t ↦ T t - c * t) (F (T t) - c) t := by
    convert (hT t).sub ((hasDerivAt_id t).const_mul c) using 1
    · rfl
    · ring
  have hm := monotone_of_hasDerivAt_nonneg hd (fun t ↦ sub_nonneg.mpr (hlower (T t)))
  have hlin (t : ℝ) (ht : 0 ≤ t) : a + c * t ≤ T t := by
    have hh := hm ht
    dsimp only at hh
    rw [hT₀] at hh
    linarith
  refine ⟨T, hT₀, hT, hlin, ?_⟩
  apply tendsto_atTop_mono' atTop (f₁ := fun t : ℝ ↦ a + c * t) _
    (tendsto_atTop_add_const_left atTop a (tendsto_id.const_mul_atTop hc))
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
  exact hlin t ht

/-- The actual bounded logistic slope on either branch is globally Lipschitz. -/
theorem logistic_slope_lipschitz_both {γ : ℝ} (hγ₁ : γ < 1) (lower : Bool)
    {v : ℝ → ℝ} (hv : ∀ t, v t ∈ Ioo 0 γ ∧
      HasDerivAt v (logisticSlopeRate γ lower (logisticParameter t) (v t)) t) :
    ∃ L : ℝ≥0, LipschitzWith L v := by
  obtain ⟨L, _, hbound, _⟩ := logisticSlopeRate_uniform_bounds hγ₁ lower
  refine ⟨L, lipschitzWith_of_nnnorm_deriv_le (fun t ↦ (hv t).2.differentiableAt) ?_⟩
  intro t
  rw [(hv t).2.deriv]
  exact_mod_cast hbound _ ⟨(logisticParameter_mem t).1.le, (logisticParameter_mem t).2.le⟩
    _ ⟨(hv t).1.1.le, (hv t).1.2.le⟩

/-- Clamping below the initial parameter makes the decaying exponential globally Lipschitz. -/
theorem exp_neg_max_lipschitz (a : ℝ) :
    LipschitzWith ⟨Real.exp (-a), (Real.exp_pos _).le⟩
      (fun x : ℝ ↦ Real.exp (-max x a)) := by
  let C : ℝ≥0 := ⟨Real.exp (-a), (Real.exp_pos _).le⟩
  have he : LipschitzOnWith C (fun x : ℝ ↦ Real.exp (-x)) (Ici a) := by
    apply (convex_Ici a).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
      (fun x _ ↦ ((hasDerivAt_id x).neg.exp).hasDerivWithinAt)
    intro x hx
    change ‖Real.exp (-x) * -1‖₊ ≤ C
    simp only [mul_neg_one, nnnorm_neg, Real.nnnorm_of_nonneg (Real.exp_pos _).le]
    exact_mod_cast Real.exp_le_exp.mpr (neg_le_neg hx)
  have hm := LipschitzWith.id.max_const a
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have hx : max x a ∈ Ici a := by change a ≤ max x a; exact le_max_right x a
  have hy : max y a ∈ Ici a := by change a ≤ max y a; exact le_max_right y a
  have hh := he.dist_le_mul _ hx _ hy
  change dist (Real.exp (-max x a)) (Real.exp (-max y a)) ≤
    Real.exp (-a) * dist (max x a) (max y a) at hh
  change dist (Real.exp (-max x a)) (Real.exp (-max y a)) ≤ Real.exp (-a) * dist x y
  exact hh.trans (mul_le_mul_of_nonneg_left (by simpa using hm.dist_le_mul x y)
    (Real.exp_pos (-a)).le)

/-- The full upper-branch ratio coordinate in logarithmic graph time. -/
def upperOrbitU (γ t : ℝ) : ℝ := saddleU γ * (1 + Real.exp (-t))

/-- The full upper-branch control state reconstructed from its bounded logistic chord. -/
def upperOrbitS (γ : ℝ) (v : ℝ → ℝ) (t : ℝ) : ℝ :=
  saddleS γ + saddleU γ * Real.exp (-t) * v t

/-- The positive upper-branch clock recovers both original LV derivatives. -/
theorem upperOrbit_derivatives {γ : ℝ} (hγ₁ : γ < 1) {v T : ℝ → ℝ}
    (hv : ∀ t, v t ∈ Ioo 0 γ ∧
      HasDerivAt v (logisticSlopeRate γ false (logisticParameter t) (v t)) t)
    (t : ℝ) (hT : HasDerivAt T (upperOrbitU γ (T t) * (1 - v (T t))) t) :
    HasDerivAt (fun u ↦ upperOrbitS γ v (T u))
        (sRate γ (upperOrbitS γ v (T t)) (upperOrbitU γ (T t))) t ∧
      HasDerivAt (fun u ↦ upperOrbitU γ (T u))
        (uRate (upperOrbitS γ v (T t)) (upperOrbitU γ (T t))) t := by
  have hs := ((((hasDerivAt_id (T t)).neg.exp).const_mul (saddleU γ)).mul
    (hv (T t)).2).const_add (saddleS γ)
  have hU := (((hasDerivAt_id (T t)).neg.exp).const_add 1).const_mul (saddleU γ)
  have hn : 1 - v (T t) ≠ 0 := by linarith [(hv (T t)).1.2]
  have hg : 1 - γ ≠ 0 := by linarith
  have hlog : logisticParameter (T t) = Real.exp (-T t) / (1 + Real.exp (-T t)) := by
    unfold logisticParameter
    rw [Real.exp_neg]
    field_simp
    ring
  have hden : 1 + Real.exp (-T t) ≠ 0 := by positivity
  constructor
  · convert hs.comp t hT using 1
    · rfl
    · dsimp [upperOrbitS, upperOrbitU, sRate, logisticSlopeRate, logisticP,
        logisticQ, logisticR, saddleS, saddleU]
      rw [hlog]
      field_simp
      ring
  · convert hU.comp t hT using 1
    · rfl
    · dsimp [upperOrbitS, upperOrbitU, uRate, saddleS, saddleU]
      field_simp
      ring

/-- A clipped bounded positive clock gives genuine global forward LV time on the upper branch. -/
theorem exists_upper_timechange {γ : ℝ} (hγ₁ : γ < 1) {v : ℝ → ℝ}
    (hv : ∀ t, v t ∈ Ioo 0 γ) {L : ℝ≥0} (hLip : LipschitzWith L v) (a : ℝ) :
    ∃ T : ℝ → ℝ, T 0 = a ∧
      (∀ t ≥ 0, HasDerivAt T (upperOrbitU γ (T t) * (1 - v (T t))) t) ∧
      (∀ t ≥ 0, a + 2 * t ≤ T t) ∧ Tendsto T atTop atTop := by
  let B := saddleU γ
  have hB : 0 < B := saddleU_pos hγ₁
  let A : ℝ → ℝ := fun x ↦ B * (1 + Real.exp (-max x a))
  let D : ℝ := B * (1 + Real.exp (-a))
  have hD : 0 < D := by dsimp [D]; positivity
  have hA (x : ℝ) : B ≤ A x ∧ A x ≤ D := by
    have he := Real.exp_le_exp.mpr (neg_le_neg (le_max_right x a))
    dsimp [A, D]
    constructor
    · nlinarith [Real.exp_pos (-max x a)]
    · exact mul_le_mul_of_nonneg_left (by linarith) hB.le
  let LA : ℝ≥0 := ⟨B * Real.exp (-a), by positivity⟩
  have hALip : LipschitzWith LA A := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    have hh := mul_le_mul_of_nonneg_left ((exp_neg_max_lipschitz a).dist_le_mul x y) hB.le
    change dist (B * (1 + Real.exp (-max x a))) (B * (1 + Real.exp (-max y a))) ≤ _
    rw [Real.dist_eq, show B * (1 + Real.exp (-max x a)) -
      B * (1 + Real.exp (-max y a)) = B * (Real.exp (-max x a) - Real.exp (-max y a)) by ring,
      abs_mul, abs_of_pos hB]
    change B * |Real.exp (-max x a) - Real.exp (-max y a)| ≤
      B * (Real.exp (-a) * |x - y|) at hh
    change B * |Real.exp (-max x a) - Real.exp (-max y a)| ≤
      (B * Real.exp (-a)) * |x - y|
    simpa only [mul_assoc] using hh
  let F : ℝ → ℝ := fun x ↦ A x * (1 - v x)
  let LF : ℝ≥0 := ⟨D, hD.le⟩ * L + LA
  have hFLip : LipschitzWith LF F := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    have hxA : |A x| ≤ D := by rw [abs_of_pos (hB.trans_le (hA x).1)]; exact (hA x).2
    have hyv : |1 - v y| ≤ 1 := by rw [abs_of_pos (by linarith [(hv y).2])]; linarith [(hv y).1]
    have hid : F x - F y = A x * (v y - v x) + (A x - A y) * (1 - v y) := by dsimp [F]; ring
    rw [Real.dist_eq, hid]
    calc
      _ ≤ |A x| * |v y - v x| + |A x - A y| * |1 - v y| := by
        simpa only [abs_mul] using abs_add_le (A x * (v y - v x)) ((A x - A y) * (1 - v y))
      _ ≤ D * (L * |x - y|) + (LA * |x - y|) * 1 := by
        apply add_le_add
        · exact mul_le_mul hxA (by simpa only [Real.dist_eq, abs_sub_comm] using hLip.dist_le_mul x y)
            (abs_nonneg _) hD.le
        · exact mul_le_mul (by simpa only [Real.dist_eq] using hALip.dist_le_mul x y) hyv
            (abs_nonneg _) (mul_nonneg LA.coe_nonneg (abs_nonneg _))
      _ = LF * dist x y := by
        change D * (L * |x - y|) + (LA * |x - y|) * 1 = (D * L + LA) * |x - y|
        ring
  have hFbound (x : ℝ) : ‖F x‖ ≤ (⟨D, hD.le⟩ : ℝ≥0) := by
    have hpos : 0 < F x := mul_pos (hB.trans_le (hA x).1) (by linarith [(hv x).2])
    rw [Real.norm_eq_abs, abs_of_pos hpos]
    change A x * (1 - v x) ≤ D
    nlinarith [(hA x).2, (hv x).1, (hA x).1]
  have hFlower (x : ℝ) : 2 ≤ F x := by
    have hBcancel : B * (1 - γ) = 2 := by
      dsimp [B, saddleU]
      field_simp [(by linarith : 1 - γ ≠ 0)]
    calc
      2 = B * (1 - γ) := hBcancel.symm
      _ ≤ A x * (1 - v x) := mul_le_mul (hA x).1 (by linarith [(hv x).2])
        (by linarith) (hB.trans_le (hA x).1).le
  obtain ⟨T, hT₀, hT, hlin, hinf⟩ := exists_bounded_positive_timechange
    (by norm_num : (0 : ℝ) < 2) hFLip hFlower hFbound a
  refine ⟨T, hT₀, ?_, hlin, hinf⟩
  intro t ht
  have hTa : a ≤ T t := by linarith [hlin t ht]
  simpa only [F, A, max_eq_left hTa, upperOrbitU, B] using hT t

/-- Original-time global forward existence on the full separating graph,
including its upper branch and the stationary saddle. -/
theorem exists_global_stable_orbit_with_branch {γ U₀ : ℝ} (hγ : 0 < γ) (hγ₁ : γ < 1)
    (G : SubcriticalGraph γ) (hU₀ : 0 < U₀) :
    ∃ s U : ℝ → ℝ, s 0 = G.σ U₀ ∧ U 0 = U₀ ∧
      (∀ t ≥ 0, HasDerivAt s (sRate γ (s t) (U t)) t ∧
        HasDerivAt U (uRate (s t) (U t)) t) ∧
      (∀ t ≥ 0, s t = G.σ (U t) ∧ 0 < s t ∧ 0 < U t) ∧
      (∀ t ≥ 0, (U₀ < saddleU γ → U t < saddleU γ) ∧
        (saddleU γ < U₀ → saddleU γ < U t)) ∧
      Tendsto s atTop (𝓝 (saddleS γ)) ∧ Tendsto U atTop (𝓝 (saddleU γ)) := by
  have hB : 0 < saddleU γ := saddleU_pos hγ₁
  rcases lt_trichotomy U₀ (saddleU γ) with hlow | heq | hupp
  · let v := G.lowerLogisticSlope
    have hv (t : ℝ) : v t ∈ Ioo 0 γ ∧
        HasDerivAt v (logisticSlopeRate γ true (logisticParameter t) (v t)) t :=
      ⟨G.lowerLogisticSlope_bounds hγ₁ t, G.lowerLogisticSlope_hasDerivAt hγ₁ t⟩
    obtain ⟨L, hLip⟩ := logistic_slope_lipschitz hγ₁ hv
    let a := lowerGraphTime γ U₀
    obtain ⟨T, hT₀, hT, _, hinf⟩ := exists_positive_timechange hγ₁ hB (fun t ↦ (hv t).1) hLip a
    let s := fun t ↦ lowerOrbitS γ v (T t)
    let U := fun t ↦ lowerOrbitU γ (T t)
    have hUzero : U 0 = U₀ := by
      dsimp [U, lowerOrbitU]
      rw [hT₀, lowerGraphTime_parameter hγ₁ ⟨hU₀, hlow⟩]
      field_simp
      ring
    have hgraph (t : ℝ) : s t = G.σ (U t) := by
      have hh := congrFun (G.lowerLogisticSlope_eq hγ hγ₁
        (fun t ↦ ⟨⟨(hv t).1.1.le, (hv t).1.2.le⟩, (hv t).2⟩)) (T t)
      change (saddleS γ - G.σ (saddleU γ - saddleU γ / 2 * (2 * logisticParameter (T t)))) /
        (saddleU γ / 2 * (2 * logisticParameter (T t))) = v (T t) at hh
      have hden : saddleU γ / 2 * (2 * logisticParameter (T t)) = saddleU γ * logisticParameter (T t) := by ring
      have harg : saddleU γ - saddleU γ * logisticParameter (T t) = U t := by dsimp [U, lowerOrbitU]; ring
      rw [hden, harg] at hh
      have hm := (div_eq_iff (mul_pos hB (logisticParameter_mem (T t)).1).ne').mp hh
      change saddleS γ - saddleU γ * logisticParameter (T t) * v (T t) = G.σ (U t)
      linarith
    have hUp (t : ℝ) : 0 < U t := mul_pos hB (sub_pos.mpr (logisticParameter_mem (T t)).2)
    have hqinf := logisticParameter_tendsto_zero.comp hinf
    have hqv : Tendsto (fun t ↦ logisticParameter (T t) * v (T t)) atTop (𝓝 0) := by
      apply squeeze_zero_norm' (Eventually.of_forall (fun t ↦ ?_))
        (by simpa using hqinf.norm.const_mul γ)
      simp only [norm_mul, Real.norm_eq_abs, abs_of_pos (hv (T t)).1.1]
      nlinarith [abs_nonneg (logisticParameter (T t)), (hv (T t)).1.2]
    refine ⟨s, U, by rw [hgraph, hUzero], hUzero,
      fun t _ ↦ lowerOrbit_derivatives hγ₁ hv hT t,
      fun t _ ↦ ⟨hgraph t, ?_, hUp t⟩, ?_, ?_, ?_⟩
    · rw [hgraph]
      exact G.positive hγ hγ₁ (hUp t)
    · intro t _
      refine ⟨fun _ ↦ ?_, fun h ↦ (not_lt_of_gt hlow h).elim⟩
      change saddleU γ * (1 - logisticParameter (T t)) < saddleU γ
      nlinarith [mul_pos hB (logisticParameter_mem (T t)).1]
    · simpa only [s, lowerOrbitS, mul_zero, sub_zero, mul_assoc] using
        (tendsto_const_nhds (x := saddleS γ)).sub (hqv.const_mul (saddleU γ))
    · simpa only [U, lowerOrbitU, sub_zero, mul_one, Function.comp_def] using
        ((tendsto_const_nhds (x := (1 : ℝ))).sub hqinf).const_mul (saddleU γ)
  · subst U₀
    refine ⟨fun _ ↦ saddleS γ, fun _ ↦ saddleU γ, G.saddle.symm, rfl, ?_, ?_, ?_,
      tendsto_const_nhds, tendsto_const_nhds⟩
    · intro t _
      have hrel := saddleS_eq_one_add_mul_saddleU (ne_of_lt hγ₁)
      have hrel' : saddleS γ + 1 - saddleU γ = 0 := by
        dsimp [saddleS, saddleU]
        field_simp [(by linarith : 1 - γ ≠ 0)]
        ring
      have hsr : saddleS γ - 1 - γ * saddleU γ = 0 := by linarith
      simpa only [sRate, uRate, hsr, mul_zero, hrel'] using
        And.intro (hasDerivAt_const t (saddleS γ)) (hasDerivAt_const t (saddleU γ))
    · intro _ _
      exact ⟨G.saddle.symm, saddleS_pos hγ hγ₁, hB⟩
    · intro _ _
      exact ⟨fun h ↦ (lt_irrefl _ h).elim, fun h ↦ (lt_irrefl _ h).elim⟩
  · let v := G.upperLogisticSlope
    have hv (t : ℝ) : v t ∈ Ioo 0 γ ∧
        HasDerivAt v (logisticSlopeRate γ false (logisticParameter t) (v t)) t :=
      ⟨G.upperLogisticSlope_bounds hγ₁ t, G.upperLogisticSlope_hasDerivAt hγ₁ t⟩
    obtain ⟨L, hLip⟩ := logistic_slope_lipschitz_both hγ₁ false hv
    let a := upperGraphTime γ U₀
    obtain ⟨T, hT₀, hT, _, hinf⟩ := exists_upper_timechange hγ₁ (fun t ↦ (hv t).1) hLip a
    let s := fun t ↦ upperOrbitS γ v (T t)
    let U := fun t ↦ upperOrbitU γ (T t)
    have hEa : Real.exp (-a) = (U₀ - saddleU γ) / saddleU γ := by
      dsimp [a, upperGraphTime]
      rw [Real.exp_neg, Real.exp_log (div_pos hB (sub_pos.mpr hupp))]
      field_simp
    have hUzero : U 0 = U₀ := by
      dsimp [U, upperOrbitU]
      rw [hT₀, hEa]
      field_simp
      ring
    have hgraph (t : ℝ) : s t = G.σ (U t) := by
      have hh : (saddleS γ - G.σ (saddleU γ - saddleU γ / 2 * -(2 * Real.exp (-T t)))) /
        (saddleU γ / 2 * -(2 * Real.exp (-T t))) = v (T t) := rfl
      have hden : saddleU γ / 2 * -(2 * Real.exp (-T t)) = -(saddleU γ * Real.exp (-T t)) := by ring
      have harg : saddleU γ - -(saddleU γ * Real.exp (-T t)) = U t := by dsimp [U, upperOrbitU]; ring
      rw [hden, harg] at hh
      have hm := (div_eq_iff (neg_ne_zero.mpr (mul_pos hB (Real.exp_pos _)).ne')).mp hh
      change saddleS γ + saddleU γ * Real.exp (-T t) * v (T t) = G.σ (U t)
      linarith
    have hUp (t : ℝ) : 0 < U t := by dsimp [U, upperOrbitU]; positivity
    have hEinf : Tendsto (fun t ↦ Real.exp (-T t)) atTop (𝓝 0) :=
      Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp hinf)
    have hEv : Tendsto (fun t ↦ Real.exp (-T t) * v (T t)) atTop (𝓝 0) := by
      apply squeeze_zero_norm' (Eventually.of_forall (fun t ↦ ?_))
        (by simpa using hEinf.norm.const_mul γ)
      simp only [norm_mul, Real.norm_eq_abs, abs_of_pos (hv (T t)).1.1,
        abs_of_pos (Real.exp_pos _)]
      nlinarith [Real.exp_pos (-T t), (hv (T t)).1.2]
    refine ⟨s, U, by rw [hgraph, hUzero], hUzero,
      fun t ht ↦ upperOrbit_derivatives hγ₁ hv t (hT t ht),
      fun t _ ↦ ⟨hgraph t, ?_, hUp t⟩, ?_, ?_, ?_⟩
    · change 0 < saddleS γ + saddleU γ * Real.exp (-T t) * v (T t)
      exact add_pos (saddleS_pos hγ hγ₁) (mul_pos (mul_pos hB (Real.exp_pos _)) (hv (T t)).1.1)
    · intro t _
      refine ⟨fun h ↦ (not_lt_of_gt hupp h).elim, fun _ ↦ ?_⟩
      change saddleU γ < saddleU γ * (1 + Real.exp (-T t))
      nlinarith [mul_pos hB (Real.exp_pos (-T t))]
    · simpa only [s, upperOrbitS, mul_zero, add_zero, mul_assoc] using
        (tendsto_const_nhds (x := saddleS γ)).add (hEv.const_mul (saddleU γ))
    · simpa only [U, upperOrbitU, add_zero, mul_one, Function.comp_def] using
        ((tendsto_const_nhds (x := (1 : ℝ))).add hEinf).const_mul (saddleU γ)

/-- Global original-time convergence, after forgetting the branch bounds. -/
theorem exists_global_stable_orbit {γ U₀ : ℝ} (hγ : 0 < γ) (hγ₁ : γ < 1)
    (G : SubcriticalGraph γ) (hU₀ : 0 < U₀) :
    ∃ s U : ℝ → ℝ, s 0 = G.σ U₀ ∧ U 0 = U₀ ∧
      (∀ t ≥ 0, HasDerivAt s (sRate γ (s t) (U t)) t ∧
        HasDerivAt U (uRate (s t) (U t)) t) ∧
      (∀ t ≥ 0, s t = G.σ (U t) ∧ 0 < s t ∧ 0 < U t) ∧
      Tendsto s atTop (𝓝 (saddleS γ)) ∧ Tendsto U atTop (𝓝 (saddleU γ)) := by
  obtain ⟨s, U, hs₀, hUzero, hd, hp, _, hsinf, hUinf⟩ :=
    exists_global_stable_orbit_with_branch hγ hγ₁ G hU₀
  exact ⟨s, U, hs₀, hUzero, hd, hp, hsinf, hUinf⟩

/-- The article's two stable branches are actual original-time trajectories:
they remain in their stated regions, are strictly monotone in U, and tend
to the saddle. This includes every positive graph point. -/
theorem exists_global_stable_solution {γ U₀ : ℝ} (hγ : 0 < γ) (hγ₁ : γ < 1)
    (G : SubcriticalGraph γ) (hU₀ : 0 < U₀) :
    ∃ α : ℝ → ℝ × ℝ, α 0 = (G.σ U₀, U₀) ∧ IsSolutionOn γ α (Ici 0) ∧
      (∀ t ≥ 0, α t ∈ positiveQuadrant ∧ (α t).1 = G.σ ((α t).2)) ∧
      (∀ t ≥ 0, (U₀ < saddleU γ → α t ∈ lowerRegion γ) ∧
        (saddleU γ < U₀ → α t ∈ upperRegion γ)) ∧
      (U₀ < saddleU γ → StrictMonoOn (fun t ↦ (α t).2) (Ici 0)) ∧
      (saddleU γ < U₀ → StrictAntiOn (fun t ↦ (α t).2) (Ici 0)) ∧
      Tendsto α atTop (𝓝 (saddlePoint γ)) := by
  obtain ⟨s, U, hs₀, hUzero, hd, hp, hbranch, hsinf, hUinf⟩ :=
    exists_global_stable_orbit_with_branch hγ hγ₁ G hU₀
  let α := fun t ↦ (s t, U t)
  have hα (t : ℝ) (ht : 0 ≤ t) : HasDerivAt α (vectorField γ (α t)) t :=
    (hd t ht).1.prodMk (hd t ht).2
  have hreg (t : ℝ) (ht : 0 ≤ t) : (U₀ < saddleU γ → α t ∈ lowerRegion γ) ∧
      (saddleU γ < U₀ → α t ∈ upperRegion γ) := by
    constructor
    · intro hlo
      have hh := G.lower (U t) ⟨(hp t ht).2.2, (hbranch t ht).1 hlo⟩
      change 0 < s t ∧ s t < saddleS γ ∧ 0 < U t ∧ U t < s t + 1
      rw [(hp t ht).1]
      exact ⟨G.positive hγ hγ₁ (hp t ht).2.2, hh.2.1, (hp t ht).2.2, by linarith [hh.2.2]⟩
    · intro hhi
      have hh := G.upper (U t) ((hbranch t ht).2 hhi)
      change saddleS γ ≤ s t ∧ (s t - 1) / γ ≤ U t
      rw [(hp t ht).1]
      exact ⟨hh.1.le, (div_le_iff₀ hγ).mpr (by linarith [hh.2.1])⟩
  refine ⟨α, Prod.ext hs₀ hUzero, hα, fun t ht ↦ ⟨⟨(hp t ht).2.1, (hp t ht).2.2⟩,
    (hp t ht).1⟩, hreg, ?_, ?_, hsinf.prodMk_nhds hUinf⟩
  · intro hlo
    apply strictMonoOn_of_deriv_pos (convex_Ici 0)
      (fun t ht ↦ (hd t ht).2.continuousAt.continuousWithinAt)
    intro t ht
    rw [interior_Ici] at ht
    rw [(hd t ht.le).2.deriv]
    exact lowerRegion_uRate_pos ((hreg t ht.le).1 hlo)
  · intro hhi
    apply strictAntiOn_of_deriv_neg (convex_Ici 0)
      (fun t ht ↦ (hd t ht).2.continuousAt.continuousWithinAt)
    intro t ht
    rw [interior_Ici] at ht
    rw [(hd t ht.le).2.deriv]
    apply upperRegion_uRate_neg hγ hγ₁ ((hreg t ht.le).2 hhi)
    intro he
    have hh := congrArg Prod.snd he
    change U t = saddleU γ at hh
    exact (ne_of_gt ((hbranch t ht.le).2 hhi)) hh

end
end krylov.Strings.OptimizerQuadratures
