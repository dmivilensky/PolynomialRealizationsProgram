import krylov.LotkaVolterra.GlobalEndpointUniqueness
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
Article: `main_krylov`, `apC:prop:g1`, global orbit time parameterization.

The compact shooting graph is an actual endpoint Lotka--Volterra orbit.
The logarithmic state coordinate solves `q' = e(exp(max 0 q)) + 1`, whose
speed lies between two and four. Bounded continuation therefore gives an
orbit for all positive time, with `U ≥ exp(2t)`.

Source: bounded Picard continuation and the time change `U = exp q`.
-/

namespace krylov.LotkaVolterra
noncomputable section
open Set Filter
open scoped NNReal Topology

private def logField (e : ℝ → ℝ) (q : ℝ) : ℝ := e (Real.exp (max 0 q)) + 1

private theorem exists_log_orbit {e : ℝ → ℝ}
    (he : ∀ U ≥ 1, e U ∈ Icc (1 : ℝ) 3 ∧
      HasDerivAt e (endpointGraphRate U (e U)) U) :
    ∃ q : ℝ → ℝ, q 0 = 0 ∧ ∀ t, HasDerivAt q (logField e (q t)) t := by
  have heLip : LipschitzOnWith 6 e (Ici 1) := by
    apply (convex_Ici 1).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
      (fun U hU ↦ (he U hU).2.hasDerivWithinAt)
    intro U hU
    exact_mod_cast endpointGraphRate_norm_le hU (he U hU).1
  have hExp (q : ℝ) : 1 ≤ Real.exp (max 0 q) := by
    rw [Real.one_le_exp_iff]
    exact le_max_left 0 q
  have hball (a : ℝ≥0) : ∃ K : ℝ≥0, ∀ t : ℝ,
      LipschitzOnWith K (logField e) (Metric.closedBall (0 : ℝ) a) := by
    let K : ℝ≥0 := 6 * Real.toNNReal (Real.exp a)
    refine ⟨K, fun _ ↦ ?_⟩
    have hElip : LipschitzOnWith (Real.toNNReal (Real.exp a)) Real.exp (Icc (0 : ℝ) a) := by
      apply (convex_Icc 0 (a : ℝ)).lipschitzOnWith_of_nnnorm_deriv_le
        (fun q _ ↦ Real.differentiableAt_exp)
      intro q hq
      change |deriv Real.exp q| ≤ (Real.toNNReal (Real.exp a) : ℝ)
      rw [Real.deriv_exp, abs_of_pos (Real.exp_pos _),
        Real.coe_toNNReal _ (Real.exp_pos _).le]
      exact Real.exp_le_exp.mpr hq.2
    apply LipschitzOnWith.of_dist_le_mul
    intro q hq r hr
    have hq' : max 0 q ∈ Icc (0 : ℝ) a := by
      refine ⟨le_max_left _ _, max_le a.coe_nonneg ?_⟩
      exact (le_abs_self q).trans (by simpa [Real.dist_eq] using hq)
    have hr' : max 0 r ∈ Icc (0 : ℝ) a := by
      refine ⟨le_max_left _ _, max_le a.coe_nonneg ?_⟩
      exact (le_abs_self r).trans (by simpa [Real.dist_eq] using hr)
    calc
      dist (logField e q) (logField e r) =
          dist (e (Real.exp (max 0 q))) (e (Real.exp (max 0 r))) := by
        simp [logField]
      _ ≤ 6 * dist (Real.exp (max 0 q)) (Real.exp (max 0 r)) :=
        heLip.dist_le_mul _ (hExp q) _ (hExp r)
      _ ≤ 6 * ((Real.toNNReal (Real.exp a) : ℝ) * dist (max 0 q) (max 0 r)) :=
        mul_le_mul_of_nonneg_left (hElip.dist_le_mul _ hq' _ hr') (by norm_num)
      _ ≤ 6 * ((Real.toNNReal (Real.exp a) : ℝ) * dist q r) := by
        gcongr
        simpa using (LipschitzWith.id.const_max (0 : ℝ)).dist_le_mul q r
      _ = (K : ℝ) * dist q r := by simp [K, mul_assoc]
  exact exists_global_solution_of_bounded_lipschitz_on_balls (L := 4) (0 : ℝ)
    hball (fun _ ↦ continuous_const) (fun _ q ↦ by
      have h := (he _ (hExp q)).1
      change |e (Real.exp (max 0 q)) + 1| ≤ (4 : ℝ)
      rw [abs_le]
      constructor <;> linarith [h.1, h.2])

/-- Existence of a genuine separating endpoint orbit, defined for all
nonnegative orbit times and with explicit divergence of the state coordinate.
The graph and orbit are both constructed from the ODE. -/
theorem exists_global_endpoint_orbit_with_graph :
    ∃ e : ℝ → ℝ,
      (∀ U ≥ 1, e U ∈ Icc (1 : ℝ) 3 ∧
        HasDerivAt e (endpointGraphRate U (e U)) U) ∧
      ∃ α : ℝ → ℝ × ℝ, (α 0).2 = 1 ∧
        ∀ t ≥ 0, HasDerivAt α (vectorField 1 (α t)) t ∧
          (α t).2 + 1 < (α t).1 ∧ (α t).1 < (α t).2 + 3 ∧
          (α t).1 ≤ 4 * (α t).2 ∧ Real.exp (2 * t) ≤ (α t).2 ∧
          (α t).1 = (α t).2 + e ((α t).2) := by
  obtain ⟨e, he⟩ := exists_global_endpoint_graph_gap
  obtain ⟨q, hq₀, hq⟩ := exists_log_orbit he
  have heArg (t : ℝ) : 1 ≤ Real.exp (max 0 (q t)) := by
    rw [Real.one_le_exp_iff]
    exact le_max_left 0 (q t)
  have hqgrow (t : ℝ) (ht : 0 ≤ t) : 2 * t ≤ q t := by
    have hd := mul_sub_le_image_sub_of_le_deriv
      (fun t ↦ (hq t).differentiableAt)
      (C := (2 : ℝ)) (fun t ↦ by
        rw [(hq t).deriv]
        have h := (he _ (heArg t)).1.1
        dsimp [logField]
        linarith) ht
    simpa [hq₀] using hd
  let U : ℝ → ℝ := fun t ↦ Real.exp (q t)
  let α : ℝ → ℝ × ℝ := fun t ↦ (U t + e (U t), U t)
  refine ⟨e, he, α, by simp [α, U, hq₀], fun t ht ↦ ?_⟩
  have hqt : 0 ≤ q t := by linarith [hqgrow t ht]
  have hUt : 1 ≤ U t := by dsimp [U]; simpa using Real.exp_le_exp.mpr hqt
  have hgap := endpoint_graph_gap_strict he hUt
  have hUder : HasDerivAt U (U t * (e (U t) + 1)) t := by
    simpa [U, logField, max_eq_right hqt] using (hq t).exp
  have heder := (he (U t) hUt).2.comp t hUder
  have hSder : HasDerivAt (fun t ↦ U t + e (U t))
      (2 * (U t + e (U t)) * (e (U t) - 1)) t := by
    convert hUder.add heder using 1
    · rfl
    · rw [endpointGraphRate_eq (ne_of_gt (lt_of_lt_of_le (by norm_num) hUt))
        (by linarith [hgap.1])]
      rw [div_mul_cancel₀ _ (mul_ne_zero (show U t ≠ 0 by linarith)
        (show e (U t) + 1 ≠ 0 by linarith [hgap.1]))]
      ring
  refine ⟨?_, by dsimp [α]; linarith [hgap.1], by dsimp [α]; linarith [hgap.2],
    by dsimp [α]; linarith [hgap.2], Real.exp_le_exp.mpr (hqgrow t ht), rfl⟩
  have hv : (2 * (U t + e (U t)) * (e (U t) - 1), U t * (e (U t) + 1)) =
      vectorField 1 (α t) := by
    apply Prod.ext <;> dsimp [α, vectorField, sRate, uRate] <;> ring
  rw [← hv]
  exact hSder.prodMk hUder

/-- Endpoint orbit existence after forgetting its explicit graph witness. -/
theorem exists_global_endpoint_orbit :
    ∃ α : ℝ → ℝ × ℝ, (α 0).2 = 1 ∧
      ∀ t ≥ 0, HasDerivAt α (vectorField 1 (α t)) t ∧
        (α t).2 + 1 < (α t).1 ∧ (α t).1 < (α t).2 + 3 ∧
        (α t).1 ≤ 4 * (α t).2 ∧ Real.exp (2 * t) ≤ (α t).2 := by
  obtain ⟨_, _, α, hα₀, hα⟩ := exists_global_endpoint_orbit_with_graph
  refine ⟨α, hα₀, fun t ht ↦ ?_⟩
  exact ⟨(hα t ht).1, (hα t ht).2.1, (hα t ht).2.2.1,
    (hα t ht).2.2.2.1, (hα t ht).2.2.2.2.1⟩

/-- Qualitative form of the constructed endpoint orbit, in the article's
phase-plane regions. In particular the separating initial point lies
strictly between two and four, and its orbit never enters the escape wedge. -/
theorem exists_endpoint_separating_orbit :
    ∃ s₀ ∈ Ioo (2 : ℝ) 4, ∃ α : ℝ → ℝ × ℝ,
      α 0 = (s₀, 1) ∧ IsSolutionOn 1 α (Ici 0) ∧
      (∀ t ≥ 0, α t ∈ endpointRegion \ endpointEscapeRegion) ∧
      Tendsto (fun t ↦ (α t).2) atTop atTop := by
  obtain ⟨α, hα₀, hα⟩ := exists_global_endpoint_orbit
  have h₀ := hα 0 le_rfl
  refine ⟨(α 0).1, ?_, α, Prod.ext rfl hα₀, fun t ht ↦ (hα t ht).1, ?_, ?_⟩
  · rw [hα₀] at h₀
    constructor <;> linarith [h₀.2.1, h₀.2.2.1]
  · intro t ht
    have hh := hα t ht
    have hp : 0 < (α t).2 := (Real.exp_pos _).trans_le hh.2.2.2.2
    refine ⟨⟨hp, by linarith [hh.2.1]⟩, ?_⟩
    intro he
    change 4 < (α t).1 ∧ 0 < (α t).2 ∧ (α t).2 < (α t).1 / 4 at he
    linarith [hh.2.2.2.1, he.2.2]
  · apply tendsto_atTop_mono' atTop
      ((eventually_ge_atTop (0 : ℝ)).mono fun t ht ↦ (hα t ht).2.2.2.2)
    exact Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 2))

end
end krylov.LotkaVolterra
