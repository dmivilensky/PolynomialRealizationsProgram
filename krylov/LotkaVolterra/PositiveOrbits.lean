import krylov.LotkaVolterra.LocalFlow
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
Article: `main_krylov`, `apC:prop:LV` and `apC:prop:g1`.

An actual integral curve with positive initial coordinates remains positive
throughout its whole open time interval of existence. The proof supplies the
two exact exponential integral formulas, using the existing fundamental
theorem of calculus and constancy theorem instead of a new comparison theory.

Source: the standard integrating-factor proof for scalar linear ODEs,
applied to each multiplicative coordinate equation of `(LV_γ)`.
-/
namespace krylov.LotkaVolterra
noncomputable section
open Set MeasureTheory

/-- Standard scalar integrating-factor identity on an open interval. The
coefficient only needs to be continuous on that interval. -/
theorem scalar_linear_exp_formula {a f : ℝ → ℝ} {l r t₀ : ℝ}
    (ht₀ : t₀ ∈ Ioo l r) (ha : ContinuousOn a (Ioo l r))
    (hf : ∀ t ∈ Ioo l r, HasDerivAt f (a t * f t) t) :
    ∀ t ∈ Ioo l r, f t = f t₀ * Real.exp (∫ u in t₀..t, a u) := by
  let A : ℝ → ℝ := fun t ↦ ∫ u in t₀..t, a u
  have hA (t : ℝ) (ht : t ∈ Ioo l r) : HasDerivAt A (a t) t := by
    have hsub : uIcc t₀ t ⊆ Ioo l r := ordConnected_Ioo.uIcc_subset ht₀ ht
    exact intervalIntegral.integral_hasDerivAt_right
      (ha.mono hsub).intervalIntegrable
      (ha.stronglyMeasurableAtFilter isOpen_Ioo t ht)
      (ha.continuousAt (isOpen_Ioo.mem_nhds ht))
  let H : ℝ → ℝ := fun t ↦ f t * Real.exp (-A t)
  have hH (t : ℝ) (ht : t ∈ Ioo l r) : HasDerivAt H 0 t := by
    convert (hf t ht).mul ((hA t ht).neg.exp) using 1
    dsimp [H]
    ring
  intro t ht
  have hconst : H t = H t₀ :=
    isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo
      (fun u hu ↦ (hH u hu).differentiableAt.differentiableWithinAt)
      (fun u hu ↦ (hH u hu).deriv) ht ht₀
  have hprod : f t * Real.exp (-A t) = f t₀ := by
    simpa [H, A] using hconst
  change f t = f t₀ * Real.exp (A t)
  calc
    f t = f t * (Real.exp (-A t) * Real.exp (A t)) := by
      rw [← Real.exp_add]
      simp
    _ = f t₀ * Real.exp (A t) := by rw [← mul_assoc, hprod]

/-- The control coordinate has the exact multiplicative representation
throughout every open interval on which the actual solution exists. -/
theorem s_coordinate_exp_formula {γ l r t₀ : ℝ} {α : ℝ → ℝ × ℝ}
    (hα : IsSolutionOn γ α (Ioo l r)) (ht₀ : t₀ ∈ Ioo l r) :
    ∀ t ∈ Ioo l r, (α t).1 = (α t₀).1 *
      Real.exp (∫ u in t₀..t, 2 * ((α u).1 - 1 - γ * (α u).2)) := by
  have hc : ContinuousOn α (Ioo l r) := HasDerivAt.continuousOn hα
  apply scalar_linear_exp_formula ht₀ (by fun_prop)
  intro t ht
  have h := (hasFDerivAt_fst (𝕜 := ℝ) (p := α t)).comp_hasDerivAt t (hα t ht)
  convert! h using 1
  dsimp [vectorField, sRate]
  ring

/-- The state coordinate has the corresponding exact exponential formula. -/
theorem u_coordinate_exp_formula {γ l r t₀ : ℝ} {α : ℝ → ℝ × ℝ}
    (hα : IsSolutionOn γ α (Ioo l r)) (ht₀ : t₀ ∈ Ioo l r) :
    ∀ t ∈ Ioo l r, (α t).2 = (α t₀).2 *
      Real.exp (∫ u in t₀..t, (α u).1 + 1 - (α u).2) := by
  have hc : ContinuousOn α (Ioo l r) := HasDerivAt.continuousOn hα
  apply scalar_linear_exp_formula ht₀ (by fun_prop)
  intro t ht
  have h := (hasFDerivAt_snd (𝕜 := ℝ) (p := α t)).comp_hasDerivAt t (hα t ht)
  convert! h using 1
  dsimp [vectorField, uRate]
  ring

/-- Positivity throughout an existing orbit, both forward and backward in
time. No a priori boundedness or smallness of the time interval is required. -/
theorem solution_positive_on_interval {γ l r t₀ : ℝ} {α : ℝ → ℝ × ℝ}
    (hα : IsSolutionOn γ α (Ioo l r)) (ht₀ : t₀ ∈ Ioo l r)
    (hpos : α t₀ ∈ positiveQuadrant) :
    ∀ t ∈ Ioo l r, α t ∈ positiveQuadrant := by
  intro t ht
  change 0 < (α t).1 ∧ 0 < (α t).2
  rw [s_coordinate_exp_formula hα ht₀ t ht, u_coordinate_exp_formula hα ht₀ t ht]
  exact ⟨mul_pos hpos.1 (Real.exp_pos _), mul_pos hpos.2 (Real.exp_pos _)⟩

/-- Axis initial data remain on that axis throughout an existing solution.
This supplies the invariant axes without presupposing a maximal flow. -/
theorem solution_axes_invariant {γ l r t₀ : ℝ} {α : ℝ → ℝ × ℝ}
    (hα : IsSolutionOn γ α (Ioo l r)) (ht₀ : t₀ ∈ Ioo l r) :
    ((α t₀).1 = 0 → ∀ t ∈ Ioo l r, (α t).1 = 0) ∧
    ((α t₀).2 = 0 → ∀ t ∈ Ioo l r, (α t).2 = 0) := by
  constructor
  · intro hs t ht
    rw [s_coordinate_exp_formula hα ht₀ t ht, hs, zero_mul]
  · intro hU t ht
    rw [u_coordinate_exp_formula hα ht₀ t ht, hU, zero_mul]

/-- Positive initial points admit a joint continuous local flow on an entire
neighborhood of positive initial data, with all of its actual solution
curves staying in the physical quadrant throughout the common time window. -/
theorem exists_continuous_local_positive_flow (γ t₀ : ℝ) {z₀ : ℝ × ℝ}
    (hz₀ : z₀ ∈ positiveQuadrant) :
    ∃ r > 0, ∃ ε > 0, ∃ Φ : (ℝ × ℝ) × ℝ → ℝ × ℝ,
      ContinuousOn Φ (Metric.closedBall z₀ r ×ˢ Icc (t₀ - ε) (t₀ + ε)) ∧
      ∀ z ∈ Metric.closedBall z₀ r, Φ (z, t₀) = z ∧
        IsSolutionOn γ (fun t ↦ Φ (z, t)) (Ioo (t₀ - ε) (t₀ + ε)) ∧
        ∀ t ∈ Ioo (t₀ - ε) (t₀ + ε), Φ (z, t) ∈ positiveQuadrant := by
  obtain ⟨r, hr, ε, hε, Φ, hc, hΦ⟩ := exists_continuous_local_flow γ t₀ z₀
  obtain ⟨δ, hδ, hδQ⟩ := Metric.mem_nhds_iff.mp
    (isOpen_positiveQuadrant.mem_nhds hz₀)
  let r' := min r (δ / 2)
  have hr' : 0 < r' := lt_min hr (by positivity)
  have hsub : Metric.closedBall z₀ r' ⊆ Metric.closedBall z₀ r :=
    Metric.closedBall_subset_closedBall (min_le_left _ _)
  have hQ : Metric.closedBall z₀ r' ⊆ positiveQuadrant := by
    apply Set.Subset.trans (Metric.closedBall_subset_ball ?_) hδQ
    dsimp [r']
    linarith [min_le_right r (δ / 2)]
  refine ⟨r', hr', ε, hε, Φ, hc.mono (Set.prod_mono hsub Subset.rfl), ?_⟩
  intro z hz
  obtain ⟨h₀, hsol⟩ := hΦ z (hsub hz)
  refine ⟨h₀, hsol, ?_⟩
  apply solution_positive_on_interval hsol
    (show t₀ ∈ Ioo (t₀ - ε) (t₀ + ε) by constructor <;> linarith)
  simpa only [h₀] using hQ hz

end
end krylov.LotkaVolterra
