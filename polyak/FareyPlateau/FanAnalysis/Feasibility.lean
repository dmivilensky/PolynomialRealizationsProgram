import polyak.FareyPlateau.FanAnalysis.AllGrid
import polyak.FareyPlateau.FanAnalysis.Periodicity
import polyak.FareyPlateau.FanAnalysis.GridArithmetic

/-! The all-grid inequalities give actual two-Dirac solutions of FP for
both Farey fan families. The mass correction is the explicit optimal one. -/
noncomputable section
namespace polyak.FareyPlateau.FanAnalysis.Actual
open General Levels ModeLocking Set Filter MeasureTheory
open scoped Topology BigOperators
variable {q : Tuning} {j k : ℕ} (A : Edge.AdjacentData q j k)

theorem phase_constraints (P : Fan.Data) (hj : P.j = j) (hk : P.k = k)
    {e δ : ℝ} (hδ : P.delta = δ)
    (hgrid : ∀ θ ∈ Icc (-Real.pi) Real.pi,
      (∃ n : ℤ, θ = (n : ℝ) * k * δ) →
      (∃ n : ℤ, θ = 2 * Real.pi / k + ((A.lower : ℝ) + (n : ℝ) * k) * δ) →
      0 ≤ phi A e δ θ) (n : ℤ) :
    0 ≤ phi A e δ ((n : ℝ) * P.near) := by
  obtain ⟨θ, hθ, l, he⟩ := phase_representative ((n : ℝ) * P.near)
  have hlattices := P.grid_lattices A.inverse A.lower n l
    (by simpa only [hj, hk] using A.inverse_mod)
    (by rw [hk, A.lower_class, Int.emod_eq_of_lt A.inverse_pos.le A.inverse_lt])
  have hrepr : (n : ℝ) * P.near - (l : ℝ) * (2 * Real.pi) = θ := by linarith
  simp only [hk, Int.cast_natCast, hδ, hrepr] at hlattices
  have hpos := hgrid θ hθ hlattices.1 hlattices.2
  rw [he]
  change 0 ≤ constraint ((k : ℝ) - 1) (correction A) (nearAngle A e) (farAngle A e) δ (θ + l * (2 * Real.pi))
  rw [constraint_periodic]
  exact hpos

theorem eventually_mass_and_minimizer (e : ℝ) : ∀ᶠ δ in 𝓝 0,
    0 < (k : ℝ) - 1 + correction A * δ ∧
    0 < ((k : ℝ) - 1 + correction A * δ) * Real.cos (nearAngle A e δ) + Real.cos (farAngle A e δ) := by
  have hm : (0 : ℝ) < (k : ℝ) - 1 := by
    have hkR : (3 : ℝ) ≤ k := by exact_mod_cast A.period_ge
    linarith
  have hw : ContinuousAt (fun δ : ℝ => (k : ℝ) - 1 + correction A * δ) 0 := by fun_prop
  have hM : ContinuousAt (fun δ : ℝ => ((k : ℝ) - 1 + correction A * δ) *
      Real.cos (nearAngle A e δ) + Real.cos (farAngle A e δ)) 0 := by
    have ha := (near_analytic A e).continuousAt
    have hc := (far_analytic A e).continuousAt
    fun_prop
  have hMpos : 0 < ((k : ℝ) - 1 + correction A * 0) *
      Real.cos (nearAngle A e 0) + Real.cos (farAngle A e 0) := by
    rw [near_value A e, far_value A e]
    simp only [mul_zero, add_zero]
    have hh : ((k : ℝ) - 1) * Real.cos (Real.pi / k) + Real.cos (Real.pi / k) =
        (k : ℝ) * Real.cos (Real.pi / k) := by ring
    rw [hh]
    exact mul_pos (by have hkR : (3 : ℝ) ≤ k := by exact_mod_cast A.period_ge
                      linarith) (cos_positive A)
  exact (hw.eventually (eventually_gt_nhds (show 0 < (k : ℝ) - 1 + correction A * 0 by simpa only [mul_zero, add_zero] using hm))).and
    (hM.eventually (eventually_gt_nhds hMpos))

theorem eventually_frequencies (B : ℝ) : ∀ᶠ δ : ℝ in 𝓝 0,
    (A.frequency : ℝ) + B * δ ∈ Ioo 0 Real.pi := by
  have hc : ContinuousAt (fun δ : ℝ => (A.frequency : ℝ) + B * δ) 0 := by fun_prop
  have hn : Ioo (0 : ℝ) Real.pi ∈ 𝓝 ((A.frequency : ℝ) + B * 0) := by
    simpa only [mul_zero, add_zero] using isOpen_Ioo.mem_nhds (frequency_interior A)
  exact hc.eventually hn

theorem fan_feasible_small {e : ℝ} (he : e < critical A) :
    ∀ᶠ δ in 𝓝[≠] 0, ∀ P : Fan.Data, P.j = j → P.k = k → P.delta = δ →
      ∃ a c : Frequency, (a : ℝ) = P.near ∧ (c : ℝ) = P.far ∧
        ProgramSolution (Geometry.shiftedCurve q (A.edgeShift - e * δ^2)) nonzeroLags
          (atomicMeasure ![Real.toNNReal ((k : ℝ) - 1 + correction A * δ), 1] ![a, c]) := by
  have ha := anglePath_actual q A.edgeShift A.frequency 1 e (frequency_interior A)
  have hc := anglePath_actual q A.edgeShift A.frequency (-((k : ℝ) - 1)) e (frequency_interior A)
  filter_upwards [all_grid_nonnegative A he,
    (eventually_mass_and_minimizer A e).filter_mono nhdsWithin_le_nhds,
    (eventually_frequencies A 1).filter_mono nhdsWithin_le_nhds,
    (eventually_frequencies A (-((k : ℝ) - 1))).filter_mono nhdsWithin_le_nhds,
    ha.filter_mono nhdsWithin_le_nhds, hc.filter_mono nhdsWithin_le_nhds]
    with δ hgrid hmass hnear hfar hanglea hanglec P hj hk hδ
  have hcenter : P.center = (A.frequency : ℝ) := by
    change 2 * Real.pi * P.j / P.k = 2 * Real.pi * j / k
    rw [hj, hk]
    push_cast
    rfl
  have hne : P.near = (A.frequency : ℝ) + δ := by
    have hh := P.near_displacement
    rw [hcenter, hδ] at hh
    linarith
  have hfa : P.far = (A.frequency : ℝ) + (-((k : ℝ) - 1)) * δ := by
    have hh := P.far_displacement
    rw [hcenter, hk, hδ] at hh
    push_cast at hh
    linarith
  simp only [one_mul] at hnear hanglea
  let a : Frequency := ⟨P.near, by rw [hne]; exact ⟨hnear.1.le, hnear.2.le⟩⟩
  let c : Frequency := ⟨P.far, by rw [hfa]; exact ⟨hfar.1.le, hfar.2.le⟩⟩
  let w : Fin 2 → NNReal := ![Real.toNNReal ((k : ℝ) - 1 + correction A * δ), 1]
  let ω : Fin 2 → Frequency := ![a, c]
  have hwa : (Real.toNNReal ((k : ℝ) - 1 + correction A * δ) : ℝ) = (k : ℝ) - 1 + correction A * δ := by
    exact Real.coe_toNNReal _ hmass.1.le
  have hca : Geometry.shiftedCurve q (A.edgeShift - e * δ^2) a = nearAngle A e δ := by
    change Geometry.shiftedAngle q _ P.near = _
    rw [hne]
    exact hanglea.symm
  have hcc : Geometry.shiftedCurve q (A.edgeShift - e * δ^2) c = farAngle A e δ := by
    change Geometry.shiftedAngle q _ P.far = _
    rw [hfa]
    exact hanglec.symm
  refine ⟨a, c, rfl, rfl, inferInstance, atomicMeasure_ne_zero w ω ?_, ?_, ?_⟩
  · simp only [w, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    positivity
  · rw [atomicMeasure_integral]
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, hwa,
      NNReal.coe_one, one_mul, Curve.minimizer, hca, hcc]
    exact hmass.2.le
  · intro n _
    rw [atomicMeasure_integral]
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, hwa,
      NNReal.coe_one, one_mul, Curve.lag, hca, hcc]
    change 0 ≤ ((k : ℝ) - 1 + correction A * δ) *
      (Real.cos (nearAngle A e δ) - Real.cos ((n : ℝ) * P.near - nearAngle A e δ)) +
      (Real.cos (farAngle A e δ) - Real.cos ((n : ℝ) * P.far - farAngle A e δ))
    rw [companion_cosine P n (farAngle A e δ), hk]
    push_cast
    have hh := phase_constraints A P hj hk hδ hgrid n
    simpa only [phi, constraint, add_sub_assoc] using hh

end polyak.FareyPlateau.FanAnalysis.Actual
