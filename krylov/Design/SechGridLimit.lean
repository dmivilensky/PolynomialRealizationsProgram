import krylov.Design.SechExtremum
import Mathlib.Algebra.Order.Floor.Semiring

/-!
Article: main_krylov, the lower Chebyshev majorant and the concluding grid
limit in apC:sec:design.
Use: the actual maximum over all positive integer degrees is attained at one
of the two samples bracketing the constructed continuous optimizer. Its
scaled value converges to the genuine continuous maximum as spacing vanishes.
Source: the proved strict unimodality, floor inequalities, and continuity.
-/

namespace krylov.Design
noncomputable section
open Real Filter Set jacobi.Young
open scoped Topology

/-- The integer immediately below the continuous maximizer in units of the mesh.
Article: main_krylov, discretization of the lower Chebyshev majorant. -/
def sechGridIndex (θ : ℝ) : ℕ := ⌊sechOptimizer / θ⌋₊

/-- The larger of the two actual lattice values bracketing the continuous optimizer.
Article: main_krylov, the lower Chebyshev majorant. -/
def sechGridMaximum (θ : ℝ) : ℝ :=
  max (sechProfile ((sechGridIndex θ : ℝ) * θ))
    (sechProfile (((sechGridIndex θ : ℝ) + 1) * θ))

/-- The unscaled genuine supremum over all positive integer degrees.
Article: main_krylov, max_m m*sech(m*theta). -/
def discreteSechMaximum (θ : ℝ) : ℝ :=
  sSup (range (fun n : ℕ => ((n : ℝ) + 1) * sech (((n : ℝ) + 1) * θ)))

/-- The actual two lattice nodes straddle the continuous maximizer, within one mesh.
Article: main_krylov, the lower-majorant grid limit. -/
theorem sechGrid_bracket {θ : ℝ} (hθ : 0 < θ) :
    (sechGridIndex θ : ℝ) * θ ≤ sechOptimizer ∧
      sechOptimizer < ((sechGridIndex θ : ℝ) + 1) * θ := by
  have hr : 0 ≤ sechOptimizer := le_trans (by norm_num) sechOptimizer_spec.1.1.le
  exact ⟨(le_div_iff₀ hθ).mp (Nat.floor_le (div_nonneg hr hθ.le)),
    (div_lt_iff₀ hθ).mp (Nat.lt_floor_add_one (sechOptimizer / θ))⟩

/-- Every genuine lattice sample lies below the larger bracketing value.
Article: main_krylov, actual integer maximization in the lower majorant. -/
theorem sechProfile_grid_le {θ : ℝ} (hθ : 0 < θ) (m : ℕ) :
    sechProfile ((m : ℝ) * θ) ≤ sechGridMaximum θ := by
  have hb := sechGrid_bracket hθ
  unfold sechGridMaximum
  by_cases hm : m ≤ sechGridIndex θ
  · apply le_max_of_le_left
    have hmm : (m : ℝ) * θ ≤ (sechGridIndex θ : ℝ) * θ :=
      mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hm) hθ.le
    exact sechProfile_strictMonoOn.monotoneOn
      ⟨mul_nonneg (Nat.cast_nonneg _) hθ.le, hmm.trans hb.1⟩
      ⟨mul_nonneg (Nat.cast_nonneg _) hθ.le, hb.1⟩ hmm
  · apply le_max_of_le_right
    have hnm : sechGridIndex θ + 1 ≤ m := Nat.succ_le_iff.mpr (lt_of_not_ge hm)
    have hmm : ((sechGridIndex θ : ℝ) + 1) * θ ≤ (m : ℝ) * θ := by
      apply mul_le_mul_of_nonneg_right _ hθ.le
      exact_mod_cast hnm
    exact sechProfile_strictAntiOn.antitoneOn hb.2.le (hb.2.le.trans hmm) hmm

/-- The genuine lattice maximum is attained at a positive integer degree.
Article: main_krylov, max_m m*sech(m*theta), including its actual attainment. -/
theorem sechGridMaximum_attained {θ : ℝ} (hθ : 0 < θ) :
    ∃ m : ℕ, 0 < m ∧ sechGridMaximum θ = sechProfile ((m : ℝ) * θ) := by
  by_cases hc : sechProfile (((sechGridIndex θ : ℝ) + 1) * θ) ≤
      sechProfile ((sechGridIndex θ : ℝ) * θ)
  · refine ⟨sechGridIndex θ, ?_, max_eq_left hc⟩
    by_contra hn
    have hn0 : sechGridIndex θ = 0 := Nat.eq_zero_of_not_pos hn
    simp only [hn0, Nat.cast_zero, zero_mul, zero_add, one_mul, sechProfile] at hc
    have hp := mul_pos hθ (sech_pos θ)
    nlinarith
  · refine ⟨sechGridIndex θ + 1, Nat.succ_pos _, ?_⟩
    simpa only [sechGridMaximum, Nat.cast_add, Nat.cast_one] using max_eq_right (le_of_not_ge hc)

/-- The unscaled source supremum is an actual maximum, and scaling gives the bracketing formula.
Article: main_krylov, the precise meaning of the lower-majorant maximum. -/
theorem discreteSechMaximum_attained {θ : ℝ} (hθ : 0 < θ) :
    (∃ n : ℕ, discreteSechMaximum θ = ((n : ℝ) + 1) * sech (((n : ℝ) + 1) * θ)) ∧
      θ * discreteSechMaximum θ = sechGridMaximum θ := by
  obtain ⟨m, hm, he⟩ := sechGridMaximum_attained hθ
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm.ne'
  let v := ((n : ℝ) + 1) * sech (((n : ℝ) + 1) * θ)
  have he' : sechGridMaximum θ = θ * v := by
    rw [he]
    simp only [sechProfile, v, Nat.cast_succ]
    ring
  have hv : ∀ k : ℕ, ((k : ℝ) + 1) * sech (((k : ℝ) + 1) * θ) ≤ v := by
    intro k
    have h := sechProfile_grid_le hθ (k + 1)
    rw [he'] at h
    apply (mul_le_mul_iff_right₀ hθ).mp
    simpa only [sechProfile, Nat.cast_add, Nat.cast_one, mul_assoc, mul_comm θ,
      mul_left_comm θ] using h
  have hs : discreteSechMaximum θ = v := by
    apply le_antisymm
    · exact csSup_le (range_nonempty _) (by rintro _ ⟨k, rfl⟩; exact hv k)
    · exact le_csSup ⟨v, by rintro _ ⟨k, rfl⟩; exact hv k⟩ (mem_range_self n)
  exact ⟨⟨n, hs⟩, hs ▸ he'.symm⟩

/-- The actual lower lattice node converges to the constructed continuous optimizer.
Article: main_krylov, the lower-majorant grid limit. -/
theorem sechGrid_lower_tendsto :
    Tendsto (fun θ : ℝ => (sechGridIndex θ : ℝ) * θ) (𝓝[>] 0) (𝓝 sechOptimizer) := by
  have hl : Tendsto (fun θ : ℝ => sechOptimizer - θ) (𝓝[>] 0) (𝓝 sechOptimizer) := by
    have h := (tendsto_const_nhds (x := sechOptimizer)).sub (tendsto_id.mono_left nhdsWithin_le_nhds :
      Tendsto (fun θ : ℝ => θ) (𝓝[>] 0) (𝓝 0))
    simpa only [sub_zero, id_eq] using! h
  apply hl.squeeze' tendsto_const_nhds
  · filter_upwards [self_mem_nhdsWithin] with θ hθ
    have hb := (sechGrid_bracket hθ).2
    linarith
  · filter_upwards [self_mem_nhdsWithin] with θ hθ
    exact (sechGrid_bracket hθ).1

/-- The true lattice maximum converges to the continuous maximum as spacing vanishes.
Article: main_krylov, the concluding lower-majorant limit in apC:sec:design. -/
theorem sechGridMaximum_tendsto :
    Tendsto sechGridMaximum (𝓝[>] 0) (𝓝 (sechProfile sechOptimizer)) := by
  have hu : Tendsto (fun θ : ℝ => ((sechGridIndex θ : ℝ) + 1) * θ)
      (𝓝[>] 0) (𝓝 sechOptimizer) := by
    have h := sechGrid_lower_tendsto.add (tendsto_id.mono_left nhdsWithin_le_nhds :
      Tendsto (fun θ : ℝ => θ) (𝓝[>] 0) (𝓝 0))
    convert! h using 1
    · funext θ
      simp only [id_eq]
      ring
    · simp only [add_zero]
  have hl := sechProfile_continuous.continuousAt.tendsto.comp sechGrid_lower_tendsto
  have hh := sechProfile_continuous.continuousAt.tendsto.comp hu
  simpa only [sechGridMaximum, Function.comp_def, max_self] using! hl.max hh

/-- The full source expression theta*max_m m*sech(m*theta) tends to the genuine continuous maximum.
Article: main_krylov, the final assertion of the proof of the Chebyshev majorants. -/
theorem discreteSechMaximum_scaled_tendsto :
    Tendsto (fun θ : ℝ => θ * discreteSechMaximum θ) (𝓝[>] 0)
      (𝓝 (sechProfile sechOptimizer)) := by
  apply sechGridMaximum_tendsto.congr'
  filter_upwards [self_mem_nhdsWithin] with θ hθ
  exact (discreteSechMaximum_attained hθ).2.symm

end
end krylov.Design
