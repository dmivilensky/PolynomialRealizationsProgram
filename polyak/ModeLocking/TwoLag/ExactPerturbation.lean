import polyak.ModeLocking.TwoLag.ExactJets

/-! E1 and E2 suffice for the global six-lag perturbation. All bounds and
the positive perturbation size are derived by compactness. -/
noncomputable section
namespace polyak.ModeLocking.TwoLag.ExactData
open General Levels Set Filter
variable {q : Tuning} {s : ℝ} {K L : ℕ} (D : ExactData q s K L)

theorem lift_values_zero : ∀z∈D.zeros,lift q s K L z=0 := by
  intro z hz
  simp only [zeros, Finset.mem_insert, Finset.mem_singleton] at hz
  rcases hz with rfl|rfl|rfl
  · exact lift_zero_endpoint q s K L
  · exact lift_grid_zero D.K_ge D.L_ge q s (D.grid 0)
  · exact lift_grid_zero D.K_ge D.L_ge q s (D.grid 1)

theorem lift_slopes_zero : ∀z∈D.zeros,deriv (lift q s K L) z=0 := by
  intro z hz
  simp only [zeros, Finset.mem_insert, Finset.mem_singleton] at hz
  rcases hz with rfl|rfl|rfl
  · exact lift_slope_endpoint q s K L
  · exact lift_grid_slope D.K_ge D.L_ge q s (D.grid 0)
  · exact lift_grid_slope D.K_ge D.L_ge q s (D.grid 1)

/-- The global perturbation and its positive source weights are constructed,
not included in the hypotheses E1–E4. -/
theorem exists_positive_pinning : ∃ε : ℝ, 0<ε ∧ 2*ε<D.a ∧ 2*ε<D.b ∧
    Nonempty (Analysis.NegativeJetCover 0 Real.pi D.zeros
      (finiteSymbol q s (pinLags K L) (pinWeight K D.a D.b ε))) := by
  have hf : ∀x∈Icc 0 Real.pi,ContDiffAt ℝ 2 (extension q s K D.a D.b) x :=
    fun x hx=>(analyticAt_extension q s K D.a D.b hx).contDiffAt
  have hc2 : ContinuousOn (iteratedDeriv 2 (extension q s K D.a D.b)) (Icc 0 Real.pi) := by
    intro x hx
    rw [iteratedDeriv_eq_iterate]
    exact (analyticAt_extension q s K D.a D.b hx).deriv.deriv.continuousAt.continuousWithinAt
  have hE : ∀x∈Icc 0 Real.pi,ContDiffAt ℝ 2 (lift q s K L) x :=
    fun x hx=>(analyticAt_lift q s K L hx).contDiffAt
  have hE2 : ContinuousOn (iteratedDeriv 2 (lift q s K L)) (Icc 0 Real.pi) := by
    intro x hx
    rw [iteratedDeriv_eq_iterate]
    exact (analyticAt_lift q s K L hx).deriv.deriv.continuousAt.continuousWithinAt
  obtain ⟨r,hr,hpert⟩ := Analysis.finite_zero_perturbation D.zeros_nonempty D.zeros_subset hf hc2
    D.values_zero D.slopes_zero D.curvature_negative D.strict_off_zeros hE hE2
    D.lift_values_zero D.lift_slopes_zero
  let ε := min (r/2) (min (D.a/4) (D.b/4))
  have hε : 0<ε := lt_min (by positivity) (lt_min (by positivity [D.a_pos]) (by positivity [D.b_pos]))
  have hεr : |ε|<r := by
    rw [abs_of_pos hε]
    have h := min_le_left (r/2) (min (D.a/4) (D.b/4))
    change ε≤r/2 at h
    linarith
  have hεa : 2*ε<D.a := by
    have h := (min_le_right (r/2) (min (D.a/4) (D.b/4))).trans (min_le_left _ _)
    change ε≤D.a/4 at h
    linarith [D.a_pos]
  have hεb : 2*ε<D.b := by
    have h := (min_le_right (r/2) (min (D.a/4) (D.b/4))).trans (min_le_right _ _)
    change ε≤D.b/4 at h
    linarith [D.b_pos]
  refine ⟨ε,hε,hεa,hεb,?_⟩
  have h := hpert ε hεr
  have heq : finiteSymbol q s (pinLags K L) (pinWeight K D.a D.b ε)=
      fun x=>extension q s K D.a D.b x+ε*lift q s K L x :=
    funext (pin_extension_identity D.K_ge D.L_ge q s D.a D.b ε)
  rwa [←heq] at h

end polyak.ModeLocking.TwoLag.ExactData
