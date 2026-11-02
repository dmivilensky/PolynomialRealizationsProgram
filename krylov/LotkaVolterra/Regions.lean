import krylov.LotkaVolterra.Basic

/-!
Article: `main_krylov`, `apC:prop:LV` and `apC:prop:g1`.

Exact nullcline and boundary calculations for the planar regions used in the
separatrix argument. All signs are proved from the defining inequalities.
These are the boundary inputs for an invariance/exit theorem; the assertions
below do not replace such a theorem by an assumed flow.

Source: the polynomial identities in the article's planar phase portrait.
-/
namespace krylov.LotkaVolterra
noncomputable section

/-- Bounded region below the state nullcline, for `0 < γ < 1`. -/
def lowerRegion (γ : ℝ) : Set (ℝ × ℝ) :=
  {z | 0 < z.1 ∧ z.1 < saddleS γ ∧ 0 < z.2 ∧ z.2 < z.1 + 1}

/-- Unbounded region above the control nullcline. The positive-quadrant
restriction follows from these inequalities for the physical parameters. -/
def upperRegion (γ : ℝ) : Set (ℝ × ℝ) :=
  {z | saddleS γ ≤ z.1 ∧ (z.1 - 1) / γ ≤ z.2}

/-- The endpoint region in which both coordinates increase. -/
def endpointRegion : Set (ℝ × ℝ) := {z | 0 < z.2 ∧ z.2 < z.1 - 1}

/-- The positive-quadrant part of the forward escape region at `γ = 1`. -/
def endpointEscapeRegion : Set (ℝ × ℝ) :=
  {z | 4 < z.1 ∧ 0 < z.2 ∧ z.2 < z.1 / 4}

theorem s_axis_invariant_field (γ U : ℝ) : sRate γ 0 U = 0 := by
  simp [sRate]

theorem u_axis_invariant_field (s : ℝ) : uRate s 0 = 0 := by
  simp [uRate]

theorem s_nullcline (γ s : ℝ) :
    sRate γ s (s + 1) = -2 * s * ((1 + γ) - (1 - γ) * s) := by
  unfold sRate
  ring

theorem u_nullcline (s : ℝ) : uRate s (s + 1) = 0 := by
  simp [uRate]

theorem lowerRegion_uRate_pos {γ : ℝ} {z : ℝ × ℝ}
    (hz : z ∈ lowerRegion γ) : 0 < uRate z.1 z.2 := by
  exact mul_pos hz.2.2.1 (sub_pos.mpr hz.2.2.2)

theorem lowerRegion_subset_positiveQuadrant (γ : ℝ) :
    lowerRegion γ ⊆ positiveQuadrant := fun _ hz ↦ ⟨hz.1, hz.2.2.1⟩

/-- On `U = s + 1`, the outward difference derivative is strictly positive
below the saddle. -/
theorem lower_diagonal_outward {γ s : ℝ} (hγ₁ : γ < 1)
    (hs : 0 < s) (hsF : s < saddleS γ) :
    0 < uRate s (s + 1) - sRate γ s (s + 1) := by
  have h : (1 - γ) * s < 1 + γ := by
    have := (lt_div_iff₀ (show 0 < 1 - γ by linarith)).mp hsF
    nlinarith only [this]
  rw [u_nullcline, s_nullcline]
  nlinarith [mul_pos hs (by linarith : 0 < (1 + γ) - (1 - γ) * s)]

/-- On the vertical boundary `s = sF`, the field points to larger `s`
as long as `U < UF`. -/
theorem lower_vertical_outward {γ U : ℝ} (hγ : 0 < γ) (hγ₁ : γ < 1)
    (hU : U < saddleU γ) : 0 < sRate γ (saddleS γ) U := by
  have hs := saddleS_pos hγ hγ₁
  have he := saddleS_eq_one_add_mul_saddleU (ne_of_lt hγ₁)
  unfold sRate
  have hf : 0 < saddleS γ - 1 - γ * U := by
    nlinarith [mul_pos hγ (sub_pos.mpr hU)]
  positivity

/-- Exact vertical-edge formula quoted in the article. -/
theorem saddle_vertical_rate {γ U : ℝ} (hγ : γ ≠ 1) :
    sRate γ (saddleS γ) U = 2 * γ * saddleS γ * (saddleU γ - U) := by
  have he := saddleS_eq_one_add_mul_saddleU hγ
  unfold sRate
  nlinarith [congrArg (fun x : ℝ ↦ 2 * saddleS γ * x) he]

/-- The upper wedge lies above the `U` nullcline. -/
theorem upperRegion_above_u_nullcline {γ : ℝ} (hγ : 0 < γ) (hγ₁ : γ < 1)
    {z : ℝ × ℝ} (hz : z ∈ upperRegion γ) : z.1 + 1 ≤ z.2 := by
  have hs : 1 + γ ≤ (1 - γ) * z.1 := by
    have := (div_le_iff₀ (show 0 < 1 - γ by linarith)).mp hz.1
    nlinarith only [this]
  have hU := (div_le_iff₀ hγ).mp hz.2
  nlinarith

theorem upperRegion_subset_positiveQuadrant {γ : ℝ} (hγ : 0 < γ)
    (hγ₁ : γ < 1) : upperRegion γ ⊆ positiveQuadrant := by
  intro z hz
  have hs : 0 < z.1 := lt_of_lt_of_le (saddleS_pos hγ hγ₁) hz.1
  exact ⟨hs, by linarith [upperRegion_above_u_nullcline hγ hγ₁ hz]⟩

theorem upperRegion_rates_nonpos {γ : ℝ} (hγ : 0 < γ) (hγ₁ : γ < 1)
    {z : ℝ × ℝ} (hz : z ∈ upperRegion γ) :
    sRate γ z.1 z.2 ≤ 0 ∧ uRate z.1 z.2 ≤ 0 := by
  have hp := upperRegion_subset_positiveQuadrant hγ hγ₁ hz
  have hU := (div_le_iff₀ hγ).mp hz.2
  have hn := upperRegion_above_u_nullcline hγ hγ₁ hz
  have hs := hp.1
  constructor
  · exact mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)
  · exact mul_nonpos_of_nonneg_of_nonpos hp.2.le (by linarith)

/-- The `U` component vanishes in the upper wedge only at its saddle vertex. -/
theorem upperRegion_uRate_zero_iff {γ : ℝ} (hγ : 0 < γ) (hγ₁ : γ < 1)
    {z : ℝ × ℝ} (hz : z ∈ upperRegion γ) :
    uRate z.1 z.2 = 0 ↔ z = saddlePoint γ := by
  constructor
  · intro h
    have hp := upperRegion_subset_positiveQuadrant hγ hγ₁ hz
    have hn := (mul_eq_zero.mp h).resolve_left (ne_of_gt hp.2)
    have hU := (div_le_iff₀ hγ).mp hz.2
    have hs : z.1 ≤ saddleS γ := by
      apply (le_div_iff₀ (show 0 < 1 - γ by linarith)).mpr
      nlinarith
    have heq : z.1 = saddleS γ := le_antisymm hs hz.1
    apply Prod.ext heq
    change z.2 = saddleU γ
    rw [saddleU_eq_saddleS_add_one (ne_of_lt hγ₁)]
    linarith
  · rintro rfl
    change uRate (saddleS γ) (saddleU γ) = 0
    rw [saddleU_eq_saddleS_add_one (ne_of_lt hγ₁), u_nullcline]

/-- Proposition `apC:prop:LV`: strict monotonicity of the state component
throughout the upper wedge except at the equilibrium. -/
theorem upperRegion_uRate_neg {γ : ℝ} (hγ : 0 < γ) (hγ₁ : γ < 1)
    {z : ℝ × ℝ} (hz : z ∈ upperRegion γ) (hne : z ≠ saddlePoint γ) :
    uRate z.1 z.2 < 0 :=
  lt_of_le_of_ne (upperRegion_rates_nonpos hγ hγ₁ hz).2
    (mt ((upperRegion_uRate_zero_iff hγ hγ₁ hz).mp) hne)

theorem endpointRegion_rates_pos {z : ℝ × ℝ} (hz : z ∈ endpointRegion) :
    0 < sRate 1 z.1 z.2 ∧ 0 < uRate z.1 z.2 := by
  have hs : 0 < z.1 := by linarith [hz.1, hz.2]
  have he : 0 < z.1 - 1 - z.2 := by linarith [hz.2]
  have hU : 0 < z.1 + 1 - z.2 := by linarith [hz.2]
  simp only [sRate, uRate, one_mul]
  constructor
  · positivity
  · exact mul_pos hz.1 hU

theorem endpointEscapeRegion_subset : endpointEscapeRegion ⊆ endpointRegion := by
  intro z hz
  exact ⟨hz.2.1, by linarith [hz.1, hz.2.2]⟩

/-- Strict exit through the lower boundary of the endpoint wedge. -/
theorem endpoint_exit_identity (s : ℝ) :
    uRate s (s - 1) - sRate 1 s (s - 1) = 2 * (s - 1) := by
  unfold sRate uRate
  ring

theorem endpoint_exit_outward {s : ℝ} (hs : 1 < s) :
    0 < uRate s (s - 1) - sRate 1 s (s - 1) := by
  rw [endpoint_exit_identity]
  linarith

/-- Exact sloping-boundary calculation for the forward escape region. -/
theorem endpoint_escape_edge_identity (s : ℝ) :
    uRate s (s / 4) - sRate 1 s (s / 4) / 4 =
      (3 * s / 4) * (1 - s / 4) := by
  unfold sRate uRate
  ring

theorem endpoint_escape_edge_inward {s : ℝ} (hs : 4 < s) :
    uRate s (s / 4) - sRate 1 s (s / 4) / 4 < 0 := by
  rw [endpoint_escape_edge_identity]
  exact mul_neg_of_pos_of_neg (by linarith) (by linarith)

theorem endpoint_escape_vertical_inward {U : ℝ} (hU : U ≤ 1) :
    0 < sRate 1 4 U := by
  unfold sRate
  nlinarith

/-- The endpoint gap variable `e = s - U` obeys the scalar identity used
later in the optimizer's large-`U` estimates. -/
theorem endpoint_gap_rate (s U : ℝ) :
    sRate 1 s U - uRate s U = U * ((s - U) - 3) +
      2 * (s - U) * ((s - U) - 1) := by
  unfold sRate uRate
  ring

theorem endpoint_state_rate_gap (s U : ℝ) : uRate s U = U * ((s - U) + 1) := by
  unfold uRate
  ring

end
end krylov.LotkaVolterra
