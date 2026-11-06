import nesterov.Quadratic.Rate

/-!
Article: Theorem price of extrapolation and its proof in Appendix A.
Use: the sharp bound is on the actual root maximum, with the complete equality case.
-/

noncomputable section
set_option maxHeartbeats 800000
namespace nesterov.Quadratic

def effectiveCondition (μ L τ : ℝ) : ℝ := (1 + 2 * τ) * (L / μ) - 2 * τ

def priceFactor (μ L τ : ℝ) : ℝ :=
  (Real.sqrt (effectiveCondition μ L τ) - 1) / (Real.sqrt (effectiveCondition μ L τ) + 1)

theorem effectiveCondition_gt_one {μ L τ : ℝ} (hμ : 0 < μ) (hL : μ < L)
    (hτ : 0 ≤ τ) : 1 < effectiveCondition μ L τ := by
  have hκ : 1 < L / μ := (one_lt_div hμ).mpr hL
  dsimp [effectiveCondition]
  nlinarith

theorem endpoint_rate_bounds {μ L β τ h : ℝ} (hμL : μ ≤ L)
    (hstable : Stable μ L β τ h) :
    (1 - quadraticRate μ L β τ h) ^ 2 ≤ h * μ ∧
    (1 - quadraticRate μ L β τ h) ^ 2 ≤ 2 * (1 + β) - h * L * (1 + 2 * τ) ∧
    β - h * μ * τ ≤ quadraticRate μ L β τ h ^ 2 := by
  let ρ := quadraticRate μ L β τ h
  have hρ := quadraticRate_nonneg hμL hstable
  have hρ1 := quadraticRate_lt_one hμL hstable
  have hroot (lam : ℝ) (hlam : lam ∈ Set.Icc μ L) :
      ∀ z : ℂ, z ^ 2 - (S β τ h lam : ℂ) * z + (Q β τ h lam : ℂ) = 0 → ‖z‖ ≤ ρ := by
    intro z hz
    apply root_norm_le_rate hμL hstable hlam
    rwa [characteristic_eq]
  obtain ⟨hm, _, hq⟩ := endpoint_bounds hρ hρ1 (hroot μ ⟨le_rfl, hμL⟩)
  obtain ⟨_, hlast, _⟩ := endpoint_bounds hρ hρ1 (hroot L ⟨hμL, le_rfl⟩)
  dsimp [S, Q] at hm hlast hq
  refine ⟨?_, ?_, hq⟩ <;> nlinarith

theorem price_squared {μ L β τ h : ℝ} (hμ : 0 < μ) (hL : μ < L)
    (hτ : 0 ≤ τ) (hstable : Stable μ L β τ h) :
    effectiveCondition μ L τ * (1 - quadraticRate μ L β τ h) ^ 2 ≤
      (1 + quadraticRate μ L β τ h) ^ 2 := by
  let ρ := quadraticRate μ L β τ h
  obtain ⟨hm, hlast, hq⟩ := endpoint_rate_bounds hL.le hstable
  have hid : h * μ * effectiveCondition μ L τ =
      h * L * (1 + 2 * τ) - 2 * h * μ * τ := by
    dsimp [effectiveCondition]
    field_simp
  have hbound : h * μ * effectiveCondition μ L τ ≤ (1 + ρ) ^ 2 := by
    rw [hid]
    dsimp [ρ]
    nlinarith
  have hK := effectiveCondition_gt_one hμ hL hτ
  have hmul := mul_le_mul_of_nonneg_right hm (show 0 ≤ effectiveCondition μ L τ by linarith)
  nlinarith

theorem price_of_extrapolation {μ L β τ h : ℝ} (hμ : 0 < μ) (hL : μ < L)
    (hτ : 0 ≤ τ) (hstable : Stable μ L β τ h) :
    priceFactor μ L τ ≤ quadraticRate μ L β τ h := by
  let ρ := quadraticRate μ L β τ h
  have hρ := quadraticRate_nonneg hL.le hstable
  have hρ1 := quadraticRate_lt_one hL.le hstable
  have hK := effectiveCondition_gt_one hμ hL hτ
  have hs := Real.sq_sqrt (show 0 ≤ effectiveCondition μ L τ by linarith)
  have hs0 := Real.sqrt_nonneg (effectiveCondition μ L τ)
  have hp := price_squared hμ hL hτ hstable
  have hproduct : Real.sqrt (effectiveCondition μ L τ) * (1 - ρ) ≤ 1 + ρ := by
    nlinarith [mul_nonneg hs0 (show 0 ≤ 1 - ρ by linarith)]
  dsimp [priceFactor]
  apply (div_le_iff₀ (show 0 < Real.sqrt (effectiveCondition μ L τ) + 1 by positivity)).mpr
  dsimp [ρ] at hproduct
  nlinarith

/-- Equality in the price bound determines all three physical tuning parameters. -/
theorem price_equality_only_polyak {μ L β τ h : ℝ} (hμ : 0 < μ) (hL : μ < L)
    (hh : 0 < h) (hτ : 0 ≤ τ) (hstable : Stable μ L β τ h)
    (heq : quadraticRate μ L β τ h = priceFactor μ L τ) :
    τ = 0 ∧ β = polyak.Dynamics.polyakBeta μ L ∧ h = polyak.Dynamics.polyakAlpha μ L := by
  let ρ := quadraticRate μ L β τ h
  have hρ : 0 ≤ ρ := quadraticRate_nonneg hL.le hstable
  have hρ1 : ρ < 1 := quadraticRate_lt_one hL.le hstable
  have hK := effectiveCondition_gt_one hμ hL hτ
  have hK0 : 0 < effectiveCondition μ L τ := by linarith
  have hs := Real.sq_sqrt hK0.le
  have hs0 := Real.sqrt_nonneg (effectiveCondition μ L τ)
  have he : Real.sqrt (effectiveCondition μ L τ) * (1 - ρ) = 1 + ρ := by
    have heq' : ρ = (Real.sqrt (effectiveCondition μ L τ) - 1) /
        (Real.sqrt (effectiveCondition μ L τ) + 1) := heq
    have he := (eq_div_iff (show Real.sqrt (effectiveCondition μ L τ) + 1 ≠ 0 by positivity)).mp heq'
    nlinarith
  have hsq : effectiveCondition μ L τ * (1 - ρ) ^ 2 = (1 + ρ) ^ 2 := by
    calc
      _ = (Real.sqrt (effectiveCondition μ L τ) * (1 - ρ)) ^ 2 := by rw [mul_pow, hs]
      _ = _ := congrArg (fun x : ℝ => x ^ 2) he
  obtain ⟨hm, hlast, hq⟩ := endpoint_rate_bounds hL.le hstable
  have hid : h * μ * effectiveCondition μ L τ =
      h * L * (1 + 2 * τ) - 2 * h * μ * τ := by
    dsimp [effectiveCondition]
    field_simp
  have hbound : h * μ * effectiveCondition μ L τ ≤ (1 + ρ) ^ 2 := by
    rw [hid]
    dsimp [ρ]
    nlinarith
  have hmle : h * μ ≤ (1 - ρ) ^ 2 := by
    apply le_of_mul_le_mul_right _ hK0
    rw [mul_comm ((1 - ρ) ^ 2), hsq]
    exact hbound
  have hmeq : h * μ = (1 - ρ) ^ 2 := le_antisymm hmle hm
  have hvalue : h * L * (1 + 2 * τ) - 2 * h * μ * τ = (1 + ρ) ^ 2 := by
    rw [← hid, hmeq, mul_comm, hsq]
  have hqeq : β - h * μ * τ = ρ ^ 2 := by
    dsimp [ρ] at hvalue ⊢
    nlinarith
  have hlast_eq : 1 - (-S β τ h L) + Q β τ h L = (1 - ρ) ^ 2 := by
    dsimp [S, Q]
    nlinarith
  have hnegroot : ∀ z : ℂ, z ^ 2 - ((-S β τ h L : ℝ) : ℂ) * z + (Q β τ h L : ℂ) = 0 → ‖z‖ ≤ ρ := by
    intro z hz
    have hz' : characteristic β τ h L (-z) = 0 := by
      rw [characteristic_eq]
      push_cast at hz
      linear_combination hz
    simpa using root_norm_le_rate hL.le hstable (Set.right_mem_Icc.mpr hL.le) hz'
  obtain ⟨_, hqL⟩ := endpoint_equality hρ hρ1 hnegroot hlast_eq
  have htprod : (h * (L - μ)) * τ = 0 := by
    dsimp [Q] at hqL
    nlinarith
  have hτ0 : τ = 0 := (mul_eq_zero.mp htprod).resolve_left
    (ne_of_gt (mul_pos hh (sub_pos.mpr hL)))
  have hρQ : ρ = polyak.Dynamics.polyakQ μ L := by
    rw [hτ0] at heq
    calc
      ρ = priceFactor μ L 0 := by simpa only [ρ, hτ0] using heq
      _ = polyak.Dynamics.conditionQ (L / μ) := by simp [priceFactor, effectiveCondition, polyak.Dynamics.conditionQ]
      _ = _ := (polyak.Dynamics.polyakQ_eq_conditionQ hμ hL).symm
  have hβQ : β = polyak.Dynamics.polyakBeta μ L := by
    rw [hτ0] at hqeq
    simpa [polyak.Dynamics.polyakBeta, hρQ] using hqeq
  have hαμ : polyak.Dynamics.polyakAlpha μ L * μ =
      (1 - polyak.Dynamics.polyakQ μ L) ^ 2 := by
    have ha := polyak.Dynamics.polyak_normalizedA hμ hL
    have hb := polyak.Dynamics.polyak_normalizedB hμ hL
    dsimp [polyak.Dynamics.normalizedA, polyak.Dynamics.normalizedB,
      polyak.Dynamics.polyakBeta] at ha hb
    nlinarith
  exact ⟨hτ0, hβQ, by rw [hρQ] at hmeq; nlinarith⟩

theorem price_equality_iff_polyak {μ L β τ h : ℝ} (hμ : 0 < μ) (hL : μ < L)
    (hh : 0 < h) (hτ : 0 ≤ τ) (hstable : Stable μ L β τ h) :
    quadraticRate μ L β τ h = priceFactor μ L τ ↔
      τ = 0 ∧ β = polyak.Dynamics.polyakBeta μ L ∧ h = polyak.Dynamics.polyakAlpha μ L := by
  constructor
  · exact price_equality_only_polyak hμ hL hh hτ hstable
  · rintro ⟨rfl, rfl, rfl⟩
    rw [quadraticRate_tau_zero, polyak.Dynamics.polyak_quadraticRate hμ hL,
      polyak.Dynamics.polyakQ_eq_conditionQ hμ hL]
    simp [priceFactor, effectiveCondition, polyak.Dynamics.conditionQ]

end nesterov.Quadratic
