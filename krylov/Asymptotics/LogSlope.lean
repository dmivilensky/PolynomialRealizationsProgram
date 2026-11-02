import krylov.ContinuumControl.CanonicalGraph
import krylov.LotkaVolterra.GlobalGraphRegularity
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
Article: main_krylov, apC:lem:B.
Use: the sharp logarithmic slope bounds for the actual globally constructed
separating graphs, including the subcritical saddle. These are the uniform
regularity estimates used in the discrete drift/impulse comparison.
Source: the proved graph wedges and ordinary differentiation/mean values.
-/

namespace krylov.Asymptotics
noncomputable section
open Set Filter
open krylov.LotkaVolterra
open scoped Topology ContDiff

/-- The logarithmic Lipschitz constant in the source. -/
def graphBound (γ : ℝ) : ℝ := if γ < 1 then γ else 1 / 2

/-- Logarithmic derivative of the feedback control `sqrt σ`. This definition
continues through the saddle, where the printed rational quotient is 0/0. -/
def logSlope (σ : ℝ → ℝ) (r : ℝ) : ℝ := r * deriv σ r / (2 * σ r)

namespace SubcriticalGraph

variable {γ : ℝ} (G : krylov.LotkaVolterra.SubcriticalGraph γ)

/-- Away from the saddle the derivative definition is the printed quotient. -/
theorem logSlope_eq {r : ℝ} (hγ : 0 < γ) (hγ₁ : γ < 1)
    (hr : 0 < r) (hne : r ≠ saddleU γ) :
    logSlope G.σ r = (G.σ r - 1 - γ * r) / (G.σ r + 1 - r) := by
  have hs := G.positive hγ hγ₁ hr
  have hden : G.σ r + 1 - r ≠ 0 := by
    rcases lt_or_gt_of_ne hne with hlo | hhi
    · linarith [(G.lower r ⟨hr, hlo⟩).2.2]
    · linarith [(G.upper r hhi).2.2]
  rw [logSlope, (G.derivative r hr hne).deriv]
  field_simp

/-- Sharp bounds off the stationary point follow directly from the wedges. -/
theorem logSlope_bounds_of_ne {r : ℝ} (hγ : 0 < γ) (hγ₁ : γ < 1)
    (hr : 0 < r) (hne : r ≠ saddleU γ) :
    0 ≤ logSlope G.σ r ∧ logSlope G.σ r ≤ γ := by
  rw [logSlope_eq G hγ hγ₁ hr hne]
  have hA : (1 - γ) * saddleS γ = 1 + γ := by
    have he := saddleS_eq_one_add_mul_saddleU (ne_of_lt hγ₁)
    rw [saddleU_eq_saddleS_add_one (ne_of_lt hγ₁)] at he
    nlinarith
  rcases lt_or_gt_of_ne hne with hlo | hhi
  · have hb := G.lower r ⟨hr, hlo⟩
    have hd : 0 < G.σ r + 1 - r := by linarith [hb.2.2]
    refine ⟨div_nonneg (by linarith [hb.1]) hd.le, (div_le_iff₀ hd).2 ?_⟩
    nlinarith [mul_nonneg (show 0 ≤ 1 - γ by linarith)
      (show 0 ≤ saddleS γ - G.σ r by linarith [hb.2.1])]
  · have hb := G.upper r hhi
    have hd : G.σ r + 1 - r < 0 := by linarith [hb.2.2]
    refine ⟨div_nonneg_of_nonpos (by linarith [hb.2.1]) hd.le,
      (div_le_iff_of_neg hd).2 ?_⟩
    nlinarith [mul_nonneg (show 0 ≤ 1 - γ by linarith)
      (show 0 ≤ G.σ r - saddleS γ by linarith [hb.1])]

/-- The actual derivative quotient is continuous through the saddle. -/
theorem logSlope_continuousAt {r : ℝ} (hγ : 0 < γ) (hγ₁ : γ < 1)
    (hr : 0 < r) : ContinuousAt (logSlope G.σ) r := by
  have hG := G.contDiffAt_one hγ hγ₁ hr
  have hd : ContinuousAt (deriv G.σ) r :=
    (hG.derivWithin (m := 0) (by norm_num)).continuousAt
  exact (continuousAt_id.mul hd).div (continuousAt_const.mul hG.continuousAt)
    (mul_ne_zero (by norm_num) (G.positive hγ hγ₁ hr).ne')

/-- The sharp source estimate holds at every positive ratio, including the
saddle by continuity of the genuine derivative rather than division by 0. -/
theorem logSlope_bounds {r : ℝ} (hγ : 0 < γ) (hγ₁ : γ < 1) (hr : 0 < r) :
    0 ≤ logSlope G.σ r ∧ logSlope G.σ r ≤ γ := by
  by_cases heq : r = saddleU γ
  · subst r
    have hc := logSlope_continuousAt G hγ hγ₁ (saddleU_pos hγ₁)
    have hlim : Tendsto (logSlope G.σ) (𝓝[>] saddleU γ)
        (𝓝 (logSlope G.σ (saddleU γ))) := hc.tendsto.mono_left nhdsWithin_le_nhds
    have he : ∀ᶠ U in 𝓝[>] saddleU γ,
        0 ≤ logSlope G.σ U ∧ logSlope G.σ U ≤ γ := by
      filter_upwards [self_mem_nhdsWithin] with U hU
      exact logSlope_bounds_of_ne G hγ hγ₁ ((saddleU_pos hγ₁).trans hU) (ne_of_gt hU)
    exact ⟨ge_of_tendsto hlim (he.mono fun _ h ↦ h.1),
      le_of_tendsto hlim (he.mono fun _ h ↦ h.2)⟩
  · exact logSlope_bounds_of_ne G hγ hγ₁ hr heq

end SubcriticalGraph

/-- Endpoint bounds use the actual strict gap corridor `1<σ(r)−r<3`. -/
theorem endpoint_logSlope_bounds {σ : ℝ → ℝ}
    (hb : ∀ r ≥ 1, r + 1 < σ r ∧ σ r < r + 3)
    (hd : ∀ r ≥ 1, HasDerivAt σ
      (2 * σ r * (σ r - 1 - r) / (r * (σ r + 1 - r))) r)
    {r : ℝ} (hr : 1 ≤ r) :
    0 ≤ logSlope σ r ∧ logSlope σ r ≤ 1 / 2 := by
  have hs : 0 < σ r := by linarith [(hb r hr).1]
  have hrp : 0 < r := by linarith
  have hden : 0 < σ r + 1 - r := by linarith [(hb r hr).1]
  have he : logSlope σ r = (σ r - 1 - r) / (σ r + 1 - r) := by
    rw [logSlope, (hd r hr).deriv]
    field_simp
  rw [he]
  refine ⟨div_nonneg (by linarith [(hb r hr).1]) hden.le,
    (div_le_iff₀ hden).2 ?_⟩
  linarith [(hb r hr).2]

end
end krylov.Asymptotics
