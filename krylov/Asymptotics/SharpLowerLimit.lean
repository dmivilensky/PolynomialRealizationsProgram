import krylov.Asymptotics.RecoveryLowerBound
import krylov.Asymptotics.SharpRecoveryGraph

/-!
Article: main_krylov, thm:limit, sharp lower limits.
Use: genuine compact recovery states approach the same actual continuum
Bellman value. An arbitrarily small fixed mesh inflation then proves every
strict lower target, for the original infinite and growing finite optima.
Source: constructed actual optimizer type states and spectrally admissible
finite probability recovery designs; all approximation limits are proved.
-/
namespace krylov.Asymptotics
noncomputable section
open Set Real Filter MeasureTheory
open krylov.Design krylov.ContinuumControl
open scoped Topology

/-- A fixed inflation arbitrarily close to one preserves every strict
lower target; the sign of that target is unrestricted. -/
theorem exists_inflation_above {b r : ℝ} (hb : b < r) : ∃ c > (1 : ℝ), b < r / c := by
  by_cases hb₀ : b ≤ 0
  · refine ⟨2, by norm_num, (lt_div_iff₀ (by norm_num : (0 : ℝ) < 2)).2 ?_⟩
    linarith
  · have hbp : 0 < b := lt_of_not_ge hb₀
    have hr : 1 < r / b := (lt_div_iff₀ hbp).2 (by simpa only [one_mul] using hb)
    obtain ⟨c, hc, hcr⟩ := exists_between hr
    refine ⟨c, hc, (lt_div_iff₀ (zero_lt_one.trans hc)).2 ?_⟩
    have hh := (lt_div_iff₀ hbp).1 hcr
    simpa only [mul_comm] using hh

/-- Actual near-optimal smooth states give the full sharp lower limit
for the original optimized infinite design problem. -/
theorem eventually_lower_sharp_infinite {ι : Type*} {l : Filter ι} {γ : ℝ} {σ : ℝ → ℝ}
    (hγ : 0 < γ)
    (hnear : ∀ ε > (0 : ℝ), ∃ Y > (0 : ℝ), ∃ R : RecoveryState Y,
      feedbackValue γ σ 1 - ε < ∫ y in 0..Y, R.energy y ^ (-γ))
    {I : ι → chebyshev1.SpectralInterval}
    (hR : Tendsto (fun i ↦ (I i).kappa - 1) l atTop)
    {b : ℝ} (hb : b < feedbackValue γ σ 1) :
    ∀ᶠ i in l, b < designSpacing (I i) * infinitePowerValue (I i) γ := by
  obtain ⟨Y, hY, R, hrew⟩ := hnear ((feedbackValue γ σ 1 - b) / 2) (by linarith)
  have hbr : b < ∫ y in 0..Y, R.energy y ^ (-γ) := by linarith
  obtain ⟨c, hc, hbc⟩ := exists_inflation_above hbr
  exact R.eventually_lower_infinitePowerValue hY hγ hc hR hbc

/-- Actual near-optimal states also give the sharp lower limit for every
finite degree budget whose true type-time budget tends to infinity. -/
theorem eventually_lower_sharp_finite {ι : Type*} {l : Filter ι} {γ : ℝ} {σ : ℝ → ℝ}
    (hγ : 0 < γ)
    (hnear : ∀ ε > (0 : ℝ), ∃ Y > (0 : ℝ), ∃ R : RecoveryState Y,
      feedbackValue γ σ 1 - ε < ∫ y in 0..Y, R.energy y ^ (-γ))
    {I : ι → chebyshev1.SpectralInterval} {M : ι → ℕ}
    (hR : Tendsto (fun i ↦ (I i).kappa - 1) l atTop)
    (hM : Tendsto (fun i ↦ (M i : ℝ) * designSpacing (I i)) l atTop)
    {b : ℝ} (hb : b < feedbackValue γ σ 1) :
    ∀ᶠ i in l, b < designSpacing (I i) * optimalValue (I i) (M i) (fun _ ↦ 1) γ := by
  obtain ⟨Y, hY, R, hrew⟩ := hnear ((feedbackValue γ σ 1 - b) / 2) (by linarith)
  have hbr : b < ∫ y in 0..Y, R.energy y ^ (-γ) := by linarith
  obtain ⟨c, hc, hbc⟩ := exists_inflation_above hbr
  exact R.eventually_lower_optimalValue hY hγ hc hR hM hbc

end
end krylov.Asymptotics
