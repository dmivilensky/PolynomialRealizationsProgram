import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import nesterov.Rates.RootBounds

/-!
The elementary stability input used for arbitrary finite memory. A complex
Banach-algebra element whose entire spectrum lies in the open unit disk has
an absolutely summable sequence of powers. Repeated roots are included.
-/
namespace nesterov.IQC
noncomputable section
open Filter
open scoped Topology NNReal ENNReal

/-- Stable spectral radius gives the ℓ¹ bound needed by actual causal filters. -/
theorem summable_norm_powers {A : Type*} [NormedRing A] [NormedAlgebra ℂ A]
    [CompleteSpace A] [Nontrivial A] (a : A)
    (h : ∀ z ∈ spectrum ℂ a,‖z‖<1) : Summable (fun n : ℕ=>‖a^n‖) := by
  have hs : spectralRadius ℂ a<1 := by
    apply spectrum.spectralRadius_lt_of_forall_lt a
    intro z hz
    exact_mod_cast h z hz
  obtain ⟨q,hq0,hq,hq1⟩ : ∃ q : ℝ≥0,0<q ∧ spectralRadius ℂ a<q ∧ q<1 := by
    obtain ⟨q,hq,hq1⟩:=ENNReal.lt_iff_exists_nnreal_btwn.mp hs
    exact ⟨q,by exact_mod_cast (lt_of_le_of_lt (zero_le : (0:ℝ≥0∞)≤spectralRadius ℂ a) hq),hq,
      by exact_mod_cast hq1⟩
  have ht:=spectrum.pow_norm_pow_one_div_tendsto_nhds_spectralRadius a
  have he : ∀ᶠ n : ℕ in atTop,‖a^n‖^((n:ℝ)⁻¹)<(q:ℝ) := by
    have hh:=ht.eventually (gt_mem_nhds hq)
    filter_upwards [hh] with n hn
    have hn' : ENNReal.ofReal (‖a^n‖^((n:ℝ)⁻¹))<(q:ℝ≥0∞) := by
      simpa only [one_div] using hn
    exact (ENNReal.ofReal_lt_coe_iff (Real.rpow_nonneg (norm_nonneg _) _)).mp hn'
  have hb : ∀ᶠ n : ℕ in atTop,‖a^n‖≤(q:ℝ)^n := by
    filter_upwards [he,eventually_gt_atTop 0] with n hn hn0
    calc
      _=(‖a^n‖^((n:ℝ)⁻¹))^n :=
        (Real.rpow_inv_natCast_pow (norm_nonneg _) (by omega)).symm
      _≤(q:ℝ)^n := pow_le_pow_left₀ (Real.rpow_nonneg (norm_nonneg _) _) hn.le n
  apply (summable_geometric_of_lt_one q.coe_nonneg (by exact_mod_cast hq1)).of_norm_bounded_eventually
  have hb' : ∀ᶠ n : ℕ in cofinite,‖a^n‖≤(q:ℝ)^n := by
    simpa only [Nat.cofinite_eq_atTop] using hb
  filter_upwards [hb'] with n hn
  simpa only [Real.norm_eq_abs,abs_of_nonneg (norm_nonneg _)] using hn

end
end nesterov.IQC
