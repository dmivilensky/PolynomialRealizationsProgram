import polyak.Growth.Original
import polyak.Growth.Rate
import polyak.Dynamics.Rate
import Mathlib.Topology.Order.LiminfLimsup

/-!
Article: Appendix A, spectralgeneral(b), passage from Γ to the original rate.
Use: the exact original dimension-uniform limsup is bounded by free-state growth.
Proof: the √2 factor has nth root tending to one.
-/

namespace polyak.Growth
noncomputable section
open Filter
open scoped Topology

/-- Article: upper original rate. Use: retain the from-rest source problem and its limsup definition. -/
theorem originalRate_le_growthRate {μ L α β : ℝ} (hμ : 0 < μ) (hL : μ < L)
    (hα : 0 < α) (hβ : 0 ≤ β) :
    Dynamics.rate μ L α β ≤
      growthRate (Dynamics.normalizedA μ L α β) (Dynamics.normalizedB μ L α) β := by
  let A := Dynamics.normalizedA μ L α β
  let B := Dynamics.normalizedB μ L α
  have hB : B ≠ 0 := by dsimp [B, Dynamics.normalizedB]; positivity
  have hinv : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hc : Tendsto (fun n : ℕ => (Real.sqrt 2)^((n : ℝ)⁻¹)) atTop (𝓝 1) := by
    simpa only [Real.rpow_zero, Function.comp_def] using
      (Real.continuousAt_const_rpow (a := Real.sqrt 2) (b := 0) (by positivity)).tendsto.comp hinv
  have hg := hc.mul (tendsto_envelope_root (A := A) (β := β) hB)
  simp only [one_mul] at hg
  have hh : ∀ n : ℕ, Dynamics.worstAll μ L α β n ^ ((n : ℝ)⁻¹) ≤
      Real.sqrt 2 ^ ((n : ℝ)⁻¹) * envelope A B β n ^ ((n : ℝ)⁻¹) := by
    intro n
    calc
      _ ≤ (Real.sqrt 2*envelope A B β n)^((n : ℝ)⁻¹) :=
        Real.rpow_le_rpow (Dynamics.worstAll_nonneg hμ hL hα.le hβ n)
          (worstAll_le_envelope μ L α β n) (by positivity)
      _ = _ := Real.mul_rpow (Real.sqrt_nonneg _) (envelope_nonneg A B β n)
  have hl := limsup_le_limsup (Eventually.of_forall hh)
    (isCoboundedUnder_le_of_le atTop (fun n =>
      Real.rpow_nonneg (Dynamics.worstAll_nonneg hμ hL hα.le hβ n) _)) hg.isBoundedUnder_le
  rwa [hg.limsup_eq] at hl

end
end polyak.Growth
