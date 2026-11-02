import krylov.ContinuumBV.BochnerSums
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
Article: main_krylov, apC:lem:fund, physical integrals with atomic mass.
Use: pointwise limits of bounded exact chord coefficients identify actual
tagged density sums with their Bochner integrals. Unlike a uniform-continuity
argument, this permits the coefficient to change at countably many atoms.
Source: Bochner dominated convergence with the actual integrable state density.
-/

namespace krylov.ContinuumBV
noncomputable section
open Set Filter MeasureTheory
open scoped Topology

variable {X V ι : Type*} [MeasurableSpace X] [NormedAddCommGroup V] [NormedSpace ℝ V]
  [CompleteSpace V]

omit [CompleteSpace V] in
/-- The limiting operator acts integrably on the real state density. This
also rules out default-zero nonintegrable Bochner values in later identities. -/
theorem density_partition_limit_integrable [DecidableEq ι] {μ : Measure X} {h : X → V}
    (hi : Integrable h μ) (s : ℕ → Finset ι) (A : ℕ → ι → Set X)
    (c : ℕ → ι → V →L[ℝ] ℝ) {f : X → V →L[ℝ] ℝ}
    (hA : ∀ k i, i ∈ s k → MeasurableSet (A k i))
    (hdisj : ∀ k, (s k : Set ι).PairwiseDisjoint (A k))
    (hcover : ∀ k, ∀ᵐ x ∂μ, ∃ i ∈ s k, x ∈ A k i)
    (hbound : ∃ C, ∀ k i, i ∈ s k → ‖c k i‖ ≤ C)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun k => partitionCoefficient (s k) (A k) (c k) x)
      atTop (𝓝 (f x))) : Integrable (fun x => f x (h x)) μ := by
  let step : ℕ → X → V →L[ℝ] ℝ := fun k => partitionCoefficient (s k) (A k) (c k)
  obtain ⟨C, hC⟩ := hbound
  have hmeas : ∀ k, AEStronglyMeasurable (fun x => step k x (h x)) μ := by
    intro k
    have hm : Integrable (fun x => step k x (h x)) μ := by
      simp_rw [show step k = partitionCoefficient (s k) (A k) (c k) from rfl,
        partitionCoefficient_apply]
      exact integrable_finsetSum _ (fun i hi' => ((c k i).integrable_comp hi).indicator (hA k i hi'))
    exact hm.aestronglyMeasurable
  have hb : ∀ k, ∀ᵐ x ∂μ, ‖step k x (h x)‖ ≤ C * ‖h x‖ := by
    intro k
    filter_upwards [hcover k] with x hx
    obtain ⟨i, hi', hxi⟩ := hx
    rw [show step k x = c k i from partitionCoefficient_eq (hdisj k) hi' hxi]
    exact (c k i).le_opNorm (h x) |>.trans
      (mul_le_mul_of_nonneg_right (hC k i hi') (norm_nonneg _))
  have hl : ∀ᵐ x ∂μ, Tendsto (fun k => step k x (h x)) atTop (𝓝 (f x (h x))) := by
    filter_upwards [hlim] with x hx
    exact ((ContinuousLinearMap.apply ℝ ℝ (h x)).continuous.tendsto _).comp hx
  apply (hi.norm.const_mul C).mono' (aestronglyMeasurable_of_tendsto_ae atTop hmeas hl)
  filter_upwards [hl, ae_all_iff.2 hb] with x hx hb
  exact le_of_tendsto hx.norm (Eventually.of_forall hb)

/-- Bounded partition coefficients converge against any genuine integrable
state density whenever their actual step functions converge almost everywhere.
No density substitution identity or limiting integral is assumed. -/
theorem density_partition_sums_tendsto [DecidableEq ι] {μ : Measure X} {h : X → V}
    (hi : Integrable h μ) (s : ℕ → Finset ι) (A : ℕ → ι → Set X)
    (c : ℕ → ι → V →L[ℝ] ℝ) {f : X → V →L[ℝ] ℝ}
    (hA : ∀ k i, i ∈ s k → MeasurableSet (A k i))
    (hdisj : ∀ k, (s k : Set ι).PairwiseDisjoint (A k))
    (hcover : ∀ k, ∀ᵐ x ∂μ, ∃ i ∈ s k, x ∈ A k i)
    (hbound : ∃ C, ∀ k i, i ∈ s k → ‖c k i‖ ≤ C)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun k => partitionCoefficient (s k) (A k) (c k) x)
      atTop (𝓝 (f x))) :
    Tendsto (fun k => ∑ i ∈ s k, c k i (∫ x in A k i, h x ∂μ))
      atTop (𝓝 (∫ x, f x (h x) ∂μ)) := by
  let step : ℕ → X → V →L[ℝ] ℝ := fun k => partitionCoefficient (s k) (A k) (c k)
  obtain ⟨C, hC⟩ := hbound
  have hmeas : ∀ k, AEStronglyMeasurable (fun x => step k x (h x)) μ := by
    intro k
    have hm : Integrable (fun x => step k x (h x)) μ := by
      simp_rw [show step k = partitionCoefficient (s k) (A k) (c k) from rfl,
        partitionCoefficient_apply]
      exact integrable_finsetSum _ (fun i hi' => ((c k i).integrable_comp hi).indicator (hA k i hi'))
    exact hm.aestronglyMeasurable
  have hb : ∀ k, ∀ᵐ x ∂μ, ‖step k x (h x)‖ ≤ C * ‖h x‖ := by
    intro k
    filter_upwards [hcover k] with x hx
    obtain ⟨i, hi', hxi⟩ := hx
    rw [show step k x = c k i from partitionCoefficient_eq (hdisj k) hi' hxi]
    exact (c k i).le_opNorm (h x) |>.trans
      (mul_le_mul_of_nonneg_right (hC k i hi') (norm_nonneg _))
  have hl : ∀ᵐ x ∂μ, Tendsto (fun k => step k x (h x)) atTop (𝓝 (f x (h x))) := by
    filter_upwards [hlim] with x hx
    exact ((ContinuousLinearMap.apply ℝ ℝ (h x)).continuous.tendsto _).comp hx
  have he := tendsto_integral_of_dominated_convergence (fun x => C * ‖h x‖)
    hmeas (hi.norm.const_mul C) hb hl
  simpa only [step, integral_partitionCoefficient_apply hi _ _ _ (hA _)] using he

end
end krylov.ContinuumBV
