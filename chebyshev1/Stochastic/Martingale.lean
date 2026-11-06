import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.Analysis.InnerProductSpace.Basic

/-!
Mean and exact squared-norm identity for a finite Hilbert-space martingale
difference sum. Orthogonality is derived from conditional centering and
adaptedness, rather than assumed.
-/
namespace chebyshev1.Stochastic
noncomputable section
open MeasureTheory Filter
open scoped BigOperators RealInnerProductSpace

variable {Ω E : Type*} [mΩ : MeasurableSpace Ω]
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- A conditionally centered future increment is orthogonal to every integrable past test. -/
theorem integral_inner_eq_zero_of_condExp {m : MeasurableSpace Ω} (hm : m ≤ mΩ)
    {X Y : Ω → E} (hX : AEStronglyMeasurable[m] X μ)
    (hY : Integrable Y μ) (hXY : Integrable (fun ω => ⟪X ω, Y ω⟫) μ)
    (hcenter : μ[Y | m] =ᵐ[μ] 0) :
    (∫ ω, ⟪X ω, Y ω⟫ ∂μ) = 0 := by
  have hpull := condExp_bilin_of_aestronglyMeasurable_left (innerSL ℝ) hX hXY hY
  change μ[fun ω => ⟪X ω, Y ω⟫ | m] =ᵐ[μ]
    (fun ω => ⟪X ω, μ[Y | m] ω⟫) at hpull
  have hzero : μ[fun ω => ⟪X ω, Y ω⟫ | m] =ᵐ[μ] 0 := by
    filter_upwards [hpull, hcenter] with ω hp hc
    simpa only [hc, Pi.zero_apply, inner_zero_right] using hp
  rw [← integral_condExp hm, integral_congr_ae hzero]
  simp

theorem integral_eq_zero_of_condExp {m : MeasurableSpace Ω} (hm : m ≤ mΩ)
    {Y : Ω → E} (hcenter : μ[Y | m] =ᵐ[μ] 0) : (∫ ω, Y ω ∂μ) = 0 := by
  rw [← integral_condExp hm, integral_congr_ae hcenter]
  simp

theorem martingaleDifference_integral_inner (m : ℕ → MeasurableSpace Ω)
    (hm : ∀ t, m t ≤ mΩ) (hmono : Monotone m) (Y : ℕ → Ω → E) (N : ℕ)
    (hadapt : ∀ s < N, StronglyMeasurable[m (s+1)] (Y s))
    (hint : ∀ s < N, Integrable (Y s) μ)
    (hinner : ∀ s < N, ∀ t < N, Integrable (fun ω => ⟪Y s ω, Y t ω⟫) μ)
    (hcenter : ∀ s < N, μ[Y s | m s] =ᵐ[μ] 0) {s t : ℕ}
    (hs : s < N) (ht : t < N) (hst : s ≠ t) :
    (∫ ω, ⟪Y s ω, Y t ω⟫ ∂μ) = 0 := by
  rcases lt_or_gt_of_ne hst with hst | hts
  · exact integral_inner_eq_zero_of_condExp (hm t)
      ((hadapt s hs).mono (hmono (by omega))).aestronglyMeasurable
      (hint t ht) (hinner s hs t ht) (hcenter t ht)
  · have h := integral_inner_eq_zero_of_condExp (hm s)
      ((hadapt t ht).mono (hmono (by omega))).aestronglyMeasurable
      (hint s hs) (hinner t ht s hs) (hcenter s hs)
    simpa only [real_inner_comm] using h

/-- Exact martingale second-moment sum, under explicit integrability hypotheses. -/
theorem martingaleDifference_sum_norm_sq (m : ℕ → MeasurableSpace Ω)
    (hm : ∀ t, m t ≤ mΩ) (hmono : Monotone m) (Y : ℕ → Ω → E) (N : ℕ)
    (hadapt : ∀ s < N, StronglyMeasurable[m (s+1)] (Y s))
    (hint : ∀ s < N, Integrable (Y s) μ)
    (hinner : ∀ s < N, ∀ t < N, Integrable (fun ω => ⟪Y s ω, Y t ω⟫) μ)
    (hcenter : ∀ s < N, μ[Y s | m s] =ᵐ[μ] 0) :
    (∫ ω, ‖∑ s ∈ Finset.range N, Y s ω‖ ^ 2 ∂μ) =
      ∑ s ∈ Finset.range N, ∫ ω, ‖Y s ω‖ ^ 2 ∂μ := by
  have heq : (fun ω => ‖∑ s ∈ Finset.range N, Y s ω‖ ^ 2) =
      (fun ω => ∑ s ∈ Finset.range N, ∑ t ∈ Finset.range N, ⟪Y s ω, Y t ω⟫) := by
    funext ω
    rw [← real_inner_self_eq_norm_sq, sum_inner]
    simp_rw [inner_sum]
  rw [heq, integral_finsetSum _ (fun s hs => integrable_finsetSum _
    (fun t ht => hinner s (Finset.mem_range.mp hs) t (Finset.mem_range.mp ht)))]
  apply Finset.sum_congr rfl
  intro s hs
  rw [integral_finsetSum _ (fun t ht =>
    hinner s (Finset.mem_range.mp hs) t (Finset.mem_range.mp ht))]
  rw [Finset.sum_eq_single_of_mem s hs]
  · simp
  · intro t ht hts
    exact martingaleDifference_integral_inner m hm hmono Y N hadapt hint hinner hcenter
      (Finset.mem_range.mp hs) (Finset.mem_range.mp ht) hts.symm

/-- A finite martingale difference sum has zero mean. -/
theorem martingaleDifference_sum_mean (m : ℕ → MeasurableSpace Ω)
    (hm : ∀ t, m t ≤ mΩ) (Y : ℕ → Ω → E) (N : ℕ)
    (hint : ∀ s < N, Integrable (Y s) μ)
    (hcenter : ∀ s < N, μ[Y s | m s] =ᵐ[μ] 0) :
    (∫ ω, ∑ s ∈ Finset.range N, Y s ω ∂μ) = 0 := by
  rw [integral_finsetSum _ (fun s hs => hint s (Finset.mem_range.mp hs))]
  apply Finset.sum_eq_zero
  intro s hs
  exact integral_eq_zero_of_condExp (hm s) (hcenter s (Finset.mem_range.mp hs))

end
end chebyshev1.Stochastic
