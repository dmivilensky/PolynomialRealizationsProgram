import chebyshev1.Stochastic.Martingale
import Mathlib.MeasureTheory.Function.L2Space

/-!
Two successively centered noises per query. The intermediate sigma-algebra
contains the oracle noise, so update noise may depend on that oracle noise.
-/
namespace chebyshev1.Stochastic
noncomputable section
open MeasureTheory Filter
open scoped BigOperators RealInnerProductSpace

variable {Ω E : Type*} [mΩ : MeasurableSpace Ω]
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]

omit [IsProbabilityMeasure μ] [CompleteSpace E] in
theorem integrable_inner_of_memLp_two {X Y : Ω → E}
    (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) :
    Integrable (fun ω => ⟪X ω, Y ω⟫) μ := by
  have hnorm := hX.norm.integrable_mul hY.norm
  exact hnorm.mono' (hX.aestronglyMeasurable.inner hY.aestronglyMeasurable)
    (Eventually.of_forall fun ω => norm_inner_le_norm (X ω) (Y ω))

theorem conditionalCenter_of_le {m q : MeasurableSpace Ω}
    (hmq : m ≤ q) (hq : q ≤ mΩ) {X : Ω → E}
    (hc : μ[X | q] =ᵐ[μ] 0) : μ[X | m] =ᵐ[μ] 0 := by
  exact (condExp_condExp_of_le hmq hq).symm.trans
    ((condExp_congr_ae hc).trans (by rw [condExp_zero]))

omit [IsProbabilityMeasure μ] in
theorem conditionalCenter_linearMap {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [CompleteSpace F] {m : MeasurableSpace Ω}
    {X : Ω → E} (hX : Integrable X μ) (hc : μ[X | m] =ᵐ[μ] 0)
    (T : E →L[ℝ] F) : μ[fun ω => T (X ω) | m] =ᵐ[μ] 0 := by
  have hcomm := T.comp_condExp_comm (m := m) hX
  change (fun ω => T (μ[X | m] ω)) =ᵐ[μ] μ[fun ω => T (X ω) | m] at hcomm
  filter_upwards [hcomm, hc] with ω hcomm hc
  simpa only [Function.comp_apply, hc, Pi.zero_apply, map_zero] using hcomm.symm

/-- Exact mean and variance for two noises with the stated causal conditioning. -/
theorem pairedNoise_mean_variance (m q : ℕ → MeasurableSpace Ω)
    (hm : ∀ s, m s ≤ mΩ) (hq : ∀ s, q s ≤ mΩ) (hmono : Monotone m)
    (hpast : ∀ s, m s ≤ q s) (hfuture : ∀ s, q s ≤ m (s+1))
    (U V : ℕ → Ω → E) (N : ℕ)
    (hU : ∀ s < N, StronglyMeasurable[q s] (U s))
    (hV : ∀ s < N, StronglyMeasurable[m (s+1)] (V s))
    (hU2 : ∀ s < N, MemLp (U s) 2 μ) (hV2 : ∀ s < N, MemLp (V s) 2 μ)
    (hcU : ∀ s < N, μ[U s | m s] =ᵐ[μ] 0)
    (hcV : ∀ s < N, μ[V s | q s] =ᵐ[μ] 0) :
    (∫ ω, ∑ s ∈ Finset.range N, (U s ω + V s ω) ∂μ) = 0 ∧
      (∫ ω, ‖∑ s ∈ Finset.range N, (U s ω + V s ω)‖ ^ 2 ∂μ) =
        ∑ s ∈ Finset.range N,
          ((∫ ω, ‖U s ω‖ ^ 2 ∂μ) + (∫ ω, ‖V s ω‖ ^ 2 ∂μ)) := by
  let Y : ℕ → Ω → E := fun s ω => U s ω + V s ω
  have hY2 : ∀ s < N, MemLp (Y s) 2 μ := by
    intro s hs
    exact (hU2 s hs).add (hV2 s hs)
  have hYint : ∀ s < N, Integrable (Y s) μ := by
    intro s hs
    exact (hY2 s hs).integrable (by norm_num)
  have hYmeas : ∀ s < N, StronglyMeasurable[m (s+1)] (Y s) := by
    intro s hs
    exact ((hU s hs).mono (hfuture s)).add (hV s hs)
  have hYcenter : ∀ s < N, μ[Y s | m s] =ᵐ[μ] 0 := by
    intro s hs
    have h := condExp_add ((hU2 s hs).integrable (by norm_num))
      ((hV2 s hs).integrable (by norm_num)) (m s)
    change μ[Y s | m s] =ᵐ[μ]
      (fun ω => μ[U s | m s] ω + μ[V s | m s] ω) at h
    have hvc := conditionalCenter_of_le (hpast s) (hq s) (hcV s hs)
    filter_upwards [h, hcU s hs, hvc] with ω hadd hu hv
    simpa only [hu, hv, Pi.zero_apply, zero_add] using hadd
  have hYinner : ∀ s < N, ∀ t < N,
      Integrable (fun ω => ⟪Y s ω, Y t ω⟫) μ := by
    intro s hs t ht
    exact integrable_inner_of_memLp_two (hY2 s hs) (hY2 t ht)
  constructor
  · exact martingaleDifference_sum_mean m hm Y N hYint hYcenter
  · rw [martingaleDifference_sum_norm_sq m hm hmono Y N hYmeas hYint hYinner hYcenter]
    apply Finset.sum_congr rfl
    intro s hs
    have hsN := Finset.mem_range.mp hs
    have hiU : Integrable (fun ω => ‖U s ω‖^2) μ :=
      (hU2 s hsN).integrable_norm_pow (by norm_num)
    have hiV : Integrable (fun ω => ‖V s ω‖^2) μ :=
      (hV2 s hsN).integrable_norm_pow (by norm_num)
    have hiUV := integrable_inner_of_memLp_two (hU2 s hsN) (hV2 s hsN)
    have hcross := integral_inner_eq_zero_of_condExp (hq s)
      (hU s hsN).aestronglyMeasurable ((hV2 s hsN).integrable (by norm_num))
      hiUV (hcV s hsN)
    have hiFirst : Integrable (fun ω => ‖U s ω‖ ^ 2 + 2*⟪U s ω, V s ω⟫) μ :=
      hiU.add (hiUV.const_mul 2)
    simp only [Y, norm_add_sq_real]
    rw [integral_add hiFirst hiV,
      integral_add hiU (hiUV.const_mul 2), integral_const_mul, hcross]
    ring

end
end chebyshev1.Stochastic
