import krylov.LotkaVolterra.ExitStopped
import krylov.LotkaVolterra.GlobalGraphRegularity

/-!
Article: `main_krylov`, `apC:prop:LV`, the two precise exit alternatives.
The signed difference from the actual separating graph satisfies a scalar
linear ODE. Its integrating factor stays strictly positive, including at
the closed time endpoints. The initial side therefore selects the exit edge.

Source: the integrating-factor formula and the exact polynomial graph
identity, extended across the saddle by its vanishing factors.
-/
namespace krylov.LotkaVolterra
noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff Topology

/-- Closed-interval sign preservation for an actual scalar linear ODE.
The positive factor is constructed by integrating a continuous extension
of the coefficient; no extension of the solution is required. -/
theorem scalar_linear_endpoint_factor {a f : ℝ → ℝ} {T : ℝ} (hT : 0 ≤ T)
    (ha : ContinuousOn a (Icc 0 T))
    (hf : ∀ t ∈ Icc (0 : ℝ) T, HasDerivAt f (a t * f t) t) :
    ∃ k > 0, f T = f 0 * k := by
  let q : ℝ → ℝ := fun t ↦ max 0 (min t T)
  have hq (t : ℝ) : q t ∈ Icc (0 : ℝ) T :=
    ⟨le_max_left _ _, max_le hT (min_le_right _ _)⟩
  have hqeq (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) : q t = t := by
    simp [q, min_eq_left ht.2, max_eq_right ht.1]
  let ae : ℝ → ℝ := a ∘ q
  have hae : Continuous ae := ha.comp_continuous (by dsimp [q]; fun_prop) hq
  let A : ℝ → ℝ := fun t ↦ ∫ u in (0 : ℝ)..t, ae u
  have hA (t : ℝ) : HasDerivAt A (ae t) t :=
    intervalIntegral.integral_hasDerivAt_right (hae.intervalIntegrable 0 t)
      (hae.stronglyMeasurableAtFilter volume _) hae.continuousAt
  let H : ℝ → ℝ := fun t ↦ f t * Real.exp (-A t)
  have hHC : ContinuousOn H (Icc (0 : ℝ) T) :=
    (HasDerivAt.continuousOn hf).mul
      (Real.continuous_exp.comp (continuous_iff_continuousAt.mpr fun t ↦ (hA t).continuousAt).neg).continuousOn
  have hH (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) : HasDerivAt H 0 t := by
    have hae_eq : ae t = a t := by simp only [ae, Function.comp_apply, hqeq t ht]
    convert (hf t ht).mul ((hA t).neg.exp) using 1
    dsimp [H]
    rw [hae_eq]
    ring
  have hconst := constant_of_has_deriv_right_zero hHC
    (fun t ht ↦ (hH t ⟨ht.1, ht.2.le⟩).hasDerivWithinAt) T ⟨hT, le_rfl⟩
  have hprod : f T * Real.exp (-A T) = f 0 := by simpa [H, A] using hconst
  refine ⟨Real.exp (A T), Real.exp_pos _, ?_⟩
  calc
    f T = f T * (Real.exp (-A T) * Real.exp (A T)) := by
      rw [← Real.exp_add]
      simp
    _ = f 0 * Real.exp (A T) := by rw [← mul_assoc, hprod]

namespace SubcriticalGraph
variable {γ : ℝ} (G : SubcriticalGraph γ)

/-- The polynomial graph equation remains valid at the saddle itself. -/
theorem graph_equation_all (hγ₁ : γ < 1) {U : ℝ} (hU : 0 < U) :
    deriv G.σ U * (U * (G.σ U + 1 - U)) =
      2 * G.σ U * (G.σ U - 1 - γ * U) := by
  by_cases he : U = saddleU γ
  · rw [he, G.saddle]
    have hA := saddleS_eq_one_add_mul_saddleU (ne_of_lt hγ₁)
    have hB := saddleU_eq_saddleS_add_one (ne_of_lt hγ₁)
    have hzero : saddleS γ + 1 - saddleU γ = 0 := by linarith
    have hzero' : saddleS γ - 1 - γ * saddleU γ = 0 := by linarith
    rw [hzero, hzero']
    ring
  · rw [(G.derivative U hU he).deriv]
    have hden : U * (G.σ U + 1 - U) ≠ 0 := by
      apply mul_ne_zero (ne_of_gt hU)
      rcases lt_or_gt_of_ne he with hlo | hhi
      · exact ne_of_gt (by linarith [(G.lower U ⟨hU, hlo⟩).2.2])
      · exact ne_of_lt (by linarith [(G.upper U hhi).2.2])
    exact div_mul_cancel₀ _ hden

/-- The signed difference from the separating graph preserves its sign
on every actual positive-state orbit segment. -/
theorem orbit_difference_factor (hγ : 0 < γ) (hγ₁ : γ < 1)
    {T : ℝ} (hT : 0 ≤ T) {α : ℝ → ℝ × ℝ}
    (hα : IsSolutionOn γ α (Icc 0 T))
    (hU : ∀ t ∈ Icc (0 : ℝ) T, 0 < (α t).2) :
    ∃ k > 0, (α T).1 - G.σ ((α T).2) =
      ((α 0).1 - G.σ ((α 0).2)) * k := by
  have hαC := HasDerivAt.continuousOn hα
  have hGC : ContinuousOn (fun t ↦ G.σ ((α t).2)) (Icc (0 : ℝ) T) :=
    (G.continuousOn hγ₁).comp hαC.snd hU
  have hG₁ : ContDiffOn ℝ 1 G.σ (Ioi 0) :=
    fun U hU ↦ (G.contDiffAt_one hγ hγ₁ hU).contDiffWithinAt
  have hRC : ContinuousOn (fun t ↦ deriv G.σ ((α t).2)) (Icc (0 : ℝ) T) :=
    (hG₁.continuousOn_deriv_of_isOpen isOpen_Ioi le_rfl).comp hαC.snd hU
  let a : ℝ → ℝ := fun t ↦
    2 * ((α t).1 + G.σ ((α t).2) - 1 - γ * (α t).2) -
      (α t).2 * deriv G.σ ((α t).2)
  have haC : ContinuousOn a (Icc (0 : ℝ) T) := by dsimp [a]; fun_prop
  apply scalar_linear_endpoint_factor hT haC
  intro t ht
  have hdS : HasDerivAt (fun t ↦ (α t).1)
      (2 * (α t).1 * ((α t).1 - 1 - γ * (α t).2)) t := by
    convert! (hasFDerivAt_fst (𝕜 := ℝ) (p := α t)).comp_hasDerivAt t (hα t ht) using 1
  have hdU : HasDerivAt (fun t ↦ (α t).2)
      ((α t).2 * ((α t).1 + 1 - (α t).2)) t := by
    convert! (hasFDerivAt_snd (𝕜 := ℝ) (p := α t)).comp_hasDerivAt t (hα t ht) using 1
  have hGd := ((G.contDiffAt_one hγ hγ₁ (hU t ht)).differentiableAt (by norm_num)).hasDerivAt
  have hh := hdS.sub (hGd.comp t hdU)
  have heq := G.graph_equation_all hγ₁ (hU t ht)
  convert hh using 1
  · rfl
  · dsimp [a]
    nlinarith only [heq]

end SubcriticalGraph

/-- The initial point below the separator exits through the diagonal edge;
the initial point above it exits through the horizontal saddle-height edge. -/
theorem exists_lower_classified_exit {γ s₀ : ℝ} (hγ : 0 < γ) (hγ₁ : γ < 1)
    (G : SubcriticalGraph γ) (hs₀ : s₀ ∈ Ioo (0 : ℝ) (saddleS γ))
    (hne : s₀ ≠ G.σ 1) :
    ∃ α : ℝ → ℝ × ℝ, α 0 = (s₀, 1) ∧ ∃ T > 0,
      IsSolutionOn γ α (Icc 0 T) ∧
      (∀ t ∈ Ico 0 T, 0 < (α t).1 ∧ (α t).1 < saddleS γ ∧
        0 < (α t).2 ∧ (α t).2 < (α t).1 + 1) ∧
      0 < (α T).1 ∧ 0 < (α T).2 ∧
      (s₀ < G.σ 1 → (α T).2 = (α T).1 + 1) ∧
      (G.σ 1 < s₀ → (α T).1 = saddleS γ) := by
  obtain ⟨α, hα₀, T, hT, hα, hbefore, hsT, hUT, hedge⟩ :=
    exists_lower_stopped_exit hγ hγ₁ G hs₀ hne
  have hp (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) : 0 < (α t).2 := by
    rcases lt_or_eq_of_le ht.2 with hlt | heq
    · exact (hbefore t ⟨ht.1, hlt⟩).2.2.1
    · simpa only [heq] using hUT
  obtain ⟨k, hk, hdiff⟩ := G.orbit_difference_factor hγ hγ₁ hT.le hα hp
  rw [hα₀] at hdiff
  have hsbound : (α T).1 ≤ saddleS γ := by
    apply le_of_tendsto ((hα T ⟨hT.le, le_rfl⟩).continuousAt.fst.tendsto.mono_left
      (show 𝓝[<] T ≤ 𝓝 T from nhdsWithin_le_nhds))
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (Ioi_mem_nhds hT)] with t ht ht₀
    exact (hbefore t ⟨ht₀.le, ht⟩).2.1.le
  have hUbound : (α T).2 ≤ (α T).1 + 1 := by
    have hCT : ContinuousAt (fun t ↦ (α t).1 + 1 - (α t).2) T :=
      ((hα T ⟨hT.le, le_rfl⟩).continuousAt.fst.add continuousAt_const).sub
        (hα T ⟨hT.le, le_rfl⟩).continuousAt.snd
    have hh : 0 ≤ (α T).1 + 1 - (α T).2 := by
      apply ge_of_tendsto (hCT.tendsto.mono_left
        (show 𝓝[<] T ≤ 𝓝 T from nhdsWithin_le_nhds))
      filter_upwards [self_mem_nhdsWithin,
        nhdsWithin_le_nhds (Ioi_mem_nhds hT)] with t ht ht₀
      linarith [(hbefore t ⟨ht₀.le, ht⟩).2.2.2]
    linarith
  have hUB : (α T).2 ≤ saddleU γ := by
    have hAB := saddleU_eq_saddleS_add_one (ne_of_lt hγ₁)
    linarith
  have hGhi : G.σ ((α T).2) ≤ saddleS γ := by
    rcases lt_or_eq_of_le hUB with hlo | heq
    · exact (G.lower _ ⟨hUT, hlo⟩).2.1.le
    · rw [heq, G.saddle]
  have hGlo : (α T).2 - 1 ≤ G.σ ((α T).2) := by
    rcases lt_or_eq_of_le hUB with hlo | heq
    · exact (G.lower _ ⟨hUT, hlo⟩).2.2.le
    · rw [heq, G.saddle]
      have hAB := saddleU_eq_saddleS_add_one (ne_of_lt hγ₁)
      linarith
  refine ⟨α, hα₀, T, hT, hα, hbefore, hsT, hUT, ?_, ?_⟩
  · intro hbelow
    rcases hedge with htop | hdiag
    · have hnegative : (s₀ - G.σ 1) * k < 0 := mul_neg_of_neg_of_pos (sub_neg.mpr hbelow) hk
      rw [htop] at hdiff
      linarith
    · exact hdiag
  · intro habove
    rcases hedge with htop | hdiag
    · exact htop
    · have hpositive : 0 < (s₀ - G.σ 1) * k := mul_pos (sub_pos.mpr habove) hk
      linarith

end
end krylov.LotkaVolterra
