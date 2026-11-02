import krylov.LotkaVolterra.ExitNonexit
import krylov.LotkaVolterra.PositiveOrbits

/-!
Article: `main_krylov`, `apC:prop:LV`, initial-value classification of
bounded nonexit trajectories.

The eventual graph identity from `ExitNonexit` is propagated backward by
the exact linear equation for `s(t)-σ(U(t))`. Continuity then includes the
initial endpoint. No backwards global existence hypothesis is introduced.
-/
namespace krylov.LotkaVolterra
noncomputable section
open Set Filter
open scoped Topology

theorem lower_nonexit_initial_on_graph {γ : ℝ} (hγ : 0 < γ) (hγ₁ : γ < 1)
    (G : SubcriticalGraph γ) {s U : ℝ → ℝ} (hU₀ : U 0 = 1)
    (hreg : ∀ t ≥ 0, 0 < s t ∧ s t < saddleS γ ∧ 1 ≤ U t ∧ U t < s t + 1)
    (hds : ∀ t ≥ 0, HasDerivAt s (2 * s t * (s t - 1 - γ * U t)) t)
    (hdU : ∀ t ≥ 0, HasDerivAt U (U t * (s t + 1 - U t)) t) :
    s 0 = G.σ 1 := by
  have heventual := lower_nonexit_eventually_on_graph hγ hγ₁ G hU₀ hreg hds hdU
  have hB := saddleU_eq_saddleS_add_one (ne_of_lt hγ₁)
  have hUr (t : ℝ) (ht : 0 ≤ t) : U t ∈ Ioo (0 : ℝ) (saddleU γ) := by
    have hh := hreg t ht
    exact ⟨by linarith [hh.2.2.1], by linarith [hh.2.1, hh.2.2.2]⟩
  let R : ℝ → ℝ := fun t ↦
    2 * G.σ (U t) * (G.σ (U t) - 1 - γ * U t) / (U t * (G.σ (U t) + 1 - U t))
  let d : ℝ → ℝ := fun t ↦ s t - G.σ (U t)
  let a : ℝ → ℝ := fun t ↦ 2 * (s t + G.σ (U t) - 1 - γ * U t) - U t * R t
  have hsC : ContinuousOn s (Ioo (0 : ℝ) 2) :=
    HasDerivAt.continuousOn fun t ht ↦ hds t ht.1.le
  have hUC : ContinuousOn U (Ioo (0 : ℝ) 2) :=
    HasDerivAt.continuousOn fun t ht ↦ hdU t ht.1.le
  have hGC : ContinuousOn (fun t ↦ G.σ (U t)) (Ioo (0 : ℝ) 2) :=
    (G.continuousOn hγ₁).comp hUC (fun t ht ↦ (hUr t ht.1.le).1)
  have hden (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 2) : U t * (G.σ (U t) + 1 - U t) ≠ 0 := by
    exact mul_ne_zero (ne_of_gt (hUr t ht.1.le).1)
      (ne_of_gt (by linarith [(G.lower (U t) (hUr t ht.1.le)).2.2]))
  have hRC : ContinuousOn R (Ioo (0 : ℝ) 2) :=
    ((hGC.const_mul 2).mul ((hGC.sub continuousOn_const).sub (hUC.const_mul γ))).div
      (hUC.mul ((hGC.add continuousOn_const).sub hUC)) hden
  have haC : ContinuousOn a (Ioo (0 : ℝ) 2) :=
    (((hsC.add hGC).sub continuousOn_const).sub (hUC.const_mul γ)).const_mul 2 |>.sub (hUC.mul hRC)
  have hd (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 2) : HasDerivAt d (a t * d t) t := by
    have hG := G.derivative (U t) (hUr t ht.1.le).1 (ne_of_lt (hUr t ht.1.le).2)
    have hh := (hds t ht.1.le).sub (hG.comp t (hdU t ht.1.le))
    have hmul : R t * (U t * (G.σ (U t) + 1 - U t)) =
        2 * G.σ (U t) * (G.σ (U t) - 1 - γ * U t) := div_mul_cancel₀ _ (hden t ht)
    convert hh using 1
    · rfl
    · change (2 * (s t + G.σ (U t) - 1 - γ * U t) - U t * R t) *
          (s t - G.σ (U t)) =
        2 * s t * (s t - 1 - γ * U t) - R t * (U t * (s t + 1 - U t))
      nlinarith only [hmul]
  have hd₁ : d 1 = 0 := sub_eq_zero.mpr (heventual 1 le_rfl)
  have hformula := scalar_linear_exp_formula (f := d) (a := a)
    (show (1 : ℝ) ∈ Ioo (0 : ℝ) 2 by norm_num) haC hd
  have hdZero (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 2) : d t = 0 := by
    rw [hformula t ht, hd₁, zero_mul]
  have hdC₀ : ContinuousAt d 0 := by
    have hUr₀ := hUr 0 le_rfl
    exact (hds 0 le_rfl).continuousAt.sub
      ((G.derivative _ hUr₀.1 (ne_of_lt hUr₀.2)).continuousAt.comp (hdU 0 le_rfl).continuousAt)
  have hzero : Tendsto d (𝓝[>] 0) (𝓝 (0 : ℝ)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (Iio_mem_nhds (by norm_num : (0 : ℝ) < 2))] with t ht ht₂
    exact (hdZero t ⟨ht, ht₂⟩).symm
  have hd₀ : d 0 = 0 := tendsto_nhds_unique
    (hdC₀.tendsto.mono_left nhdsWithin_le_nhds) hzero
  exact sub_eq_zero.mp (by simpa only [d, hU₀] using hd₀)

end
end krylov.LotkaVolterra
