import krylov.LotkaVolterra.GlobalGraphChord
import krylov.LotkaVolterra.GlobalSaddleChord

/-!
Uniqueness of bounded actual chord graphs, without assuming a limiting
value at the singular point. Exponential pullback converts each chord into
the actual bounded slope equation already proved unique in `GlobalSaddleLimit`.
-/
namespace krylov.LotkaVolterra
noncomputable section
open Set

theorem chord_exponential_pullback {γ ε : ℝ} {w : ℝ → ℝ}
    (hε : |ε| ≤ 1) (hε₀ : ε ≠ 0)
    (hstrip : ∀ u ∈ Icc (-1 : ℝ) 1, u ≠ 0 → w u ∈ Icc 0 γ)
    (hder : ∀ u ∈ Icc (-1 : ℝ) 1, u ≠ 0 →
      HasDerivAt w (saddleSlopeRate γ ((saddleU γ / 2) * u) (w u) / u) u) :
    ∀ t ≥ 0, w (ε * Real.exp (-t)) ∈ Icc 0 γ ∧
      HasDerivAt (fun t ↦ w (ε * Real.exp (-t)))
        (-saddleSlopeRate γ (ε * (saddleU γ / 2) * Real.exp (-t)) (w (ε * Real.exp (-t)))) t := by
  intro t ht
  have hE : Real.exp (-t) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hu : ε * Real.exp (-t) ∈ Icc (-1 : ℝ) 1 := by
    apply abs_le.mp
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    exact (mul_le_mul_of_nonneg_right hε (Real.exp_pos _).le).trans (by simpa using hE)
  have hu₀ : ε * Real.exp (-t) ≠ 0 := mul_ne_zero hε₀ (ne_of_gt (Real.exp_pos _))
  refine ⟨hstrip _ hu hu₀, ?_⟩
  have hdU : HasDerivAt (fun t ↦ ε * Real.exp (-t)) (-(ε * Real.exp (-t))) t := by
    simpa using ((hasDerivAt_id t).neg.exp.const_mul ε)
  have hh := (hder _ hu hu₀).comp t hdU
  have harg : (saddleU γ / 2) * (ε * Real.exp (-t)) = ε * (saddleU γ / 2) * Real.exp (-t) := by ring
  rw [harg] at hh
  have hid : saddleSlopeRate γ (ε * (saddleU γ / 2) * Real.exp (-t)) (w (ε * Real.exp (-t))) /
      (ε * Real.exp (-t)) * -(ε * Real.exp (-t)) =
      -saddleSlopeRate γ (ε * (saddleU γ / 2) * Real.exp (-t)) (w (ε * Real.exp (-t))) := by
    field_simp
  rw [hid] at hh
  exact hh

theorem bounded_saddle_chord_unique {γ : ℝ} (hγ : 0 < γ) (hγ₁ : γ < 1)
    {w₁ w₂ : ℝ → ℝ}
    (hs₁ : ∀ u ∈ Icc (-1 : ℝ) 1, u ≠ 0 → w₁ u ∈ Icc 0 γ)
    (hs₂ : ∀ u ∈ Icc (-1 : ℝ) 1, u ≠ 0 → w₂ u ∈ Icc 0 γ)
    (hd₁ : ∀ u ∈ Icc (-1 : ℝ) 1, u ≠ 0 →
      HasDerivAt w₁ (saddleSlopeRate γ ((saddleU γ / 2) * u) (w₁ u) / u) u)
    (hd₂ : ∀ u ∈ Icc (-1 : ℝ) 1, u ≠ 0 →
      HasDerivAt w₂ (saddleSlopeRate γ ((saddleU γ / 2) * u) (w₂ u) / u) u) :
    ∀ u ∈ Icc (-1 : ℝ) 1, u ≠ 0 → w₁ u = w₂ u := by
  intro u hu hu₀
  have ht := neg_log_nonneg_of_abs_le_one hu₀ (abs_le.mpr hu)
  rcases lt_or_gt_of_ne hu₀ with hun | hup
  · have hε : |(-1 : ℝ)| ≤ 1 := by norm_num
    have hε₀ : (-1 : ℝ) ≠ 0 := by norm_num
    have huniq := bounded_saddle_slope_unique hγ hγ₁ hε
      (chord_exponential_pullback hε hε₀ hs₁ hd₁)
      (chord_exponential_pullback hε hε₀ hs₂ hd₂)
    have hh := huniq ht
    simpa only [neg_neg, Real.exp_log_eq_abs hu₀, abs_of_neg hun, neg_mul, one_mul, neg_neg] using hh
  · have hε : |(1 : ℝ)| ≤ 1 := by norm_num
    have hε₀ : (1 : ℝ) ≠ 0 := by norm_num
    have huniq := bounded_saddle_slope_unique hγ hγ₁ hε
      (chord_exponential_pullback hε hε₀ hs₁ hd₁)
      (chord_exponential_pullback hε hε₀ hs₂ hd₂)
    have hh := huniq ht
    simpa only [neg_neg, Real.exp_log_eq_abs hu₀, abs_of_pos hup, one_mul] using hh

end
end krylov.LotkaVolterra
