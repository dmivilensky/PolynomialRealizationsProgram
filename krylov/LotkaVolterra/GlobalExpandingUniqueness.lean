import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic

/-!
Uniqueness of a bounded scalar trajectory for a uniformly expanding field.
This short comparison argument is used for the constructed saddle slopes.
Source: differentiate squared separation and apply the mean-value theorem.
-/
namespace krylov.LotkaVolterra
noncomputable section
open Set

theorem bounded_expanding_solution_unique {F : ℝ → ℝ → ℝ} {a b c : ℝ}
    (hc : 0 < c)
    (hF : ∀ t ≥ 0, ∀ x ∈ Icc a b, ∀ y ∈ Icc a b,
      c * (x - y) ^ 2 ≤ (x - y) * (F t x - F t y))
    {e f : ℝ → ℝ}
    (he : ∀ t ≥ 0, e t ∈ Icc a b ∧ HasDerivAt e (F t (e t)) t)
    (hf : ∀ t ≥ 0, f t ∈ Icc a b ∧ HasDerivAt f (F t (f t)) t) :
    EqOn e f (Ici 0) := by
  let D : ℝ → ℝ := fun t ↦ (e t - f t) ^ 2
  let M : ℝ := (b - a) ^ 2
  have hd (t : ℝ) (ht : 0 ≤ t) :
      HasDerivAt D (2 * (e t - f t) * (F t (e t) - F t (f t))) t := by
    convert ((he t ht).2.sub (hf t ht).2).pow 2 using 1
    simp only [Pi.sub_apply, show (2 - 1 : ℕ) = 1 by decide, pow_one, Nat.cast_ofNat]
  have hgrow (t : ℝ) (ht : 0 ≤ t) : 2 * c * D t ≤ deriv D t := by
    rw [(hd t ht).deriv]
    have hh := hF t ht (e t) (he t ht).1 (f t) (hf t ht).1
    dsimp [D]
    nlinarith
  have hmono : MonotoneOn D (Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
      (HasDerivAt.continuousOn fun t ht ↦ hd t ht)
      (fun t ht ↦ (hd t (interior_subset ht)).differentiableAt.differentiableWithinAt)
    intro t ht
    have hh := hgrow t (interior_subset ht)
    exact (mul_nonneg (by linarith : 0 ≤ 2 * c) (sq_nonneg _)).trans hh
  have hbound (t : ℝ) (ht : 0 ≤ t) : D t ≤ M := by
    have h₁ := (he t ht).1
    have h₂ := (hf t ht).1
    have hh := mul_nonneg (show 0 ≤ (b - a) - (e t - f t) by linarith [h₁.2, h₂.1])
      (show 0 ≤ (b - a) + (e t - f t) by linarith [h₁.1, h₂.2])
    dsimp [D, M]
    nlinarith
  intro t ht
  by_contra hne
  have hDpos : 0 < D t := sq_pos_of_ne_zero (sub_ne_zero.mpr hne)
  have hden : 0 < 2 * c * D t := by positivity
  have hM : 0 < M + 1 := by dsimp [M]; positivity
  let T : ℝ := t + (M + 1) / (2 * c * D t)
  have htT : t < T := lt_add_of_pos_right _ (div_pos hM hden)
  have hT : 0 ≤ T := ht.trans htT.le
  have hlinear : (2 * c * D t) * (T - t) ≤ D T - D t := by
    apply (convex_Ici t).mul_sub_le_image_sub_of_le_deriv
      (HasDerivAt.continuousOn fun u hu ↦ hd u (ht.trans hu))
      (fun u hu ↦ (hd u (ht.trans (interior_subset hu))).differentiableAt.differentiableWithinAt)
      (fun u hu ↦ (mul_le_mul_of_nonneg_left
        (hmono ht (ht.trans (interior_subset hu)) (interior_subset hu))
        (by linarith : 0 ≤ 2 * c)).trans (hgrow u (ht.trans (interior_subset hu))))
      t (mem_Ici.mpr le_rfl) T (mem_Ici.mpr htT.le) htT.le
  have hid : (2 * c * D t) * (T - t) = M + 1 := by
    dsimp [T]
    field_simp
    ring
  rw [hid] at hlinear
  linarith [hbound T hT]

end
end krylov.LotkaVolterra
