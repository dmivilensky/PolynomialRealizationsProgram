import krylov.LotkaVolterra.ExitComparison
import krylov.LotkaVolterra.GlobalSubcriticalGraph

/-!
Article: main_krylov, apC:prop:LV, bounded nonexit trajectories.
Use: an actual orbit that remains in the lower region eventually lies on the
constructed stable graph. The proof uses monotonicity, a polynomial chord
equation and quantitative scalar expansion, without an omega-limit theorem.
Source: the exact LV/chord equations and bounded expanding uniqueness.
-/

namespace krylov.LotkaVolterra
noncomputable section
open Set

theorem lower_nonexit_eventually_on_graph {γ : ℝ} (hγ : 0 < γ) (hγ₁ : γ < 1)
    (G : SubcriticalGraph γ) {s U : ℝ → ℝ} (hU₀ : U 0 = 1)
    (hreg : ∀ t ≥ 0, 0 < s t ∧ s t < saddleS γ ∧ 1 ≤ U t ∧ U t < s t + 1)
    (hds : ∀ t ≥ 0, HasDerivAt s (2 * s t * (s t - 1 - γ * U t)) t)
    (hdU : ∀ t ≥ 0, HasDerivAt U (U t * (s t + 1 - U t)) t) :
    ∀ t ≥ 1, s t = G.σ (U t) := by
  have hB := saddleU_eq_saddleS_add_one (ne_of_lt hγ₁)
  have hUrange (t : ℝ) (ht : 0 ≤ t) : U t ∈ Ioo (0 : ℝ) (saddleU γ) := by
    have hh := hreg t ht
    exact ⟨by linarith [hh.2.2.1], by linarith [hh.2.1, hh.2.2.2]⟩
  have hUm : StrictMonoOn U (Ici 0) := by
    apply strictMonoOn_of_deriv_pos (convex_Ici 0)
      (HasDerivAt.continuousOn fun t ht ↦ hdU t ht)
    intro t ht
    have ht₀ : 0 ≤ t := interior_subset ht
    rw [(hdU t ht₀).deriv]
    exact mul_pos (hUrange t ht₀).1 (by linarith [(hreg t ht₀).2.2.2])
  have hU₁ : 1 < U 1 := by
    simpa only [hU₀] using hUm (a := (0 : ℝ)) (b := (1 : ℝ))
      (by norm_num) (by norm_num) (by norm_num)
  let v : ℝ → ℝ := fun t ↦ chordSlope γ (s t) (U t)
  let w : ℝ → ℝ := fun t ↦ chordSlope γ (G.σ (U t)) (U t)
  have hv (t : ℝ) (ht : 0 ≤ t) : v t ∈ Ioo (0 : ℝ) 1 :=
    chordSlope_mem hγ₁ (hreg t ht).2.1 (hreg t ht).2.2.2
  have hw (t : ℝ) (ht : 0 ≤ t) : w t ∈ Ioo (0 : ℝ) γ := by
    have hg := G.lower (U t) (hUrange t ht)
    have hz := sub_pos.mpr (hUrange t ht).2
    have hA := saddleS_eq_one_add_mul_saddleU (ne_of_lt hγ₁)
    refine ⟨div_pos (by linarith [hg.2.1]) hz, ?_⟩
    apply (div_lt_iff₀ hz).mpr
    rw [hA]
    linarith [hg.1]
  have hvd (t : ℝ) (ht : 0 ≤ t) : HasDerivAt v
      (2 * s t * (v t - γ) + v t * U t * (1 - v t)) t :=
    hasDerivAt_chordSlope hγ₁ (sub_pos.mpr (hUrange t ht).2).ne' (hds t ht) (hdU t ht)
  have hvγ : ∀ t ≥ 1, v t ≤ γ := by
    apply nonescaping_chord_le_gamma (γ := γ) (T := 1) (δ := U 1 - 1)
      (s := s) (U := U) (v := v) (sub_pos.mpr hU₁) _ (fun t ht ↦ hvd t (by linarith))
    intro t ht
    have hUmono : U 1 ≤ U t := hUm.monotoneOn (a := (1 : ℝ)) (b := t)
      (by norm_num) (by change 0 ≤ t; linarith) ht
    have hv' := hv t (by linarith)
    exact ⟨hv'.1, hv'.2, by linarith [(hreg t (by linarith)).2.2.2],
      (hUrange t (by linarith)).1.le⟩
  have hUrate (t : ℝ) (ht : 0 ≤ t) :
      s t + 1 - U t = (saddleU γ - U t) * (1 - v t) := by
    have hden := (sub_pos.mpr (hUrange t ht).2).ne'
    dsimp [v, chordSlope]
    field_simp
    rw [hB]
    ring
  have hwd (t : ℝ) (ht : 0 ≤ t) : HasDerivAt w
      (-U t * (1 - v t) * saddleSlopeRate γ (saddleU γ - U t) (w t)) t := by
    have hd := (hasDerivAt_graph_chord hγ₁ (hUrange t ht).1.ne'
      (sub_pos.mpr (hUrange t ht).2).ne' (by linarith [(hw t ht).2])
      (G.derivative _ (hUrange t ht).1 (ne_of_lt (hUrange t ht).2))).comp t (hdU t ht)
    convert hd using 1
    · rfl
    · change -U t * (1 - v t) * saddleSlopeRate γ (saddleU γ - U t) (w t) =
        (-saddleSlopeRate γ (saddleU γ - U t) (w t) / (saddleU γ - U t)) *
          (U t * (s t + 1 - U t))
      rw [hUrate t ht]
      field_simp [(sub_pos.mpr (hUrange t ht).2).ne']
  have hvd' (t : ℝ) (ht : 0 ≤ t) : HasDerivAt v
      (-U t * (1 - v t) * saddleSlopeRate γ (saddleU γ - U t) (v t)) t := by
    have he := physical_chord_rate_eq (hUrange t ht).1.ne'
      (sub_pos.mpr (hUrange t ht).2).ne' (by change 1 - v t ≠ 0; linarith [(hv t ht).2])
    rw [← he]
    exact hvd t ht
  have hvshift : ∀ t ≥ 0, v (t + 1) ∈ Icc 0 γ ∧ HasDerivAt (fun t ↦ v (t + 1))
      (-U (t + 1) * (1 - v (t + 1)) * saddleSlopeRate γ (saddleU γ - U (t + 1)) (v (t + 1))) t := by
    intro t ht
    refine ⟨⟨(hv (t + 1) (by linarith)).1.le, hvγ (t + 1) (by linarith)⟩, ?_⟩
    convert! (hvd' (t + 1) (by linarith)).comp t ((hasDerivAt_id t).add_const 1) using 1
    ring
  have hwshift : ∀ t ≥ 0, w (t + 1) ∈ Icc 0 γ ∧ HasDerivAt (fun t ↦ w (t + 1))
      (-U (t + 1) * (1 - v (t + 1)) * saddleSlopeRate γ (saddleU γ - U (t + 1)) (w (t + 1))) t := by
    intro t ht
    refine ⟨⟨(hw (t + 1) (by linarith)).1.le, (hw (t + 1) (by linarith)).2.le⟩, ?_⟩
    convert! (hwd (t + 1) (by linarith)).comp t ((hasDerivAt_id t).add_const 1) using 1
    ring
  have hshift := bounded_physical_chords_unique (U := fun t ↦ U (t + 1))
    (z := fun t ↦ saddleU γ - U (t + 1))
    (v := fun t ↦ v (t + 1)) (w := fun t ↦ w (t + 1)) hγ₁
    (show 0 < U 1 by linarith) (fun t ht ↦ hUm.monotoneOn (a := (1 : ℝ)) (b := t + 1)
      (by norm_num) (by change 0 ≤ t + 1; linarith) (by linarith))
    (fun t ht ↦ by
      have hh := hUrange (t + 1) (by linarith)
      exact ⟨by linarith [hh.2], by linarith [(hreg (t + 1) (by linarith)).2.2.1]⟩)
    hvshift hwshift
  intro t ht
  have hh := hshift (x := t - 1) (by change 0 ≤ t - 1; linarith)
  simp only [sub_add_cancel] at hh
  dsimp [v, w, chordSlope] at hh
  have hn := (sub_pos.mpr (hUrange t (by linarith)).2).ne'
  have he := (div_left_inj' hn).mp hh
  linarith

end
end krylov.LotkaVolterra
