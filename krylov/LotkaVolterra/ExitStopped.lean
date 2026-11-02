import krylov.LotkaVolterra.ExitFinite
import krylov.LotkaVolterra.GlobalClippedFlow

/-!
Article: `main_krylov`, `apC:prop:LV`, unconditional finite stopped exits.
A complete clipped auxiliary flow constructs the trajectory. If it never
meets either exit edge, it is an actual bounded original trajectory and
hence starts on the separating graph. Off the graph, the first edge contact
therefore occurs at finite time, and the auxiliary and original fields
agree all the way through that time.

Source: compact continuation, first contact, and the already proved actual
nonexit classification. No global existence of the quadratic field is
assumed.
-/
namespace krylov.LotkaVolterra
noncomputable section
open Set Filter
open scoped Topology

/-- A continuous positive function that becomes nonpositive has a first
zero, and remains strictly positive before it. -/
theorem exists_first_zero_of_nonpositive {w : ℝ → ℝ} (hw : Continuous w)
    (h₀ : 0 < w 0) (hex : ∃ t ≥ 0, w t ≤ 0) :
    ∃ T > 0, w T = 0 ∧ ∀ t ∈ Ico (0 : ℝ) T, 0 < w t := by
  obtain ⟨b, hb, hwb⟩ := hex
  let C : Set ℝ := Icc 0 b ∩ {t | w t ≤ 0}
  have hC : IsCompact C := isCompact_Icc.inter_right (isClosed_le hw continuous_const)
  obtain ⟨T, hT⟩ := hC.exists_isLeast ⟨b, ⟨⟨hb, le_rfl⟩, hwb⟩⟩
  have hT₀ : 0 < T := by
    have hTnonneg := hT.1.1.1
    by_contra! hn
    have heq : T = 0 := le_antisymm hn hTnonneg
    have h := hT.1.2
    change w T ≤ 0 at h
    rw [heq] at h
    linarith
  have hbefore (t : ℝ) (ht : t ∈ Ico (0 : ℝ) T) : 0 < w t := by
    by_contra! hn
    have hh := hT.2 (show t ∈ C from ⟨⟨ht.1, ht.2.le.trans hT.1.1.2⟩, hn⟩)
    linarith [ht.2]
  have hTnonneg : 0 ≤ w T := by
    apply ge_of_tendsto (hw.continuousAt.tendsto.mono_left
      (show 𝓝[<] T ≤ 𝓝 T from nhdsWithin_le_nhds))
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (Ioi_mem_nhds hT₀)] with t ht ht₀
    exact (hbefore t ⟨ht₀.le, ht⟩).le
  exact ⟨T, hT₀, le_antisymm hT.1.2 hTnonneg, hbefore⟩

/-- Every initial point in the lower wedge off its unique separating value
has an actual solution through its first finite exit edge. The closed time
interval includes the contact itself. -/
theorem exists_lower_stopped_exit {γ s₀ : ℝ} (hγ : 0 < γ) (hγ₁ : γ < 1)
    (G : SubcriticalGraph γ) (hs₀ : s₀ ∈ Ioo (0 : ℝ) (saddleS γ))
    (hne : s₀ ≠ G.σ 1) :
    ∃ α : ℝ → ℝ × ℝ, α 0 = (s₀, 1) ∧ ∃ T > 0,
      IsSolutionOn γ α (Icc 0 T) ∧
      (∀ t ∈ Ico 0 T, 0 < (α t).1 ∧ (α t).1 < saddleS γ ∧
        0 < (α t).2 ∧ (α t).2 < (α t).1 + 1) ∧
      0 < (α T).1 ∧ 0 < (α T).2 ∧
      ((α T).1 = saddleS γ ∨ (α T).2 = (α T).1 + 1) := by
  have hB := saddleU_pos hγ₁
  have hAB := saddleU_eq_saddleS_add_one (ne_of_lt hγ₁)
  obtain ⟨α, hα₀, hα⟩ := exists_global_clipped_solution γ hB.le (s₀, 1)
  have hp : ∀ t ≥ 0, α t ∈ positiveQuadrant :=
    clipped_solution_positive hB.le hα (by rw [hα₀]; exact ⟨hs₀.1, by norm_num⟩)
  have hαC : Continuous α := continuous_iff_continuousAt.mpr fun t ↦ (hα t).continuousAt
  let w : ℝ → ℝ := fun t ↦ min (saddleS γ - (α t).1) ((α t).1 + 1 - (α t).2)
  have hwC : Continuous w := by dsimp [w]; fun_prop
  have hw₀ : 0 < w 0 := by
    dsimp [w]
    rw [hα₀]
    exact lt_min (sub_pos.mpr hs₀.2) (by simpa using hs₀.1)
  have hex : ∃ t ≥ 0, w t ≤ 0 := by
    by_contra! hno
    have hbounds (t : ℝ) (ht : 0 ≤ t) :
        α t ∈ Icc (0 : ℝ) (saddleU γ) ×ˢ Icc (0 : ℝ) (saddleU γ) := by
      have hm := hno t ht
      have hs : (α t).1 < saddleS γ := by have := (lt_min_iff.mp hm).1; dsimp [w] at *; linarith
      have hU : (α t).2 < (α t).1 + 1 := by have := (lt_min_iff.mp hm).2; dsimp [w] at *; linarith
      exact ⟨⟨(hp t ht).1.le, by linarith⟩, ⟨(hp t ht).2.le, by linarith⟩⟩
    have hd (t : ℝ) (ht : 0 ≤ t) : HasDerivAt α (vectorField γ (α t)) t := by
      simpa only [clippedVectorField_eq (hbounds t ht)] using hα t
    have hds (t : ℝ) (ht : 0 ≤ t) :
        HasDerivAt (fun t ↦ (α t).1) (2 * (α t).1 * ((α t).1 - 1 - γ * (α t).2)) t := by
      convert! (hasFDerivAt_fst (𝕜 := ℝ) (p := α t)).comp_hasDerivAt t (hd t ht) using 1
    have hdU (t : ℝ) (ht : 0 ≤ t) :
        HasDerivAt (fun t ↦ (α t).2) ((α t).2 * ((α t).1 + 1 - (α t).2)) t := by
      convert! (hasFDerivAt_snd (𝕜 := ℝ) (p := α t)).comp_hasDerivAt t (hd t ht) using 1
    obtain ⟨t, ht, he⟩ := lower_finite_exit_of_global_solution hγ hγ₁ G
      (show (α 0).2 = 1 by rw [hα₀]) hp hds hdU (by simpa only [hα₀] using hne)
    have hm := lt_min_iff.mp (hno t ht)
    rcases he with he | he <;> linarith
  obtain ⟨T, hT, hwT, hbefore⟩ := exists_first_zero_of_nonpositive hwC hw₀ hex
  have hclosed (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) : 0 ≤ w t := by
    rcases lt_or_eq_of_le ht.2 with hlt | heq
    · exact (hbefore t ⟨ht.1, hlt⟩).le
    · simp only [heq, hwT, le_refl]
  have hbox (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
      α t ∈ Icc (0 : ℝ) (saddleU γ) ×ˢ Icc (0 : ℝ) (saddleU γ) := by
    have hm := le_min_iff.mp (hclosed t ht)
    exact ⟨⟨(hp t ht.1).1.le, by linarith [hm.1]⟩,
      ⟨(hp t ht.1).2.le, by linarith [hm.1, hm.2]⟩⟩
  refine ⟨α, hα₀, T, hT, ?_, ?_, (hp T hT.le).1, (hp T hT.le).2, ?_⟩
  · intro t ht
    simpa only [clippedVectorField_eq (hbox t ht)] using hα t
  · intro t ht
    have hm := lt_min_iff.mp (hbefore t ht)
    exact ⟨(hp t ht.1).1, by linarith [hm.1], (hp t ht.1).2, by linarith [hm.2]⟩
  · dsimp [w] at hwT
    rcases le_total (saddleS γ - (α T).1) ((α T).1 + 1 - (α T).2) with hh | hh
    · rw [min_eq_left hh] at hwT
      exact Or.inl (by linarith)
    · rw [min_eq_right hh] at hwT
      exact Or.inr (by linarith)

end
end krylov.LotkaVolterra
