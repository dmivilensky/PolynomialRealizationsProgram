import krylov.Strings.OptimizerFiniteState

/-!
Article: main_krylov, s3:def:string, type clock for finite physical lengths.
Use: construct one actual type clock on `[0,ℓ)` from the Radon–Nikodym densities
of its compact representatives. Almost-everywhere RN locality is proved before
the clocks are glued; no pointwise identification of chosen densities is used.
Source: `Mass.typeClock_eq_of_restrict_eq`, interval integration and absolute
continuity of the actual integral clocks.
-/

namespace krylov.Strings.OptimizerFinite
noncomputable section
open Set Filter MeasureTheory
open scoped Topology NNReal

/-- Actual compact type clocks agree everywhere on their overlap, although
the chosen Radon–Nikodym densities need agree only almost everywhere. -/
theorem clock_compatible {ℓ : ℝ} (hℓ : 0 < ℓ)
    (f : StieltjesFunction (Ico (0 : ℝ) ℓ)) (h₀ : f ⟨0, ⟨le_rfl, hℓ⟩⟩ = 1)
    (w v : Windows ℓ) {x : ℝ} (hx₀ : 0 ≤ x)
    (hxw : x ≤ (w.val : ℝ)) (hxv : x ≤ (v.val : ℝ)) :
    (windowMass hℓ f h₀ w).typeClock x = (windowMass hℓ f h₀ v).typeClock x := by
  apply Mass.typeClock_eq_of_restrict_eq _ _ (windowMass_compatible hℓ f h₀ w v) hx₀
  simpa using le_min hxw hxv

/-- The actual type clock of any compact representative is monotone on the
physical half-line, by nonnegativity of its measured type density. -/
theorem compactClock_monotone (M : Mass) : MonotoneOn M.typeClock (Ici 0) := by
  intro x hx y hy hxy
  rw [M.typeClock_eq_integral hx, M.typeClock_eq_integral hy]
  apply setIntegral_mono_set (M.typeDensity_integrableOn 0 y)
  · exact Eventually.of_forall M.typeDensity_nonneg
  · exact Eventually.of_forall (fun _ ht ↦ ⟨ht.1, ht.2.trans hxy⟩)

/-- The finite-endpoint source has one type clock, normalized and monotone,
continuous on its whole physical domain and absolutely continuous on every
compact subwindow. Its value on each subwindow is exactly the integral of
that representative's genuine square-root RN density. Endpoint divergence,
arbitrarily many atoms and singular continuous mass are permitted.
-/
theorem exists_clock {ℓ : ℝ} (hℓ : 0 < ℓ)
    (f : StieltjesFunction (Ico (0 : ℝ) ℓ)) (h₀ : f ⟨0, ⟨le_rfl, hℓ⟩⟩ = 1) :
    ∃ y : ℝ → ℝ, ContinuousOn y (Ico 0 ℓ) ∧ y 0 = 0 ∧ MonotoneOn y (Ico 0 ℓ) ∧
      (∀ w : Windows ℓ, EqOn y (windowMass hℓ f h₀ w).typeClock (Icc 0 (w.val : ℝ))) ∧
      ∀ w : Windows ℓ, AbsolutelyContinuousOnInterval y 0 (w.val : ℝ) := by
  let windowAt (x : ℝ) (hx : x < ℓ) : Windows ℓ :=
    ⟨⟨(max x 0 + ℓ) / 2, by linarith [le_max_right x 0]⟩,
      by
        change (max x 0 + ℓ) / 2 < ℓ
        have hmax : max x 0 < ℓ := max_lt hx hℓ
        linarith⟩
  let y : ℝ → ℝ := fun x ↦ if hx : x ∈ Ico 0 ℓ then
    (windowMass hℓ f h₀ (windowAt x hx.2)).typeClock x else 0
  have hbound (x : ℝ) (hx : x < ℓ) : x < ((windowAt x hx).val : ℝ) := by
    change x < (max x 0 + ℓ) / 2
    linarith [le_max_left x 0]
  have hagree (w : Windows ℓ) : EqOn y (windowMass hℓ f h₀ w).typeClock
      (Icc 0 (w.val : ℝ)) := by
    intro x hx
    have hxℓ : x ∈ Ico 0 ℓ := ⟨hx.1, hx.2.trans_lt w.property⟩
    dsimp [y]
    rw [dite_eq_left hxℓ]
    exact clock_compatible hℓ f h₀ (windowAt x hxℓ.2) w hx.1 (hbound x hxℓ.2).le hx.2
  have hac (w : Windows ℓ) : AbsolutelyContinuousOnInterval y 0 (w.val : ℝ) := by
    apply ((windowMass hℓ f h₀ w).typeClock_absolutelyContinuousOnInterval w.val.property).congr
    intro x hx
    have hL : (0 : ℝ) ≤ (w.val : ℝ) := w.val.property
    have hx' : x ∈ Icc 0 (w.val : ℝ) := by
      rcases mem_uIcc.mp hx with hx | hx
      · exact hx
      · exact ⟨hL.trans hx.1, hx.2.trans hL⟩
    exact (hagree w hx').symm
  have hcont : ContinuousOn y (Ico 0 ℓ) := by
    intro x hx
    let w := windowAt x hx.2
    have hL : (0 : ℝ) ≤ (w.val : ℝ) := w.val.property
    have hc : ContinuousOn y (Icc 0 (w.val : ℝ)) := by
      simpa only [uIcc_of_le hL] using (hac w).continuousOn
    apply (hc x ⟨hx.1, (hbound x hx.2).le⟩).mono_of_mem_nhdsWithin
    have ht : ∀ᶠ t in 𝓝[Ico 0 ℓ] x, t < (w.val : ℝ) :=
      (eventually_lt_nhds (hbound x hx.2)).filter_mono nhdsWithin_le_nhds
    filter_upwards [self_mem_nhdsWithin, ht] with t hts htw
    exact ⟨hts.1, htw.le⟩
  have hz : y 0 = 0 := by
    rw [hagree (windowAt 0 hℓ) ⟨le_rfl, (hbound 0 hℓ).le⟩, Mass.typeClock_zero]
  have hm : MonotoneOn y (Ico 0 ℓ) := by
    intro a ha b hb hab
    let w := windowAt b hb.2
    rw [hagree w ⟨ha.1, hab.trans (hbound b hb.2).le⟩,
      hagree w ⟨hb.1, (hbound b hb.2).le⟩]
    exact compactClock_monotone _ ha.1 hb.1 hab
  exact ⟨y, hcont, hz, hm, hagree, hac⟩

/-- Clock gluing is unique on the complete physical domain. -/
theorem clock_unique {ℓ : ℝ} (hℓ : 0 < ℓ)
    (f : StieltjesFunction (Ico (0 : ℝ) ℓ)) (h₀ : f ⟨0, ⟨le_rfl, hℓ⟩⟩ = 1)
    {y z : ℝ → ℝ}
    (hy : ∀ w : Windows ℓ, EqOn y (windowMass hℓ f h₀ w).typeClock (Icc 0 (w.val : ℝ)))
    (hz : ∀ w : Windows ℓ, EqOn z (windowMass hℓ f h₀ w).typeClock (Icc 0 (w.val : ℝ))) :
    EqOn y z (Ico 0 ℓ) := by
  intro x hx
  let w : Windows ℓ := ⟨⟨x, hx.1⟩, hx.2⟩
  have hxw : x ∈ Icc 0 (w.val : ℝ) := ⟨hx.1, le_rfl⟩
  exact (hy w hxw).trans (hz w hxw).symm

end
end krylov.Strings.OptimizerFinite
