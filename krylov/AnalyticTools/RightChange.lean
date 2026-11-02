import krylov.AnalyticTools.ScalarFunctions

/-!
Article: main_krylov, thm:value, analyticity at the initial physical endpoint.
Use: transfer an analytic right germ through an actual positive clock whose
right inverse is known. Only the analytic extension of the clock is inverted;
the actual clock and density may have arbitrary values at negative times.
Source: analytic scalar inversion and equality of germs within a half-line.
-/

namespace krylov.AnalyticTools
noncomputable section
open Set Filter
open scoped Topology

/-- A one-sided physical change of variables preserves an analytic right
germ when the extended clock has nonzero derivative. -/
theorem analyticWithinAt_right_change {q ρ Q R v i : ℝ → ℝ}
    (hq : AnalyticAt ℝ q 0) (hρ : AnalyticAt ℝ ρ 0) (hq₀ : q 0 = 0)
    (hqd : deriv q 0 ≠ 0) (hi : ContinuousAt i 0) (hi₀ : i 0 = 0)
    (hip : ∀ x ≥ 0, 0 ≤ i x) (hQi : ∀ x ≥ 0, Q (i x) = x)
    (hQ : Q =ᶠ[𝓝[Ici 0] 0] q) (hR : R =ᶠ[𝓝[Ici 0] 0] ρ)
    (hv : v =ᶠ[𝓝[Ici 0] 0] fun x ↦ R (i x)) :
    AnalyticWithinAt ℝ v (Ici 0) 0 := by
  obtain ⟨κ, hκ, hκ₀, hleft, _⟩ := exists_analytic_scalar_inverse hq hqd
  rw [hq₀] at hκ hκ₀
  have ha : AnalyticAt ℝ (fun x ↦ ρ (κ x)) 0 := by
    exact hρ.comp_of_eq hκ hκ₀
  have hit : Tendsto i (𝓝[Ici 0] 0) (𝓝 0) := by
    simpa only [hi₀] using hi.tendsto.mono_left nhdsWithin_le_nhds
  have hiw : Tendsto i (𝓝[Ici 0] 0) (𝓝[Ici 0] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨hit, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact hip x hx
  have heq : v =ᶠ[𝓝[Ici 0] 0] fun x ↦ ρ (κ x) := by
    filter_upwards [self_mem_nhdsWithin, hv, hiw.eventually hQ,
      hiw.eventually hR, hit.eventually hleft] with x hx hvx hqx hrx hix
    have hqix : q (i x) = x := hqx.symm.trans (hQi x hx)
    rw [hqix] at hix
    change v x = ρ (κ x)
    rw [hix, hvx, hrx]
  exact ha.analyticWithinAt.congr_of_eventuallyEq heq (heq.eq_of_nhdsWithin (by simp))

end
end krylov.AnalyticTools
