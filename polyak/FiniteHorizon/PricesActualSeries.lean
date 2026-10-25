import polyak.FiniteHorizon.ExactPrices

/-!
Article: Appendix C, the literal infinite sum in Lemma prices(ii).
Use: the actual window functional bounds every nonnegative partial sum, hence
the full discounted energy is summable and has that same price bound.
-/
noncomputable section
namespace polyak.FiniteHorizon
universe u
open Growth Growth.FiniteHorizon Energy Filter
open scoped Topology

theorem windowPrice7_run_series {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {A B β t a δ ε : ℝ} {H : ℕ} {C : WindowMatrix7} {d : ℕ → ℝ}
    (data : BandedData7 C d ε) (hB : B≠0) (ha : 0<a) (hδ : 0<δ) (hε : ε=a*δ) (hH : 7≤H)
    (hRate : growthRate A B β H<Real.exp t) (hsource : BandedSource7.{u} A B β t H C d)
    (r : HRun E A B β H) (k : ℕ) (hk : H≤k) :
    Summable (fun i : ℕ => Real.exp (-2*t)^i*‖r.x (k+i-5)‖^2) ∧
      δ*(∑' i : ℕ,Real.exp (-2*t)^i*‖r.x (k+i-5)‖^2)≤windowPrice7 data H a t (runWindow r k) := by
  have hpartial (N : ℕ) : δ*(∑ i∈Finset.range N,Real.exp (-2*t)^i*‖r.x (k+i-5)‖^2)≤
      windowPrice7 data H a t (runWindow r k):=
    windowPrice7_run_finite_bound data hB ha hδ.le hε hH hRate hsource r k hk N
  have hb (N : ℕ) : (∑ i∈Finset.range N,Real.exp (-2*t)^i*‖r.x (k+i-5)‖^2)≤
      windowPrice7 data H a t (runWindow r k)/δ := by
    apply (le_div_iff₀ hδ).mpr
    simpa only [mul_comm] using hpartial N
  have hs : Summable (fun i : ℕ => Real.exp (-2*t)^i*‖r.x (k+i-5)‖^2):=
    summable_of_sum_range_le (fun i => by positivity) hb
  refine ⟨hs,?_⟩
  exact le_of_tendsto (tendsto_const_nhds.mul hs.hasSum.tendsto_sum_nat) (Eventually.of_forall hpartial)

/-- The actual source-data record discharges the banded inequality input. -/
theorem AboveRateData7.run_series {A B β T a M δ : ℝ} {H : ℕ}
    (data : AboveRateData7 A B β T a M H δ) (hB : B≠0) (ha : 0<a) (hδ : 0<δ) (hH : 7≤H)
    (hRate : growthRate A B β H<Real.exp (T+δ))
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (r : HRun E A B β H) (k : ℕ) (hk : H≤k) :
    Summable (fun i : ℕ => Real.exp (-2*(T+δ))^i*‖r.x (k+i-5)‖^2) ∧
      δ*(∑' i : ℕ,Real.exp (-2*(T+δ))^i*‖r.x (k+i-5)‖^2)≤
        windowPrice7 data.factors H a (T+δ) (runWindow r k) :=
  windowPrice7_run_series data.factors hB ha hδ rfl hH hRate data.source r k hk

end polyak.FiniteHorizon
