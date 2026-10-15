import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Topology.Order.Compact

/-!
Article: 2606.16671v2, Theorem E.3.
Differentiation under a finite interval integral from continuous derivatives on a rectangle.
Use: `«2606.16671v2».Analysis.hasDerivAt_integral_rectangle` feeds
`«2606.16671v2».SineJacobi.ellipticK_deriv` (elliptic K deriv).
Proof chain: `«2606.16671v2».SineJacobi.sineProfile_ode` — 2606.16671v2, Theorem E.3; Hard-edge
recurrence, singular ODE, uniqueness and endpoint limits.
Source: mathlib, Mathlib.Analysis.Calculus.ParametricIntervalIntegral,
Mathlib.Topology.Order.Compact — differentiation under a compact parameter integral. The needed form
is proved here.
-/
namespace «2606.16671v2».Analysis
noncomputable section
open Set Filter MeasureTheory Topology

/--
Differentiation under a finite interval integral from continuous derivatives on a rectangle.
The compact rectangle supplies the uniform dominator, so applications need no separate
measure-theoretic hypotheses.

The actual derivative at the stated point: `HasDerivAt (fun u => ∫ t in a..b, F u t) (∫ t in
a..b, F' x t) x`.

Use: `«2606.16671v2».Analysis.sinc_deriv` uses this derivative formula to establish the actual
derivative at the stated point: `HasDerivAt sinc (sinc₁ x) x`.

Article: 2606.16671v2, Theorem E.3 via `«2606.16671v2».SineJacobi.sineProfile_ode`.

Source: mathlib, Mathlib.Analysis.Calculus.ParametricIntervalIntegral,
Mathlib.Topology.Order.Compact — differentiation under a compact parameter integral.

Proof: Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
at an arbitrary point in that intersection.
-/
theorem hasDerivAt_integral_rectangle
    (F F' : ℝ → ℝ → ℝ) {lo hi a b x : ℝ} (hx : x ∈ Ioo lo hi) (hab : a ≤ b)
    (hF : ∀ u ∈ Icc lo hi, ContinuousOn (F u) (Icc a b))
    (hF' : ContinuousOn F'.uncurry (Icc lo hi ×ˢ Icc a b))
    (hder : ∀ u ∈ Icc lo hi, ∀ t ∈ Icc a b, HasDerivAt (fun u => F u t) (F' u t) u) :
    HasDerivAt (fun u => ∫ t in a..b, F u t) (∫ t in a..b, F' x t) x := by
  -- Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
  -- at an arbitrary point in that intersection.
  obtain ⟨M, hM⟩ := ((isCompact_Icc (a := lo) (b := hi)).prod
    (isCompact_Icc (a := a) (b := b))).bddAbove_image hF'.norm
  have hmem : Icc lo hi ∈ 𝓝 x := Icc_mem_nhds hx.1 hx.2
  have hxc : x ∈ Icc lo hi := ⟨hx.1.le, hx.2.le⟩
  -- Establish continuity hF before using the function at limits or in calculus arguments.
  have hF'x : ContinuousOn (F' x) (Icc a b) := by
    exact hF'.comp (continuousOn_const.prodMk continuousOn_id)
      (by intro t ht; exact ⟨hxc, ht⟩)
  have hFxint := (hF x hxc).intervalIntegrable_of_Icc (μ := volume) hab
  have hF'xint := hF'x.intervalIntegrable_of_Icc (μ := volume) hab
  refine (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := F) (F' := F') (s := Icc lo hi) (bound := fun _ => M) (μ := volume)
    hmem ?_ hFxint hF'xint.def'.aestronglyMeasurable ?_ intervalIntegrable_const ?_).2
  · filter_upwards [hmem] with u hu
    exact ((hF u hu).intervalIntegrable_of_Icc (μ := volume) hab).def'.aestronglyMeasurable
  · apply Filter.Eventually.of_forall
    intro t ht u hu
    have ht' : t ∈ Icc a b := by
      rw [uIoc_of_le hab] at ht
      exact ⟨ht.1.le, ht.2⟩
    exact hM (mem_image_of_mem (fun p : ℝ × ℝ => ‖F'.uncurry p‖)
      (show (u,t) ∈ Icc lo hi ×ˢ Icc a b from ⟨hu, ht'⟩))
  · apply Filter.Eventually.of_forall
    intro t ht u hu
    have ht' : t ∈ Icc a b := by
      rw [uIoc_of_le hab] at ht
      exact ⟨ht.1.le, ht.2⟩
    exact hder u hu t ht'

end
end «2606.16671v2».Analysis
