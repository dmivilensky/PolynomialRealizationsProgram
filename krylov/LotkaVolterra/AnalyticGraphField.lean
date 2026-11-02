import krylov.AnalyticTools.RescaledFlow
import krylov.AnalyticTools.ContinuousInverse
import krylov.LotkaVolterra.GlobalSubcriticalGraph

/-!
Article: main_krylov, apC:prop:LV and apC:prop:g1, graph regularity off a saddle.
Use: prove analyticity of an actual rational graph ODE by lifting its two
denominators to units in the continuous-path Banach algebra. Only local
nonvanishing is needed; no global regularization of a rational pole is used.
Source: the analytic Picard implicit construction and analytic algebra inversion.
-/

namespace krylov.LotkaVolterra
noncomputable section
open Set Filter
open krylov.AnalyticTools
open scoped Topology

private def pathFirst : C(PathDomain, ℝ × ℝ) →L[ℝ] C(PathDomain, ℝ) :=
  (ContinuousLinearMap.fst ℝ ℝ ℝ).compLeftContinuous ℝ PathDomain
private def pathSecond : C(PathDomain, ℝ × ℝ) →L[ℝ] C(PathDomain, ℝ) :=
  (ContinuousLinearMap.snd ℝ ℝ ℝ).compLeftContinuous ℝ PathDomain
private def pathSecondIn : C(PathDomain, ℝ) →L[ℝ] C(PathDomain, ℝ × ℝ) :=
  (ContinuousLinearMap.inr ℝ ℝ ℝ).compLeftContinuous ℝ PathDomain

def graphField (γ : ℝ) (z : ℝ × ℝ) : ℝ × ℝ :=
  (1, 2 * z.2 * (z.2 - 1 - γ * z.1) / (z.1 * (z.2 + 1 - z.1)))

def liftedGraphField (γ : ℝ) (f : C(PathDomain, ℝ × ℝ)) : C(PathDomain, ℝ × ℝ) :=
  ContinuousMap.const PathDomain (1, 0) + pathSecondIn
    (ContinuousMap.const PathDomain 2 * pathSecond f *
      (pathSecond f - 1 - ContinuousMap.const PathDomain γ * pathFirst f) *
      Ring.inverse (pathFirst f) * Ring.inverse (pathSecond f + 1 - pathFirst f))

private theorem graphLift_units {z : ℝ × ℝ} (hU : z.1 ≠ 0) (hD : z.2 + 1 - z.1 ≠ 0) :
    IsUnit (pathFirst (ContinuousMap.const PathDomain z)) ∧
      IsUnit (pathSecond (ContinuousMap.const PathDomain z) + 1 -
        pathFirst (ContinuousMap.const PathDomain z)) := by
  constructor
  · apply ContinuousMap.isUnit_iff_forall_ne_zero _ |>.mpr
    intro u
    simpa [pathFirst] using hU
  · apply ContinuousMap.isUnit_iff_forall_ne_zero _ |>.mpr
    intro u
    simpa [pathFirst, pathSecond] using hD

theorem analyticAt_liftedGraphField {γ : ℝ} {z : ℝ × ℝ}
    (hU : z.1 ≠ 0) (hD : z.2 + 1 - z.1 ≠ 0) :
    AnalyticAt ℝ (liftedGraphField γ) (ContinuousMap.const PathDomain z) := by
  have hA := pathFirst.analyticAt (ContinuousMap.const PathDomain z)
  have hB := pathSecond.analyticAt (ContinuousMap.const PathDomain z)
  have hden : AnalyticAt ℝ (fun f ↦ pathSecond f + 1 - pathFirst f)
      (ContinuousMap.const PathDomain z) := (hB.add analyticAt_const).sub hA
  have hu := graphLift_units hU hD
  have hIA := (analyticAt_continuousMap_inverse hu.1).comp (f := pathFirst) hA
  have hID := (analyticAt_continuousMap_inverse hu.2).comp
    (f := fun f ↦ pathSecond f + 1 - pathFirst f) hden
  have hn : AnalyticAt ℝ (fun f ↦ ContinuousMap.const PathDomain 2 * pathSecond f *
      (pathSecond f - 1 - ContinuousMap.const PathDomain γ * pathFirst f) *
      Ring.inverse (pathFirst f) * Ring.inverse (pathSecond f + 1 - pathFirst f))
      (ContinuousMap.const PathDomain z) :=
    ((((analyticAt_const.mul hB).mul
      ((hB.sub analyticAt_const).sub (analyticAt_const.mul hA))).mul hIA).mul hID)
  exact analyticAt_const.add ((pathSecondIn.analyticAt _).comp hn)

theorem liftedGraphField_eventually {γ : ℝ} {z : ℝ × ℝ}
    (hU : z.1 ≠ 0) (hD : z.2 + 1 - z.1 ≠ 0) :
    ∀ᶠ f in 𝓝 (ContinuousMap.const PathDomain z), ∀ u,
      liftedGraphField γ f u = graphField γ (f u) := by
  have hu := graphLift_units hU hD
  have hA : ∀ᶠ f in 𝓝 (ContinuousMap.const PathDomain z), IsUnit (pathFirst f) :=
    pathFirst.continuous.continuousAt.preimage_mem_nhds (Units.isOpen.mem_nhds hu.1)
  have hD' : ∀ᶠ f in 𝓝 (ContinuousMap.const PathDomain z),
      IsUnit (pathSecond f + 1 - pathFirst f) :=
    ((pathSecond.continuous.add continuous_const).sub pathFirst.continuous).continuousAt.preimage_mem_nhds
      (Units.isOpen.mem_nhds hu.2)
  filter_upwards [hA, hD'] with f hfA hfD u
  have hinvA := inverse_continuousMap_apply hfA u
  have hinvD := inverse_continuousMap_apply hfD u
  ext
  · change (1 : ℝ) + 0 = 1
    exact add_zero _
  · change (0 : ℝ) + 2 * (f u).2 * ((f u).2 - 1 - γ * (f u).1) *
        Ring.inverse (pathFirst f) u * Ring.inverse (pathSecond f + 1 - pathFirst f) u =
      2 * (f u).2 * ((f u).2 - 1 - γ * (f u).1) / ((f u).1 * ((f u).2 + 1 - (f u).1))
    rw [zero_add, hinvA, hinvD]
    change 2 * (f u).2 * ((f u).2 - 1 - γ * (f u).1) * ((f u).1)⁻¹ *
        ((f u).2 + 1 - (f u).1)⁻¹ = _
    simp only [div_eq_mul_inv, mul_inv_rev, mul_assoc, mul_comm]

/-- A genuine solution of the rational graph equation is analytic wherever
its two actual denominators do not vanish. -/
theorem analyticAt_graph_solution {γ x : ℝ} {σ : ℝ → ℝ} (hx : x ≠ 0)
    (hden : σ x + 1 - x ≠ 0)
    (hd : ∀ᶠ U in 𝓝 x, HasDerivAt σ
      (2 * σ U * (σ U - 1 - γ * U) / (U * (σ U + 1 - U))) U) :
    AnalyticAt ℝ σ x := by
  let α : ℝ → ℝ × ℝ := fun U ↦ (U, σ U)
  have hα : ∀ᶠ U in 𝓝 x, HasDerivAt α (graphField γ (α U)) U := by
    filter_upwards [hd] with U hU
    exact (hasDerivAt_id U).prodMk hU
  have ha : AnalyticAt ℝ α x := analyticAt_of_local_lifted_field (liftedGraphField γ)
    (liftedGraphField_eventually hx hden) (analyticAt_liftedGraphField hx hden) hα
  exact analyticAt_snd.comp (f := α) ha

end
end krylov.LotkaVolterra
