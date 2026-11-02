import krylov.LotkaVolterra.LocalFlow
import krylov.AnalyticTools.RescaledFlow

/-!
Article: main_krylov, apC:prop:LV and apC:prop:g1, analytic orbit regularity.
Use: prove analyticity of actual Lotka--Volterra solutions from the explicit
polynomial lift on continuous paths and the analytic Picard construction.
Source: the analytic implicit function theorem in Banach spaces, as reduced to
mathlib's analytic inverse theorem in AnalyticTools.Implicit.
-/

namespace krylov.LotkaVolterra
noncomputable section
open Set Filter
open krylov.AnalyticTools
open scoped Topology

private def pathS : C(PathDomain, ℝ × ℝ) →L[ℝ] C(PathDomain, ℝ) :=
  (ContinuousLinearMap.fst ℝ ℝ ℝ).compLeftContinuous ℝ PathDomain

private def pathU : C(PathDomain, ℝ × ℝ) →L[ℝ] C(PathDomain, ℝ) :=
  (ContinuousLinearMap.snd ℝ ℝ ℝ).compLeftContinuous ℝ PathDomain

private def pathInS : C(PathDomain, ℝ) →L[ℝ] C(PathDomain, ℝ × ℝ) :=
  (ContinuousLinearMap.inl ℝ ℝ ℝ).compLeftContinuous ℝ PathDomain

private def pathInU : C(PathDomain, ℝ) →L[ℝ] C(PathDomain, ℝ × ℝ) :=
  (ContinuousLinearMap.inr ℝ ℝ ℝ).compLeftContinuous ℝ PathDomain

/-- The actual polynomial field acting pointwise on continuous paths. -/
def liftedField (γ : ℝ) (f : C(PathDomain, ℝ × ℝ)) : C(PathDomain, ℝ × ℝ) :=
  pathInS (2 * pathS f *
    (pathS f - 1 - ContinuousMap.const PathDomain γ * pathU f)) +
  pathInU (pathU f * (pathS f + 1 - pathU f))

theorem liftedField_apply (γ : ℝ) (f : C(PathDomain, ℝ × ℝ)) (u : PathDomain) :
    liftedField γ f u = vectorField γ (f u) := by
  have htwo : (2 : C(PathDomain, ℝ)) u = 2 := rfl
  ext <;> simp_all [liftedField, pathS, pathU, pathInS, pathInU, vectorField, sRate, uRate]

/-- The lifted field is analytic on the actual path Banach space: all its
operations are bounded linear maps, products and constants. -/
theorem analyticAt_liftedField (γ : ℝ) (f : C(PathDomain, ℝ × ℝ)) :
    AnalyticAt ℝ (liftedField γ) f := by
  have hs := pathS.analyticAt f
  have hU := pathU.analyticAt f
  have h₁ : AnalyticAt ℝ (fun f : C(PathDomain, ℝ × ℝ) ↦
      2 * pathS f * (pathS f - 1 - ContinuousMap.const PathDomain γ * pathU f)) f :=
    (analyticAt_const.mul hs).mul
      ((hs.sub analyticAt_const).sub (analyticAt_const.mul hU))
  have h₂ : AnalyticAt ℝ (fun f : C(PathDomain, ℝ × ℝ) ↦
      pathU f * (pathS f + 1 - pathU f)) f :=
    hU.mul ((hs.add analyticAt_const).sub hU)
  exact ((pathInS.analyticAt _).comp h₁).add ((pathInU.analyticAt _).comp h₂)

/-- Actual solutions are real analytic at every point where the differential
equation holds on a neighborhood. This proves orbit regularity, rather than
inferring it merely from analyticity of the vector field. -/
theorem analyticAt_solution {γ t₀ : ℝ} {α : ℝ → ℝ × ℝ} (hc : Continuous α)
    (hd : ∀ᶠ t in 𝓝 t₀, HasDerivAt α (vectorField γ (α t)) t) :
    AnalyticAt ℝ α t₀ := by
  have ha := analyticAt_of_lifted_field hc t₀
    (liftedField γ)
    (liftedField_apply γ) (analyticAt_liftedField γ _) hd
  have hsub : AnalyticAt ℝ (fun t : ℝ ↦ t - t₀) t₀ :=
    analyticAt_id.sub analyticAt_const
  have hcomp := ha.comp_of_eq hsub (by simp)
  simpa only [Function.comp_def, add_sub_cancel] using hcomp

/-- The analyticity theorem is local: no regularity of a curve outside its
actual ODE domain is required. A continuous compact extension supplies the
Banach-path construction, and germ equality transfers the conclusion back. -/
theorem analyticAt_solution_of_eventually {γ t₀ : ℝ} {α : ℝ → ℝ × ℝ}
    (hd : ∀ᶠ t in 𝓝 t₀, HasDerivAt α (vectorField γ (α t)) t) :
    AnalyticAt ℝ α t₀ :=
  analyticAt_of_local_lifted_field (liftedField γ)
    (Eventually.of_forall (liftedField_apply γ)) (analyticAt_liftedField γ _) hd

end
end krylov.LotkaVolterra
