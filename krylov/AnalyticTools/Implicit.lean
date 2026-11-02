import krylov.AnalyticTools.LocalInverse
import Mathlib.Analysis.Calculus.FDeriv.Prod

/-!
Article: main_krylov, apC:prop:LV, analytic background.
Use: an analytic implicit equation in Banach spaces follows from the existing
analytic inverse theorem, by keeping the parameter as the first coordinate.
Source: the standard inverse-to-implicit-function construction; mathlib supplies
the analytic inverse and the triangular continuous linear equivalence.
-/

namespace krylov.AnalyticTools
noncomputable section
open Filter
open scoped Topology

/-- Analytic implicit functions, with a derivative written in block form.
The invertibility hypothesis concerns the unknown coordinate only. -/
theorem exists_analytic_implicit
    {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
    {f : E × F → G} {a : E} {b : F}
    (hf : AnalyticAt ℝ f (a, b)) (hz : f (a, b) = 0)
    (A : E →L[ℝ] G) (B : F ≃L[ℝ] G)
    (hd : HasFDerivAt f (A.coprod (B : F →L[ℝ] G)) (a, b)) :
    ∃ u : E → F, AnalyticAt ℝ u a ∧ u a = b ∧
      (∀ᶠ x in 𝓝 a, f (x, u x) = 0) ∧
      ∀ᶠ p in 𝓝 (a, b), f p = 0 → p.2 = u p.1 := by
  let H : E × F → E × G := fun p ↦ (p.1, f p)
  let i : (E × F) ≃L[ℝ] E × G :=
    (ContinuousLinearEquiv.refl ℝ E).skewProd B A
  have ha : AnalyticAt ℝ H (a, b) := analyticAt_fst.prod hf
  have hi : fderiv ℝ H (a, b) = (i : (E × F) →L[ℝ] E × G) := by
    have h := (hasFDerivAt_fst (𝕜 := ℝ) (p := (a, b))).prodMk hd
    convert h.fderiv using 1
    ext p <;> simp [i, ContinuousLinearMap.coprod_apply, add_comm]
  obtain ⟨g, hg, hgb, hleft, hright⟩ := exists_analytic_local_inverse ha i hi
  have hH : H (a, b) = (a, 0) := by simp [H, hz]
  rw [hH] at hg hgb hright
  let u : E → F := fun x ↦ (g (x, 0)).2
  have htanalytic : AnalyticAt ℝ (fun x : E ↦ (x, (0 : G))) a :=
    analyticAt_id.prod analyticAt_const
  have hgcomp : AnalyticAt ℝ (fun x : E ↦ g (x, (0 : G))) a :=
    hg.comp (f := fun x : E ↦ (x, (0 : G))) htanalytic
  have hu : AnalyticAt ℝ u a := analyticAt_snd.comp hgcomp
  refine ⟨u, hu, congrArg Prod.snd hgb, ?_, ?_⟩
  · have ht : Tendsto (fun x : E ↦ (x, (0 : G))) (𝓝 a) (𝓝 (a, 0)) :=
      continuousAt_id.prodMk continuousAt_const
    filter_upwards [ht.eventually hright] with x hx
    have hx₁ : (g (x, 0)).1 = x := congrArg Prod.fst hx
    have hx₂ : f (g (x, 0)) = 0 := congrArg Prod.snd hx
    change f (x, (g (x, 0)).2) = 0
    have hp : g (x, 0) = (x, (g (x, 0)).2) := Prod.ext hx₁ rfl
    rwa [hp] at hx₂
  · filter_upwards [hleft] with p hp hzero
    have hHp : H p = (p.1, 0) := by simp [H, hzero]
    rw [hHp] at hp
    exact (congrArg Prod.snd hp).symm

end
end krylov.AnalyticTools
