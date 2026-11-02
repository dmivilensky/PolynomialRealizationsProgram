import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Analysis.Calculus.FDeriv.Analytic

/-!
Article: main_krylov, apC:prop:LV and apC:prop:g1, analytic background.
Use: expose the existing analytic inverse theorem in an existence form useful
for a Banach-space Picard/implicit construction. This does not postulate
analyticity of an ODE flow or existence of a stable manifold.
Source: mathlib's strict inverse theorem and analytic inverse power series.
-/

namespace krylov.AnalyticTools
noncomputable section
open Filter
open scoped Topology

/-- A real-analytic map with invertible derivative has an actual analytic
local inverse between Banach spaces, with both local inverse identities. -/
theorem exists_analytic_local_inverse
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {f : E → F} {a : E} (hf : AnalyticAt ℝ f a) (i : E ≃L[ℝ] F)
    (hi : fderiv ℝ f a = i) :
    ∃ g : F → E, AnalyticAt ℝ g (f a) ∧ g (f a) = a ∧
      (∀ᶠ x in 𝓝 a, g (f x) = x) ∧ (∀ᶠ y in 𝓝 (f a), f (g y) = y) := by
  have hd : HasStrictFDerivAt f (i : E →L[ℝ] F) a := by
    rw [← hi]
    exact hf.hasStrictFDerivAt
  let e := hd.toOpenPartialHomeomorph f
  have ha : a ∈ e.source := hd.mem_toOpenPartialHomeomorph_source
  have hae : AnalyticAt ℝ e.symm (e a) := e.analyticAt_symm' ha hf hi
  refine ⟨e.symm, hae, e.left_inv ha, ?_, ?_⟩
  · exact e.eventually_left_inverse ha
  · exact e.eventually_right_inverse' ha

end
end krylov.AnalyticTools
