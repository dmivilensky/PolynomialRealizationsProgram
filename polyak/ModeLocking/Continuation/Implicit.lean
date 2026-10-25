import Mathlib.Analysis.Calculus.ImplicitFunction.ProdDomain
import Mathlib.Analysis.Calculus.FDeriv.Analytic

/-! Real analytic implicit functions on a product domain, obtained from the
analytic inverse theorem. Invertibility refers to the actual partial derivative. -/
noncomputable section
namespace polyak.ModeLocking.Continuation
open Filter
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]

theorem analytic_implicit_function {f : E × F → G} {u : E × F}
    (hf : AnalyticAt ℝ f u)
    (hpartial : (fderiv ℝ f u ∘L ContinuousLinearMap.inr ℝ E F).IsInvertible) :
    ∃ ψ : E → F, AnalyticAt ℝ ψ u.1 ∧ ψ u.1 = u.2 ∧
      (∀ᶠ x in 𝓝 u.1, f (x, ψ x) = f u) := by
  let hd := hf.hasStrictFDerivAt
  let φ := hd.implicitFunctionDataOfProdDomain hpartial
  let ψ := hd.implicitFunctionOfProdDomain hpartial
  have hprod : AnalyticAt ℝ φ.prodFun u := hf.prod analyticAt_fst
  have hinv : AnalyticAt ℝ φ.toOpenPartialHomeomorph.symm (φ.prodFun u) :=
    φ.toOpenPartialHomeomorph.analyticAt_symm' φ.pt_mem_toOpenPartialHomeomorph_source
      hprod φ.hasStrictFDerivAt.hasFDerivAt.fderiv
  have hinput : AnalyticAt ℝ (fun x : E => (f u, x)) u.1 :=
    analyticAt_const.prod analyticAt_id
  have hc : AnalyticAt ℝ (fun x : E => φ.toOpenPartialHomeomorph.symm (f u, x)) u.1 :=
    hinv.comp (f := fun x : E => (f u, x)) hinput
  refine ⟨ψ, ?_, ?_, hd.eventually_apply_implicitFunctionOfProdDomain hpartial⟩
  · exact analyticAt_snd.comp hc
  · exact (hd.eventually_apply_eq_iff_implicitFunctionOfProdDomain hpartial).self_of_nhds.mp rfl

end polyak.ModeLocking.Continuation
