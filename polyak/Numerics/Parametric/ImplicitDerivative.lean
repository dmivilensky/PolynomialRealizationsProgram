import polyak.Numerics.Parametric.Analytic
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Pi

/-!
Article: Appendix B, differentiating actual checked continuation roots.
Use: a differentiable branch satisfying the source equations locally has exactly
the implicit derivative equation used by the interval slope certificates.
-/
noncomputable section
namespace polyak.Numerics.Parametric
open LeanCert.Core LeanCert.Engine Filter Matrix
open scoped Topology

/-- The matrix Jacobian is the actual unknown differential on every vector. -/
theorem jacobian_mulVec {n : ℕ} (F : Fin n → Expr) (s : ℝ) (x v : Fin n → ℝ) :
    jacobian F s x *ᵥ v=fderiv ℝ (system F s) x v := by
  exact LinearMap.toMatrix'_mulVec _ _

/-- Exact chain rule for an actual local root branch, in arbitrary finite dimension. -/
theorem implicit_derivative {n : ℕ} (F : Fin n → Expr) (hF : ∀ i, ADSupported (F i))
    {g : ℝ → (Fin n → ℝ)} {s : ℝ} (hg : DifferentiableAt ℝ g s)
    (hz : ∀ᶠ t in 𝓝 s,system F t (g t)=0) :
    jacobian F s (g s) *ᵥ deriv g s=
      -(fun i => deriv (fun r : ℝ => eval (F i) r (g s)) s) := by
  let L:=fderiv ℝ (joint F) (s,g s)
  have hL : HasFDerivAt (joint F) L (s,g s) :=
    ((joint_contDiff F hF).differentiable (by simp)).differentiableAt.hasFDerivAt
  have hpair : HasDerivAt (fun t : ℝ => (t,g t)) (1,deriv g s) s :=
    (hasDerivAt_id s).prodMk hg.hasDerivAt
  have hzero : L (1,deriv g s)=0 := by
    have hc := (hL.comp_hasDerivAt s hpair).congr_of_eventuallyEq
      (show (fun _ : ℝ => (0 : Fin n → ℝ))=ᶠ[𝓝 s] joint F ∘ (fun t => (t,g t)) from
        hz.mono (fun _ ht => ht.symm))
    exact hc.unique (hasDerivAt_const s (0 : Fin n → ℝ))
  have hparam : HasDerivAt (fun r : ℝ => system F r (g s)) (L (1,0)) s := by
    exact hL.comp_hasDerivAt s ((hasDerivAt_id s).prodMk (hasDerivAt_const s (g s)))
  have hparam_eq : L (1,0)=(fun i => deriv (fun r : ℝ => eval (F i) r (g s)) s) := by
    ext i
    have hi := (ContinuousLinearMap.proj i : (Fin n → ℝ) →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt s hparam
    exact hi.deriv.symm
  have hpartial : L (0,deriv g s)=fderiv ℝ (system F s) (g s) (deriv g s) := by
    have hh:=congrArg (fun M : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) => M (deriv g s))
      (joint_partial F hF s (g s))
    exact hh
  have hsplit : L (1,deriv g s)=L (1,0)+L (0,deriv g s) := by
    rw [←map_add]
    congr 1
    simp
  rw [hsplit,hparam_eq,hpartial] at hzero
  rw [jacobian_mulVec]
  exact eq_neg_of_add_eq_zero_right hzero

/-- Analytic roots supplied by the checked implicit function theorem need no
additional differentiability or derivative-equation hypothesis. -/
theorem analytic_implicit_derivative {n : ℕ} (F : Fin n → Expr)
    (hF : ∀ i, ADSupported (F i)) {g : ℝ → (Fin n → ℝ)} {s : ℝ}
    (hg : AnalyticAt ℝ g s) (hz : ∀ᶠ t in 𝓝 s,system F t (g t)=0) :
    jacobian F s (g s) *ᵥ deriv g s=
      -(fun i => deriv (fun r : ℝ => eval (F i) r (g s)) s) :=
  implicit_derivative F hF hg.differentiableAt hz

end polyak.Numerics.Parametric
