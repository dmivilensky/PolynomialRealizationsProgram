import Mathlib.Analysis.Calculus.ImplicitContDiff

/-!
Article: chebyshev2, Lemma 19.
A continuous solution of a nonsingular scalar implicit equation agrees locally with mathlib's
implicit function, also on a closed parameter domain.
Use: `chebyshev2.Calculus.scalar_derivative_invertible` feeds
`chebyshev2.Calibration.positiveRoot_contDiffOn` (positive Root cont Diff On).
Proof chain: `chebyshev2.DualCertificate.Data.admissible_stable` — chebyshev2, Theorem E.1;
Stability of strict admissibility and uniform transfer of the certificate value.
Source: mathlib, Mathlib.Analysis.Calculus — parameter differentiation, Taylor integral remainder
and implicit-function calculus. The needed form is proved here.
-/
namespace chebyshev2.Calculus
noncomputable section
open Filter Set
open scoped Topology ContDiff

/--
Smoothness to the stated order: `ContDiffWithinAt ℝ n g s x`.

Use: `chebyshev2.Calibration.positiveRoot_contDiffOn` uses this assertion to establish
smoothness to the stated order: `ContDiffOn ℝ ∞ (fun p : ℝ × ℝ × ℝ => positiveRoot p.1 p.2.1
p.2.2) {p | 0 < p.1 ∧ 0 ≤ p.2.1 ∧ 0 < p.2.2}`.

Article: chebyshev2, Theorem E.1 via `chebyshev2.DualCertificate.Data.admissible_stable`.

Source: mathlib, Mathlib.Analysis.Calculus — parameter differentiation, Taylor integral
remainder and implicit-function calculus.

Proof: Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
at an arbitrary point in that intersection.
-/
theorem implicit_contDiffWithinAt {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {f : E × ℝ → ℝ} {g : E → ℝ}
    {s : Set E} {x : E} {n : ℕ∞ω}
    (hf : ContDiffAt ℝ n f (x,g x)) (hn : n ≠ 0)
    (hg : ContinuousWithinAt g s x)
    (he : ∀ᶠ y in 𝓝[s] x, f (y,g y)=f (x,g x))
    (hd : (fderiv ℝ f (x,g x) ∘L ContinuousLinearMap.inr ℝ E ℝ).IsInvertible) :
    ContDiffWithinAt ℝ n g s x := by
  -- Record the convergence hgraph with its source filter and target limit before taking limits
  -- in the subsequent identities/bounds.
  have hgraph : Tendsto (fun y => (y,g y)) (𝓝[s] x) (𝓝 (x,g x)) :=
    tendsto_nhdsWithin_of_tendsto_nhds tendsto_id |>.prodMk_nhds hg
  have hiff := hgraph.eventually (hf.eventually_apply_eq_iff_implicitFunction hn hd)
  have heq : g=ᶠ[𝓝[s] x] hf.implicitFunction hn hd := by
    filter_upwards [hiff,he] with y hy hey
    exact ((hy.mp hey)).symm
  exact (hf.contDiffAt_implicitFunction hn hd).contDiffWithinAt.congr_of_eventuallyEq
    heq (hf.implicitFunction_apply_self hn hd).symm

/--
The precise assertion is `(fderiv ℝ f (x,v) ∘L ContinuousLinearMap.inr ℝ E ℝ).IsInvertible`.

Use: `chebyshev2.Calibration.positiveRoot_contDiffOn` uses this assertion to establish
smoothness to the stated order: `ContDiffOn ℝ ∞ (fun p : ℝ × ℝ × ℝ => positiveRoot p.1 p.2.1
p.2.2) {p | 0 < p.1 ∧ 0 ≤ p.2.1 ∧ 0 < p.2.2}`.

Article: chebyshev2, Theorem E.1 via `chebyshev2.DualCertificate.Data.admissible_stable`.

Source: mathlib, Mathlib.Analysis.Calculus — parameter differentiation, Taylor integral
remainder and implicit-function calculus.

Proof: Expand/rewrite the named definitions and identities appearing in the tactic block; the
remaining goal is a direct simplification or algebraic consequence.
-/
theorem scalar_derivative_invertible {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f : E × ℝ → ℝ} {x : E} {v d : ℝ}
    (hf : DifferentiableAt ℝ f (x,v))
    (hd : HasDerivAt (fun y => f (x,y)) d v) (hne : d ≠ 0) :
    (fderiv ℝ f (x,v) ∘L ContinuousLinearMap.inr ℝ E ℝ).IsInvertible := by
  -- Expand/rewrite the named definitions and identities appearing in the tactic block; the
  -- remaining goal is a direct simplification or algebraic consequence.
  have hpair : HasFDerivAt (fun y : ℝ => (x,y))
      (ContinuousLinearMap.inr ℝ E ℝ) v := by
    exact (hasFDerivAt_const (𝕜 := ℝ) x v).prodMk (hasFDerivAt_id v)
  have hcomp := hf.hasFDerivAt.comp v hpair
  have he := hcomp.unique hd.hasFDerivAt
  rw [he]
  apply ContinuousLinearMap.IsInvertible.of_inverse
    (g := ContinuousLinearMap.toSpanSingleton ℝ d⁻¹)
  · ext
    simp [ContinuousLinearMap.toSpanSingleton_apply,hne]
  · ext
    simp [ContinuousLinearMap.toSpanSingleton_apply,hne]

end
end chebyshev2.Calculus
