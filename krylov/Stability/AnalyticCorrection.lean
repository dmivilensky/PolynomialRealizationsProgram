import krylov.Stability.AnalyticSolve
import krylov.Methods.RepeatedCorrection
import krylov.Methods.NormalizedCorrection

/-!
Article: main_krylov, lem:U(d) and lem:projected-residual, actual RFC correction regularity.
Use: differentiate the real repeated observed-gradient model corrections;
no regularity of a returned trajectory is supplied as an assumption.
Source: the proved actual analytic inverse coefficients and finite analytic composition.
-/

namespace krylov.Stability
noncomputable section
open Matrix krylov.Methods
open scoped BigOperators
variable {E X : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [NormedAddCommGroup X] [NormedSpace ℝ X]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- Genuine finite physical synthesis is analytic in the actual vectors and actual scalar coefficients.
Use: computed model coefficients give regular actual correction displacements.
Article: main_krylov, lem:U(d), finite observed-vector combinations.
Proof: each physical summand is an analytic scalar multiple of an analytic observed vector. -/
theorem analytic_combine (s : X → ι → E) (c : X → ι → ℝ) (x : X)
    (hs : ∀ i, AnalyticAt ℝ (fun p => s p i) x) (hc : ∀ i, AnalyticAt ℝ (fun p => c p i) x) :
    AnalyticAt ℝ (fun p => combine (s p) (c p)) x := by
  convert! Finset.analyticAt_sum Finset.univ (fun i _ => (hc i).smul (hs i)) using 1
  funext p
  simp only [combine, Finset.sum_apply, Pi.smul_apply']

/-- The actual physical model correction is analytic at its genuine finite inverse domain.
Use: analytic stored data and actual model entries propagate through the real computed solve.
Article: main_krylov, lem:U(d), χ=−UH⁻¹Uᵀg.
Proof: synthesize the previously proved genuine analytic inverse-model coefficients. -/
theorem analytic_modelCorrection (s : X → ι → E) (H : X → Matrix ι ι ℝ) (g : X → E) (x : X)
    (hs : ∀ i, AnalyticAt ℝ (fun p => s p i) x)
    (hH : ∀ i j, AnalyticAt ℝ (fun p => H p i j) x) (hg : AnalyticAt ℝ g x)
    (hu : (H x).det≠0) :
    AnalyticAt ℝ (fun p => combine (s p) (modelCoefficients (s p) (H p) (g p))) x :=
  analytic_combine s _ x hs (analytic_modelCoefficients s H g x hs hH hg hu)

omit [DecidableEq ι] in
/-- The actual finite projected residual is analytic in its real observed window and gradient in the genuine Euclidean norm.
Use: actual quadratic projected orthogonality produces a first-order residual estimate without assuming one.
Article: main_krylov, lem:projected-residual, incoming projected residual order.
Proof: real inner-product entries form an analytic finite coordinate vector;
the actual continuous linear Euclidean coordinate equivalence preserves analyticity. -/
theorem analytic_projectedResidual (s : X → ι → E) (g : X → E) (x : X)
    (hs : ∀ i, AnalyticAt ℝ (fun p => s p i) x) (hg : AnalyticAt ℝ g x) :
    AnalyticAt ℝ (fun p => projectedResidual (s p) (g p)) x := by
  have hc : AnalyticAt ℝ (fun p i => inner ℝ (s p i) (g p)) x := AnalyticAt.pi (fun i => analytic_inner (hs i) hg)
  exact ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : ι => ℝ)).symm.toContinuousLinearMap.analyticAt _).comp hc

/-- Every fixed finite actual RFC correction phase is analytic in its genuine model, window, operator and incoming gradient.
Use: real returned gradients and movements acquire regularity through the observed-query recursion.
Article: main_krylov, lem:U(d), RFC and RFC_k corrections.
Proof: each real inverse solve gives an analytic physical query; the actual
operator produces its analytic observed gradient, which becomes the next real
right-hand side in a finite induction with the same genuine model domain. -/
theorem repeatedModel_phase_analytic (s : X → ι → E) (H : X → Matrix ι ι ℝ)
    (B : X → E →L[ℝ] E) (g : X → E) (x : X) (count : ℕ)
    (hs : ∀ i, AnalyticAt ℝ (fun p => s p i) x)
    (hH : ∀ i j, AnalyticAt ℝ (fun p => H p i j) x) (hB : AnalyticAt ℝ B x)
    (hg : AnalyticAt ℝ g x) (hu : (H x).det≠0) :
    AnalyticAt ℝ (fun p => (runCorrections (repeatedModelTree (s p) (H p) count (g p)) (B p) (g p)).movement) x ∧
      AnalyticAt ℝ (fun p => (runCorrections (repeatedModelTree (s p) (H p) count (g p)) (B p) (g p)).gradient) x := by
  -- Induction follows the actual query's returned gradient, not an independently prescribed model residual.
  induction count generalizing g with
  | zero => exact ⟨analyticAt_const,hg⟩
  | succ count ih =>
    let χ := fun p => combine (s p) (modelCoefficients (s p) (H p) (g p))
    have hχ : AnalyticAt ℝ χ x := analytic_modelCorrection s H g x hs hH hg hu
    let gnew := fun p => g p+B p (χ p)
    have hn : AnalyticAt ℝ gnew x := hg.add (analytic_operator_apply hB hχ)
    have ht := ih gnew hn
    exact ⟨hχ.add ht.1,ht.2⟩

end
end krylov.Stability
