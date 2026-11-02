import krylov.Variation.FCResponse
import krylov.Stability.AnalyticRemainder

/-!
Article: main_krylov, thm:A, actual adaptive local quadratic response remainder.
Use: the actual FC terminal canonical gradient equals its proved sharp spatial
first variation plus a genuine quadratic remainder along analytic perturbations.
Source: actual adaptive analyticity, exact derivative identification and analytic Taylor calculus.
-/

namespace krylov.Variation
noncomputable section
open Matrix Finset Filter Topology Asymptotics krylov.Methods krylov.Reference krylov.Secant krylov.Stability
open scoped InnerProductSpace BigOperators
variable {n : ℕ}

/-- The real adaptive full-memory FC terminal canonical gradient has the proved sharp first variation and a genuine local quadratic remainder.
Use: gives the pointwise analytic-path expansion; the uniform (n,κ)-only bound is proved separately in Stability/UniformResponseScale.lean.
Article: main_krylov, thm:A, pointwise ĝ_n=tΣP_lE_lv_l+O(t²).
Proof: actual quadratic reference termination annihilates the constant term,
the proved real trajectory derivative is the constructed spatial response, and the actual analytic Taylor theorem gives the quadratic remainder. -/
theorem fullFC_local_response_remainder (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (hcount : referenceAtomCount base hb g=n)
    (E : ℕ → Matrix (Fin n) (Fin n) ℝ)
    (A : ℝ → ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hA : ∀ k, AnalyticAt ℝ (fun t => A t k) 0)
    (hD : ∀ k, HasDerivAt (fun t => A t k) (cumulativeDrift base E k) 0)
    (hsym : ∀ t k, (A t k).toLinearMap.IsSymmetric) (hA0 : A 0=fun _ => cgOperator base) :
    (fun t => Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (metricRoot base)⁻¹
      (fcGradient fullMemory (A t) g n)-t • fullCycleResponse base g (range n) E)=O[𝓝 (0 : ℝ)] (fun t => t^2) := by
  -- Every output and coefficient belongs to the actual executed adaptive FC cycle.
  let F := fun t => Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (metricRoot base)⁻¹
    (fcGradient fullMemory (A t) g n)
  have hG := (quadraticFC_prefix_analytic A (fun _ => g) 0 hA analyticAt_const (cgOperator base) hA0
    (cgOperator_positive base hb).1 (cgOperator_positive base hb).2 n
    (cg_nonstagnation_of_full_atoms base hb g hcount)).1
  have hF : AnalyticAt ℝ F 0 := analytic_operator_apply analyticAt_const hG
  have hF0 : F 0=0 := by
    change Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (metricRoot base)⁻¹
      (fcGradient fullMemory (A 0) g n)=0
    rw [hA0,(fullFC_reference_step (cgOperator base) (cgOperator_positive base hb).1
      (cgOperator_positive base hb).2 g n).1,
      show CG.gradient (cgOperator base) g n=0 by simpa only [hcount] using cg_terminates base hb g,map_zero]
  have hd := (fullFC_response_hasDerivAt base hb g hcount E A hA hD hsym hA0).deriv
  change deriv F 0=fullCycleResponse base g (range n) E at hd
  have hr := analytic_quadratic_remainder hF
  simpa only [zero_add,hF0,sub_zero,fderiv_eq_smul_deriv,hd,Real.norm_eq_abs,sq_abs] using hr

/-- The constructed canonical segment perturbation of the real FC cycle has its exact spatial first variation and a genuine local quadratic remainder.
Use: no analytic path, measured operator derivative or hypothetical adaptive expansion is an input to this canonical realization theorem.
Article: main_krylov, thm:A, source canonical perturbation expansion.
Proof: the actual canonical affine segment path has all primitive regularity,
derivative, symmetry and reference hypotheses proved, so the genuine actual FC local remainder theorem applies. -/
theorem canonicalFC_local_response_remainder (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (hcount : referenceAtomCount base hb g=n)
    (E : ℕ → Matrix (Fin n) (Fin n) ℝ) (hE : ∀ l, (E l).IsSymm) :
    (fun t => Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (metricRoot base)⁻¹
      (fcGradient fullMemory (canonicalFCPath base E t) g n)-t • fullCycleResponse base g (range n) E)=O[𝓝 (0 : ℝ)]
        (fun t => t^2) :=
  fullFC_local_response_remainder base hb g hcount E (canonicalFCPath base E)
    (fun k => (canonicalFCPath_calculus base E k).1) (fun k => (canonicalFCPath_calculus base E k).2)
    (canonicalFCPath_symmetric base hb E hE) (canonicalFCPath_zero base E)

end
end krylov.Variation
