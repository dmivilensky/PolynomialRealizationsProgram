import krylov.OneGradient.InformedPriorKnownFrame
import krylov.Information.FirstIncrementScenario
set_option autoImplicit false
/-!
Article: main_krylov, thm:local(b), actual physical informed sharpness scenarios.
Use: lift the exact canonical source attainers to genuine original
admissible known-base physical source families with all budgets unchanged.
Source: actual last-Lanczos prior base, its exact prior budget, genuine
Loewner budget transfer and exact physical positive-root congruence.
-/

namespace krylov.OneGradient
noncomputable section
open Matrix krylov.Reference krylov.Secant krylov.Information
open scoped BigOperators Matrix.Norms.L2Operator
variable {n : ℕ}

/-- A genuine physical known-base source built from the original
last-Lanczos prior and independent canonical increment/output witnesses.
Use: these are actual source scenarios, before executing the native method.
Article: main_krylov, thm:local(b), physical attaining scenario family. -/
def informedPhysicalScenario
    (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin (n+1))) (hg : g≠0)
    (hc : (activeSpectralValues A hA.1 g).card=n+1)
    (D : ℕ → Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (F : Matrix (Fin (n+1)) (Fin (n+1)) ℝ)
    (c t : ℝ) : Scenario (n+1) where
  base := informedPriorBase A hA g hg hc (c*t)
  increment := fun l => metricRoot A*(t • D l)*metricRoot A
  terminal := metricRoot A*(t • F)*metricRoot A
  correction := fun _ => 0

/-- Every original individual canonical budget lifts unchanged to a
true admissible physical informed sharpness scenario, including zero
profiles, radius and scale. The prior spends exactly c*t, and all query
and independent output budgets are measured in the genuine new base.
Use: native sharpness families belong to the full original source class;
no hypothetical canonical scenario or budget-shrinking premise remains.
Article: main_krylov, thm:local(b), full actual scenario admissibility.
Proof: the real nonnegative prior base is positive with its exact known
prior budget. True root congruence preserves symmetry and recovers each
known-metric canonical form exactly. Genuine prior domination transfers
that actual budget to its own base with factor one. Corrections are zero. -/
theorem informedPhysicalScenario_admissible
    (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin (n+1))) (hg : g≠0)
    (hc : (activeSpectralValues A hA.1 g).card=n+1)
    (D : ℕ → Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (F : Matrix (Fin (n+1)) (Fin (n+1)) ℝ)
    (omega : ℕ → ℝ) (hD : ∀ l<n,(D l).IsSymm ∧ ‖D l‖≤omega l)
    (hF : F.IsSymm) (w : ℝ) (hFn : ‖F‖≤w)
    (c t : ℝ) (hc0 : 0≤c) (ht : 0≤t) :
    (informedPhysicalScenario A hA g hg hc D F c t).Admissible n A (c*t)
      (fun l => omega l*t) (w*t) 0 := by
  have hct : 0≤c*t := mul_nonneg hc0 ht
  have hs (M : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hM : M.IsSymm) :
      (metricRoot A*(t • M)*metricRoot A).IsSymm := by
    simp only [Matrix.IsSymm,Matrix.transpose_mul,(metricRoot_isSymm A).eq,
      Matrix.transpose_smul,hM.eq,Matrix.mul_assoc]
  have hb (M : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (v : ℝ) (hM : ‖M‖≤v) :
      relativeBudget A (metricRoot A*(t • M)*metricRoot A)≤v*t := by
    change ‖relativeOperator A (metricRoot A*(t • M)*metricRoot A)‖≤_
    rw [← inverseRootForm A (t • M) hA,relativeOperator_inverseRootForm A _ hA,
      norm_smul,Real.norm_of_nonneg ht]
    exact (mul_le_mul_of_nonneg_left hM ht).trans_eq (mul_comm t v)
  refine ⟨informedPriorBase_posDef A hA g hg hc (c*t) hct,
    (informedPriorBase_budget A hA g hg hc (c*t) hct).le,?_,hs F hF,?_,?_⟩
  · intro l hl
    refine ⟨hs (D l) (hD l hl).1,?_⟩
    exact informedPriorBase_budget_transfer A hA g hg hc (c*t) hct _ (hs (D l) (hD l hl).1)
      (omega l*t) (mul_nonneg ((norm_nonneg _).trans (hD l hl).2) ht) (hb (D l) (omega l) (hD l hl).2)
  · exact informedPriorBase_budget_transfer A hA g hg hc (c*t) hct _ (hs F hF)
      (w*t) (mul_nonneg ((norm_nonneg _).trans hFn) ht) (hb F w hFn)
  · intro l _
    exact ⟨Matrix.isSymm_zero,by simp only [informedPhysicalScenario,relativeBudget,relativeOperator,
      Matrix.mul_zero,Matrix.zero_mul,chebyshev1.opNorm,norm_zero,le_refl]⟩

end
end krylov.OneGradient
