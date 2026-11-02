import krylov.OneGradient.InformedPhysicalOperators
import krylov.OneGradient.ScenarioCanonicalIncrements
set_option autoImplicit false
/-!
Article: main_krylov, thm:local(b), exact genuine physical attaining parameters.
Use: native physical source families have exactly their intended actual
known-frame canonical prior, individual increments and independent output.
Source: genuine physical prior alignment, exact source extension increments
and actual positive-root congruence cancellation.
-/

namespace krylov.OneGradient
noncomputable section
open Matrix krylov.Reference krylov.Methods krylov.Secant krylov.Information
open scoped Matrix.Norms.L2Operator
variable {n : ℕ}

/-- Every actual known-frame canonical increment of the genuine physical
attaining family is its original scale times its real canonical witness;
the independent output slot contains F and all later slots are zero.
Use: homogeneity of the source coefficient applies to the actual operators.
Article: main_krylov, thm:local(b), exact physical attainer increments.
Proof: the true source/native increment dictionary selects the original
query or terminal form. The actual known root congruence cancels exactly. -/
theorem informedPhysicalScenario_canonical_increments
    (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin (n+1))) (hg : g≠0)
    (hc : (activeSpectralValues A hA.1 g).card=n+1)
    (D : ℕ → Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (F : Matrix (Fin (n+1)) (Fin (n+1)) ℝ)
    (c t : ℝ) (l : ℕ) :
    let S := informedPhysicalScenario A hA g hg hc D F c t
    canonicalIncrement A (oneGradientScenarioMatrices S n) l=
      t • (if l<n then D l else if l=n then F else 0) := by
  dsimp only
  rw [oneGradientScenarioMatrices_canonicalIncrement]
  have hform (M : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) :
      relativeOperator A (metricRoot A*(t • M)*metricRoot A)=t • M := by
    rw [← inverseRootForm A (t • M) hA,relativeOperator_inverseRootForm A _ hA]
  by_cases hl : l<n
  · simp only [ite_eq_left hl,informedPhysicalScenario,hform]
  · simp only [ite_eq_right hl]
    by_cases he : l=n
    · simp only [ite_eq_left he,informedPhysicalScenario,hform]
    · simp only [ite_eq_right he,smul_zero]

/-- The actual physical attaining prior in the native operator extension
is exactly scale times any canonical rank-one source prior attainer with
the genuine known last-CG axis and prior coefficient c.
Use: native output homogeneity uses the actual physical base displacement,
rather than assuming the intended canonical prior is realized.
Article: main_krylov, thm:local(b), exact actual prior witness realization.
Proof: the first native matrix is the real scenario base. The genuine
physical prior has known-frame form c*t times the true last-axis projector.
The exact real matrix/operator equivalence identifies this with t*R. -/
theorem informedPhysicalScenario_canonical_prior
    (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin (n+1))) (hg : g≠0)
    (hc : (activeSpectralValues A hA.1 g).card=n+1)
    (D : ℕ → Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (F R : Matrix (Fin (n+1)) (Fin (n+1)) ℝ)
    (c t : ℝ) (hR : cgOperator R=c • InnerProductSpace.rankOne ℝ
      (canonicalCGUnitStep A g n) (canonicalCGUnitStep A g n)) :
    let S := informedPhysicalScenario A hA g hg hc D F c t
    relativeOperator A (oneGradientScenarioMatrices S n 0-A)=t • R := by
  dsimp only
  rw [oneGradientScenarioMatrices_zero]
  apply (Matrix.toEuclideanCLM (n := Fin (n+1)) (𝕜 := ℝ)).injective
  change cgOperator (relativeOperator A (informedPriorBase A hA g hg hc (c*t)-A))=cgOperator (t • R)
  rw [informedPriorBase_known_canonical_form]
  simp only [cgOperator,map_smul] at hR ⊢
  rw [hR,smul_smul,mul_comm c t]

end
end krylov.OneGradient
