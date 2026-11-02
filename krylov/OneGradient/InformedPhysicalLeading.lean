import krylov.OneGradient.SourcePivotHomogeneity
import krylov.OneGradient.InformedPhysicalParameters
set_option autoImplicit false
/-!
Article: main_krylov, thm:local(b), actual physical informed leading vector.
Use: original physical attaining scenarios execute the genuine informed
method with their exact correlated source coefficient and cubic remainder.
Source: true physical prior/increment realization, exact coefficient
homogeneity, primitive source operator data and genuine source output theorem.
-/

namespace krylov.OneGradient
noncomputable section
open Matrix Finset Filter Topology Asymptotics krylov.Reference krylov.Methods krylov.Secant
  krylov.Information krylov.Correction krylov.Envelope
open scoped BigOperators InnerProductSpace Matrix.Norms.L2Operator
variable {n : ℕ}

/-- The complete correlated coefficient of the actual physical source
family is exactly t² times its original known-reference matrix witness.
Use: sharpness is realized by genuine original physical source parameters,
including zero scales, rather than a postulated canonical response field.
Article: main_krylov, thm:local(b), exact physical attaining coefficient.
Proof: the real prior is t*R in the genuine known last-CG axis; actual
query/output canonical forms are t*D and t*F. Apply the exact source
parameter dictionary and original quadratic coefficient homogeneity. -/
theorem informedPhysicalScenario_leading
    (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin (n+1))) (hg : g≠0)
    (hc : (activeSpectralValues A hA.1 g).card=n+1)
    (D : ℕ → Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (R F : Matrix (Fin (n+1)) (Fin (n+1)) ℝ)
    (c t : ℝ) (hR : cgOperator R=c • InnerProductSpace.rankOne ℝ
      (canonicalCGUnitStep A g n) (canonicalCGUnitStep A g n)) :
    informedSourcePivotCoefficient A g (informedPhysicalScenario A hA g hg hc D F c t)=
      t^2 • informedReferencePivotCoefficient A g D R F := by
  let S := informedPhysicalScenario A hA g hg hc D F c t
  have hprior : relativeOperator A (S.base-A)=t • R := by
    simpa only [oneGradientScenarioMatrices_zero] using
      informedPhysicalScenario_canonical_prior A hA g hg hc D F R c t hR
  have hquery (l : ℕ) (hl : l<n) : canonicalIncrement A (oneGradientScenarioMatrices S n) l=t • D l := by
    simpa only [ite_eq_left hl] using informedPhysicalScenario_canonical_increments A hA g hg hc D F c t l
  have hterm : canonicalIncrement A (oneGradientScenarioMatrices S n) n=t • F := by
    simpa only [lt_self_iff_false,ite_false,ite_true] using informedPhysicalScenario_canonical_increments A hA g hg hc D F c t n
  rw [informedSourcePivotCoefficient_of_parameters A g S (fun l => t • D l) (t • R) (t • F) hprior hquery hterm]
  exact informedReferencePivotCoefficient_smul A g D R F t

/-- The actual informed S output on the genuine physical attaining
source family has its exact scale-squared full correlated leading vector
and a cubic real-scale remainder, from primitive physical data alone.
Use: original physical sharpness concerns the true executed method and
its true source-oracle output, with all native domains and fields derived.
Article: main_krylov, thm:local(b), genuine physical native output expansion.
Proof: the true affine physical source matrices have derived C-one
regularity, symmetry and actual known quadratic reference. Reuse the
general genuine source output cubic theorem. The physical parameter
dictionary and exact coefficient homogeneity identify its real leading vector. -/
theorem informedPhysicalScenario_output_cubic_basis (directions : Bool)
    (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin (n+1))) (hg : g≠0)
    (hc : (activeSpectralValues A hA.1 g).card=n+1)
    (D : ℕ → Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (R F : Matrix (Fin (n+1)) (Fin (n+1)) ℝ)
    (hD : ∀ l<n,(D l).IsSymm) (hF : F.IsSymm) (c : ℝ)
    (hR : cgOperator R=c • InnerProductSpace.rankOne ℝ
      (canonicalCGUnitStep A g n) (canonicalCGUnitStep A g n)) :
    (fun t : ℝ => cgOperator (metricRoot A)⁻¹
      (informedScenarioOutput directions A g (informedPhysicalScenario A hA g hg hc D F c t))+
        t^2 • (‖cgCanonicalError A g n‖ • informedReferencePivotCoefficient A g D R F))
      =O[𝓝 0] (fun t => ‖t‖^3) := by
  let S := fun t => informedPhysicalScenario A hA g hg hc D F c t
  have hdata := informedPhysicalScenario_operator_data A hA g hg hc D F hD hF c
  have h := informed_basis_scenario_output_cubic directions A hA g (full_gradient_atom_count A hA g hc) S
    hdata.1 hdata.2.1 hdata.2.2
  apply h.congr_left
  intro t
  rw [informedPhysicalScenario_leading A hA g hg hc D R F c t hR,smul_comm]

/-- The original S specialization of the common native-basis theorem.
Use: preserve the established step-policy physical source interface.
Article: main_krylov, thm:local(b).
Proof: specialize the shared genuine physical theorem to the S basis. -/
theorem informedPhysicalScenario_output_cubic
    (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin (n+1))) (hg : g≠0)
    (hc : (activeSpectralValues A hA.1 g).card=n+1)
    (D : ℕ → Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (R F : Matrix (Fin (n+1)) (Fin (n+1)) ℝ)
    (hD : ∀ l<n,(D l).IsSymm) (hF : F.IsSymm) (c : ℝ)
    (hR : cgOperator R=c • InnerProductSpace.rankOne ℝ
      (canonicalCGUnitStep A g n) (canonicalCGUnitStep A g n)) :
    (fun t : ℝ => cgOperator (metricRoot A)⁻¹
      (informedScenarioOutput false A g (informedPhysicalScenario A hA g hg hc D F c t))+
        t^2 • (‖cgCanonicalError A g n‖ • informedReferencePivotCoefficient A g D R F))
      =O[𝓝 0] (fun t => ‖t‖^3)  := by
  exact informedPhysicalScenario_output_cubic_basis false A hA g hg hc D R F hD hF c hR

end
end krylov.OneGradient
