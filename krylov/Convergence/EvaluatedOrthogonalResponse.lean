import krylov.Convergence.EvaluatedTensorCubic
import krylov.OneGradient.InformedStaircase

/-!
Article: main_krylov, prop:EL, original orthogonal-flag formula.
Use: identify the genuine evaluated-launch compression response with the
printed old-CG-projection staircase and its full accumulated trial miss.
Source: actual evaluated columns, nonzero diagonal covariance and full CG basis.
-/
namespace krylov.Convergence
noncomputable section
open Matrix Finset krylov.Methods krylov.Reference krylov.Functions krylov.OneGradient krylov.Secant
  krylov.Correction krylov.Variation
open scoped InnerProductSpace BigOperators Matrix.Norms.L2Operator
variable {k : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin (k+1))

/-- The original evaluated-launch coefficient is exactly the printed
orthogonal staircase, including its uncompressed final source slice.
Article: main_krylov, prop:EL. -/
theorem evaluatedLaunchResponse_eq_orthogonal
    (trial : History E → ℝ) (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (hb : base.PosDef)
    (g : E) (hc : referenceAtomCount base hb g=k+1)
    (ht : ∀ i<k+1,trial (oneGradientRun (evaluatedLaunchMethod trial) (fun _=>cgOperator base) g i)≠0)
    (A : ℕ → E →L[ℝ] E) :
    evaluatedLaunchResponse trial base g A=
      ((∑ l∈range k,(oldFlag base g l).starProjection*A l*(oldFlag base g l).starProjection)+A k)
        (∑ i∈range (k+1),(evaluatedTrialError trial base g i*Real.sqrt (cgEnergy base g i)) •
          canonicalCGUnitStep base g i) := by
  have hP (l : ℕ) : cgOperator (transportedFlag (evaluatedCanonicalColumns trial base g) l)=
      (oldFlag base g l).starProjection := evaluated_canonical_flags trial base hb g hc ht l
  have hPt (l : ℕ) : cgOperator (transportedFlag (evaluatedCanonicalColumns trial base g) l)ᵀ=
      (oldFlag base g l).starProjection := by
    rw [cgOperator_transpose,hP]
    exact (Submodule.starProjection_isSymmetric _).clm_adjoint_eq
  unfold evaluatedLaunchResponse
  simp_rw [hP,hPt]
  rw [sum_range_succ,fullCG_last_projection base hb g hc,one_mul,mul_one]

end
end krylov.Convergence
