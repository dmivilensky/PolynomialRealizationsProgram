import krylov.Convergence.VirtualTensorBound
import krylov.Convergence.RestartChebyshevProfile
import krylov.Functions.RFCFPrintedTensor

/-!
Article: main_krylov, thm:V, genuine tensor-norm bound.
Use: discharge the canonical slice budget from the original diagonal
norm of the actual symmetric third tensor, using Banach's theorem already
formalized in the common tensor library.
Source: genuine physical/canonical tensor coordinates and cubic polarization.
-/
namespace krylov.Convergence
noncomputable section
open Matrix Set krylov.Methods krylov.Reference krylov.Functions krylov.Secant krylov.OneGradient krylov.Envelope
open scoped InnerProductSpace BigOperators Matrix.Norms.L2Operator
variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)

/-- A genuine physical third derivative has exactly the true canonical
Riesz tensor slice after the real inverse-root congruence. Article: thm:V. -/
theorem canonical_third_slice_eq
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (D : E →L[ℝ] E →L[ℝ] E) (T : SymmetricCubic E)
    (hT : ∀ a b c,T.form (cgOperator (metricRoot base) a) (cgOperator (metricRoot base) b)
      (cgOperator (metricRoot base) c)=inner ℝ (D a b) c) (v : E) :
    cgOperator (metricRoot base)⁻¹*(D v)*cgOperator (metricRoot base)⁻¹=
      canonicalVariation T (cgOperator (metricRoot base) v) := by
  rw [←cubicSliceMatrix_operator,←physicalCanonicalMatrix_third_tensor base hb D T hT]
  change _=Matrix.toEuclideanCLM (𝕜:=ℝ) (physicalCanonicalMatrix base hb (D v))
  rw [physicalCanonicalMatrix_operator]
  rfl

/-- Actual canonical third-derivative slices satisfy the original tensor
budget directly from the true diagonal cubic norm. Article: thm:V. -/
theorem canonical_third_slice_bound
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (D : E →L[ℝ] E →L[ℝ] E) (T : SymmetricCubic E)
    (hT : ∀ a b c,T.form (cgOperator (metricRoot base) a) (cgOperator (metricRoot base) b)
      (cgOperator (metricRoot base) c)=inner ℝ (D a b) c)
    (M : ℝ) (hM : 0≤M) (hdiag : ∀ v,‖v‖=1 →|T.form v v v|≤M) (v : E) :
    ‖cgOperator (metricRoot base)⁻¹*(D v)*cgOperator (metricRoot base)⁻¹‖≤
      M*‖cgOperator (metricRoot base) v‖ := by
  rw [canonical_third_slice_eq base hb D T hT]
  exact cubic_slice_norm_le T M hM hdiag _

/-- The printed XRFC tensor estimate uses the genuine diagonal third
norm, with no independent slice-budget assumption.
Article: main_krylov, thm:V, Banach-norm estimate. -/
theorem xrfcTensorCoefficient_diagonal_norm_bound
    (trial : History E → ℝ) (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (D : E →L[ℝ] E →L[ℝ] E) (T : SymmetricCubic E)
    (hT : ∀ a b c,T.form (cgOperator (metricRoot base) a) (cgOperator (metricRoot base) b)
      (cgOperator (metricRoot base) c)=inner ℝ (D a b) c)
    (u : E) (hc : referenceAtomCount base hb (cgOperator base u)=n)
    (M : ℝ) (hM : 0≤M) (hdiag : ∀ v,‖v‖=1 →|T.form v v v|≤M) :
    ‖xrfcTensorCoefficient trial base D u‖≤M*∑ l∈Finset.range n,
      |xrfcTrialCoefficient trial base (cgOperator base u) n l| *
      ‖cgOperator (transportedFlag (xrfcCanonicalColumns trial base (cgOperator base u)) l)‖*
      ‖cgOperator (metricRoot base) (xrfcReferenceMidpointDrift trial (cgOperator base) u l)‖ :=
  xrfcTensorCoefficient_norm_bound trial base hb D u hc M
    (canonical_third_slice_bound base hb D T hT M hM hdiag)

end
end krylov.Convergence
