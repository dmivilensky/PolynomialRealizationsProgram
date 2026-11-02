import krylov.Convergence.VirtualDirectionTensorCoordinates
import krylov.Convergence.VirtualTensorBanach

/-!
Article: main_krylov, thm:V, original direction-basis tensor estimate.
Use: bound the true scalar-cycle direction response with Pi_l=I using
only the actual symmetric canonical cubic's diagonal spectral budget.
Source: the true orthonormal CG frame, Banach's symmetric tensor identity
already proved in the tensor library, and the finite triangle inequality.
-/
namespace krylov.Convergence
noncomputable section
open Matrix Set krylov.Methods krylov.Reference krylov.Functions krylov.OneGradient krylov.Secant krylov.Envelope
open scoped InnerProductSpace BigOperators Matrix.Norms.L2Operator
variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)

/-- The actual native direction-basis coefficient has exactly the
article's no-oblique-factor norm bound. Article: main_krylov, thm:V. -/
theorem xrfcDTensorCoefficient_norm_bound
    (trial : History E → ℝ) (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (D : E →L[ℝ] E →L[ℝ] E) (u : E)
    (hc : referenceAtomCount base hb (cgOperator base u)=n) (M : ℝ)
    (hbudget : ∀ v,‖cgOperator (metricRoot base)⁻¹*(D v)*cgOperator (metricRoot base)⁻¹‖≤
      M*‖cgOperator (metricRoot base) v‖) :
    ‖xrfcDTensorCoefficient trial base D u‖≤M*∑ l∈Finset.range n,
      |xrfcTrialCoefficient trial base (cgOperator base u) n l| *
      ‖cgOperator (metricRoot base) (xrfcDReferenceMidpointDrift trial (cgOperator base) u l)‖ := by
  have ho:=canonicalCGUnitStep_orthonormal base hb (cgOperator base u) n
    (fun i hi=>cg_nonstagnation base hb (cgOperator base u) i (by rw [hc];exact hi))
  rw [xrfcDTensorCoefficient,xrfcDirectionResponse,Finset.mul_sum]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro l hl
  have hu:=ho.norm_eq_one ⟨l,Finset.mem_range.mp hl⟩
  rw [norm_smul,Real.norm_eq_abs]
  have hs:=((cgOperator (metricRoot base)⁻¹*(D (xrfcDReferenceMidpointDrift trial (cgOperator base) u l))*
      cgOperator (metricRoot base)⁻¹).le_opNorm (canonicalCGUnitStep base (cgOperator base u) l)).trans
    (by simpa only [hu,mul_one] using hbudget (xrfcDReferenceMidpointDrift trial (cgOperator base) u l))
  exact (mul_le_mul_of_nonneg_left hs (abs_nonneg _)).trans_eq (by ring)

/-- The no-Pi estimate follows directly from the actual canonical
symmetric cubic diagonal budget by the proved Banach identity.
Article: main_krylov, thm:V, direction-basis norm estimate. -/
theorem xrfcDTensorCoefficient_diagonal_norm_bound
    (trial : History E → ℝ) (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (D : E →L[ℝ] E →L[ℝ] E) (T : SymmetricCubic E)
    (hT : ∀ a b c,T.form (cgOperator (metricRoot base) a) (cgOperator (metricRoot base) b)
      (cgOperator (metricRoot base) c)=inner ℝ (D a b) c)
    (u : E) (hc : referenceAtomCount base hb (cgOperator base u)=n)
    (M : ℝ) (hM : 0≤M) (hdiag : ∀ v,‖v‖=1 → |T.form v v v|≤M) :
    ‖xrfcDTensorCoefficient trial base D u‖≤M*∑ l∈Finset.range n,
      |xrfcTrialCoefficient trial base (cgOperator base u) n l| *
      ‖cgOperator (metricRoot base) (xrfcDReferenceMidpointDrift trial (cgOperator base) u l)‖ :=
  xrfcDTensorCoefficient_norm_bound trial base hb D u hc M
    (canonical_third_slice_bound base hb D T hT M hM hdiag)

end
end krylov.Convergence
