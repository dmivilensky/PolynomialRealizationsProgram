import krylov.Convergence.RestartRFCChebyshevProfile
import krylov.Functions.MetricFCSpatialResponse

/-!
Article: main_krylov, thm:D, true-minimizer tensor coefficients.
Use: connect the actual spatial native FC/RFC coefficients to the sharp
Chebyshev restart bounds already proved for genuine independent-gradient
references. The original canonical unit initial error fixes the scale.
Source: exact physical midpoint identities and original CG root transport.
-/
namespace krylov.Convergence
noncomputable section
open Matrix Set Finset krylov.Methods krylov.Reference krylov.Functions krylov.Tensor
  krylov.Variation krylov.Stability krylov.Design krylov.LinearAlgebra krylov.Secant krylov.Envelope
open scoped InnerProductSpace BigOperators Matrix.Norms.L2Operator
variable {k : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin (k+1))

/-- Actual fixed-Hstar and independent-gradient FC midpoint increments
coincide exactly at the true reference gradient Qu. Article: thm:D. -/
theorem fcCompatibleIncrements_eq_own
    (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (hb : base.PosDef)
    (D : E →L[ℝ] E →L[ℝ] E) (u : E) :
    fcCompatibleIncrements base hb D u=ownFCCompatibleIncrements base hb D (cgOperator base u) := by
  funext l
  rw [fcCompatibleIncrements,ownFCCompatibleIncrements,←physicalCanonicalMatrix_sub,←map_sub]
  apply congrArg (fun v=>physicalCanonicalMatrix base hb (D v))
  exact fcOwnReferenceMidpoint_sub (cgOperator base) (cgOperator base u) u l

/-- The actual spatial native RFC coefficient is exactly the already
bounded independent-gradient coefficient. Article: thm:D. -/
theorem rfcTensorCanonicalCoefficient_eq_own
    (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (hb : base.PosDef)
    (D : E →L[ℝ] E →L[ℝ] E) (u : E) :
    rfcTensorCanonicalCoefficient base hb D u=rfcOwnTensorCanonicalCoefficient base hb D (cgOperator base u) := rfl

/-- The real canonical unit start supplies a genuine FCReference with
exact initial error norm one. Article: thm:D. -/
def orderUnitReference (I : chebyshev1.SpectralInterval)
    (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (hb : base.PosDef)
    (u : E) (hc : referenceAtomCount base hb (cgOperator base u)=k+1)
    (hband : ∀ i,I.mu≤hb.1.eigenvalues i ∧hb.1.eigenvalues i≤I.mu*I.kappa) :
    FCReference (k+1) I.mu I.kappa where
  base:=base
  positive:=hb
  gradient:=cgOperator base u
  nonzero:=cg_nonstagnation base hb (cgOperator base u) 0 (by rw [hc];omega)
  full:=hc
  interval:=hband

/-- The original initial canonical norm is exactly the physical metric
norm of the initial error direction. Article: thm:D. -/
theorem orderUnitReference_initialNorm
    (I : chebyshev1.SpectralInterval)
    (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (hb : base.PosDef)
    (u : E) (hc : referenceAtomCount base hb (cgOperator base u)=k+1)
    (hband : ∀ i,I.mu≤hb.1.eigenvalues i ∧hb.1.eigenvalues i≤I.mu*I.kappa) :
    (orderUnitReference I base hb u hc hband).initialNorm=‖cgOperator (metricRoot base) u‖ := by
  change ‖cgOperator (metricRoot base)⁻¹ (cgOperator base u)‖=_
  exact congrArg norm (canonical_reference_action base hb u)

/-- Actual FC's canonical coefficient has the printed restart constant
at every true metric-unit full reference. Article: thm:D, FC. -/
theorem fc_spatial_tensor_restart_constant
    (I : chebyshev1.SpectralInterval)
    (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (hb : base.PosDef)
    (D : E →L[ℝ] E →L[ℝ] E) (T : SymmetricCubic E)
    (hT : ∀ a b c,T.form (cgOperator (metricRoot base) a) (cgOperator (metricRoot base) b)
      (cgOperator (metricRoot base) c)=inner ℝ (D a b) c)
    (m : ℝ) (hm : 0≤m) (hdiag : ∀ v,‖v‖=1 → |T.form v v v|≤2*m)
    (hband : ∀ i,I.mu≤hb.1.eigenvalues i ∧hb.1.eigenvalues i≤I.mu*I.kappa)
    (u : E) (hc : referenceAtomCount base hb (cgOperator base u)=k+1)
    (hu : ‖cgOperator (metricRoot base) u‖=1) :
    ‖fullCycleResponse base (cgOperator base u) (range (k+1)) (fcCompatibleIncrements base hb D u)‖≤
      m*fcRestartConstant (designSpacing I) k := by
  have hh:=fc_tensor_chebyshev_constant I (orderUnitReference I base hb u hc hband) D T hT m hm hdiag
  rw [orderUnitReference_initialNorm,hu,one_pow,mul_one] at hh
  rw [fcCompatibleIncrements_eq_own]
  exact hh

/-- Actual RFC's canonical coefficient has the printed cubic restart
constant at every true metric-unit full reference. Article: thm:D, RFC. -/
theorem rfc_spatial_tensor_restart_constant
    (I : chebyshev1.SpectralInterval)
    (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (hb : base.PosDef)
    (D : E →L[ℝ] E →L[ℝ] E) (T : SymmetricCubic E)
    (hT : ∀ a b c,T.form (cgOperator (metricRoot base) a) (cgOperator (metricRoot base) b)
      (cgOperator (metricRoot base) c)=inner ℝ (D a b) c)
    (m : ℝ) (hm : 0≤m) (hdiag : ∀ v,‖v‖=1 → |T.form v v v|≤2*m)
    (hband : ∀ i,I.mu≤hb.1.eigenvalues i ∧hb.1.eigenvalues i≤I.mu*I.kappa)
    (u : E) (hc : referenceAtomCount base hb (cgOperator base u)=k+1)
    (hu : ‖cgOperator (metricRoot base) u‖=1) :
    ‖rfcTensorCanonicalCoefficient base hb D u‖≤m^2*rfcRestartConstant (designSpacing I) k := by
  have hh:=rfc_tensor_chebyshev_constant I (orderUnitReference I base hb u hc hband) D T hT m hm hdiag
  rw [orderUnitReference_initialNorm,hu,one_pow,mul_one] at hh
  rw [rfcTensorCanonicalCoefficient_eq_own]
  exact hh

end
end krylov.Convergence
