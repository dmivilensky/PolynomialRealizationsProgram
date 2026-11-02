import krylov.Convergence.VirtualTensorCoordinates

/-!
Article: main_krylov, thm:V, printed coefficient estimate.
Use: retain the actual oblique-projector norms and measured amplitudes in
the tensor coefficient bound. The supplied budget is the genuine canonical
third-derivative slice norm, not an asserted output-response bound.
Source: the true orthonormal CG frame and the finite triangle inequality.
-/
namespace krylov.Convergence
noncomputable section
open Matrix Set Metric krylov.Methods krylov.Reference krylov.Functions krylov.Stability krylov.OneGradient
  krylov.Secant krylov.Envelope
open scoped InnerProductSpace BigOperators Matrix.Norms.L2Operator
variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)

/-- The original actual XRFC tensor coefficient obeys the printed
|a_l| norm(Pi_l) norm(xi_l) sum bound with its genuine canonical tensor
budget. Article: main_krylov, thm:V. -/
theorem xrfcTensorCoefficient_norm_bound
    (trial : History E → ℝ) (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (D : E →L[ℝ] E →L[ℝ] E) (u : E)
    (hc : referenceAtomCount base hb (cgOperator base u)=n) (M : ℝ)
    (hbudget : ∀ v,‖cgOperator (metricRoot base)⁻¹*(D v)*cgOperator (metricRoot base)⁻¹‖≤
      M*‖cgOperator (metricRoot base) v‖) :
    ‖xrfcTensorCoefficient trial base D u‖≤M*∑ l∈Finset.range n,
      |xrfcTrialCoefficient trial base (cgOperator base u) n l| *
      ‖cgOperator (transportedFlag (xrfcCanonicalColumns trial base (cgOperator base u)) l)‖*
      ‖cgOperator (metricRoot base) (xrfcReferenceMidpointDrift trial (cgOperator base) u l)‖ := by
  let g := cgOperator base u
  let R := cgOperator (metricRoot base)⁻¹
  let P := fun l=>cgOperator (transportedFlag (xrfcCanonicalColumns trial base g) l)
  let W := fun l=>xrfcReferenceMidpointDrift trial (cgOperator base) u l
  have ho := canonicalCGUnitStep_orthonormal base hb g n
    (fun i hi=>cg_nonstagnation base hb g i (by rw [hc];exact hi))
  rw [xrfcTensorCoefficient,xrfcStepResponse,Finset.mul_sum]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro l hl
  have hu := ho.norm_eq_one ⟨l,Finset.mem_range.mp hl⟩
  have hP : ‖cgOperator (transportedFlag (xrfcCanonicalColumns trial base g) l)ᵀ‖=‖P l‖ := by
    rw [cgOperator_transpose]
    exact ContinuousLinearMap.adjoint.norm_map _
  rw [norm_smul,Real.norm_eq_abs]
  have hstep : ‖(R*(D (W l))*R) (canonicalCGUnitStep base g l)‖≤M*‖cgOperator (metricRoot base) (W l)‖ := by
    exact ((R*(D (W l))*R).le_opNorm _).trans (by simpa only [hu,mul_one] using hbudget (W l))
  have hp := ((cgOperator (transportedFlag (xrfcCanonicalColumns trial base g) l)ᵀ).le_opNorm _).trans
    (mul_le_mul_of_nonneg_left hstep (norm_nonneg _))
  rw [hP] at hp
  exact (mul_le_mul_of_nonneg_left hp (abs_nonneg _)).trans_eq (by dsimp only [P,W,g];ring)

end
end krylov.Convergence
