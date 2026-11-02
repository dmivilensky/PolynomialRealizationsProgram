import krylov.Functions.NativeRFCFSpatialResponse
import krylov.Functions.RFCFSelfConcordantTensor
import krylov.Functions.RFCFOwnCanonical

/-!
Article: main_krylov, prop:Fcycle(i), the actual asymptotic norm bound.
Use: apply the exact tensor budget two in the TRUE minimizer Hessian metric
and bound the actual returned RFC-F gradient with its printed 4 n^(3/2)
coefficient and uniform little-o remainder. Actual first-secant drift is
handled separately by the proved own-reference transfer, never by asserting
an exact budget two in a perturbed finite-cycle metric.
Source: the genuine physical/canonical response dictionaries, actual scalar
self-concordance and the native leading-gradient theorem.
-/
namespace krylov.Functions
noncomputable section
open Matrix Set Metric krylov.Reference krylov.Nonlinear krylov.Secant
open scoped InnerProductSpace Matrix.Norms.L2Operator NNReal
variable {k : ℕ}

/-- At the true quadratic reference the independent-gradient and start-vector
RFC-F coefficients coincide exactly. Article: main_krylov, prop:Fcycle(i). -/
theorem rfcFTensorCanonicalCoefficient_eq_own
    (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (hb : base.PosDef)
    (D : EuclideanSpace ℝ (Fin (k+1)) →L[ℝ]
      EuclideanSpace ℝ (Fin (k+1)) →L[ℝ] EuclideanSpace ℝ (Fin (k+1)))
    (u : EuclideanSpace ℝ (Fin (k+1)))
    (hcount : referenceAtomCount base hb (cgOperator base u)=k+1) :
    rfcFTensorCanonicalCoefficient base hb D u=
      rfcFOwnTensorCanonicalCoefficient base hb D (cgOperator base u) := by
  have hfixed := rfcFTensorPhysicalCoefficient_eq_canonical base hb D u (by rw [hcount])
  have hown := rfcFOwnTensorPhysicalCoefficient_eq_canonical base hb D (cgOperator base u) u (by rw [hcount])
  rw [rfcFOwnTensorPhysicalCoefficient_quadratic] at hown
  exact hfixed.symm.trans hown

/-- The true-minimizer canonical RFC-F coefficient has exactly the printed
SC bound, with no perturbed-metric tensor-budget premise.
Article: main_krylov, prop:Fcycle(i). -/
theorem rfcFTensorCanonicalCoefficient_selfConcordant_bound
    (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (hb : base.PosDef)
    (f : EuclideanSpace ℝ (Fin (k+1)) → ℝ) (U : Set (EuclideanSpace ℝ (Fin (k+1))))
    (S : StandardSelfConcordantData f U) (hH₀ : S.hessian 0=cgOperator base)
    {r : ℝ} (hr : 0<r) (hU : ∀ z,‖metricCoordinates base hb z‖≤r → z∈U)
    (u : EuclideanSpace ℝ (Fin (k+1)))
    (hcount : referenceAtomCount base hb (cgOperator base u)=k+1) :
    ‖rfcFTensorCanonicalCoefficient base hb (S.variation 0) u‖≤
      ‖canonicalCGStep base (cgOperator base u) k‖*
        (4*(k+1)*Real.sqrt (k+1)*‖cgCanonicalError base (cgOperator base u) 0‖*
          ‖cgCanonicalError base (cgOperator base u) 1‖) := by
  rw [rfcFTensorCanonicalCoefficient_eq_own base hb _ u hcount]
  exact rfcFOwnTensorCanonicalCoefficient_selfConcordant_bound base hb f U S hH₀ hr hU _ hcount

/-- The actual returned gradient has the printed SC 4 n^(3/2) leading norm
bound plus a compact-uniform little-o cubic remainder, in the true minimizer
Hessian metric. This states the bound at the scalar-function level.
Article: main_krylov, prop:Fcycle(i). -/
theorem metricRFCFPoint_selfConcordant_asymptotic_norm
    (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (hb : base.PosDef) (hk : 0<k)
    (f : EuclideanSpace ℝ (Fin (k+1)) → ℝ) (U : Set (EuclideanSpace ℝ (Fin (k+1))))
    (S : StandardSelfConcordantData f U) (hG₀ : gradient f 0=0)
    (hH₀ : S.hessian 0=cgOperator base) {r : ℝ} (hr : 0<r)
    (hU : ∀ z,‖metricCoordinates base hb z‖≤r → z∈U)
    {L : ℝ≥0} (hLr : (L : ℝ)*r≤1/2)
    (hH : LipschitzOnWith L (coordinateDerivative (metricCoordinates base hb) S.hessian) (closedBall 0 r))
    (K : Set (EuclideanSpace ℝ (Fin (k+1)))) (hK : IsCompact K)
    (hcount : ∀ g∈K, referenceAtomCount base hb g=k+1)
    (R : ℝ) (hR : 0<R) :
    ∀ η : ℝ, 0<η → ∃ ep : ℝ, 0<ep ∧ ∀ ε : ℝ, 0<ε → ε<ep →
      ∀ u : EuclideanSpace ℝ (Fin (k+1)), ‖u‖≤R → cgOperator base u∈K →
      ‖cgOperator (metricRoot base)⁻¹
          (gradient f (rfcFPoint (metricCoordinates base hb) f (gradient f) r (ε • u) k))‖≤
        ε^3*(‖canonicalCGStep base (cgOperator base u) k‖*
          (4*(k+1)*Real.sqrt (k+1)*‖cgCanonicalError base (cgOperator base u) 0‖*
            ‖cgCanonicalError base (cgOperator base u) 1‖))+η*ε^3 := by
  have hzero : (0 : EuclideanSpace ℝ (Fin (k+1)))∈U :=
    hU 0 (by simpa only [map_zero,norm_zero] using hr.le)
  have hF z (hz : ‖metricCoordinates base hb z‖≤r) :
      HasFDerivAt f (innerSL ℝ (gradient f z)) z :=
    (S.differentiable.differentiableAt (S.open_domain.mem_nhds (hU z hz))).hasGradientAt.hasFDerivAt
  have hG z (hz : ‖metricCoordinates base hb z‖≤r) := S.gradient_derivative z (hU z hz)
  intro η hη
  obtain ⟨ep,hep,hbound⟩ := metricRFCFPoint_spatial_leading_gradient base hb hk f (gradient f) S.hessian
    (S.variation 0) (S.hessian_derivative 0 hzero) hr hG₀ hH₀ hLr hH hF hG K hK hcount R hR η hη
  refine ⟨ep,hep,?_⟩
  intro ε hε he u hu hKu
  have hp := hbound ε hε he u hu hKu
  have hc := rfcFTensorCanonicalCoefficient_selfConcordant_bound base hb f U S hH₀ hr hU u (hcount _ hKu)
  let v := cgOperator (metricRoot base)⁻¹
    (gradient f (rfcFPoint (metricCoordinates base hb) f (gradient f) r (ε • u) k))
  let c := rfcFTensorCanonicalCoefficient base hb (S.variation 0) u
  have hn : ‖v‖≤‖v+ε^3 • c‖+‖ε^3 • c‖ := by
    have hh := norm_sub_le (v+ε^3 • c) (ε^3 • c)
    rw [add_sub_cancel_right] at hh
    exact hh
  rw [norm_smul,Real.norm_of_nonneg (pow_nonneg hε.le 3)] at hn
  exact hn.trans ((add_le_add hp (mul_le_mul_of_nonneg_left hc (pow_nonneg hε.le 3))).trans_eq (by ring))

end
end krylov.Functions
