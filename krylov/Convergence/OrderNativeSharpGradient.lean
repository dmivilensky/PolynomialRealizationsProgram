import krylov.Convergence.OrderTensorConstants
import krylov.Functions.NativeRFCSpatialResponse

/-!
Article: main_krylov, thm:D, original sharp actual cycle constants.
Use: apply the genuine tensor Chebyshev constants to the actual scalar
FC/RFC outputs in the true minimizer metric, uniformly on compact full
references. Source: the native spatial tensor expansions and the exact
compatible-coefficient dictionaries proved in OrderTensorConstants.
-/
namespace krylov.Convergence
noncomputable section
open Matrix Set Metric Finset krylov.Methods krylov.Reference krylov.Functions krylov.Tensor
  krylov.Nonlinear krylov.Variation krylov.Stability krylov.Design krylov.Secant
open scoped InnerProductSpace NNReal Matrix.Norms.L2Operator
variable {k : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin (k+1))

/-- The genuine actual FC returned gradient has exactly the article's
printed leading constant, with compact-uniform little-o(e²) remainder.
Article: main_krylov, thm:D, FC. -/
theorem nativeFC_sharp_gradient
    (I : chebyshev1.SpectralInterval)
    (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (hb : base.PosDef)
    (f : E → ℝ) (G : E → E) (H : E → E →L[ℝ] E)
    (D : E →L[ℝ] E →L[ℝ] E) (hD : HasFDerivAt H D 0)
    {r : ℝ} (hr : 0<r) (hG₀ : G 0=0) (hH₀ : H 0=cgOperator base)
    {L : ℝ≥0} (hLr : (L:ℝ)*r≤1/2)
    (hH : LipschitzOnWith L (coordinateDerivative (metricCoordinates base hb) H) (closedBall 0 r))
    (hF : ∀ z,‖metricCoordinates base hb z‖≤r → HasFDerivAt f (innerSL ℝ (G z)) z)
    (hG : ∀ z,‖metricCoordinates base hb z‖≤r → HasFDerivAt G (H z) z)
    (T : SymmetricCubic E)
    (hT : ∀ a b c,T.form (cgOperator (metricRoot base) a) (cgOperator (metricRoot base) b)
      (cgOperator (metricRoot base) c)=inner ℝ (D a b) c)
    (m : ℝ) (hm : 0≤m) (hdiag : ∀ v,‖v‖=1 → |T.form v v v|≤2*m)
    (hband : ∀ i,I.mu≤hb.1.eigenvalues i ∧hb.1.eigenvalues i≤I.mu*I.kappa)
    (K : Set E) (hK : IsCompact K) (hcount : ∀ g∈K,referenceAtomCount base hb g=k+1)
    (B : ℝ) (hB : 0<B) :
    ∀ η : ℝ,0<η →∃ ep : ℝ,0<ep ∧∀ ε : ℝ,0<ε → ε<ep →∀ u,‖u‖≤B → cgOperator base u∈K →
      ‖cgOperator (metricRoot base) u‖=1 →
      ‖cgOperator (metricRoot base)⁻¹ (G (metricFCPoint (metricCoordinates base hb) f G fullMemory r (ε • u) (k+1)))‖≤
        (m*fcRestartConstant (designSpacing I) k+η)*ε^2 := by
  intro η hη
  obtain ⟨ep,hep,hbound⟩:=metricFCPoint_spatial_leading_gradient base hb f G H D hD hr hG₀ hH₀ hLr hH hF hG
    K hK hcount B hB η hη
  refine ⟨ep,hep,?_⟩
  intro ε hε he u hu hKu hunit
  have hrem:=hbound ε hε he u hu hKu
  have hcoef:=fc_spatial_tensor_restart_constant I base hb D T hT m hm hdiag hband u (hcount _ hKu) hunit
  have hn:=norm_le_norm_sub_add
    (cgOperator (metricRoot base)⁻¹ (G (metricFCPoint (metricCoordinates base hb) f G fullMemory r (ε • u) (k+1))))
    (ε^2 • fullCycleResponse base (cgOperator base u) (range (k+1)) (fcCompatibleIncrements base hb D u))
  rw [norm_smul,Real.norm_of_nonneg (sq_nonneg ε)] at hn
  exact hn.trans ((add_le_add hrem (mul_le_mul_of_nonneg_left hcoef (sq_nonneg ε))).trans_eq (by ring))

/-- The genuine actual RFC returned gradient has exactly the article's
printed cubic constant, with compact-uniform little-o(e³) remainder.
Article: main_krylov, thm:D, RFC. -/
theorem nativeRFC_sharp_gradient
    (I : chebyshev1.SpectralInterval)
    (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (hb : base.PosDef) (hk : 0<k)
    (f : E → ℝ) (G : E → E) (H : E → E →L[ℝ] E)
    (D : E →L[ℝ] E →L[ℝ] E) (hD : HasFDerivAt H D 0)
    {r : ℝ} (hr : 0<r) (hG₀ : G 0=0) (hH₀ : H 0=cgOperator base)
    {L : ℝ≥0} (hLr : (L:ℝ)*r≤1/2)
    (hH : LipschitzOnWith L (coordinateDerivative (metricCoordinates base hb) H) (closedBall 0 r))
    (hF : ∀ z,‖metricCoordinates base hb z‖≤r → HasFDerivAt f (innerSL ℝ (G z)) z)
    (hG : ∀ z,‖metricCoordinates base hb z‖≤r → HasFDerivAt G (H z) z)
    (T : SymmetricCubic E)
    (hT : ∀ a b c,T.form (cgOperator (metricRoot base) a) (cgOperator (metricRoot base) b)
      (cgOperator (metricRoot base) c)=inner ℝ (D a b) c)
    (m : ℝ) (hm : 0≤m) (hdiag : ∀ v,‖v‖=1 → |T.form v v v|≤2*m)
    (hband : ∀ i,I.mu≤hb.1.eigenvalues i ∧hb.1.eigenvalues i≤I.mu*I.kappa)
    (K : Set E) (hK : IsCompact K) (hcount : ∀ g∈K,referenceAtomCount base hb g=k+1)
    (B : ℝ) (hB : 0<B) :
    ∀ η : ℝ,0<η →∃ ep : ℝ,0<ep ∧∀ ε : ℝ,0<ε → ε<ep →∀ u,‖u‖≤B → cgOperator base u∈K →
      ‖cgOperator (metricRoot base) u‖=1 →
      ‖cgOperator (metricRoot base)⁻¹ (G (rfcFunctionPoint (metricCoordinates base hb) f G fullMemory r (ε • u) (k+1)))‖≤
        (m^2*rfcRestartConstant (designSpacing I) k+η)*ε^3 := by
  intro η hη
  obtain ⟨ep,hep,hbound⟩:=metricRFCPoint_spatial_leading_gradient base hb hk f G H D hD hr hG₀ hH₀ hLr hH hF hG
    K hK hcount B hB η hη
  refine ⟨ep,hep,?_⟩
  intro ε hε he u hu hKu hunit
  have hrem:=hbound ε hε he u hu hKu
  have hcoef:=rfc_spatial_tensor_restart_constant I base hb D T hT m hm hdiag hband u (hcount _ hKu) hunit
  have hn:=norm_le_norm_sub_add
    (cgOperator (metricRoot base)⁻¹ (G (rfcFunctionPoint (metricCoordinates base hb) f G fullMemory r (ε • u) (k+1))))
    (-(ε^3 • rfcTensorCanonicalCoefficient base hb D u))
  rw [sub_neg_eq_add,norm_neg,norm_smul,Real.norm_of_nonneg (pow_nonneg hε.le 3)] at hn
  exact hn.trans ((add_le_add hrem (mul_le_mul_of_nonneg_left hcoef (pow_nonneg hε.le 3))).trans_eq (by ring))

end
end krylov.Convergence
