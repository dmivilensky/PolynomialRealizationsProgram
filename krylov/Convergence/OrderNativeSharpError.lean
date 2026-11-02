import krylov.Convergence.OrderNativeSharpGradient
import krylov.Convergence.OrderGradientErrorTransfer
import krylov.Convergence.RestartedFC
import krylov.Convergence.RestartedRFCCubic

/-!
Article: main_krylov, thm:D, printed actual FC/RFC cycle error constants.
Use: retain the sharp Chebyshev coefficients for the actual true metric
errors, rather than only returned gradients. All native point bounds and
Taylor normalization estimates are derived from original function data.
Source: genuine scalar native localization, the proved sharp returned
coefficients, and the uniform true-gradient/error Taylor transfer.
-/
namespace krylov.Convergence
noncomputable section
open Matrix Set Metric Finset krylov.Methods krylov.Reference krylov.Functions krylov.Tensor
  krylov.Nonlinear krylov.Variation krylov.Stability krylov.Design krylov.Secant
open scoped InnerProductSpace NNReal Matrix.Norms.L2Operator
variable {k : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin (k+1))

/-- The original printed FC constant bounds the actual scalar cycle metric error.
Article: main_krylov, thm:D. -/
theorem nativeFC_sharp_error
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
      ‖metricCoordinates base hb (metricFCPoint (metricCoordinates base hb) f G fullMemory r (ε • u) (k+1))‖≤
        (m*fcRestartConstant (designSpacing I) k+η)*ε^2 := by
  let admission:=fun u : E=>‖u‖≤B ∧cgOperator base u∈K ∧‖cgOperator (metricRoot base) u‖=1
  let point:=fun (ε : ℝ) (u : E)=>metricFCPoint (metricCoordinates base hb) f G fullMemory r (ε • u) (k+1)
  have hpoint : ∃ ep M : ℝ,0<ep ∧0<M ∧∀ ε : ℝ,0<ε → ε<ep →∀ u,admission u →
      ‖metricCoordinates base hb (point ε u)‖≤M*ε^2 := by
    obtain ⟨ep,C,hep,hC,hbound⟩:=nativeFC_error_quadratic base hb (metricCoordinates base hb)
      (metricCoordinates_inverse_symmetric base hb) f G H hr hG₀ hH₀
      (coordinateDerivative_metric_zero base hb H hH₀) hLr hH hF hG K hK
      (fun g hg i hi=>cg_nonstagnation base hb g i (by rw [hcount g hg];exact hi)) B hB
    exact ⟨ep,C,hep,hC,fun ε hε he u hu=>hbound ε hε he u hu.1 hu.2.1⟩
  have hgradient : ∀ η : ℝ,0<η →∃ ep : ℝ,0<ep ∧∀ ε : ℝ,0<ε → ε<ep →∀ u,admission u →
      ‖cgOperator (metricRoot base)⁻¹ (G (point ε u))‖≤(m*fcRestartConstant (designSpacing I) k+η)*ε^2 := by
    intro η hη
    obtain ⟨ep,hep,hbound⟩:=nativeFC_sharp_gradient I base hb f G H D hD hr hG₀ hH₀ hLr hH hF hG
      T hT m hm hdiag hband K hK hcount B hB η hη
    exact ⟨ep,hep,fun ε hε he u hu=>hbound ε hε he u hu.1 hu.2.1 hu.2.2⟩
  have htransfer:=actual_metric_error_of_gradient_asymptotic base hb G H hr hG₀ hH₀ hH hG
    point admission 2 (Or.inl rfl) (m*fcRestartConstant (designSpacing I) k) hpoint hgradient
  intro η hη
  obtain ⟨ep,hep,hbound⟩:=htransfer η hη
  exact ⟨ep,hep,fun ε hε he u hu hKu hunit=>hbound ε hε he u ⟨hu,hKu,hunit⟩⟩

/-- The original printed RFC constant bounds the actual scalar cycle metric error.
Article: main_krylov, thm:D. -/
theorem nativeRFC_sharp_error
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
      ‖metricCoordinates base hb (rfcFunctionPoint (metricCoordinates base hb) f G fullMemory r (ε • u) (k+1))‖≤
        (m^2*rfcRestartConstant (designSpacing I) k+η)*ε^3 := by
  let admission:=fun u : E=>‖u‖≤B ∧cgOperator base u∈K ∧‖cgOperator (metricRoot base) u‖=1
  let point:=fun (ε : ℝ) (u : E)=>rfcFunctionPoint (metricCoordinates base hb) f G fullMemory r (ε • u) (k+1)
  have hpoint : ∃ ep M : ℝ,0<ep ∧0<M ∧∀ ε : ℝ,0<ε → ε<ep →∀ u,admission u →
      ‖metricCoordinates base hb (point ε u)‖≤M*ε^2 := by
    obtain ⟨ep,C,hep,hC,hbound⟩:=nativeRFC_error_cubic base hb hk (metricCoordinates base hb)
      (metricCoordinates_inverse_symmetric base hb) f G H hr hG₀ hH₀
      (coordinateDerivative_metric_zero base hb H hH₀) hLr hH hF hG K hK
      (fun g hg i hi=>cg_nonstagnation base hb g i (by rw [hcount g hg];omega)) B hB
    refine ⟨min ep 1,C,by positivity,hC,?_⟩
    intro ε hε he u hu
    have hh:=hbound ε hε (he.trans_le (min_le_left _ _)) u hu.1 hu.2.1
    have he1 : ε≤1 := he.le.trans (min_le_right _ _)
    exact hh.trans (mul_le_mul_of_nonneg_left (by nlinarith only [mul_le_mul_of_nonneg_right he1 (sq_nonneg ε)] : ε^3≤ε^2) hC.le)
  have hgradient : ∀ η : ℝ,0<η →∃ ep : ℝ,0<ep ∧∀ ε : ℝ,0<ε → ε<ep →∀ u,admission u →
      ‖cgOperator (metricRoot base)⁻¹ (G (point ε u))‖≤(m^2*rfcRestartConstant (designSpacing I) k+η)*ε^3 := by
    intro η hη
    obtain ⟨ep,hep,hbound⟩:=nativeRFC_sharp_gradient I base hb hk f G H D hD hr hG₀ hH₀ hLr hH hF hG
      T hT m hm hdiag hband K hK hcount B hB η hη
    exact ⟨ep,hep,fun ε hε he u hu=>hbound ε hε he u hu.1 hu.2.1 hu.2.2⟩
  have htransfer:=actual_metric_error_of_gradient_asymptotic base hb G H hr hG₀ hH₀ hH hG
    point admission 3 (Or.inr rfl) (m^2*rfcRestartConstant (designSpacing I) k) hpoint hgradient
  intro η hη
  obtain ⟨ep,hep,hbound⟩:=htransfer η hη
  exact ⟨ep,hep,fun ε hε he u hu hKu hunit=>hbound ε hε he u ⟨hu,hKu,hunit⟩⟩

end
end krylov.Convergence
