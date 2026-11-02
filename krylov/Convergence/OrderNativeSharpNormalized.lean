import krylov.Convergence.OrderNativeSharpError
import krylov.Convergence.OrderObservedReferenceAdmission

/-!
Article: main_krylov, thm:D, sharp cycles under literal s7:N.
Use: the printed sharp constants for actual FC/RFC metric errors with
compactness of the actual observed first-secant normalized reference.
The necessary compact full true reference family is derived, rather than
assumed. Source: actual native admission and canonical error normalization.
-/
namespace krylov.Convergence
noncomputable section
open Matrix Set Metric krylov.Methods krylov.Reference krylov.Functions krylov.Tensor
  krylov.Nonlinear krylov.Design krylov.Secant
open scoped InnerProductSpace NNReal Matrix.Norms.L2Operator
variable {k : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin (k+1))

/-- Literal observed-reference compactness suffices for the printed FC cycle error constant.
Article: main_krylov, thm:D and s7:N. -/
theorem nativeFC_sharp_normalized_error
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
    (K : Set ((E →L[ℝ] E) × E)) (hK : IsCompact K)
    (hquad : ∀ z∈K,z.1.toLinearMap.IsSymmetric ∧
      (∀ v,v≠0 → 0 < inner ℝ v (z.1 v)) ∧∀ i<k+1,CG.gradient z.1 z.2 i≠0) :
    ∀ η : ℝ,0<η →∃ ep : ℝ,0<ep ∧∀ ε : ℝ,0<ε → ε<ep →∀ u,‖cgOperator (metricRoot base) u‖=1 →
      normalizedReference (metricFCOperator (metricCoordinates base hb) f G H fullMemory r (ε • u) 0)
        (G (ε • u))∈K →
      ‖metricCoordinates base hb (metricFCPoint (metricCoordinates base hb) f G fullMemory r (ε • u) (k+1))‖≤
        (m*fcRestartConstant (designSpacing I) k+η)*ε^2 := by
  obtain ⟨ed,hed,F,hFc,hfull,hcover⟩:=nativeFC_canonical_observed_admission base hb f G H hr hG₀ hH₀ hLr hH hF hG K hK hquad
  let S:=cgOperator (metricRoot base)
  let R:=cgOperator (metricRoot base)⁻¹
  have hsize : ∀ u : E,‖S u‖=1 →‖u‖≤‖R‖+1 := by
    intro u hu
    have hcancel : R (S u)=u := by
      simp only [R,S,cgOperator]
      rw [←mul_apply_eq_comp,←map_mul,Matrix.nonsing_inv_mul _ (metricRoot_det_unit base hb),map_one,one_apply_eq_self]
    have hh:=R.le_opNorm (S u)
    rw [hcancel,hu,mul_one] at hh
    exact hh.trans (by linarith)
  intro η hη
  obtain ⟨es,hes,hbound⟩:=nativeFC_sharp_error I base hb f G H D hD hr hG₀ hH₀ hLr hH hF hG
    T hT m hm hdiag hband F hFc hfull (‖R‖+1) (by positivity) η hη
  refine ⟨min ed es,by positivity,?_⟩
  intro ε hε he u hu hn
  exact hbound ε hε (he.trans_le (min_le_right _ _)) u (hsize u hu)
    (hcover ε hε (he.trans_le (min_le_left _ _)) u hu hn) hu

/-- Literal observed-reference compactness suffices for the printed RFC cycle error constant.
Article: main_krylov, thm:D and s7:N. -/
theorem nativeRFC_sharp_normalized_error
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
    (K : Set ((E →L[ℝ] E) × E)) (hK : IsCompact K)
    (hquad : ∀ z∈K,z.1.toLinearMap.IsSymmetric ∧
      (∀ v,v≠0 → 0 < inner ℝ v (z.1 v)) ∧∀ i<k+1,CG.gradient z.1 z.2 i≠0) :
    ∀ η : ℝ,0<η →∃ ep : ℝ,0<ep ∧∀ ε : ℝ,0<ε → ε<ep →∀ u,‖cgOperator (metricRoot base) u‖=1 →
      normalizedReference (rfcFunctionSearchOperator (metricCoordinates base hb) f G H fullMemory r (ε • u) 0)
        (G (ε • u))∈K →
      ‖metricCoordinates base hb (rfcFunctionPoint (metricCoordinates base hb) f G fullMemory r (ε • u) (k+1))‖≤
        (m^2*rfcRestartConstant (designSpacing I) k+η)*ε^3 := by
  obtain ⟨ed,hed,F,hFc,hfull,hcover⟩:=nativeRFC_canonical_observed_admission base hb f G H hr hG₀ hH₀ hLr hH hF hG K hK hquad
  let S:=cgOperator (metricRoot base)
  let R:=cgOperator (metricRoot base)⁻¹
  have hsize : ∀ u : E,‖S u‖=1 →‖u‖≤‖R‖+1 := by
    intro u hu
    have hcancel : R (S u)=u := by
      simp only [R,S,cgOperator]
      rw [←mul_apply_eq_comp,←map_mul,Matrix.nonsing_inv_mul _ (metricRoot_det_unit base hb),map_one,one_apply_eq_self]
    have hh:=R.le_opNorm (S u)
    rw [hcancel,hu,mul_one] at hh
    exact hh.trans (by linarith)
  intro η hη
  obtain ⟨es,hes,hbound⟩:=nativeRFC_sharp_error I base hb hk f G H D hD hr hG₀ hH₀ hLr hH hF hG
    T hT m hm hdiag hband F hFc hfull (‖R‖+1) (by positivity) η hη
  refine ⟨min ed es,by positivity,?_⟩
  intro ε hε he u hu hn
  exact hbound ε hε (he.trans_le (min_le_right _ _)) u (hsize u hu)
    (hcover ε hε (he.trans_le (min_le_left _ _)) u hu hn) hu

end
end krylov.Convergence
