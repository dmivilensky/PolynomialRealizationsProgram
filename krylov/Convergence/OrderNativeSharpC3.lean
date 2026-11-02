import krylov.Convergence.OrderNativeSharpNormalized
import krylov.Convergence.OrderCanonicalC3Source

/-!
Article: main_krylov, thm:D, original C-three sharp FC/RFC cycles.
Use: actual returned metric errors with the printed constants under true
continuous third derivative and the original observed s7:N hypothesis.
The local canonical Hessian bound and search radius are derived from C3,
and the radius is fixed before choosing the normalized compact family.
Source: the genuine canonical mean-value source lemma and native cycles.
-/
namespace krylov.Convergence
noncomputable section
open Matrix Set Metric krylov.Methods krylov.Reference krylov.Functions krylov.Tensor
  krylov.Nonlinear krylov.Design krylov.Secant
open scoped InnerProductSpace NNReal Matrix.Norms.L2Operator
variable {k : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin (k+1))

/-- Original C-three scalar hypotheses suffice for the printed FC sharp actual error.
Article: main_krylov, thm:D. -/
theorem nativeFC_C3_sharp_error
    (I : chebyshev1.SpectralInterval)
    (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (hb : base.PosDef)
    (f : E → ℝ) (G : E → E) (H : E → E →L[ℝ] E)
    (D : E → E →L[ℝ] E →L[ℝ] E)
    {r : ℝ} (hr : 0<r) (hG₀ : G 0=0) (hH₀ : H 0=cgOperator base)
    (hF : ∀ z,‖metricCoordinates base hb z‖<r → HasFDerivAt f (innerSL ℝ (G z)) z)
    (hG : ∀ z,‖metricCoordinates base hb z‖<r → HasFDerivAt G (H z) z)
    (hD : ∀ z,‖metricCoordinates base hb z‖<r → HasFDerivAt H (D z) z)
    (hDc : ContinuousAt D 0)
    (T : SymmetricCubic E)
    (hT : ∀ a b c,T.form (cgOperator (metricRoot base) a) (cgOperator (metricRoot base) b)
      (cgOperator (metricRoot base) c)=inner ℝ (D 0 a b) c)
    (m : ℝ) (hm : 0≤m) (hdiag : ∀ v,‖v‖=1 → |T.form v v v|≤2*m)
    (hband : ∀ i,I.mu≤hb.1.eigenvalues i ∧hb.1.eigenvalues i≤I.mu*I.kappa)
    : ∃ s : ℝ,0<s ∧s<r ∧∀ K : Set ((E →L[ℝ] E) × E),IsCompact K →
      (∀ z∈K,z.1.toLinearMap.IsSymmetric ∧
        (∀ v,v≠0 → 0 < inner ℝ v (z.1 v)) ∧∀ i<k+1,CG.gradient z.1 z.2 i≠0) →
    ∀ η : ℝ,0<η →∃ ep : ℝ,0<ep ∧∀ ε : ℝ,0<ε → ε<ep →∀ u,‖cgOperator (metricRoot base) u‖=1 →
      normalizedReference (metricFCOperator (metricCoordinates base hb) f G H fullMemory s (ε • u) 0)
        (G (ε • u))∈K →
      ‖metricCoordinates base hb (metricFCPoint (metricCoordinates base hb) f G fullMemory s (ε • u) (k+1))‖≤
        (m*fcRestartConstant (designSpacing I) k+η)*ε^2 := by
  obtain ⟨s,L,hs,hsr,hLr,hLip⟩:=exists_canonical_hessian_lipschitz_closedBall
    (metricCoordinates base hb) H D hr hD hDc
  refine ⟨s,hs,hsr,?_⟩
  intro K hK hquad
  exact nativeFC_sharp_normalized_error I base hb f G H (D 0)
    (hD 0 (by simpa only [map_zero,norm_zero] using hr)) hs hG₀ hH₀ hLr hLip
    (fun z hz=>hF z (hz.trans_lt hsr)) (fun z hz=>hG z (hz.trans_lt hsr))
    T hT m hm hdiag hband K hK hquad

/-- Original C-three scalar hypotheses suffice for the printed RFC sharp actual error.
Article: main_krylov, thm:D. -/
theorem nativeRFC_C3_sharp_error
    (I : chebyshev1.SpectralInterval)
    (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (hb : base.PosDef) (hk : 0<k)
    (f : E → ℝ) (G : E → E) (H : E → E →L[ℝ] E)
    (D : E → E →L[ℝ] E →L[ℝ] E)
    {r : ℝ} (hr : 0<r) (hG₀ : G 0=0) (hH₀ : H 0=cgOperator base)
    (hF : ∀ z,‖metricCoordinates base hb z‖<r → HasFDerivAt f (innerSL ℝ (G z)) z)
    (hG : ∀ z,‖metricCoordinates base hb z‖<r → HasFDerivAt G (H z) z)
    (hD : ∀ z,‖metricCoordinates base hb z‖<r → HasFDerivAt H (D z) z)
    (hDc : ContinuousAt D 0)
    (T : SymmetricCubic E)
    (hT : ∀ a b c,T.form (cgOperator (metricRoot base) a) (cgOperator (metricRoot base) b)
      (cgOperator (metricRoot base) c)=inner ℝ (D 0 a b) c)
    (m : ℝ) (hm : 0≤m) (hdiag : ∀ v,‖v‖=1 → |T.form v v v|≤2*m)
    (hband : ∀ i,I.mu≤hb.1.eigenvalues i ∧hb.1.eigenvalues i≤I.mu*I.kappa)
    : ∃ s : ℝ,0<s ∧s<r ∧∀ K : Set ((E →L[ℝ] E) × E),IsCompact K →
      (∀ z∈K,z.1.toLinearMap.IsSymmetric ∧
        (∀ v,v≠0 → 0 < inner ℝ v (z.1 v)) ∧∀ i<k+1,CG.gradient z.1 z.2 i≠0) →
    ∀ η : ℝ,0<η →∃ ep : ℝ,0<ep ∧∀ ε : ℝ,0<ε → ε<ep →∀ u,‖cgOperator (metricRoot base) u‖=1 →
      normalizedReference (rfcFunctionSearchOperator (metricCoordinates base hb) f G H fullMemory s (ε • u) 0)
        (G (ε • u))∈K →
      ‖metricCoordinates base hb (rfcFunctionPoint (metricCoordinates base hb) f G fullMemory s (ε • u) (k+1))‖≤
        (m^2*rfcRestartConstant (designSpacing I) k+η)*ε^3 := by
  obtain ⟨s,L,hs,hsr,hLr,hLip⟩:=exists_canonical_hessian_lipschitz_closedBall
    (metricCoordinates base hb) H D hr hD hDc
  refine ⟨s,hs,hsr,?_⟩
  intro K hK hquad
  exact nativeRFC_sharp_normalized_error I base hb hk f G H (D 0)
    (hD 0 (by simpa only [map_zero,norm_zero] using hr)) hs hG₀ hH₀ hLr hLip
    (fun z hz=>hF z (hz.trans_lt hsr)) (fun z hz=>hG z (hz.trans_lt hsr))
    T hT m hm hdiag hband K hK hquad

end
end krylov.Convergence
