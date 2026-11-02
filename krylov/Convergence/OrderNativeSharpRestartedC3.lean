import krylov.Convergence.OrderNativeSharpRestarted

/-!
Article: main_krylov, thm:D, original C-three restarted sharp inequalities.
Use: the true restarted FC/RFC errors satisfy the printed constants plus
little-o, encoded as an eventual bound for every positive tolerance.
All canonical Lipschitz domains are derived before choosing the restart
point. Source: actual C3 derivative mean-value calculus and sharp cycles.
-/

/-!
Article: krylov, Theorem E.14 [thm:D].

Actual restarted scalar FC/RFC executors have the printed sharp true-Hessian error constants
and C3 little-o recurrences.
The literal observed compact normalized-reference condition is retained; convergence of cycle-
start errors is a hypothesis, rather than inferred from the formal asymptotic inequality alone.
-/
namespace krylov.Convergence
noncomputable section
open Matrix Set Metric Filter Topology krylov.Methods krylov.Reference krylov.Functions
  krylov.Tensor krylov.Nonlinear krylov.Design krylov.Secant
open scoped InnerProductSpace NNReal Matrix.Norms.L2Operator
variable {k : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin (k+1))

/-- The printed FC restarted inequality under the original C3 function assumptions.
Article: main_krylov, thm:D. -/
theorem restarted_nativeFC_C3_sharp_error
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
    (K : Set ((E →L[ℝ] E) × E)) (hK : IsCompact K)
    (hquad : ∀ z∈K,z.1.toLinearMap.IsSymmetric ∧
      (∀ v,v≠0 → 0 < inner ℝ v (z.1 v)) ∧∀ i<k+1,CG.gradient z.1 z.2 i≠0)
    : ∃ s : ℝ,0<s ∧s<r ∧∀ x₀ : E,
    let T:=metricCoordinates base hb
    let x:=fcRestartedPoints T f G s (k+1) x₀
    let e:=fun c=>‖T (x c)‖
    (∀ᶠ c in atTop,0<e c →normalizedReference (metricFCOperator T f G H fullMemory s (x c) 0) (G (x c))∈K) →
    Tendsto e atTop (𝓝 0) →
    ∀ η : ℝ,0<η →∀ᶠ c in atTop,e (c+1)≤(m*fcRestartConstant (designSpacing I) k+η)*(e c)^2 := by
  obtain ⟨s,L,hs,hsr,hLr,hLip⟩:=exists_canonical_hessian_lipschitz_closedBall
    (metricCoordinates base hb) H D hr hD hDc
  refine ⟨s,hs,hsr,?_⟩
  intro x₀
  exact restarted_nativeFC_sharp_error I base hb f G H (D 0)
    (hD 0 (by simpa only [map_zero,norm_zero] using hr)) hs hG₀ hH₀ hLr hLip
    (fun z hz=>hF z (hz.trans_lt hsr)) (fun z hz=>hG z (hz.trans_lt hsr))
    T hT m hm hdiag hband K hK hquad x₀

/-- The printed RFC restarted inequality under the original C3 function assumptions.
Article: main_krylov, thm:D. -/
theorem restarted_nativeRFC_C3_sharp_error
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
    (K : Set ((E →L[ℝ] E) × E)) (hK : IsCompact K)
    (hquad : ∀ z∈K,z.1.toLinearMap.IsSymmetric ∧
      (∀ v,v≠0 → 0 < inner ℝ v (z.1 v)) ∧∀ i<k+1,CG.gradient z.1 z.2 i≠0)
    : ∃ s : ℝ,0<s ∧s<r ∧∀ x₀ : E,
    let T:=metricCoordinates base hb
    let x:=rfcRestartedPoints T f G s (k+1) x₀
    let e:=fun c=>‖T (x c)‖
    (∀ᶠ c in atTop,0<e c →normalizedReference (rfcFunctionSearchOperator T f G H fullMemory s (x c) 0) (G (x c))∈K) →
    Tendsto e atTop (𝓝 0) →
    ∀ η : ℝ,0<η →∀ᶠ c in atTop,e (c+1)≤(m^2*rfcRestartConstant (designSpacing I) k+η)*(e c)^3 := by
  obtain ⟨s,L,hs,hsr,hLr,hLip⟩:=exists_canonical_hessian_lipschitz_closedBall
    (metricCoordinates base hb) H D hr hD hDc
  refine ⟨s,hs,hsr,?_⟩
  intro x₀
  exact restarted_nativeRFC_sharp_error I base hb hk f G H (D 0)
    (hD 0 (by simpa only [map_zero,norm_zero] using hr)) hs hG₀ hH₀ hLr hLip
    (fun z hz=>hF z (hz.trans_lt hsr)) (fun z hz=>hG z (hz.trans_lt hsr))
    T hT m hm hdiag hband K hK hquad x₀

end
end krylov.Convergence
