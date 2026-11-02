import krylov.Convergence.OrderDeferredRestarted
import krylov.Convergence.OrderCanonicalC3Source
import krylov.Convergence.OrderSharpRestarted
import krylov.Convergence.OrderCounting

/-!
Article: main_krylov, thm:D, actual fresh-memory Schur DC restarts.
Use: the genuine source policy retains the exact printed restart constant;
stationary tails are derived from scalar objective localization.
Source: actual native normalized cycles and canonical-unit normalization.
-/
namespace krylov.Convergence
noncomputable section
open Matrix Set Metric Filter Topology krylov.Methods krylov.Reference krylov.Functions
  krylov.Tensor krylov.Nonlinear krylov.Design krylov.Secant krylov.Cancellation
open scoped InnerProductSpace NNReal Matrix.Norms.L2Operator

variable {k : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin (k+1))

/-- Original continuous-third-derivative source hypotheses give the exact
printed DC restart inequality under literal actual s7:N. Article: thm:D. -/
theorem restarted_nativeDC_C3_sharp_error
    (I : chebyshev1.SpectralInterval)
    (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (hb : base.PosDef) (hk : 0<k)
    (mu upper : ℝ) (hmu : 0<mu) (hmuL : mu≤upper)
    (hlo : (base-mu • 1).PosSemidef) (hhi : (upper • 1-base).PosSemidef)
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
    let x:=deferredRestartedPoints (dcSchurGaussRadauEstimate fullMemory mu upper) T f G s (k+1) x₀
    let e:=fun c=>‖T (x c)‖
    (∀ᶠ c in atTop,0<e c →normalizedReference (scalarSearchOnlyOperator (deferredDataMethod fullMemory (k+1) (dcSchurGaussRadauEstimate fullMemory mu upper)) T f G H s (x c) 0) (G (x c))∈K) →
    Tendsto e atTop (𝓝 0) →
    ∀ η : ℝ,0<η →∀ᶠ c in atTop,e (c+1)≤(m*dcRestartConstant (designSpacing I) ((upper-mu)/(upper+mu)) k+η)*(e c)^2 := by
  obtain ⟨s,L,hs,hsr,hLr,hLip⟩:=exists_canonical_hessian_lipschitz_closedBall
    (metricCoordinates base hb) H D hr hD hDc
  refine ⟨s,hs,hsr,?_⟩
  intro x₀
  exact restarted_nativeDC_sharp_error I base hb hk mu upper hmu hmuL hlo hhi f G H (D 0)
    (hD 0 (by simpa only [map_zero,norm_zero] using hr)) hs hG₀ hH₀ hLr hLip
    (fun z hz=>hF z (hz.trans_lt hsr)) (fun z hz=>hG z (hz.trans_lt hsr))
    T hT m hm hdiag hband K hK hquad x₀

end
end krylov.Convergence
