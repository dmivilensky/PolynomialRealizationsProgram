import krylov.Convergence.OrderDeferredNormalized
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

/-- Actual fresh-memory restarts of the original search-only deferred policy.
Article: thm:D, each restart clears all previous physical observations. -/
def deferredRestartedPoints {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (estimate : History E → ℝ) (T : E ≃L[ℝ] E) (f : E → ℝ) (G : E → E) (r : ℝ) (N : ℕ)
    (x₀ : E) : ℕ → E
  | 0=>x₀
  | c+1=>scalarFunctionPoint (deferredDataMethod fullMemory N estimate) T f G r
    (deferredRestartedPoints estimate T f G r N x₀ c) N

variable {k : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin (k+1))

/-- Exact printed DC constant along the genuine restarted scalar sequence.
Article: main_krylov, thm:D. -/
theorem restarted_nativeDC_sharp_error
    (I : chebyshev1.SpectralInterval)
    (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (hb : base.PosDef) (hk : 0<k)
    (mu upper : ℝ) (hmu : 0<mu) (hmuL : mu≤upper)
    (hlo : (base-mu • 1).PosSemidef) (hhi : (upper • 1-base).PosSemidef)
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
      (∀ v,v≠0 → 0 < inner ℝ v (z.1 v)) ∧∀ i<k+1,CG.gradient z.1 z.2 i≠0)
    (x₀ : E) :
    let T:=metricCoordinates base hb
    let x:=deferredRestartedPoints (dcSchurGaussRadauEstimate fullMemory mu upper) T f G r (k+1) x₀
    let e:=fun c=>‖T (x c)‖
    (∀ᶠ c in atTop,0<e c →normalizedReference (scalarSearchOnlyOperator (deferredDataMethod fullMemory (k+1) (dcSchurGaussRadauEstimate fullMemory mu upper)) T f G H r (x c) 0) (G (x c))∈K) →
    Tendsto e atTop (𝓝 0) →
    ∀ η : ℝ,0<η →∀ᶠ c in atTop,e (c+1)≤(m*dcRestartConstant (designSpacing I) ((upper-mu)/(upper+mu)) k+η)*(e c)^2 := by
  let C:=metricCoordinates base hb
  let cycle:=fun x : E=>scalarFunctionPoint (deferredDataMethod fullMemory (k+1) (dcSchurGaussRadauEstimate fullMemory mu upper)) C f G r x (k+1)
  let admission:=fun x : E=>normalizedReference (scalarSearchOnlyOperator (deferredDataMethod fullMemory (k+1) (dcSchurGaussRadauEstimate fullMemory mu upper)) C f G H r x 0) (G x)∈K
  have hcycle:=nativeDC_sharp_normalized_error I base hb hk mu upper hmu hmuL hlo hhi f G H D hD hr hG₀ hH₀
    hLr hH hF hG T hT m hm hdiag hband K hK hquad
  have hzero : cycle 0=0 := by
    apply C.injective
    have hh:=(scalarSearchOnlyPoint_localization (deferredDataMethod fullMemory (k+1) (dcSchurGaussRadauEstimate fullMemory mu upper)) (fun _ _=>rfl) C (metricCoordinates_inverse_symmetric base hb) f G H hr
      hG₀ (coordinateDerivative_metric_zero base hb H hH₀) hLr hH hF hG 0
      (by simpa only [map_zero,norm_zero] using half_pos hr) (k+1)).1
    have hn : ‖C (cycle 0)‖=0 := le_antisymm (by simpa only [map_zero,norm_zero,mul_zero] using hh) (norm_nonneg _)
    simpa only [map_zero] using norm_eq_zero.mp hn
  dsimp only
  intro hN hconv
  exact sharp_restarted_of_unit_cycle C cycle hzero admission 2 (by norm_num) (m*dcRestartConstant (designSpacing I) ((upper-mu)/(upper+mu)) k)
    hcycle (deferredRestartedPoints (dcSchurGaussRadauEstimate fullMemory mu upper) C f G r (k+1) x₀) (fun _=>rfl) hN hconv

end
end krylov.Convergence
