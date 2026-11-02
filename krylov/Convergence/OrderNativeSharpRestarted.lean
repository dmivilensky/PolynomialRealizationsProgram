import krylov.Convergence.OrderSharpRestarted

/-!
Article: main_krylov, thm:D, literal restarted FC/RFC sharp constants.
Use: actual convergent restart sequences under the observed s7:N condition
satisfy the printed one-cycle error inequalities uniformly in the cycle.
Source: the proved sharp actual cycles, exact restart recursion, canonical
unit normalization, and derived stationary execution.
-/
namespace krylov.Convergence
noncomputable section
open Matrix Set Metric Filter Topology krylov.Methods krylov.Reference krylov.Functions
  krylov.Tensor krylov.Nonlinear krylov.Design krylov.Secant
open scoped InnerProductSpace NNReal Matrix.Norms.L2Operator
variable {k : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin (k+1))

/-- The printed FC constant is retained along the actual normalized restart trajectory.
Article: main_krylov, thm:D. -/
theorem restarted_nativeFC_sharp_error
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
      (∀ v,v≠0 → 0 < inner ℝ v (z.1 v)) ∧∀ i<k+1,CG.gradient z.1 z.2 i≠0)
    (x₀ : E) :
    let T:=metricCoordinates base hb
    let x:=fcRestartedPoints T f G r (k+1) x₀
    let e:=fun c=>‖T (x c)‖
    (∀ᶠ c in atTop,0<e c →normalizedReference (metricFCOperator T f G H fullMemory r (x c) 0) (G (x c))∈K) →
    Tendsto e atTop (𝓝 0) →
    ∀ η : ℝ,0<η →∀ᶠ c in atTop,e (c+1)≤(m*fcRestartConstant (designSpacing I) k+η)*(e c)^2 := by
  let C:=metricCoordinates base hb
  let cycle:=fun x : E=>metricFCPoint C f G fullMemory r x (k+1)
  let admission:=fun x : E=>normalizedReference (metricFCOperator C f G H fullMemory r x 0) (G x)∈K
  have hcycle:=nativeFC_sharp_normalized_error I base hb f G H D hD hr hG₀ hH₀
    hLr hH hF hG T hT m hm hdiag hband K hK hquad
  have hzero : cycle 0=0 := by
    apply C.injective
    have hh:=(metricFCPoint_localization C (metricCoordinates_inverse_symmetric base hb) f G H hr
      hG₀ (coordinateDerivative_metric_zero base hb H hH₀) hLr hH hF hG fullMemory 0
      (by simpa only [map_zero,norm_zero] using half_pos hr) (k+1)).1
    have hn : ‖C (cycle 0)‖=0 := le_antisymm (by simpa only [map_zero,norm_zero,mul_zero] using hh) (norm_nonneg _)
    simpa only [map_zero] using norm_eq_zero.mp hn
  dsimp only
  intro hN hconv
  exact sharp_restarted_of_unit_cycle C cycle hzero admission 2 (by norm_num) (m*fcRestartConstant (designSpacing I) k)
    hcycle (fcRestartedPoints C f G r (k+1) x₀) (fun _=>rfl) hN hconv

/-- The printed RFC constant is retained along the actual normalized restart trajectory.
Article: main_krylov, thm:D. -/
theorem restarted_nativeRFC_sharp_error
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
      (∀ v,v≠0 → 0 < inner ℝ v (z.1 v)) ∧∀ i<k+1,CG.gradient z.1 z.2 i≠0)
    (x₀ : E) :
    let T:=metricCoordinates base hb
    let x:=rfcRestartedPoints T f G r (k+1) x₀
    let e:=fun c=>‖T (x c)‖
    (∀ᶠ c in atTop,0<e c →normalizedReference (rfcFunctionSearchOperator T f G H fullMemory r (x c) 0) (G (x c))∈K) →
    Tendsto e atTop (𝓝 0) →
    ∀ η : ℝ,0<η →∀ᶠ c in atTop,e (c+1)≤(m^2*rfcRestartConstant (designSpacing I) k+η)*(e c)^3 := by
  let C:=metricCoordinates base hb
  let cycle:=fun x : E=>rfcFunctionPoint C f G fullMemory r x (k+1)
  let admission:=fun x : E=>normalizedReference (rfcFunctionSearchOperator C f G H fullMemory r x 0) (G x)∈K
  have hcycle:=nativeRFC_sharp_normalized_error I base hb hk f G H D hD hr hG₀ hH₀
    hLr hH hF hG T hT m hm hdiag hband K hK hquad
  have hzero : cycle 0=0 := by
    change rfcFunctionPoint C f G fullMemory r 0 (k+1)=0
    rw [rfcFunctionPoint,(rfcFunctionRun_stationary C f G fullMemory r 0 hG₀ (k+1)).2,zero_add]
  dsimp only
  intro hN hconv
  exact sharp_restarted_of_unit_cycle C cycle hzero admission 3 (by norm_num) (m^2*rfcRestartConstant (designSpacing I) k)
    hcycle (rfcRestartedPoints C f G r (k+1) x₀) (fun _=>rfl) hN hconv

end
end krylov.Convergence
