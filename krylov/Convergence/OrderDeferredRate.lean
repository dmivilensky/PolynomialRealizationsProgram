import krylov.Convergence.OrderDeferredQuadraticNormalized
import krylov.Convergence.OrderDeferredRestarted
import krylov.Convergence.RecurrenceOrder

/-!
Article: main_krylov, thm:D and Table s7-orders, actual Schur DC order.
Use: derive the literal restarted order from only source Hessian data,
actual observed s7:N compactness and convergence. No third-tensor
certificate or output recurrence is supplied as an assumption.
Source: genuine native quadratic cycle and exact scalar restart recursion.
-/
namespace krylov.Convergence
noncomputable section
open Matrix Set Metric Filter Topology krylov.Methods krylov.Reference krylov.Functions
  krylov.Tensor krylov.Nonlinear krylov.Design krylov.Secant krylov.Cancellation
open scoped InnerProductSpace NNReal Matrix.Norms.L2Operator
variable {k : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin (k+1))

/-- The actual data-midpoint DC restart errors are quadratic under literal
actual s7:N, including stationary tails. Article: thm:D. -/
theorem restarted_nativeDC_quadratic
    (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (hb : base.PosDef) (hk : 0<k)
    (mu upper : ℝ) (hmu : 0<mu) (hmuL : mu≤upper)
    (hlo : (base-mu • 1).PosSemidef) (hhi : (upper • 1-base).PosSemidef)
    (f : E → ℝ) (G : E → E) (H : E → E →L[ℝ] E)
    {r : ℝ} (hr : 0<r) (hG₀ : G 0=0) (hH₀ : H 0=cgOperator base)
    {L : ℝ≥0} (hLr : (L:ℝ)*r≤1/2)
    (hH : LipschitzOnWith L (coordinateDerivative (metricCoordinates base hb) H) (closedBall 0 r))
    (hF : ∀ z,‖metricCoordinates base hb z‖≤r → HasFDerivAt f (innerSL ℝ (G z)) z)
    (hG : ∀ z,‖metricCoordinates base hb z‖≤r → HasFDerivAt G (H z) z)
    (K : Set ((E →L[ℝ] E) × E)) (hK : IsCompact K)
    (hquad : ∀ z∈K,z.1.toLinearMap.IsSymmetric ∧
      (∀ v,v≠0 → 0 < inner ℝ v (z.1 v)) ∧∀ i<k+1,CG.gradient z.1 z.2 i≠0)
    (x₀ : E) :
    let T:=metricCoordinates base hb
    let x:=deferredRestartedPoints (dcSchurGaussRadauEstimate fullMemory mu upper) T f G r (k+1) x₀
    let e:=fun c=>‖T (x c)‖
    (∀ᶠ c in atTop,0<e c →normalizedReference (scalarSearchOnlyOperator (deferredDataMethod fullMemory (k+1) (dcSchurGaussRadauEstimate fullMemory mu upper)) T f G H r (x c) 0) (G (x c))∈K) →
    Tendsto e atTop (𝓝 0) →
    ∃ C : ℝ,0<C ∧∀ᶠ c in atTop,e (c+1)≤C*(e c)^2 := by
  let C:=metricCoordinates base hb
  let cycle:=fun x : E=>scalarFunctionPoint (deferredDataMethod fullMemory (k+1) (dcSchurGaussRadauEstimate fullMemory mu upper)) C f G r x (k+1)
  let admission:=fun x : E=>normalizedReference (scalarSearchOnlyOperator (deferredDataMethod fullMemory (k+1) (dcSchurGaussRadauEstimate fullMemory mu upper)) C f G H r x 0) (G x)∈K
  obtain ⟨ep,C₀,hep,hC₀,hbound⟩:=nativeDC_normalized_quadratic base hb hk mu upper hmu hmuL hlo hhi f G H
    hr hG₀ hH₀ hLr hH hF hG K hK hquad
  have hcycle : ∀ η : ℝ,0<η →∃ ep : ℝ,0<ep ∧∀ ε : ℝ,0<ε →ε<ep →∀ u,‖C u‖=1 →admission (ε • u) →
      ‖C (cycle (ε • u))‖≤(C₀+η)*ε^2 := by
    intro η hη
    refine ⟨ep,hep,?_⟩
    intro ε hε he u hu hn
    exact (hbound ε hε he u hu hn).trans (mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg ε))
  have hzero : cycle 0=0 := by
    apply C.injective
    have hh:=(scalarSearchOnlyPoint_localization (deferredDataMethod fullMemory (k+1) (dcSchurGaussRadauEstimate fullMemory mu upper)) (fun _ _=>rfl) C (metricCoordinates_inverse_symmetric base hb) f G H hr
      hG₀ (coordinateDerivative_metric_zero base hb H hH₀) hLr hH hF hG 0
      (by simpa only [map_zero,norm_zero] using half_pos hr) (k+1)).1
    have hn : ‖C (cycle 0)‖=0 := le_antisymm (by simpa only [map_zero,norm_zero,mul_zero] using hh) (norm_nonneg _)
    simpa only [map_zero] using norm_eq_zero.mp hn
  dsimp only
  intro hN hconv
  refine ⟨C₀+1,by positivity,?_⟩
  exact sharp_restarted_of_unit_cycle C cycle hzero admission 2 (by norm_num) C₀
    hcycle (deferredRestartedPoints (dcSchurGaussRadauEstimate fullMemory mu upper) C f G r (k+1) x₀)
    (fun _=>rfl) hN hconv 1 (by norm_num)

/-- The genuine Schur DC restarted scalar sequence has cycle R-order two.
Article: main_krylov, thm:D and Table s7-orders. -/
theorem restarted_nativeDC_rorder
    (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (hb : base.PosDef) (hk : 0<k)
    (mu upper : ℝ) (hmu : 0<mu) (hmuL : mu≤upper)
    (hlo : (base-mu • 1).PosSemidef) (hhi : (upper • 1-base).PosSemidef)
    (f : E → ℝ) (G : E → E) (H : E → E →L[ℝ] E)
    {r : ℝ} (hr : 0<r) (hG₀ : G 0=0) (hH₀ : H 0=cgOperator base)
    {L : ℝ≥0} (hLr : (L:ℝ)*r≤1/2)
    (hH : LipschitzOnWith L (coordinateDerivative (metricCoordinates base hb) H) (closedBall 0 r))
    (hF : ∀ z,‖metricCoordinates base hb z‖≤r → HasFDerivAt f (innerSL ℝ (G z)) z)
    (hG : ∀ z,‖metricCoordinates base hb z‖≤r → HasFDerivAt G (H z) z)
    (K : Set ((E →L[ℝ] E) × E)) (hK : IsCompact K)
    (hquad : ∀ z∈K,z.1.toLinearMap.IsSymmetric ∧
      (∀ v,v≠0 → 0 < inner ℝ v (z.1 v)) ∧∀ i<k+1,CG.gradient z.1 z.2 i≠0)
    (x₀ : E) :
    let T:=metricCoordinates base hb
    let x:=deferredRestartedPoints (dcSchurGaussRadauEstimate fullMemory mu upper) T f G r (k+1) x₀
    let e:=fun c=>‖T (x c)‖
    (∀ᶠ c in atTop,0<e c →normalizedReference (scalarSearchOnlyOperator (deferredDataMethod fullMemory (k+1) (dcSchurGaussRadauEstimate fullMemory mu upper)) T f G H r (x c) 0) (G (x c))∈K) →
    Tendsto e atTop (𝓝 0) →
    HasROrder e 2 := by
  dsimp only
  intro hN hconv
  have hrec:=restarted_nativeDC_quadratic base hb hk mu upper hmu hmuL hlo hhi f G H
    hr hG₀ hH₀ hLr hH hF hG K hK hquad x₀ hN hconv
  exact rorder_power_recurrence _ (fun _=>norm_nonneg _) hconv 2 (by norm_num) hrec

end
end krylov.Convergence
