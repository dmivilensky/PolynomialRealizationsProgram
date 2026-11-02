import krylov.Convergence.OrderDeferredRate
import krylov.Convergence.RestartConstants

/-!
Article: main_krylov, thm:D and Table s7-orders, genuine DC clocks.
Use: actual intermediate scalar search iterates have the printed per-line
and per-gradient order 2^(1/n). No pointwise query bound is assumed.
Source: native scalar objective localization and exact integer clock conversion.
-/
namespace krylov.Convergence
noncomputable section
open Matrix Set Metric Filter Topology krylov.Methods krylov.Reference krylov.Functions
  krylov.Tensor krylov.Nonlinear krylov.Design krylov.Secant krylov.Cancellation
open scoped InnerProductSpace NNReal Matrix.Norms.L2Operator

/-- Every actual evaluated point of the original freshly restarted
search-only DC policy; one searched gradient per iteration.
Article: main_krylov, Table s7-orders. -/
def deferredCountedPoint {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (estimate : History E → ℝ) (T : E ≃L[ℝ] E) (f : E → ℝ) (G : E → E) (r : ℝ) (N : ℕ)
    (x₀ : E) (j : ℕ) : E :=
  scalarFunctionPoint (deferredDataMethod fullMemory N estimate) T f G r
    (deferredRestartedPoints estimate T f G r N x₀ (j/N)) (j%N)

variable {k : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin (k+1))

/-- Exact original DC order in the actual iteration/gradient clock.
Article: main_krylov, thm:D and Table s7-orders. -/
theorem restarted_nativeDC_counted_rorder
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
    HasROrder (fun j=>‖metricCoordinates base hb (deferredCountedPoint
        (dcSchurGaussRadauEstimate fullMemory mu upper) (metricCoordinates base hb) f G r (k+1) x₀ j)‖)
      ((2:ℝ)^(1/((k+1:ℕ):ℝ))) := by
  dsimp only
  intro hN hconv
  let T:=metricCoordinates base hb
  let estimate : History E → ℝ:=dcSchurGaussRadauEstimate fullMemory mu upper
  let x:=deferredRestartedPoints estimate T f G r (k+1) x₀
  let e:=fun c=>‖T (x c)‖
  have hcycle:=restarted_nativeDC_rorder base hb hk mu upper hmu hmuL hlo hhi f G H
    hr hG₀ hH₀ hLr hH hF hG K hK hquad x₀ hN hconv
  have hcost : 0<k+1:=by omega
  have hclock:=hcycle.clock (by norm_num : (1:ℝ)<2) (k+1) hcost
  apply hclock.eventually_mono (Real.sqrt_pos.mpr (by norm_num : (0:ℝ)<3))
  obtain ⟨N,hsmall⟩:=eventually_atTop.mp (hconv.eventually (gt_mem_nhds (half_pos hr)))
  filter_upwards [eventually_ge_atTop (N*(k+1))] with j hj
  have hidx : N≤j/(k+1):=(Nat.le_div_iff_mul_le hcost).mpr hj
  exact (scalarSearchOnlyPoint_localization (deferredDataMethod fullMemory (k+1) estimate) (fun _ _=>rfl)
    T (metricCoordinates_inverse_symmetric base hb) f G H hr hG₀ (coordinateDerivative_metric_zero base hb H hH₀)
    hLr hH hF hG (x (j/(k+1))) (hsmall _ hidx) (j%(k+1))).1

/-- The actual physical class-bound DC constant is strictly smaller than
FC's for every original n≥3. Article: main_krylov, thm:D. -/
theorem deferredClassConstant_lt_fc (θ mu upper : ℝ) (hθ : 0<θ) (hmu : 0<mu)
    (hmuL : mu≤upper) (K : ℕ) (hK : 2≤K) :
    dcRestartConstant θ ((upper-mu)/(upper+mu)) K<fcRestartConstant θ K := by
  apply dcRestartConstant_lt_fc θ _ hθ _ K hK
  rw [abs_of_nonneg (div_nonneg (sub_nonneg.mpr hmuL) (by linarith))]
  apply (div_lt_one (by linarith : 0<upper+mu)).mpr
  linarith

end
end krylov.Convergence
