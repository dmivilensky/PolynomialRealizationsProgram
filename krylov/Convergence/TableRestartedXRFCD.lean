import krylov.Convergence.RestartVirtualDirectionOrder
import krylov.Convergence.OrderCounting

/-!
Article: main_krylov, Table s7-orders, restarted XRFC.
Use: establish the order of the genuine intermediate iterates and real
one-gradient query clock. Uniform localization is derived from original
V1--V3 and the true scalar-function hypotheses; no intermediate bound is assumed.
Source: native XRFC localization and exact integral clock conversion.
-/
namespace krylov.Convergence
noncomputable section
open Matrix Set Metric Filter Topology krylov.Methods krylov.Reference krylov.Functions krylov.Nonlinear
  krylov.Stability
open scoped InnerProductSpace NNReal Matrix.Norms.L2Operator
variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)

/-- The actual evaluated vertices of recursively restarted XRFC. The
cost n clock counts major iterates; cost n+1 includes every gradient query
and the virtual endpoint which is first queried in the next cycle.
Article: main_krylov, Table s7-orders. -/
def xrfcDCountedPoint (trial : History E → ℝ) (G : E → E) (x₀ : E) (cost j : ℕ) : E :=
  xrfcDFunctionPoint trial G (xrfcDRestartedPoints trial G x₀ (j/cost)) (j%cost)

/-- Original V1--V3 imply the literal per-iteration and per-gradient
XRFC R-orders: use cost=n and cost=n+1 respectively. Actual intermediate
queries, stationary tails and all finite initial exceptions are included.
Article: main_krylov, thm:V and Table s7-orders. -/
theorem restarted_xrfcDFunction_counted_rorder
    (trial : History E → ℝ) (hhom : ObservedTrialHomogeneous trial)
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (U : Set E) (hU : IsCompact U)
    (hcount : ∀ u∈U,referenceAtomCount base hb (cgOperator base u)=n)
    (ht : ∀ u∈U,∀ i<n,0<trial (oneGradientRun (xrfcDMethod fullMemory trial)
      (fun _=>cgOperator base) (cgOperator base u) i))
    (hT : ∀ u∈U,∀ i<n,ContDiffAt ℝ 2 (trialCoordinate trial i)
      (oneGradientData (xrfcDMethod fullMemory trial) (fun _=>cgOperator base) (cgOperator base u) i))
    (G : E → E) (H : E → E →L[ℝ] E) (r : ℝ) (hr : 0<r)
    (hG₀ : G 0=0) (hH₀ : H 0=cgOperator base) {L : ℝ≥0} (hH : LipschitzOnWith L H (ball 0 r))
    (hG : ∀ x∈ball 0 r,HasFDerivAt G (H x) x)
    (x₀ : E) (cost : ℕ) (hcost : 0<cost) (hcostn : cost≤n+1) :
    let x := xrfcDRestartedPoints trial G x₀
    let e := fun c=>‖metricCoordinates base hb (x c)‖
    (∀ᶠ c in atTop,0<e c →(e c)⁻¹ • x c∈U) →Tendsto e atTop (𝓝 0) →
    HasROrder (fun j=>‖metricCoordinates base hb (xrfcDCountedPoint trial G x₀ cost j)‖)
      ((2:ℝ)^(1/(cost:ℝ))) := by
  dsimp only
  intro hadmit hconv
  let T := metricCoordinates base hb
  let x := xrfcDRestartedPoints trial G x₀
  let e := fun c=>‖T (x c)‖
  have hcycle := restarted_xrfcDFunction_rorder trial hhom base hb U hU hcount ht hT
    G H r hr hG₀ hH₀ hH hG x₀ hadmit hconv
  have hclock := hcycle.clock (by norm_num : (1:ℝ)<2) cost hcost
  have hcont : ContinuousAt H 0 := hH.continuousOn.continuousAt (isOpen_ball.mem_nhds (mem_ball_self hr))
  obtain ⟨ep,D,hep,hD,hloc⟩ := xrfcDFunction_compact_localization trial hhom base hb U hU hcount ht hT
    G H r hr hG₀ hH₀ hcont hG
  apply hclock.eventually_mono (show 0<‖T.toContinuousLinearMap‖*D+1 by positivity)
  obtain ⟨N,hN⟩ := eventually_atTop.mp (hconv.eventually (gt_mem_nhds hep) |>.and hadmit)
  filter_upwards [eventually_ge_atTop (N*cost)] with j hj
  have hidx : N≤j/cost := (Nat.le_div_iff_mul_le hcost).mpr hj
  have hc := hN (j/cost) hidx
  have hi : j%cost≤n := by have := Nat.mod_lt j hcost; omega
  change ‖T (xrfcDFunctionPoint trial G (x (j/cost)) (j%cost))‖≤
    (‖T.toContinuousLinearMap‖*D+1)*e (j/cost)
  by_cases he : 0<e (j/cost)
  · have hdecomp : e (j/cost) • ((e (j/cost))⁻¹ • x (j/cost))=x (j/cost) := by
      rw [smul_smul,mul_inv_cancel₀ he.ne',one_smul]
    have hh := ((hloc (e (j/cost)) he hc.1 ((e (j/cost))⁻¹ • x (j/cost))
      (hc.2 he)).1 (j%cost) hi).2
    rw [hdecomp] at hh
    have hm := (T.toContinuousLinearMap.le_opNorm _).trans
      (mul_le_mul_of_nonneg_left hh (norm_nonneg _))
    exact hm.trans (by nlinarith only [norm_nonneg (T (x (j/cost)))])
  · have he₀ : e (j/cost)=0 := le_antisymm (by linarith only [he]) (norm_nonneg _)
    have hx : x (j/cost)=0 := by
      apply T.injective
      simpa only [map_zero] using norm_eq_zero.mp he₀
    have hs := oneGradientFunctionRun_stationary (xrfcDMethod fullMemory trial) G 0 hG₀
      (fun H hH=>(xrfcD_policy_stationary trial H hH).1) (j%cost)
    rw [hx,xrfcDFunctionPoint,oneGradientFunctionPoint,hs.2,add_zero,map_zero,norm_zero,he₀,mul_zero]

end
end krylov.Convergence
