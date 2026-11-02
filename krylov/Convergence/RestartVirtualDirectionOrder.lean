import krylov.Convergence.VirtualDirectionReferenceComparison
import krylov.Convergence.VirtualDirectionStationary
import krylov.Convergence.RecurrenceOrder

/-!
Article: main_krylov, thm:V and restarted XRFC Table s7-orders.
Use: turn the true scalar virtual-output estimate into the actual recursively
restarted quadratic error and literal R-order. The only directional admission
is original V3; stationary tails are included without nonzero assumptions.
Source: genuine native XRFC shadow and characteristic exponential barriers.
-/
namespace krylov.Convergence
noncomputable section
open Matrix Set Metric Filter Topology krylov.Methods krylov.Reference krylov.Functions krylov.Nonlinear
  krylov.Stability
open scoped InnerProductSpace NNReal Matrix.Norms.L2Operator
variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)

/-- Actual full-memory scalar XRFC cycles, each returning its genuinely
unevaluated virtual point before fresh memory is started. Article: thm:V. -/
def xrfcDRestartedPoints (trial : History E → ℝ) (G : E → E) (x₀ : E) : ℕ → E
  | 0=>x₀
  | c+1=>xrfcDFunctionOutput trial G (xrfcDRestartedPoints trial G x₀ c)

/-- Original V1--V3 and convergence give actual quadratic restart error,
including the zero-error tail. No native source bound is supplied.
Article: main_krylov, thm:V and Table s7-orders. -/
theorem restarted_xrfcDFunction_quadratic
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
    (x₀ : E) :
    let x := xrfcDRestartedPoints trial G x₀
    let e := fun c=>‖metricCoordinates base hb (x c)‖
    (∀ᶠ c in atTop,0<e c →(e c)⁻¹ • x c∈U) →Tendsto e atTop (𝓝 0) →
    ∃ C : ℝ,0<C ∧∀ᶠ c in atTop,e (c+1)≤C*(e c)^2 := by
  dsimp only
  intro hadmit hconv
  let T := metricCoordinates base hb
  let x := xrfcDRestartedPoints trial G x₀
  let e := fun c=>‖T (x c)‖
  obtain ⟨ep,C,hep,hC,hcycle⟩ := xrfcDFunction_compact_reference_comparison trial hhom base hb U hU hcount ht hT
    G H r hr hG₀ hH₀ hH hG
  refine ⟨‖T.toContinuousLinearMap‖*C+1,by positivity,?_⟩
  filter_upwards [hconv.eventually (gt_mem_nhds hep),hadmit] with c hc hn
  change e (c+1)≤(‖T.toContinuousLinearMap‖*C+1)*(e c)^2
  by_cases he : 0<e c
  · have hdecomp : e c • ((e c)⁻¹ • x c)=x c := by
      rw [smul_smul,mul_inv_cancel₀ he.ne',one_smul]
    have hh := (hcycle (e c) he hc ((e c)⁻¹ • x c) (hn he)).2
    rw [hdecomp] at hh
    have hm := (T.toContinuousLinearMap.le_opNorm _).trans
      (mul_le_mul_of_nonneg_left hh (norm_nonneg _))
    exact hm.trans (by nlinarith only [sq_nonneg (e c)])
  · have he₀ : e c=0 := le_antisymm (by linarith only [he]) (norm_nonneg _)
    have hx : x c=0 := by
      apply T.injective
      simpa only [map_zero] using norm_eq_zero.mp he₀
    have hnext : e (c+1)=0 := by
      change ‖T (xrfcDFunctionOutput trial G (x c))‖=0
      rw [hx,xrfcDFunctionOutput_stationary trial G 0 hG₀,map_zero,norm_zero]
    rw [hnext,he₀]
    positivity

/-- The actual scalar restarted XRFC cycle has the literal guaranteed
R-order two under the article's hypotheses. Article: thm:V, Table s7-orders. -/
theorem restarted_xrfcDFunction_rorder
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
    (x₀ : E) :
    let x := xrfcDRestartedPoints trial G x₀
    let e := fun c=>‖metricCoordinates base hb (x c)‖
    (∀ᶠ c in atTop,0<e c →(e c)⁻¹ • x c∈U) →Tendsto e atTop (𝓝 0) →
    HasROrder e 2 := by
  dsimp only
  intro hadmit hconv
  have hrec := restarted_xrfcDFunction_quadratic trial hhom base hb U hU hcount ht hT
    G H r hr hG₀ hH₀ hH hG x₀ hadmit hconv
  exact rorder_power_recurrence _ (fun _=>norm_nonneg _) hconv 2 (by norm_num) hrec

end
end krylov.Convergence
