import krylov.Convergence.OrderDeferredNativeSharp
import krylov.Convergence.OrderSchurHistory
import krylov.Convergence.OrderGradientErrorTransfer
import krylov.Functions.NativeRFCFPhysicalTransfer
import krylov.Cancellation.DeferredSchurSharp

/-!
Article: main_krylov, thm:D, literal data-based DC sharp cycle error.
Use: the actual observed Schur arithmetic rule has the printed Chebyshev
constant, with no estimate homogeneity, chart, positivity or output-bound
premise. True source geometry derives every execution and error estimate.
Source: genuine scalar search-only transfer, actual Schur reference data,
compatible third-derivative response and gradient/error normalization.
-/
namespace krylov.Convergence
noncomputable section
open Matrix Set Metric krylov.Methods krylov.Reference krylov.Functions krylov.Tensor
  krylov.Nonlinear krylov.Design krylov.Secant krylov.Cancellation
open scoped InnerProductSpace NNReal Matrix.Norms.L2Operator
variable {k : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin (k+1))

/-- The actual DC cycle has a quadratic true error under only a
Lipschitz Hessian and a compact full quadratic reference family.
Article: thm:D, DC order; no third-tensor budget is assumed. -/
theorem nativeDC_error_quadratic
    (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (hb : base.PosDef)
    (mu upper : ℝ) (hmu : 0<mu) (hmuL : mu≤upper)
    (hlo : (base-mu • 1).PosSemidef) (hhi : (upper • 1-base).PosSemidef)
    (f : E → ℝ) (G : E → E) (H : E → E →L[ℝ] E)
    {r : ℝ} (hr : 0<r) (hG₀ : G 0=0) (hH₀ : H 0=cgOperator base)
    {L : ℝ≥0} (hLr : (L:ℝ)*r≤1/2)
    (hH : LipschitzOnWith L (coordinateDerivative (metricCoordinates base hb) H) (closedBall 0 r))
    (hF : ∀ z,‖metricCoordinates base hb z‖≤r → HasFDerivAt f (innerSL ℝ (G z)) z)
    (hG : ∀ z,‖metricCoordinates base hb z‖≤r → HasFDerivAt G (H z) z)
    (K : Set E) (hK : IsCompact K) (hcount : ∀ g∈K,referenceAtomCount base hb g=k+1)
    (B : ℝ) (hB : 0<B) :
    ∃ ep C : ℝ,0<ep ∧0<C ∧∀ ε : ℝ,0<ε →ε<ep →∀ u,‖u‖≤B →cgOperator base u∈K →
      ‖metricCoordinates base hb (scalarFunctionPoint (deferredDataMethod fullMemory (k+1)
          (dcSchurGaussRadauEstimate fullMemory mu upper)) (metricCoordinates base hb) f G r (ε • u) (k+1))‖≤C*ε^2 := by
  let estimate : History E → ℝ:=dcSchurGaussRadauEstimate fullMemory mu upper
  let method:=deferredDataMethod fullMemory (k+1) estimate
  let Q:=cgOperator base
  let admission:=fun u : E=>‖u‖≤B ∧Q u∈K
  let point:=fun (ε : ℝ) (u : E)=>scalarFunctionPoint method (metricCoordinates base hb) f G r (ε • u) (k+1)
  have hpre : ∀ g∈K,∀ i<k+1,CG.gradient Q g i≠0 :=
    fun g hg i hi=>cg_nonstagnation base hb g i (by rw [hcount g hg];exact hi)
  have hhom : method.Homogeneous:=deferredSchurMethod_homogeneous fullMemory (k+1) mu upper
  have hconsistent : CGConsistent method:=deferred_data_consistent fullMemory (fun _ hj=>hj) (k+1) estimate
  have hp:=cgOperator_positive base hb
  have hs g (hg : g∈K) : SmoothProbedCycleAt method 2 Q g (k+1):=
    deferred_schur_smoothCycleAt fullMemory (fun _ hj=>hj) (k+1) base hb mu upper hmu hmuL hlo hhi
      g (k+1) (hpre g hg) 2
  have hpoint : ∃ ep M : ℝ,0<ep ∧0<M ∧∀ ε : ℝ,0<ε →ε<ep →∀ u,admission u →
      ‖metricCoordinates base hb (point ε u)‖≤M*ε^2 := by
    obtain ⟨ep,C,hep,hC,hbound⟩:=scalarSearchOnlyPoint_reference_points method (fun _ _=>rfl)
      hconsistent hhom (metricCoordinates base hb) (metricCoordinates_inverse_symmetric base hb)
      f G H Q hr hG₀ hH₀ (coordinateDerivative_metric_zero base hb H hH₀) hLr hH hF hG
      hp.1 hp.2 (k+1) K hK hpre hs B hB
    refine ⟨ep,‖(metricCoordinates base hb).toContinuousLinearMap‖*C+1,hep,by positivity,?_⟩
    intro ε hε he u hu
    have hh:=hbound ε hε he u hu.1 hu.2 (k+1) le_rfl
    rw [fcQuadraticReferencePoint_full_zero base hb,smul_zero,sub_zero] at hh
    have hn:=((metricCoordinates base hb).toContinuousLinearMap.le_opNorm (point ε u)).trans
      (mul_le_mul_of_nonneg_left hh (norm_nonneg _))
    exact hn.trans (by nlinarith only [sq_nonneg ε])
  obtain ⟨ep,C,hep,hC,hbound⟩:=hpoint
  exact ⟨ep,C,hep,hC,fun ε hε he u hu hKu=>hbound ε hε he u ⟨hu,hKu⟩⟩

end
end krylov.Convergence
