import krylov.Convergence.OrderDeferredCoordinates
import krylov.Functions.MetricFCSpatialResponse

/-!
Article: main_krylov, thm:D and thm:DC, actual deferred tensor coefficient.
Use: the genuine native scalar leading coefficient is precisely the printed
deferred CG flag/tail response on compatible slices of the true third
derivative. The coefficient includes the actual observed reference estimate.
Source: complete joint policy derivative and actual CG midpoint differences.
-/
namespace krylov.Convergence
noncomputable section
open Matrix Set Metric Filter Topology Finset krylov.Cancellation krylov.Methods krylov.Reference
  krylov.Functions krylov.Stability krylov.Variation krylov.Envelope krylov.Secant krylov.Nonlinear
open scoped InnerProductSpace BigOperators NNReal Matrix.Norms.L2Operator
variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)

/-- The actual native deferred compatible-tensor coefficient is the literal
printed response on genuine successive CG midpoint slices. Article: thm:D. -/
theorem deferredTensorLeading_eq_response
    (estimate : History E → ℝ)
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (D : E →L[ℝ] E →L[ℝ] E) (hDsym : ∀ v,(D v).toLinearMap.IsSymmetric)
    (u : E) (k : ℕ) (hcount : referenceAtomCount base hb (cgOperator base u)=n) (hfull : k+1=n)
    (ha :
      let H:=methodRun (deferredDataMethod fullMemory (k+1) estimate)
        (fun _=>cgOperator base) (fun _=>cgOperator base) (cgOperator base u) k
      ContDiffAt ℝ 2 (historyEstimateChart estimate H.queryShape H.observationList.length)
        (observedArray H.observationList.length H.observationList))
    (ha0 : 0<estimate (methodRun (deferredDataMethod fullMemory (k+1) estimate)
      (fun _=>cgOperator base) (fun _=>cgOperator base) (cgOperator base u) k)) :
    let Q:=cgOperator base
    let a0:=estimate (methodRun (deferredDataMethod fullMemory (k+1) estimate)
      (fun _=>Q) (fun _=>Q) (Q u) k)
    cgOperator (metricRoot base)⁻¹ (searchOnlyTensorLeading (deferredDataMethod fullMemory (k+1) estimate) Q D u)=
      deferredResponse base (Q u) k (1-CG.length Q (Q u) k/a0) (fcCompatibleIncrements base hb D u) := by
  let z:=metricFCReferenceInputJet (cgOperator base) D u n
  have hc:=deferredFiniteTerminal_fderiv_response estimate base hb (cgOperator base u) k hcount hfull ha ha0 z
    (fun i=>hDsym _)
  have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin n))=n := finrank_euclideanSpace_fin
  unfold searchOnlyTensorLeading
  rw [hdim]
  apply hc.trans
  unfold deferredResponse
  apply sum_congr rfl
  intro l hl
  have hl0 : l<n := by have hh:=mem_range.mp hl;omega
  have hl1 : l+1<n := by have hh:=mem_range.mp hl;omega
  congr 2
  simp only [fcFiniteDrift,dite_eq_left hl0,dite_eq_left hl1,z,metricFCReferenceInputJet,
    physicalCanonicalMatrix_sub,fcCompatibleIncrements]

/-- The actual deferred scalar-function output has the printed compatible
tensor expansion for every positive primitive smooth homogeneous observed
estimate. True scalar derivatives discharge all tensor-symmetry requirements.
Concrete interval estimates discharge the estimate hypotheses separately.
Article: main_krylov, thm:D and thm:DC. -/
theorem deferredFunctionPoint_spatial_leading_gradient
    (estimate : History E → ℝ)
    (hhom : (deferredDataMethod fullMemory n estimate).Homogeneous)
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef) (k : ℕ) (hfull : k+1=n)
    (f : E → ℝ) (G : E → E) (H : E → E →L[ℝ] E)
    (D : E →L[ℝ] E →L[ℝ] E) (hD : HasFDerivAt H D 0)
    {r : ℝ} (hr : 0<r) (hG₀ : G 0=0) (hH₀ : H 0=cgOperator base)
    {L : ℝ≥0} (hLr : (L:ℝ)*r≤1/2)
    (hH : LipschitzOnWith L (coordinateDerivative (metricCoordinates base hb) H) (closedBall 0 r))
    (hF : ∀ z,‖metricCoordinates base hb z‖≤r →HasFDerivAt f (innerSL ℝ (G z)) z)
    (hG : ∀ z,‖metricCoordinates base hb z‖≤r →HasFDerivAt G (H z) z)
    (K : Set E) (hK : IsCompact K) (hcount : ∀ g∈K,referenceAtomCount base hb g=n)
    (ha : ∀ g∈K,
      let J:=methodRun (deferredDataMethod fullMemory n estimate)
        (fun _=>cgOperator base) (fun _=>cgOperator base) g k
      ContDiffAt ℝ 2 (historyEstimateChart estimate J.queryShape J.observationList.length)
        (observedArray J.observationList.length J.observationList))
    (ha0 : ∀ g∈K,0<estimate (methodRun (deferredDataMethod fullMemory n estimate)
      (fun _=>cgOperator base) (fun _=>cgOperator base) g k))
    (B : ℝ) (hB : 0<B) :
    ∀ η : ℝ,0<η →∃ ep : ℝ,0<ep ∧∀ ε : ℝ,0<ε →ε<ep →∀ u,‖u‖≤B →cgOperator base u∈K →
      let Q:=cgOperator base
      let a0:=estimate (methodRun (deferredDataMethod fullMemory n estimate) (fun _=>Q) (fun _=>Q) (Q u) k)
      ‖cgOperator (metricRoot base)⁻¹
        (G (scalarFunctionPoint (deferredDataMethod fullMemory n estimate) (metricCoordinates base hb) f G r (ε • u) n))-
        ε^2 • deferredResponse base (Q u) k (1-CG.length Q (Q u) k/a0) (fcCompatibleIncrements base hb D u)‖≤η*ε^2 := by
  let m:=deferredDataMethod fullMemory n estimate
  let T:=metricCoordinates base hb
  let J:=‖T.symm.toContinuousLinearMap‖
  have hc : CGConsistent m := deferred_data_consistent fullMemory (fun _ hj=>hj) n estimate
  have hp:=cgOperator_positive base hb
  have hpre g (hg : g∈K) i (hi : i<n) : CG.gradient (cgOperator base) g i≠0 :=
    cg_nonstagnation base hb g i (by rw [hcount g hg];exact hi)
  have hs g (hg : g∈K) : SmoothProbedCycleAt m 2 (cgOperator base) g n := by
    apply deferred_data_smoothCycleAt fullMemory (fun _ hj=>hj) n estimate _ hp.1 hp.2 g n (hpre g hg) 2
    · intro i _ hi
      have hik : i=k := by omega
      subst i
      exact ha g hg
    · intro i _ hi
      have hik : i=k := by omega
      subst i
      exact ha0 g hg
  have hpre' : ∀ g∈K,∀ i<Module.finrank ℝ E,CG.gradient (cgOperator base) g i≠0 := by
    simpa only [finrank_euclideanSpace_fin] using hpre
  have hs' : ∀ g∈K,SmoothProbedCycleAt m 2 (cgOperator base) g (Module.finrank ℝ E) := by
    simpa only [finrank_euclideanSpace_fin] using hs
  intro η hη
  obtain ⟨ep,hep,hbound⟩:=scalarSearchOnlyPoint_leading_gradient m (fun _ _=>rfl) hc hhom T
    (metricCoordinates_inverse_symmetric base hb) f G H (cgOperator base) D hD hr hG₀ hH₀
    (coordinateDerivative_metric_zero base hb H hH₀) hLr hH hF hG hp.1 hp.2 K hK hpre' hs' B hB
    (η/(J+1)) (by positivity)
  refine ⟨ep,hep,?_⟩
  intro ε hε he u hu hKu
  have hbnd:=hbound ε hε he u hu hKu
  simp only [finrank_euclideanSpace_fin] at hbnd
  have hsym v:=genuine_third_slice_symmetric T f G H D hD hr hF hG v
  have hmethod : deferredDataMethod fullMemory (k+1) estimate=deferredDataMethod fullMemory n estimate :=
    congrArg (fun N=>deferredDataMethod fullMemory N estimate) hfull
  have hcoeff:=deferredTensorLeading_eq_response estimate base hb D hsym u k (hcount _ hKu) hfull
    (by
      let P:=fun J : History E=>ContDiffAt ℝ 2
        (historyEstimateChart estimate J.queryShape J.observationList.length)
        (observedArray J.observationList.length J.observationList)
      have hj:=congrArg (fun method : ProbedMethod E=>methodRun method
        (fun _=>cgOperator base) (fun _=>cgOperator base) (cgOperator base u) k) hmethod
      exact Eq.mpr (congrArg P hj) (ha _ hKu))
    (by simpa only [hmethod] using ha0 _ hKu)
  simp only [hmethod] at hcoeff
  have hn:=T.symm.toContinuousLinearMap.le_opNorm
    (G (scalarFunctionPoint m T f G r (ε • u) n)-ε^2 • searchOnlyTensorLeading m (cgOperator base) D u)
  rw [map_sub,map_smul] at hn
  change ‖cgOperator (metricRoot base)⁻¹ (G (scalarFunctionPoint m T f G r (ε • u) n))-
    ε^2 • cgOperator (metricRoot base)⁻¹ (searchOnlyTensorLeading m (cgOperator base) D u)‖≤_ at hn
  rw [hcoeff] at hn
  apply hn.trans
  have hηeq : (η/(J+1))*(J+1)=η := div_mul_cancel₀ η (by dsimp only [J];positivity)
  have hJ : 0≤J := norm_nonneg _
  have hquot : 0≤η/(J+1) := by positivity
  have hco : J*(η/(J+1))≤η := by nlinarith only [hηeq,hquot]
  exact (mul_le_mul_of_nonneg_left hbnd hJ).trans
    (by nlinarith only [mul_le_mul_of_nonneg_right hco (sq_nonneg ε)])

end
end krylov.Convergence
