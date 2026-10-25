import polyak.Boundary.P5.Selection
import polyak.Boundary.P5.P2Endpoint
import polyak.Boundary.P5.CriticalEndpoint

/-! Exact critical and P2 joins for the actual global P5 continuation. -/
noncomputable section
namespace polyak.Boundary.P5
open LeanCert.Core LeanCert.Engine Numerics.Parametric

private theorem accepted_last : checkCorrelated Certificates.Continuation.P5.system
    Certificates.Continuation.P5.Batch019.I0 Certificates.Continuation.P5.Batch019.C0
    {precision:=-80}=true := by
  simpa only [allCorrelatedAccepted,Certificates.Continuation.P5.Batch019.slabs,
    List.all_cons,List.all_nil,Bool.and_true] using Certificates.Continuation.P5.Batch019.accepted

private theorem accepted_initial : checkCorrelated Certificates.Continuation.P5.system
    Certificates.Continuation.P5.Batch000.I0 Certificates.Continuation.P5.Batch000.C0
    {precision:=-80}=true := by
  simpa only [allCorrelatedAccepted,Certificates.Continuation.P5.Batch000.slabs,
    List.all_cons,List.all_nil,Bool.and_true] using Certificates.Continuation.P5.Batch000.accepted

/-- The selected branch starts at the exact previously constructed critical algebraic data. -/
theorem continuation_zero : Selection.continuation 0=criticalPoint := by
  have hz : (0 : ℝ)∈Certificates.Continuation.P5.Batch000.I0 := by
    norm_num [Certificates.Continuation.P5.Batch000.I0,IntervalRat.mem_def]
  obtain ⟨x,_,hu⟩ := checkCorrelated_sound _ _ _ _ accepted_initial 0 hz
  have hc := Selection.continuation_mem (0 : Fin 20) hz
  have hsource := Selection.continuation_source (by norm_num : (0 : ℝ)∈Set.Icc 0 (11791/500000))
  have he1 := hu (Selection.continuation 0) ⟨hc,by
    rwa [Certificates.Continuation.P5.source_system]⟩
  have he2 := hu criticalPoint ⟨criticalPoint_mem,by
    rw [Certificates.Continuation.P5.source_system]
    exact regularSystem_criticalPoint⟩
  exact he1.trans he2.symm

/-- The selected branch reaches the exact rational P2 source endpoint. -/
theorem continuation_endpoint : Selection.continuation (P2.Ga-1)=p2Lift P2.zetaA := by
  have hz := p2Endpoint_parameter_mem
  have hdom : P2.Ga-1∈Set.Icc (0 : ℝ) (11791/500000) := by
    constructor
    · linarith [P2.Ga_bounds.1]
    · exact centralEndpoint_lt.le
  obtain ⟨x,_,hu⟩ := checkCorrelated_sound _ _ _ _ accepted_last (P2.Ga-1) hz
  have hc := Selection.continuation_mem (19 : Fin 20) hz
  have hsource := Selection.continuation_source hdom
  have he1 := hu (Selection.continuation (P2.Ga-1)) ⟨hc,by
    rwa [Certificates.Continuation.P5.source_system]⟩
  have he2 := hu (p2Lift P2.zetaA) ⟨p2Endpoint_mem,by
    rw [Certificates.Continuation.P5.source_system]
    exact p2Endpoint_source⟩
  exact he1.trans he2.symm

theorem continuation_weight5_endpoint :
    1-Selection.continuation (P2.Ga-1) 5-Selection.continuation (P2.Ga-1) 6=0 := by
  rw [continuation_endpoint]
  change 1-P2.W P2.zetaA-(1-P2.W P2.zetaA)=0
  ring

theorem continuation_endpoint_u : branchU (P2.Ga-1) (Selection.continuation (P2.Ga-1))=P2.u P2.zetaA := by
  rw [continuation_endpoint]
  exact (p2Lift_coordinates P2.zetaA_mem).1

end polyak.Boundary.P5
