import polyak.Boundary.P5.P2EndpointExpr
import polyak.Certificates.Continuation.P5Batches.Batch019
import polyak.Numerics.KernelDecide

/-! Certified inclusion of the exact algebraic P2 endpoint in the final P5 box. -/
namespace polyak.Boundary.P5
open LeanCert.Core LeanCert.Engine Numerics.Parametric

private def rootInterval : IntervalRat := ⟨78350/100000,78351/100000,by norm_num⟩
private def discrValue := dyadicValue p2DiscriminantExpr
  (fun _ => p2ParameterInterval) {precision:=-80}

private theorem discrSucceeded : succeeded discrValue=true := by kernel_decide
private theorem rootLower : rootInterval.lo^2≤(outcome discrValue).lo := by kernel_decide
private theorem rootUpper : (outcome discrValue).hi≤rootInterval.hi^2 := by kernel_decide

private def endpointEnv (i : ℕ) : IntervalRat :=
  if i=0 then p2ParameterInterval else if i=1 then rootInterval else IntervalRat.singleton 0

private def endpointValue (i : Fin 7) := dyadicValue (p2LiftExpr i) endpointEnv {precision:=-80}

private def endpointBox : Fin 7 → IntervalRat :=
  coordinateBox Certificates.Continuation.P5.Batch019.C0.center
    Certificates.Continuation.P5.Batch019.C0.radius

private def endpointCheck (i : Fin 7) : Bool := succeeded (endpointValue i) &&
  decide ((endpointBox i).lo≤(outcome (endpointValue i)).lo ∧
    (outcome (endpointValue i)).hi≤(endpointBox i).hi)

private theorem checked0 : endpointCheck 0=true := by kernel_decide
private theorem checked1 : endpointCheck 1=true := by kernel_decide
private theorem checked2 : endpointCheck 2=true := by kernel_decide
private theorem checked3 : endpointCheck 3=true := by kernel_decide
private theorem checked4 : endpointCheck 4=true := by kernel_decide
private theorem checked5 : endpointCheck 5=true := by kernel_decide
private theorem checked6 : endpointCheck 6=true := by kernel_decide

private theorem checked (i : Fin 7) : endpointCheck i=true := by
  fin_cases i
  · exact checked0
  · exact checked1
  · exact checked2
  · exact checked3
  · exact checked4
  · exact checked5
  · exact checked6

noncomputable section

private theorem algebraicRoot_mem :
    Real.sqrt (P2.atomA P2.zetaA^2-4*P2.atomB P2.zetaA)∈rootInterval := by
  have hd := dyadicValue_mem p2DiscriminantExpr (fun _ => p2ParameterInterval)
    {precision:=-80} (by norm_num) (fun _ => P2.zetaA)
    (fun _ => zetaA_mem_p2ParameterInterval) discrSucceeded
  rw [p2DiscriminantExpr_eval P2.zetaA_mem (fun _ => P2.zetaA) rfl] at hd
  have hlo : ((rootInterval.lo : ℚ) : ℝ)^2≤(outcome discrValue).lo := by exact_mod_cast rootLower
  have hhi : ((outcome discrValue).hi : ℝ)≤((rootInterval.hi : ℚ) : ℝ)^2 := by exact_mod_cast rootUpper
  have hs := Real.sq_sqrt (P2.discriminant_pos P2.zetaA_mem).le
  have hnon := Real.sqrt_nonneg (P2.atomA P2.zetaA^2-4*P2.atomB P2.zetaA)
  have hlpos : (0 : ℝ)≤rootInterval.lo := by norm_num [rootInterval]
  have hup : (0 : ℝ)≤rootInterval.hi := by norm_num [rootInterval]
  constructor <;> nlinarith [hlo.trans hd.1,hd.2.trans hhi]

/-- The algebraic source endpoint, including its two ordered square-root atoms,
lies in the actual final accepted continuation box. -/
theorem p2Endpoint_mem : FinBoxMem (p2Lift P2.zetaA) endpointBox := by
  intro i
  have hc := checked i
  simp only [endpointCheck,Bool.and_eq_true,decide_eq_true_eq] at hc
  let ρ : ℕ → ℝ := fun j => if j=0 then P2.zetaA
    else if j=1 then Real.sqrt (P2.atomA P2.zetaA^2-4*P2.atomB P2.zetaA) else 0
  have hρ : ∀ j,ρ j∈endpointEnv j := by
    intro j
    by_cases h0 : j=0
    · simpa [ρ,endpointEnv,h0] using zetaA_mem_p2ParameterInterval
    · by_cases h1 : j=1
      · simpa [ρ,endpointEnv,h0,h1] using algebraicRoot_mem
      · simpa [ρ,endpointEnv,h0,h1] using IntervalRat.mem_singleton 0
  have hp := dyadicValue_mem (p2LiftExpr i) endpointEnv {precision:=-80}
    (by norm_num) ρ hρ hc.1
  rw [p2LiftExpr_eval P2.zetaA_mem ρ (by simp [ρ]) (by simp [ρ]) i] at hp
  have hlo : ((endpointBox i).lo : ℝ)≤(outcome (endpointValue i)).lo := by exact_mod_cast hc.2.1
  have hhi : ((outcome (endpointValue i)).hi : ℝ)≤(endpointBox i).hi := by exact_mod_cast hc.2.2
  exact ⟨hlo.trans hp.1,hp.2.trans hhi⟩

/-- The physical endpoint parameter lies in the final continuation domain. -/
theorem p2Endpoint_parameter_mem : P2.Ga-1∈Certificates.Continuation.P5.Batch019.I0 := by
  norm_num [IntervalRat.mem_def,Certificates.Continuation.P5.Batch019.I0]
  constructor
  · linarith [P2.Ga_bounds.1]
  · have hl : (16989316152/10000000000 : ℝ)∈P2.parameterInterval := by norm_num [P2.parameterInterval]
    have hc := P2.G_strictAntiOn hl P2.zetaA_mem P2.zetaA_fine_bounds.1
    have hb : P2.G (16989316152/10000000000 : ℝ)<511791/500000 := by norm_num [P2.G,P2.rMinus]
    change P2.G P2.zetaA≤_
    linarith


theorem centralEndpoint_pos : 0<P2.Ga-1 := by linarith [P2.Ga_bounds.1]

theorem centralEndpoint_lt : P2.Ga-1<(11791/500000 : ℝ) := by
  have hl : (16989316152/10000000000 : ℝ)∈P2.parameterInterval := by norm_num [P2.parameterInterval]
  have hc := P2.G_strictAntiOn hl P2.zetaA_mem P2.zetaA_fine_bounds.1
  have hb : P2.G (16989316152/10000000000 : ℝ)<511791/500000 := by norm_num [P2.G,P2.rMinus]
  change P2.G P2.zetaA-1<_
  linarith

end
end polyak.Boundary.P5
