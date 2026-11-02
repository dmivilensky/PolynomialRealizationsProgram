import krylov.Convergence.EvaluatedInputs
import krylov.Convergence.EvaluatedOutputFields
import krylov.Convergence.OneGradientReferenceComparison

/-!
Article: main_krylov, prop:EL and lem:cycle-transfer, actual evaluated-launch shadow.
Use: derive genuine quadratic shadow estimates for every actual scalar
query and its unevaluated output from literal V1--V3 and true local function
smoothness. The native output error is a conclusion, not a supplied field.
Source: actual compact source inputs and the genuine policy-field comparison.
-/
namespace krylov.Convergence
noncomputable section
open Matrix Set Metric Filter Topology krylov.Methods krylov.Reference krylov.Functions krylov.Nonlinear
  krylov.Stability
open scoped InnerProductSpace NNReal
variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)

/-- The actual quadratic evaluated-launch reference output is precisely the true
minimizer after the full active cycle. Article: lem:consistent, prop:EL. -/
theorem evaluatedLaunchReferenceOutput_zero
    (trial : History E → ℝ) (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef) (u : E)
    (hcount : referenceAtomCount base hb (cgOperator base u)=n)
    (ht : ∀ i<n,0<trial (oneGradientRun (evaluatedLaunchMethod trial)
      (fun _=>cgOperator base) (cgOperator base u) i)) :
    oneGradientReferenceOutput (evaluatedLaunchMethod trial) (cgOperator base) u n=0 := by
  have hs := cg_terminates base hb (cgOperator base u)
  rw [hcount] at hs
  have hterm := evaluatedLaunch_reference_output_gradient trial (cgOperator base)
    (cgOperator_positive base hb).1 (cgOperator_positive base hb).2 (cgOperator base u) n
    (fun i hi=>cg_nonstagnation base hb (cgOperator base u) i (by rw [hcount];exact hi))
    (fun i hi=>(ht i hi).ne')
  rw [hs] at hterm
  rw [OneGradientMethod.outputGradient,oneGradientRun_quadratic_gradient] at hterm
  have hz : cgOperator base (oneGradientReferenceOutput (evaluatedLaunchMethod trial) (cgOperator base) u n)=0 := by
    simpa only [oneGradientReferenceOutput,oneGradientReferencePoint,map_add] using hterm
  by_contra hn
  have hp := (cgOperator_positive base hb).2 _ hn
  rw [hz,inner_zero_right] at hp
  exact (lt_irrefl 0) hp

/-- Every genuine evaluated evaluated-launch vertex has a uniform quadratic shadow,
and the actual virtual output has uniform quadratic error, under precisely
the original compact full-atom and primitive trial hypotheses.
Article: main_krylov, prop:EL and Table s7-orders. -/
theorem evaluatedLaunchFunction_compact_reference_comparison
    (trial : History E → ℝ) (hhom : ObservedTrialHomogeneous trial)
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (U : Set E) (hU : IsCompact U)
    (hcount : ∀ u∈U,referenceAtomCount base hb (cgOperator base u)=n)
    (ht : ∀ u∈U,∀ i<n,0<trial (oneGradientRun (evaluatedLaunchMethod trial)
      (fun _=>cgOperator base) (cgOperator base u) i))
    (hT : ∀ u∈U,∀ i<n,ContDiffAt ℝ 2 (trialCoordinate trial i)
      (oneGradientData (evaluatedLaunchMethod trial) (fun _=>cgOperator base) (cgOperator base u) i))
    (G : E → E) (H : E → E →L[ℝ] E) (r : ℝ) (hr : 0<r)
    (hG₀ : G 0=0) (hH₀ : H 0=cgOperator base) {L : ℝ≥0} (hH : LipschitzOnWith L H (ball 0 r))
    (hG : ∀ x∈ball 0 r,HasFDerivAt G (H x) x) :
    ∃ ep C : ℝ,0<ep ∧0<C ∧∀ ε : ℝ,0<ε → ε<ep →∀ u∈U,
      (∀ i≤n,‖evaluatedLaunchFunctionPoint trial G (ε • u) i-
        ε • oneGradientReferencePoint (evaluatedLaunchMethod trial) (cgOperator base) u i‖≤C*ε^2) ∧
      ‖evaluatedLaunchFunctionOutput trial G (ε • u)‖≤C*ε^2 := by
  let Q := cgOperator base
  let K := Q '' U
  have hK : IsCompact K := hU.image Q.continuous
  have hreg := evaluatedLaunchFiniteField_contDiffAt_directions trial base hb U hcount ht hT
  obtain ⟨δ,Cf,hδ,hCf,hcomparison⟩ := compact_oneGradient_native_point_comparison
    (evaluatedLaunchMethod trial) Q n K hK hreg
    (fun A g c hc=>evaluatedLaunch_policy_homogeneous trial hhom A g c hc n)
  obtain ⟨es,S,hes,hS,hsource⟩ := evaluatedLaunchFunction_compact_source_inputs trial hhom base hb U hU hcount ht hT
    G H r hr hG₀ hH₀ hH hG
  have hcont : ContinuousAt H 0 := hH.continuousOn.continuousAt (isOpen_ball.mem_nhds (mem_ball_self hr))
  obtain ⟨el,M,hel,_,hloc⟩ := evaluatedLaunchFunction_compact_localization trial hhom base hb U hU hcount ht hT
    G H r hr hG₀ hH₀ hcont hG
  let C := (n+1:ℕ)*Cf*S+1
  have hC : 0<C := by dsimp only [C]; positivity
  refine ⟨min es (min el (δ/(S+1))),C,by positivity,hC,?_⟩
  intro ε hε he u hu
  have hs := (hsource ε hε (he.trans_le (min_le_left _ _)) u hu).1
  have hp := (hloc ε hε (he.trans_le ((min_le_right _ _).trans (min_le_left _ _))) u hu).1
  have hinput : ‖oneGradientFunctionInput (evaluatedLaunchMethod trial) G H Q ε u n‖≤δ := by
    have hh := (lt_div_iff₀ (by positivity : 0<S+1)).mp
      (he.trans_le ((min_le_right _ _).trans (min_le_right _ _)))
    exact hs.trans (by nlinarith only [hh,hε])
  have hruns := oneGradientFunctionRun_eq_of_local (evaluatedLaunchMethod trial) G H (ε • u) n r
    hH.continuousOn hG (fun i hi=>(hp i hi).1)
  obtain ⟨hpoints,hout⟩ := hcomparison G H ε hε u ⟨u,hu,rfl⟩ hinput hruns
  have hbound (i : ℕ) (hi : i≤n+1) :
      (i:ℝ)*(Cf*ε*‖oneGradientFunctionInput (evaluatedLaunchMethod trial) G H Q ε u n‖)≤C*ε^2 := by
    have hs' := mul_le_mul_of_nonneg_left hs (mul_nonneg hCf.le hε.le)
    have hi' : (i:ℝ)≤(n+1:ℕ) := Nat.cast_le.mpr hi
    have hm := mul_le_mul_of_nonneg_right hi' (mul_nonneg (mul_nonneg hCf.le hS.le) (sq_nonneg ε))
    have hstep := mul_le_mul_of_nonneg_left hs' (Nat.cast_nonneg i)
    dsimp only [C]
    nlinarith only [hm,hstep,sq_nonneg ε]
  refine ⟨fun i hi=>(hpoints i hi).trans (hbound i (by omega)),?_⟩
  rw [evaluatedLaunchReferenceOutput_zero trial base hb u (hcount u hu) (ht u hu),smul_zero,sub_zero] at hout
  exact hout.trans (hbound (n+1) le_rfl)

end
end krylov.Convergence
