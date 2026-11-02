import krylov.Functions.PlanarBetaCentre

/-!
Article: main_krylov, thm:Fplanar, original-class admission of the centre.
Use: identify the actual endpoint-only planar centre with the final rule
of the admitted globally quadratic-consistent one-correction value method.
The canonical plane is the original normalized observation chart; all
decisions use only its actual endpoint values, gradients and retained steps.
Source: true scalar observations and the generic retained-span constructor.
-/
namespace krylov.Functions
noncomputable section
open krylov.Methods krylov.Reference krylov.Tensor.BinaryCubic
open scoped InnerProductSpace

/-- The canonical three searched planar samples. Article: thm:Fplanar. -/
def planeCycleNode (p r : ℝ) (i : ℕ) : Plane :=
  if i=0 then 0 else if i=1 then planeOfPair (p,0) else planeOfPair (p,r*p)

/-- The two actual retained planar steps. Article: thm:Fplanar. -/
def planeCycleStep (p r : ℝ) (i : ℕ) : Plane :=
  if i=0 then planeOfPair (p,0) else planeOfPair (0,r*p)

/-- True scalar/gradient endpoint observations of the canonical planar
model, including the complete actual two line objectives.
Article: main_krylov, thm:Fplanar. -/
def planeCycleTranscript (p r : ℝ) (f : Plane → ℝ) : FunctionSearchTranscript Plane 2 :=
  functionSearchTranscript f (planeCycleNode p r) (planeCycleStep p r) 2

/-- The genuine two coordinate unit directions have their actual unit
Euclidean norms. Article: main_krylov, thm:Fplanar. -/
theorem plane_axis_unit_norm : ‖planeOfPair (1,0)‖=1 ∧ ‖planeOfPair (0,1)‖=1 := by
  constructor
  · have hh := plane_norm_sq (planeOfPair (1,0))
    change ‖planeOfPair (1,0)‖^2=1^2+0^2 at hh
    nlinarith only [hh,norm_nonneg (planeOfPair (1,0))]
  · have hh := plane_norm_sq (planeOfPair (0,1))
    change ‖planeOfPair (0,1)‖^2=0^2+1^2 at hh
    nlinarith only [hh,norm_nonneg (planeOfPair (0,1))]

/-- Actual metric lengths and normalized first direction are computed
from the retained planar steps, with no hidden source coefficient.
Article: main_krylov, thm:Fplanar. -/
theorem planeCycle_step_lengths (p r : ℝ) (hp : 0<p) (hr : 0<r) :
    ‖planeOfPair (p,0)‖=p ∧ ‖planeOfPair (0,r*p)‖=r*p ∧
      NormedSpace.normalize (planeOfPair (p,0))=planeOfPair (1,0) := by
  have h0 : planeOfPair (p,0)=p • planeOfPair (1,0) := by ext i; fin_cases i <;> simp [planeOfPair]
  have hl : planeOfPair (0,r*p)=(r*p) • planeOfPair (0,1) := by ext i; fin_cases i <;> simp [planeOfPair]
  rw [h0,hl,norm_smul,norm_smul,Real.norm_of_nonneg hp.le,
    Real.norm_of_nonneg (mul_pos hr hp).le,plane_axis_unit_norm.1,plane_axis_unit_norm.2,mul_one,mul_one,
    NormedSpace.normalize_smul_of_pos hp _,NormedSpace.normalize_eq_self_of_norm_eq_one plane_axis_unit_norm.1]
  exact ⟨rfl,rfl,rfl⟩

set_option maxHeartbeats 800000 in
/-- The actual retained-step observer is exactly the endpoint-only observer
in the printed normalized plane. Article: main_krylov, thm:Fplanar. -/
theorem planeCycle_observer_eq (p r : ℝ) (hp : 0<p) (hr : 0<r) (f : Plane → ℝ) :
    metricPlaneCentreData (ContinuousLinearEquiv.refl ℝ Plane) (by decide) (planeCycleTranscript p r f)=
      planeObservedBinaryData p r (f 0) (f (planeOfPair (p,0))) (f (planeOfPair (p,r*p)))
        (gradient f 0) (gradient f (planeOfPair (p,0))) (gradient f (planeOfPair (p,r*p))) := by
  obtain ⟨h0,hl,he⟩ := planeCycle_step_lengths p r hp hr
  simp only [metricPlaneCentreData,planeCycleTranscript,functionSearchTranscript,planeCycleStep,
    observedPairDefect,observedFinalGradient,planeCycleNode,ContinuousLinearEquiv.refl_apply,
    show ¬(1:ℕ)=0 by decide,show ¬(2:ℕ)=0 by decide,show ¬(2:ℕ)=1 by decide,
    ite_true,ite_false,Nat.reduceSub,Nat.reduceAdd,h0,hl,he,mul_div_cancel_right₀ r hp.ne']
  unfold metricPlaneObservedBinaryData planeObservedBinaryData
  simp only [ContinuousLinearEquiv.refl_symm,ContinuousLinearEquiv.refl_apply,
    PiLp.inner_apply,Fin.sum_univ_two,planeOfPair,pairOfPlane,
    Matrix.cons_val_zero,Matrix.cons_val_one,Real.inner_apply,one_mul,zero_mul,add_zero]
  congr 1 <;> ring

/-- At a true planar terminal point the first-step pairing is zero exactly
when the actual terminal gradient vanishes. Article: thm:Fplanar. -/
theorem plane_first_step_pair_zero_iff (p : ℝ) (hp : p≠0) (g : Plane) (hg : g 1=0) :
    inner ℝ g (planeOfPair (p,0))=0 ↔ g=0 := by
  have hi : inner ℝ g (planeOfPair (p,0))=g 0*p := by
    simp [PiLp.inner_apply,Fin.sum_univ_two,planeOfPair,mul_comm]
  rw [hi]
  constructor
  · intro hz
    have h0 := (mul_eq_zero.mp hz).resolve_right hp
    ext i
    fin_cases i
    · exact h0
    · exact hg
  · intro hz
    rw [hz]
    simp

set_option maxHeartbeats 800000 in
/-- The actual endpoint-only budgeted centre is precisely the final rule
of the admitted original one-correction value method, on the entire
independent-beta scalar family. Thus the sharp upper policy is in the
original retained-span globally quadratic-consistent class.
Article: main_krylov, thm:Fplanar, attained class upper. -/
theorem planeBudgetObservedCentreOutput_admitted
    (B p r β : ℝ) (hp : 0<p) (hr : 0<r) (t : krylov.Tensor.BinaryCubic)
    (H : History Plane) :
    let f := planeBetaCubicObjective p r β t
    let G := gradient f
    let M := budgetedCentreValueMethod (ContinuousLinearEquiv.refl ℝ Plane) B (show 0<2 by decide)
    observedSpanFinalPolicy (by decide) M.coefficients H (planeCycleTranscript p r f)=
      planeBudgetObservedCentreOutput B p r (f 0) (f (planeOfPair (p,0))) (f (planeOfPair (p,r*p)))
        (G 0) (G (planeOfPair (p,0))) (G (planeOfPair (p,r*p))) := by
  classical
  dsimp only
  let f := planeBetaCubicObjective p r β t
  let data := planeCycleTranscript p r f
  let O := planeObservedBinaryData p r (f 0) (f (planeOfPair (p,0))) (f (planeOfPair (p,r*p)))
    (gradient f 0) (gradient f (planeOfPair (p,0))) (gradient f (planeOfPair (p,r*p)))
  let z := budgetedPlaneCentreOutput B r p O
  have hg : (gradient f (planeOfPair (p,r*p))) 1=0 := by
    simp [f,planeBetaCubicGradient_actual,planeCubicGradient_actual,planeCubicGradient,
      planarCubicGradient,planarValueCoordinateDerivative,planeOfPair,pairOfPlane]
    ring
  have hi := plane_first_step_pair_zero_iff p hp.ne' (gradient f (planeOfPair (p,r*p))) hg
  obtain ⟨h0,hl,_⟩ := planeCycle_step_lengths p r hp hr
  have hrp : r*p≠0 := (mul_pos hr hp).ne'
  have hs0 : data.lineSteps ⟨0,by decide⟩=planeOfPair (p,0) := rfl
  have hsl : data.lineSteps ⟨2-1,by decide⟩=planeOfPair (0,r*p) := rfl
  change metricPlaneResponseFinalPolicy (budgetedPlaneCentreOutput B) (ContinuousLinearEquiv.refl ℝ Plane)
    (by decide) H data=(if gradient f (planeOfPair (p,r*p))=0 then planeOfPair (p,r*p) else z)
  unfold metricPlaneResponseFinalPolicy observedSpanFinalPolicy observedSpanFinalCorrection
  change planeOfPair (p,r*p)+(if inner ℝ (gradient f (planeOfPair (p,r*p))) (planeOfPair (p,0))=0 then 0
    else ∑ i,metricPlaneResponseCoefficients (budgetedPlaneCentreOutput B)
      (ContinuousLinearEquiv.refl ℝ Plane) (by decide) H data i • data.lineSteps i)=_
  by_cases hz : gradient f (planeOfPair (p,r*p))=0
  · rw [ite_eq_left (hi.mpr hz),ite_eq_left hz,add_zero]
  · rw [ite_eq_right (fun hh=>hz (hi.mp hh)),ite_eq_right hz,metricPlaneResponse_sum,
      planeCycle_observer_eq p r hp hr f]
    dsimp only
    simp only [hs0,hsl,ContinuousLinearEquiv.refl_apply,h0,hl,mul_div_cancel_right₀ r hp.ne']
    change planeOfPair (p,r*p)+(((z 0-p)/p) • planeOfPair (p,0)+
      ((z 1-r*p)/(r*p)) • planeOfPair (0,r*p))=z
    ext i
    fin_cases i <;> simp [planeOfPair,PiLp.add_apply,PiLp.smul_apply] <;> field_simp [hp.ne',hrp] <;> ring

end
end krylov.Functions
