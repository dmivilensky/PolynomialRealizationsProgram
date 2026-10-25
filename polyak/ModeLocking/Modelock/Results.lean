import polyak.ModeLocking.Regular.Persistence
import polyak.ModeLocking.Gradient.Continuation
import polyak.ModeLocking.Regular.Uniqueness

/-! The full mode-locking neighborhood, with the actual analytic maps,
fixed atoms and lags, and the weighted gradient at every tuning in it. -/
noncomputable section
namespace polyak.ModeLocking.RegularData.ContinuationData
open General Levels Filter Set
open scoped BigOperators Topology
variable {q:Tuning} {s:ℝ} {L:ℕ} {D:RegularData q s L} (C:D.ContinuationData)

structure LocalData (q':Tuning) where
  persistence : C.PersistenceFacts q'
  analytic_primalShift : AnalyticAt ℝ C.primalShift (Continuation.parameters q')
  analytic_weight : ∀n∈D.lags,AnalyticAt ℝ (fun p=>C.weight p n) (Continuation.parameters q')
  right_kernel_near : ∀ᶠp in 𝓝 (Continuation.parameters q'),
    (Continuation.tightMatrix D.reps D.atoms (Gradient.continuedPoint C.shift p)).mulVec (C.primal p)=0

theorem localData_near : ∀ᶠq' in 𝓝 q,Nonempty (C.LocalData q') := by
  have ha : ∀ᶠp in 𝓝 (Continuation.parameters q),AnalyticAt ℝ C.primalShift p :=
    (isOpen_analyticAt ℝ C.primalShift).mem_nhds C.analytic_primalShift
  have hw : ∀ᶠp in 𝓝 (Continuation.parameters q),∀n∈D.lags,
      AnalyticAt ℝ (fun p=>C.weight p n) p := by
    rw [Filter.eventually_all_finset]
    intro n _
    exact (isOpen_analyticAt ℝ (fun p=>C.weight p n)).mem_nhds (C.analytic_weight n)
  have hr := C.right_kernel_near.eventually_nhds
  have hqa:=Continuation.continuous_parameters.continuousAt.eventually ha
  have hqw:=Continuation.continuous_parameters.continuousAt.eventually hw
  have hqr:=Continuation.continuous_parameters.continuousAt.eventually hr
  filter_upwards [C.persistenceFacts_near,hqa,hqw,hqr] with q' hF ha hw hr
  obtain ⟨F⟩:=hF
  exact ⟨⟨F,ha,hw,hr⟩⟩

namespace LocalData
variable {C} {q':Tuning} (A:C.LocalData q')

def regularData : RegularData q' (C.shift (Continuation.parameters q')) L :=
  C.persistedData q' A.persistence

theorem primalShift_base : C.primalShift (Continuation.parameters q')=
    (C.shift (Continuation.parameters q'),fun i=>(A.regularData.primal i:ℝ)) := by
  apply Prod.ext
  · rfl
  · funext i
    exact (C.persistedPrimal_coe A.persistence i).symm

include A in
theorem sigma_eq : Threshold.sigma q'=C.shift (Continuation.parameters q') := RegularData.sigma_eq A.regularData

include A in
theorem sigmaPeriodic_eq : Threshold.sigmaPeriodic q' L=C.shift (Continuation.parameters q') :=
  RegularData.sigmaPeriodic_eq A.regularData

include A in
theorem determinant_zero : Continuation.tightDeterminant D.reps D.atoms
    (Continuation.sourcePoint q' (C.shift (Continuation.parameters q')))=0 :=
  RegularData.tightDeterminant_zero A.regularData

theorem primal_feasible : ProgramSolution (Geometry.shiftedCurve q' (C.shift (Continuation.parameters q')))
    nonzeroLags A.regularData.measure := A.regularData.primal_feasible

theorem weighted_gradient (v:Continuation.Parameters) :
    fderiv ℝ C.shift (Continuation.parameters q') v =
      -∑i,A.regularData.gradientWeight i*fderiv ℝ (Gradient.sourceCotangent (D.atoms i))
        (Continuation.parameters q') v :=
  A.regularData.weighted_gradient_direction C.primalShift A.analytic_primalShift A.primalShift_base
    A.right_kernel_near v

include A in
theorem kappa_derivative_neg :
    fderiv ℝ C.shift (Continuation.parameters q') Gradient.kappaDirection<0 :=
  RegularData.primal_kappa_derivative_neg A.regularData C.primalShift A.analytic_primalShift A.primalShift_base
    A.right_kernel_near

theorem extremal_iff (w:MeasureTheory.Measure Frequency) :
    ProgramSolution (Geometry.shiftedCurve q' (Threshold.sigma q')) nonzeroLags w ↔
      ∃c a:NNReal,0<c ∧
        w=(c:ENNReal) • A.regularData.measure+(a:ENNReal) • MeasureTheory.Measure.dirac frequencyZero ∧
        (a:ℝ)≤(c:ℝ)*∫ω,(Geometry.shiftedCurve q' (Threshold.sigma q')).minimizer ω ∂A.regularData.measure := by
  rw [A.sigma_eq]
  exact A.regularData.extremal_iff (fun n hn=>D.lags_nonzero n hn) (fun _ h=>h) w

end LocalData
end polyak.ModeLocking.RegularData.ContinuationData

namespace polyak.ModeLocking.RegularData
open General Levels Set
open scoped Topology
variable {q:Tuning} {s:ℝ} {L:ℕ} (D:RegularData q s L)

theorem mode_locking : ∃C:D.ContinuationData,∃U:Set Tuning,
    IsOpen U ∧ q∈U ∧ ∀q'∈U,Nonempty (C.LocalData q') := by
  obtain ⟨C⟩:=D.continuationData_nonempty
  obtain ⟨U,hU,ho,hq⟩:=mem_nhds_iff.mp C.localData_near
  exact ⟨C,U,ho,hq,fun q' hq'=>hU hq'⟩

end polyak.ModeLocking.RegularData
