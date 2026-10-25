import polyak.Boundary.P5.Selection
import polyak.Numerics.Parametric.ImplicitDerivative
import polyak.Numerics.Parametric.DerivativeTwo
import polyak.Boundary.P5.LocalLimits

/-! Actual derivative identities for the analytic selected central source branch. -/
namespace polyak.Boundary.P5
noncomputable section
open LeanCert.Core LeanCert.Engine Numerics.Parametric Filter Set
open scoped Topology

theorem continuation_derivative_equation {h : ℝ} (hh : h∈Ioo (0 : ℝ) (11791/500000)) :
    (jacobian Certificates.Continuation.P5.system h (Selection.continuation h)).mulVec
      (deriv Selection.continuation h)=
        -parameterDerivative Certificates.Continuation.P5.system h (Selection.continuation h) := by
  apply analytic_implicit_derivative _
    (fun i => ((Certificates.Continuation.P5.system i).checkADSupported_eq_true_iff).mp
      (Certificates.Continuation.P5.check_supported i)) (Selection.analyticAt hh)
  filter_upwards [Ioo_mem_nhds hh.1 hh.2] with s hs
  rw [Certificates.Continuation.P5.source_system]
  exact Selection.continuation_source ⟨hs.1.le,hs.2.le⟩

def continuationU (h : ℝ) : ℝ := branchU h (Selection.continuation h)

theorem continuationU_analyticAt {h : ℝ} (hh : h∈Ioo (0 : ℝ) (11791/500000)) :
    AnalyticAt ℝ continuationU h := by
  have hg:=Selection.analyticAt hh
  have hA : AnalyticAt ℝ (fun r => Selection.continuation r 0) h :=
    (ContinuousLinearMap.proj (0 : Fin 7) : (Fin 7 → ℝ) →L[ℝ] ℝ).analyticAt
      (Selection.continuation h) |>.comp hg
  unfold continuationU branchU
  fun_prop

theorem continuationU_hasDerivAt {h : ℝ} (hh : h∈Ioo (0 : ℝ) (11791/500000)) :
    HasDerivAt continuationU
      (Selection.continuation h 0+h*deriv Selection.continuation h 0) h := by
  have hg:=(Selection.analyticAt hh).differentiableAt.hasDerivAt
  have hA:=(ContinuousLinearMap.proj (0 : Fin 7) : (Fin 7 → ℝ) →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt h hg
  have hd:=(((hasDerivAt_id h).mul hA).const_add (1/2 : ℝ))
  convert hd using 1
  · funext s
    rfl
  · simp

def continuationWeight5 (h : ℝ) : ℝ :=
  1-Selection.continuation h 5-Selection.continuation h 6

theorem continuationWeight5_continuousOn :
    ContinuousOn continuationWeight5 (Icc (0 : ℝ) (11791/500000)) := by
  exact (continuousOn_const.sub ((continuous_apply 5).comp_continuousOn
    Selection.continuousOn)).sub ((continuous_apply 6).comp_continuousOn Selection.continuousOn)

theorem continuationWeight5_hasDerivAt {h : ℝ} (hh : h∈Ioo (0 : ℝ) (11791/500000)) :
    HasDerivAt continuationWeight5
      (-deriv Selection.continuation h 5-deriv Selection.continuation h 6) h := by
  have hg:=(Selection.analyticAt hh).differentiableAt.hasDerivAt
  have h5:=(ContinuousLinearMap.proj (5 : Fin 7) : (Fin 7 → ℝ) →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt h hg
  have h6:=(ContinuousLinearMap.proj (6 : Fin 7) : (Fin 7 → ℝ) →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt h hg
  have hd:=(((hasDerivAt_const h (1 : ℝ)).sub h5).sub h6)
  convert hd using 1
  · rfl
  · simp

def boundaryDerivative (t : ℝ) : ℝ :=
  (Selection.continuation (Real.cosh t-1) 0+
    (Real.cosh t-1)*deriv Selection.continuation (Real.cosh t-1) 0)*Real.sinh t/
      Real.sqrt (1+continuationU (Real.cosh t-1)^2)

theorem sourceValue_hasDerivAt {t : ℝ}
    (hh : Real.cosh t-1∈Ioo (0 : ℝ) (11791/500000)) :
    HasDerivAt (fun s => Real.arsinh (continuationU (Real.cosh s-1)))
      (boundaryDerivative t) t := by
  have hp:=(Real.hasDerivAt_cosh t).sub_const 1
  have hd:=((continuationU_hasDerivAt hh).comp t hp).arsinh
  convert hd using 1 <;> simp only [boundaryDerivative,Function.comp_apply,smul_eq_mul,div_eq_mul_inv]
  ring

end
end polyak.Boundary.P5
