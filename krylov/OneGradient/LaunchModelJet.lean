import krylov.Stability.ContDiffSpectralMatrix
import krylov.Secant.Canonical
import krylov.Stability.MetricRootRegularity
set_option autoImplicit false
/-!
Article: main_krylov, prop:launch, actual moving observed-model first variation.
Use: derive the original canonical compression coefficient from primitive
smooth physical steps and segment operators, without assuming a model jet.
Source: the exact genuine physical canonical flag identity, real inverse
domains and zero-reference-factor product differentiation.
-/

namespace krylov.OneGradient
noncomputable section
open Matrix Filter Topology krylov.Secant krylov.Stability
open scoped BigOperators Matrix.Norms.L2Operator
variable {n : ℕ}

/-- The true full physical latest-information model computed from the original
chronological evaluated columns and their actual segment observations.
Use: its derivative is derived from primitive data, not supplied as a coefficient field.
Article: main_krylov, prop:launch. -/
def launchObservedModel (S : Matrix (Fin n) (Fin n) ℝ)
    (A : ℕ → Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  inverseCongruence S (latest (Sᵀ*pairImages S A))

/-- The original moving observed-model error has exactly its true frozen
oblique-compression first derivative for arbitrary primitive C1 physical data.
Use: identify the source launch coefficient before any trajectory or remainder
specialization; derivatives of the moving columns disappear for a proved reason.
Article: main_krylov, prop:launch, sum Pi_l transpose E_l Pi_l.
Proof: actual local nonsingularity comes from the primitive reference matrix.
The exact physical flag identity holds on that genuine neighborhood. Each true
operator increment vanishes at the quadratic reference, so both moving-flag
product derivative terms vanish; only the original increment derivative survives. -/
theorem launch_model_error_first_jet
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (S : ℝ → Matrix (Fin n) (Fin n) ℝ) (hS : ContDiffAt ℝ 1 S 0) (hu : IsUnit (S 0).det)
    (A : ℝ → ℕ → Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ k,ContDiffAt ℝ 1 (fun t => A t k) 0)
    (hsym : ∀ t k,(A t k).IsSymm) (hA0 : ∀ k,A 0 k=base) :
    let P := fun l => transportedFlag (metricRoot base*S 0) l
    let J := krylov.Reference.cgOperator (metricRoot base)⁻¹
    HasDerivAt (fun t => krylov.Reference.cgOperator (relativeOperator base
        (A t n-launchObservedModel (S t) (A t))))
      (∑ l∈Finset.range n,krylov.Reference.cgOperator (P l)ᵀ*
        (J*(deriv (fun t => krylov.Reference.cgOperator (A t (l+1))) 0-
          deriv (fun t => krylov.Reference.cgOperator (A t l)) 0)*J)*krylov.Reference.cgOperator (P l)) 0 := by
  let V := fun t => metricRoot base*S t
  let P := fun l t => transportedFlag (V t) l
  let J := krylov.Reference.cgOperator (metricRoot base)⁻¹
  let D := fun l t => J*(krylov.Reference.cgOperator (A t (l+1))-krylov.Reference.cgOperator (A t l))*J
  have hV : ContDiffAt ℝ 1 V 0 := contDiffAt_const.mul hS
  have hv : IsUnit (V 0).det := by
    change IsUnit (metricRoot base*S 0).det
    rw [Matrix.det_mul]
    exact (metricRoot_det_unit base hb).mul hu
  have hVi := contDiff_spectral_inverse V 0 hV hv
  have hP (l : ℕ) : ContDiffAt ℝ 1 (P l) 0 :=
    (hV.mul contDiffAt_const).mul hVi
  have hPt (l : ℕ) : ContDiffAt ℝ 1 (fun t => (P l t)ᵀ) 0 := by
    let L := (Matrix.transposeLinearEquiv (R := ℝ) (m := Fin n) (n := Fin n) (α := ℝ)).toContinuousLinearEquiv
    exact L.toContinuousLinearMap.contDiff.contDiffAt.comp 0 (hP l)
  have hAop (k : ℕ) : ContDiffAt ℝ 1 (fun t => krylov.Reference.cgOperator (A t k)) 0 :=
    matrixOperator_contDiffAt _ 0 (hA k)
  have hD0 (l : ℕ) : D l 0=0 := by
    simp only [D,hA0,sub_self,mul_zero,zero_mul]
  have hD (l : ℕ) : HasDerivAt (D l)
      (J*(deriv (fun t => krylov.Reference.cgOperator (A t (l+1))) 0-
        deriv (fun t => krylov.Reference.cgOperator (A t l)) 0)*J) 0 := by
    have hd := ((hAop (l+1)).differentiableAt (by norm_num)).hasDerivAt.sub
      ((hAop l).differentiableAt (by norm_num)).hasDerivAt
    have hh := ((hasDerivAt_const (0 : ℝ) J).clm_comp hd).clm_comp (hasDerivAt_const (0 : ℝ) J)
    simpa only [D,Pi.sub_apply,ContinuousLinearMap.mul_def,ContinuousLinearMap.zero_comp,ContinuousLinearMap.comp_zero,zero_add,add_zero] using hh
  have hterm (l : ℕ) : HasDerivAt
      (fun t => krylov.Reference.cgOperator (P l t)ᵀ*D l t*krylov.Reference.cgOperator (P l t))
      (krylov.Reference.cgOperator (P l 0)ᵀ*
        (J*(deriv (fun t => krylov.Reference.cgOperator (A t (l+1))) 0-
          deriv (fun t => krylov.Reference.cgOperator (A t l)) 0)*J)*krylov.Reference.cgOperator (P l 0)) 0 := by
    have hleft := matrixOperator_contDiffAt _ 0 (hPt l)
    have hright := matrixOperator_contDiffAt _ 0 (hP l)
    have hh := ((hleft.differentiableAt (by norm_num)).hasDerivAt.clm_comp (hD l)).clm_comp
      (hright.differentiableAt (by norm_num)).hasDerivAt
    simpa only [krylov.Reference.cgOperator,ContinuousLinearMap.mul_def,hD0,ContinuousLinearMap.comp_zero,ContinuousLinearMap.zero_comp,zero_add,add_zero] using hh
  have hsum := HasDerivAt.fun_sum (u := Finset.range n) (fun l _ => hterm l)
  have hSunit : ∀ᶠ t in 𝓝 (0 : ℝ),IsUnit (S t).det := by
    have hunit : IsUnit (S 0) := (Matrix.isUnit_iff_isUnit_det _).mpr hu
    exact (hS.continuousAt.tendsto.eventually (Units.isOpen.mem_nhds hunit)).mono
      (fun t ht => (Matrix.isUnit_iff_isUnit_det _).mp ht)
  have he : (fun t => krylov.Reference.cgOperator (relativeOperator base
        (A t n-launchObservedModel (S t) (A t))))=ᶠ[𝓝 0]
      (fun t => ∑ l∈Finset.range n,krylov.Reference.cgOperator (P l t)ᵀ*D l t*krylov.Reference.cgOperator (P l t)) := by
    filter_upwards [hSunit] with t ht
    have hm := congrArg krylov.Reference.cgOperator
      (physical_canonical_flag_identities (S t) base ht hb (A t) (hsym t)).1
    simpa only [krylov.Reference.cgOperator,map_sum,map_mul,map_sub,relativeOperator,launchObservedModel,D,J,P,V] using hm
  dsimp only
  exact hsum.congr_of_eventuallyEq he

end
end krylov.OneGradient
