import krylov.OneGradient.LaunchFirstJet
import krylov.Stability.C1CubicProduct
set_option autoImplicit false
/-!
Article: main_krylov, thm:local(a), actual vanishing-gradient cubic launch.
Use: the genuine full observed-model output keeps the actual increments
and actual incoming gradient, with a cubic remainder from primitive C-one data.
Source: exact native model-error factorization and three true vanishing
factors, using the proved C-one cubic coefficient-freezing theorem. -/

namespace krylov.OneGradient
noncomputable section
open Matrix Filter Topology Asymptotics krylov.Methods krylov.Reference krylov.Secant krylov.Stability
open scoped BigOperators Matrix.Norms.L2Operator
variable {n : ℕ} {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- The genuine full observed-model output has its frozen-reference-flag
expansion in the actual increments and actual incoming gradient, with a
cubic remainder whenever that true gradient vanishes at the reference.
Only primitive C-one data on the full perturbation space are required.
Use: this is the native known-base cubic launch identity before computing
the explicit first-order incoming gradient; no output jet is assumed.
Article: main_krylov, thm:local(a).
Proof: the true full-model normal identity factors the actual semantic
output into genuine moving flags, actual increments and the actual inverse
query. True reference gradient and increments vanish. Freezing only the
smooth flags and inverse coefficients gives three actual first-order
vanishing factors per error term, hence cubic order. -/
theorem launch_semantic_c1_vanishing_gradient_remainder
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (S : X → Matrix (Fin n) (Fin n) ℝ) (hS : ContDiffAt ℝ 1 S 0) (hu : IsUnit (S 0).det)
    (A : X → ℕ → Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ k,ContDiffAt ℝ 1 (fun z => A z k) 0)
    (hsym : ∀ z k,(A z k).IsSymm) (hA0 : ∀ k,A 0 k=base)
    (g : X → EuclideanSpace ℝ (Fin n)) (hg : ContDiffAt ℝ 1 g 0) (hg0 : g 0=0) :
    let P := fun l => transportedFlag (metricRoot base*S 0) l
    let R := cgOperator (metricRoot base)⁻¹
    (fun z => R (launchSemanticGradient (S z) (A z) (g z))+
      ∑ l∈Finset.range n,cgOperator (P l)ᵀ
        ((R*(cgOperator (A z (l+1))-cgOperator (A z l))*R) (cgOperator (P l) (R (g z)))))
        =O[𝓝 0] (fun z => ‖z‖^3) := by
  let J := fun z => launchObservedModel (S z) (A z)
  let R := cgOperator (metricRoot base)⁻¹
  let V := fun z => metricRoot base*S z
  let P := fun l z => transportedFlag (V z) l
  let D := fun l z => R*(cgOperator (A z (l+1))-cgOperator (A z l))*R
  let B := fun z => cgOperator (metricRoot base)*cgOperator (J z)⁻¹
  let v := fun z => B z (g z)
  have hJ0 : J 0=base := by
    change launchObservedModel (S 0) (A 0)=base
    rw [show A 0=(fun _ => base) from funext hA0]
    exact launch_model_reference base (S 0) hb.1.isSymm hu
  have hmodel := (launch_model_contDiff S hS hu A hA).2
  have hinv := launch_model_inverse_contDiff base hb S hS hu A hA hA0
  have hB : ContDiffAt ℝ 1 B 0 := contDiffAt_const.mul (matrixOperator_contDiffAt _ 0 hinv)
  have hB0 : B 0=R := by
    apply ContinuousLinearMap.ext
    intro w
    change cgOperator (metricRoot base) (cgOperator (J 0)⁻¹ w)=R w
    rw [hJ0]
    have hcancel : cgOperator base (cgOperator base⁻¹ w)=w := by
      simp only [cgOperator,← mul_apply_eq_comp,← map_mul,
        Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hb.det_pos.ne'),map_one,one_apply_eq_self]
    have he := canonical_reference_action base hb (cgOperator base⁻¹ w)
    rw [hcancel] at he
    exact he.symm
  have hV : ContDiffAt ℝ 1 V 0 := contDiffAt_const.mul hS
  have hunitV : IsUnit (V 0).det := by
    change IsUnit (metricRoot base*S 0).det
    rw [Matrix.det_mul]
    exact (metricRoot_det_unit base hb).mul hu
  have hVi := contDiff_spectral_inverse V 0 hV hunitV
  have hP (l : ℕ) : ContDiffAt ℝ 1 (P l) 0 := (hV.mul contDiffAt_const).mul hVi
  have hPt (l : ℕ) : ContDiffAt ℝ 1 (fun z => (P l z)ᵀ) 0 := by
    let L := (Matrix.transposeLinearEquiv (R := ℝ) (m := Fin n) (n := Fin n) (α := ℝ)).toContinuousLinearEquiv
    exact L.toContinuousLinearMap.contDiff.contDiffAt.comp 0 (hP l)
  have hD (l : ℕ) : ContDiffAt ℝ 1 (D l) 0 :=
    (contDiffAt_const.mul ((matrixOperator_contDiffAt _ 0 (hA (l+1))).sub
      (matrixOperator_contDiffAt _ 0 (hA l)))).mul contDiffAt_const
  have hD0 (l : ℕ) : D l 0=0 := by simp only [D,hA0,sub_self,mul_zero,zero_mul]
  have hterm (l : ℕ) :
      (fun z => cgOperator (P l z)ᵀ (D l z (cgOperator (P l z) (v z)))-
        cgOperator (P l 0)ᵀ (D l z (cgOperator (P l 0) (R (g z))))) =O[𝓝 0] (fun z => ‖z‖^3) := by
    have ht := c1_vanishing_input_freeze_remainder (fun z => cgOperator (P l z)ᵀ) (D l)
      (fun z => cgOperator (P l z)*B z) g
      ((matrixOperator_contDiffAt _ 0 (hPt l)).differentiableAt (by norm_num))
      ((hD l).differentiableAt (by norm_num))
      (((matrixOperator_contDiffAt _ 0 (hP l)).mul hB).differentiableAt (by norm_num))
      (hg.differentiableAt (by norm_num)) (hD0 l) hg0
    simpa only [mul_apply_eq_comp,hB0,v] using ht
  have hsum := (IsBigO.sum (s := Finset.range n) (fun l _ => hterm l)).neg_left
  have hSunit : ∀ᶠ z in 𝓝 (0 : X),IsUnit (S z).det := by
    have hunit : IsUnit (S 0) := (Matrix.isUnit_iff_isUnit_det _).mpr hu
    exact (hS.continuousAt.eventually (Units.isOpen.mem_nhds hunit)).mono
      (fun z hz => (Matrix.isUnit_iff_isUnit_det _).mp hz)
  have hJunit : ∀ᶠ z in 𝓝 (0 : X),IsUnit (J z).det := by
    have hunit : IsUnit (J 0) := by
      rw [hJ0]
      exact (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hb.det_pos.ne')
    exact (hmodel.continuousAt.eventually (Units.isOpen.mem_nhds hunit)).mono
      (fun z hz => (Matrix.isUnit_iff_isUnit_det _).mp hz)
  have heq : (fun z => R (launchSemanticGradient (S z) (A z) (g z)))=ᶠ[𝓝 0]
      (fun z => -(∑ l∈Finset.range n,cgOperator (P l z)ᵀ (D l z (cgOperator (P l z) (v z))))) := by
    filter_upwards [hSunit,hJunit] with z hs hj
    rw [launch_normal_identity base hb (S z) (A z) hj (g z)]
    have hm := congrArg cgOperator
      (physical_canonical_flag_identities (S z) base hs hb (A z) (hsym z)).1
    have hm' : cgOperator (relativeOperator base (A z n-J z))=
        ∑ l∈Finset.range n,cgOperator (P l z)ᵀ*D l z*cgOperator (P l z) := by
      simpa only [cgOperator,map_sum,map_mul,map_sub,relativeOperator,J,D,R,P,V,launchObservedModel] using hm
    change -(cgOperator (relativeOperator base (A z n-J z)) (v z))=_
    rw [hm',_root_.sum_apply]
    rfl
  apply hsum.congr' _ Filter.EventuallyEq.rfl
  filter_upwards [heq] with z hz
  simp only [Finset.sum_apply]
  change -(∑ l∈Finset.range n,(cgOperator (P l z)ᵀ (D l z (cgOperator (P l z) (v z)))-
      cgOperator (P l 0)ᵀ (D l z (cgOperator (P l 0) (R (g z))))))=
    R (launchSemanticGradient (S z) (A z) (g z))+
      ∑ l∈Finset.range n,cgOperator (P l 0)ᵀ (D l z (cgOperator (P l 0) (R (g z))))
  rw [hz,Finset.sum_sub_distrib,neg_sub]
  abel

end
end krylov.OneGradient
