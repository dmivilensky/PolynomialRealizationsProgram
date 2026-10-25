import polyak.Boundary.P5.CriticalMatrix
import Mathlib.Analysis.Calculus.ImplicitContDiff

/-!
Article: Theorem p5h0, invertibility of the actual seven-variable Frechet derivative.
Use: exact nonzero block determinants and the proved lower-left zero block
supply the genuine hypothesis of the analytic implicit function theorem.
-/
noncomputable section
namespace polyak.Boundary.P5

/-- Article: the actual Frechet derivative of the critical polynomial system. -/
def criticalDifferential : Coordinates →L[ℝ] Coordinates :=
  ContinuousLinearMap.pi (fun i => polynomialDifferential (criticalSource i) criticalPoint)

/-- Article: the formal partial-derivative matrix is the actual derivative's action. -/
theorem criticalDifferential_apply (v : Coordinates) :
    criticalDifferential v=criticalJacobian.mulVec v := by
  ext i
  simp [criticalDifferential,polynomialDifferential,criticalJacobian,Matrix.mulVec,dotProduct]

/-- Article: block-triangular nonsingularity leaves no nonzero critical kernel vector. -/
theorem criticalJacobian_kernel (v : Coordinates) (h : criticalJacobian.mulVec v=0) : v=0 := by
  let vD : Fin 3 → ℝ := ![v 2,v 5,v 6]
  have hD : dualMatrix.mulVec vD=0 := by
    ext i
    fin_cases i
    · have hr := congrFun h 4
      norm_num [Matrix.mulVec,dotProduct,Fin.sum_univ_succ,lower_left_4_0,lower_left_4_1,lower_left_4_4,lower_left_4_3] at hr
      norm_num [dualMatrix,Matrix.mulVec,dotProduct,Fin.sum_univ_succ,vD]
      nlinarith
    · have hr := congrFun h 5
      norm_num [Matrix.mulVec,dotProduct,Fin.sum_univ_succ,lower_left_5_0,lower_left_5_1,lower_left_5_4,lower_left_5_3] at hr
      norm_num [dualMatrix,Matrix.mulVec,dotProduct,Fin.sum_univ_succ,vD]
      nlinarith
    · have hr := congrFun h 6
      norm_num [Matrix.mulVec,dotProduct,Fin.sum_univ_succ,lower_left_6_0,lower_left_6_1,lower_left_6_4,lower_left_6_3] at hr
      norm_num [dualMatrix,Matrix.mulVec,dotProduct,Fin.sum_univ_succ,vD]
      nlinarith
  have hvD : vD=0 := Matrix.mulVec_injective_of_det_ne_zero dualMatrix_det_ne_zero
    (by simpa using hD)
  have hv2 : v 2=0 := by have hh := congrFun hvD 0; simpa [vD] using hh
  have hv5 : v 5=0 := by have hh := congrFun hvD 1; simpa [vD] using hh
  have hv6 : v 6=0 := by have hh := congrFun hvD 2; simpa [vD] using hh
  let vP : Fin 4 → ℝ := ![v 0,v 1,v 4,v 3]
  have hP : primalMatrix.mulVec vP=0 := by
    ext i
    fin_cases i
    · have hr := congrFun h 0
      norm_num [Matrix.mulVec,dotProduct,Fin.sum_univ_succ,hv2,hv5,hv6] at hr
      norm_num [primalMatrix,Matrix.mulVec,dotProduct,Fin.sum_univ_succ,vP]
      nlinarith
    · have hr := congrFun h 1
      norm_num [Matrix.mulVec,dotProduct,Fin.sum_univ_succ,hv2,hv5,hv6] at hr
      norm_num [primalMatrix,Matrix.mulVec,dotProduct,Fin.sum_univ_succ,vP]
      nlinarith
    · have hr := congrFun h 2
      norm_num [Matrix.mulVec,dotProduct,Fin.sum_univ_succ,hv2,hv5,hv6] at hr
      norm_num [primalMatrix,Matrix.mulVec,dotProduct,Fin.sum_univ_succ,vP]
      nlinarith
    · have hr := congrFun h 3
      norm_num [Matrix.mulVec,dotProduct,Fin.sum_univ_succ,hv2,hv5,hv6] at hr
      norm_num [primalMatrix,Matrix.mulVec,dotProduct,Fin.sum_univ_succ,vP]
      nlinarith
  have hvP : vP=0 := Matrix.mulVec_injective_of_det_ne_zero primalMatrix_det_ne_zero
    (by simpa using hP)
  have hv0 : v 0=0 := by have hh := congrFun hvP 0; simpa [vP] using hh
  have hv1 : v 1=0 := by have hh := congrFun hvP 1; simpa [vP] using hh
  have hv4 : v 4=0 := by have hh := congrFun hvP 2; simpa [vP] using hh
  have hv3 : v 3=0 := by have hh := congrFun hvP 3; simpa [vP] using hh
  ext i
  fin_cases i
  · exact hv0
  · exact hv1
  · exact hv2
  · exact hv3
  · exact hv4
  · exact hv5
  · exact hv6

/-- Article: genuine critical Frechet invertibility follows from the exact block certificates. -/
theorem criticalDifferential_isInvertible : criticalDifferential.IsInvertible := by
  have hinj : Function.Injective criticalDifferential := by
    intro v w hvw
    have hz : criticalJacobian.mulVec (v-w)=0 := by
      rw [Matrix.mulVec_sub,← criticalDifferential_apply,← criticalDifferential_apply,hvw,sub_self]
    exact sub_eq_zero.mp (criticalJacobian_kernel (v-w) hz)
  have hsurj : Function.Surjective criticalDifferential :=
    (LinearMap.injective_iff_surjective (f := criticalDifferential.toLinearMap)).mp hinj
  refine ⟨(LinearEquiv.ofBijective criticalDifferential.toLinearMap ⟨hinj,hsurj⟩).toContinuousLinearEquiv,?_⟩
  ext v i
  rfl

/-- Article: the real h=0 system has exactly the derivative whose blocks were certified. -/
theorem critical_hasFDerivAt :
    HasFDerivAt (fun Z : Coordinates => regularSystem (0,Z)) criticalDifferential criticalPoint := by
  have he : (fun Z : Coordinates => regularSystem (0,Z))=
      (fun Z i => polynomialValue (criticalSource i) Z) := funext regularSystem_zero
  rw [he]
  exact hasFDerivAt_pi.mpr (fun i => polynomial_hasFDerivAt (criticalSource i) criticalPoint)

/-- Article: the exact invertible unknown-coordinate derivative required by the actual IFT. -/
theorem regularSystem_partial_isInvertible :
    (fderiv ℝ regularSystem (0,criticalPoint) ∘L
      ContinuousLinearMap.inr ℝ ℝ Coordinates).IsInvertible := by
  have hf := (regularSystem_analyticAt (0,criticalPoint)).differentiableAt
  have hp : HasFDerivAt (fun Z : Coordinates => ((0 : ℝ),Z))
      (ContinuousLinearMap.inr ℝ ℝ Coordinates) criticalPoint :=
    (hasFDerivAt_const (𝕜 := ℝ) (c := (0 : ℝ)) (x := criticalPoint)).prodMk
      (hasFDerivAt_id criticalPoint)
  have hc := hf.hasFDerivAt.comp criticalPoint hp
  rw [hc.unique critical_hasFDerivAt]
  exact criticalDifferential_isInvertible

end polyak.Boundary.P5
