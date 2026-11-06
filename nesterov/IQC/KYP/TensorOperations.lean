import nesterov.IQC.KYP.Tensor

/-! Exact finite algebra for applying one scalar storage matrix in every Hilbert space. -/
namespace nesterov.IQC.KYP
noncomputable section
open scoped BigOperators InnerProductSpace
variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def tensorForm (B : Bilinear (I→ℝ)) (x y : I→E) : ℝ:=matrixInner (bilinearMatrix B) x y

theorem tensorForm_add (B C : Bilinear (I→ℝ)) (x y : I→E) :
    tensorForm (B+C) x y=tensorForm B x y+tensorForm C x y := by
  simp only [tensorForm,matrixInner,bilinearMatrix,add_apply,add_mul,Finset.sum_add_distrib]

theorem tensorForm_neg (B : Bilinear (I→ℝ)) (x y : I→E) :
    tensorForm (-B) x y= -tensorForm B x y := by
  simp only [tensorForm,matrixInner,bilinearMatrix,neg_apply,neg_mul,Finset.sum_neg_distrib]

theorem tensorForm_sub (B C : Bilinear (I→ℝ)) (x y : I→E) :
    tensorForm (B-C) x y=tensorForm B x y-tensorForm C x y := by
  simp only [tensorForm,matrixInner,bilinearMatrix,sub_apply,sub_mul,Finset.sum_sub_distrib]

theorem tensorForm_smul (a : ℝ) (B : Bilinear (I→ℝ)) (x y : I→E) :
    tensorForm (a • B) x y=a*tensorForm B x y := by
  simp only [tensorForm,matrixInner,bilinearMatrix,smul_apply,smul_eq_mul,
    Finset.mul_sum,mul_assoc]

theorem tensorForm_sum {T : Type*} (s : Finset T) (B : T→Bilinear (I→ℝ)) (x y : I→E) :
    tensorForm (∑ i∈s,B i) x y=∑ i∈s,tensorForm (B i) x y := by
  classical
  induction s using Finset.induction_on with
  | empty=>simp [tensorForm,matrixInner,bilinearMatrix]
  | @insert i s hi ih=>simp only [Finset.sum_insert hi,tensorForm_add,ih]

theorem tensorForm_flip (B : Bilinear (I→ℝ)) (x : I→E) :
    tensorForm B.flip x x=tensorForm B x x := by
  unfold tensorForm matrixInner bilinearMatrix
  simp only [ContinuousLinearMap.flip_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [real_inner_comm]

omit [DecidableEq I] [DecidableEq J] in
theorem sum_four_comm (f : I→I→J→J→ℝ) :
    (∑ i,∑ j,∑ r,∑ s,f i j r s)=∑ r,∑ s,∑ i,∑ j,f i j r s := by
  calc
    _=∑ i,∑ r,∑ j,∑ s,f i j r s:=by
      apply Finset.sum_congr rfl
      intro i _
      exact Finset.sum_comm
    _=∑ r,∑ i,∑ j,∑ s,f i j r s:=Finset.sum_comm
    _=∑ r,∑ s,∑ i,∑ j,f i j r s:=by
      apply Finset.sum_congr rfl
      intro r _
      calc
        _=∑ i,∑ s,∑ j,f i j r s:=by
          apply Finset.sum_congr rfl
          intro i _
          exact Finset.sum_comm
        _=_:=Finset.sum_comm

/-- A fixed coordinate selection as a genuine continuous linear operator. -/
def selectCLM (σ : J→I) : (I→ℝ)→L[ℝ](J→ℝ):=
  ContinuousLinearMap.pi (fun j=>ContinuousLinearMap.proj (σ j))

omit [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] in
@[simp] theorem selectCLM_apply (σ : J→I) (x : I→ℝ) (j : J) : selectCLM σ x j=x (σ j):=rfl

/-- Selecting coordinates commutes exactly with the Hilbert tensor action. -/
theorem tensorForm_select (σ : J→I) (B : Bilinear (J→ℝ)) (x : I→E) :
    tensorForm (B.bilinearComp (selectCLM σ) (selectCLM σ)) x x=
      tensorForm B (fun j=>x (σ j)) (fun j=>x (σ j)) := by
  unfold tensorForm matrixInner bilinearMatrix
  simp only [ContinuousLinearMap.bilinearComp_apply]
  simp_rw [bilinearMatrix_apply]
  simp only [Finset.sum_mul]
  rw [sum_four_comm]
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro s _
  rw [Finset.sum_eq_single (σ r)]
  · rw [Finset.sum_eq_single (σ s)]
    · simp [selectCLM_apply,Pi.single_apply,bilinearMatrix]
    · intro j _ hj
      simp [selectCLM_apply,hj]
    · simp
  · intro i _ hi
    apply Finset.sum_eq_zero
    intro j _
    simp [selectCLM_apply,Pi.single_apply,hi]
  · simp

/-- Elementary coordinate product, prior to symmetrization. -/
def coordinateForm (i j : I) : Bilinear (I→ℝ):=
  (ContinuousLinearMap.mul ℝ ℝ).bilinearComp (ContinuousLinearMap.proj i) (ContinuousLinearMap.proj j)

omit [DecidableEq I] in
@[simp] theorem coordinateForm_apply (i j : I) (x y : I→ℝ) : coordinateForm i j x y=x i*y j:=rfl

theorem tensorForm_coordinate (i j : I) (x : I→E) : tensorForm (coordinateForm i j) x x=inner ℝ (x i) (x j) := by
  unfold tensorForm matrixInner bilinearMatrix
  simp only [coordinateForm_apply]
  rw [Finset.sum_eq_single i]
  · rw [Finset.sum_eq_single j]
    · simp
    · intro k _ hk
      simp [hk]
    · simp
  · intro k _ hk
    apply Finset.sum_eq_zero
    intro l _
    simp [Pi.single_apply,hk]
  · simp

end
end nesterov.IQC.KYP
