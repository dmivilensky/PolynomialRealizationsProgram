import nesterov.IQC.KYP.StrictStorage
import nesterov.IQC.KYP.TensorOperations

/-!
A single real storage matrix acts in every spatial Hilbert space. The transfer
is proved from scalar positive semidefiniteness, with no dimension-dependent
choice of coefficients.
-/
namespace nesterov.IQC.KYP
noncomputable section
open scoped BigOperators InnerProductSpace
open polyak.General.IQC

def boundedIndex (N n : ℕ) : Fin (N+1):=⟨min n N,by omega⟩

def kernelForm (N : ℕ) (K : NatKernel) : Bilinear (Fin (N+1)→ℝ):=
  (K.map fun p=>p.1 • coordinateForm (boundedIndex N p.2.1) (boundedIndex N p.2.2)).sum

def energyForm (N : ℕ) : Bilinear (Fin (N+1)→ℝ):=
  ∑ j : Fin (N+1),coordinateForm j j

def headOf {N : ℕ} {E : Type*} (x : Fin (N+1)→E) : Fin N→E:=fun j=>x j.castSucc
def tailOf {N : ℕ} {E : Type*} (x : Fin (N+1)→E) : Fin N→E:=fun j=>x j.succ

theorem registerStep_head {N : ℕ} {E : Type*} (x : Fin (N+1)→E) :
    registerStep (headOf x) (x (Fin.last N))=tailOf x := by
  funext j
  unfold registerStep headOf tailOf
  by_cases hj : j.val+1<N
  · simp only [hj,↓reduceDIte]
    congr 1
  · simp only [hj,↓reduceDIte]
    congr 1
    apply Fin.ext
    simp only [Fin.val_last,Fin.val_succ]
    have :=j.isLt
    omega

section Tensor
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem tensorForm_list_sum (L : List (Bilinear (Fin 1→ℝ))) (x : Fin 1→E) :
    tensorForm L.sum x x=(L.map (fun B=>tensorForm B x x)).sum := by
  induction L with
  | nil=>simp [tensorForm,matrixInner,bilinearMatrix]
  | cons B L ih=>simp only [List.sum_cons,tensorForm_add,ih,List.map_cons]

theorem tensorForm_list_sum_general {I : Type*} [Fintype I] [DecidableEq I]
    (L : List (Bilinear (I→ℝ))) (x : I→E) :
    tensorForm L.sum x x=(L.map (fun B=>tensorForm B x x)).sum := by
  induction L with
  | nil=>simp [tensorForm,matrixInner,bilinearMatrix]
  | cons B L ih=>simp only [List.sum_cons,tensorForm_add,ih,List.map_cons]

theorem tensorForm_kernel (N : ℕ) (K : NatKernel) (x : Fin (N+1)→E) :
    tensorForm (kernelForm N K) x x=NatKernel.eval K (fun n=>x (boundedIndex N n)) 0 := by
  unfold kernelForm
  rw [tensorForm_list_sum_general]
  simp only [List.map_map,NatKernel.eval,Nat.zero_add]
  simp only [Function.comp_def,tensorForm_smul,tensorForm_coordinate]

theorem tensorForm_energy (N : ℕ) (x : Fin (N+1)→E) :
    tensorForm (energyForm N) x x=∑ j,‖x j‖^2 := by
  rw [energyForm,tensorForm_sum]
  simp only [tensorForm_coordinate,real_inner_self_eq_norm_sq]

/-- The kernel only uses the current state and incoming coordinate. -/
theorem instantaneous_head {N : ℕ} {K : NatKernel} (hK : K.Supported N) (x : Fin (N+1)→E) :
    instantaneous K (headOf x) (x (Fin.last N))=
      NatKernel.eval K (fun n=>x (boundedIndex N n)) 0 := by
  unfold instantaneous NatKernel.eval
  apply congrArg List.sum
  apply List.map_congr_left
  intro p hp
  have hb:=hK p hp
  have hi (j : ℕ) (hj : j≤N) :
      (if h : j<N then headOf x ⟨j,h⟩ else x (Fin.last N))=x (boundedIndex N j) := by
    by_cases h : j<N
    · simp only [h,↓reduceDIte,headOf]
      congr 1
      apply Fin.ext
      simp only [boundedIndex,min_eq_left hj,Fin.val_castSucc]
    · simp only [h,↓reduceDIte]
      congr 1
      apply Fin.ext
      simp only [Fin.val_last,boundedIndex,min_eq_left hj]
      omega
  simp only [Nat.zero_add,hi p.2.1 hb.1,hi p.2.2 hb.2]

end Tensor

/-- A real bilinear form has the same scalar and tensor diagonal. -/
theorem tensorForm_real {I : Type*} [Fintype I] [DecidableEq I]
    (B : Bilinear (I→ℝ)) (x : I→ℝ) : tensorForm B x x=B x x := by
  conv_rhs => rw [bilinearMatrix_apply]
  unfold tensorForm matrixInner
  simp only [Real.inner_apply]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

def dissipationForm {N : ℕ} (W : Bilinear (Fin N→ℝ)) (K : NatKernel) (η : ℝ) :
    Bilinear (Fin (N+1)→ℝ):=
  W.bilinearComp (selectCLM Fin.castSucc) (selectCLM Fin.castSucc)-
    W.bilinearComp (selectCLM Fin.succ) (selectCLM Fin.succ)-kernelForm N K-η • energyForm N

/-- The scalar storage inequality transfers with the same W and η to all
real Hilbert spaces. -/
theorem tensor_storage_dissipation {N : ℕ} {K : NatKernel} (hK : K.Supported N)
    (W : Bilinear (Fin N→ℝ)) (η : ℝ)
    (hW : ∀ (x : Fin N→ℝ) (d : ℝ),
      W (registerStep x d) (registerStep x d)-W x x+instantaneous K x d≤
        -η*((∑ j,‖x j‖^2)+‖d‖^2))
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (z : Fin (N+1)→E) :
    tensorForm W (tailOf z) (tailOf z)-tensorForm W (headOf z) (headOf z)+
      instantaneous K (headOf z) (z (Fin.last N))≤ -η*(∑ j,‖z j‖^2) := by
  let B:=dissipationForm W K η
  let S:=(1/2:ℝ) • (B+B.flip)
  have hs (x y) : S x y=S y x := by
    dsimp [S]
    simp only [smul_apply,add_apply,ContinuousLinearMap.flip_apply,smul_eq_mul]
    ring
  have hp (x : Fin (N+1)→ℝ) : 0≤S x x := by
    have hh:=hW (headOf x) (x (Fin.last N))
    rw [registerStep_head,instantaneous_head hK] at hh
    have he : (∑ j : Fin (N+1),‖x j‖^2)=(∑ j : Fin N,‖headOf x j‖^2)+‖x (Fin.last N)‖^2:=by
      rw [Fin.sum_univ_castSucc]
      rfl
    have hkernel : kernelForm N K x x=NatKernel.eval K (fun n=>x (boundedIndex N n)) 0 := by
      rw [←tensorForm_real,tensorForm_kernel]
    have henergy : energyForm N x x=∑ j,‖x j‖^2 := by rw [←tensorForm_real,tensorForm_energy]
    change 0≤(1/2:ℝ)*(B x x+B x x)
    dsimp [B,dissipationForm]
    simp only [sub_apply,smul_apply,smul_eq_mul,ContinuousLinearMap.bilinearComp_apply]
    change 0≤(1/2:ℝ)*((W (headOf x) (headOf x)-W (tailOf x) (tailOf x)-kernelForm N K x x-η*energyForm N x x)+
      (W (headOf x) (headOf x)-W (tailOf x) (tailOf x)-kernelForm N K x x-η*energyForm N x x))
    rw [hkernel,henergy,he]
    linarith
  have hn:=tensor_nonneg S hs hp z
  change 0≤tensorForm S z z at hn
  dsimp [S] at hn
  rw [tensorForm_smul,tensorForm_add,tensorForm_flip] at hn
  have hnb : 0≤tensorForm B z z:=by linarith
  dsimp [B,dissipationForm] at hnb
  rw [tensorForm_sub,tensorForm_sub,tensorForm_sub,tensorForm_smul,
    tensorForm_select,tensorForm_select,tensorForm_kernel,tensorForm_energy] at hnb
  rw [instantaneous_head hK]
  change tensorForm W (fun j=>z j.succ) (fun j=>z j.succ)-
    tensorForm W (fun j=>z j.castSucc) (fun j=>z j.castSucc)+
      NatKernel.eval K (fun n=>z (boundedIndex N n)) 0≤ -η*(∑ j,‖z j‖^2)
  linarith


end
end nesterov.IQC.KYP
