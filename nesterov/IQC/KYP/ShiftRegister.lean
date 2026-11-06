import nesterov.IQC.KYP.HalfKernel

/-! The exact dynamic-programming identity for a finite shift-register supply. -/
namespace nesterov.IQC.KYP
noncomputable section
open scoped BigOperators
open polyak.General.IQC
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- One genuine shift-register update, on the fixed finite state. -/
def registerStep {N : ℕ} (x : Fin N→E) (d : E) (i : Fin N) : E:=
  if hi : i.val+1<N then x ⟨i.val+1,hi⟩ else d

/-- Prepend one arbitrarily chosen control to an actual ℓ² future. -/
def prependL2 (d : E) (u : SequenceSpace E) : SequenceSpace E:=
  lp.single 2 0 d+delayCLM 1 u

@[simp] theorem prependL2_zero (d : E) (u : SequenceSpace E) : prependL2 d u 0=d := by
  simp [prependL2,lp.single_apply]

@[simp] theorem prependL2_succ (d : E) (u : SequenceSpace E) (k : ℕ) :
    prependL2 d u (k+1)=u k := by
  simp [prependL2,lp.single_apply]

@[simp] theorem advance_prepend (d : E) (u : SequenceSpace E) : advanceCLM 1 (prependL2 d u)=u := by
  apply Subtype.ext
  funext k
  exact prependL2_succ d u k

/-- Removing one time sample exactly updates the finite head and future tail. -/
theorem advance_splice {N : ℕ} (_hN : 0<N) (x : Fin N→E) (u : SequenceSpace E) :
    advanceCLM 1 (spliceCLM N (x,u))=
      spliceCLM N (registerStep x (u 0),advanceCLM 1 u) := by
  apply Subtype.ext
  funext k
  simp only [advanceCLM_apply,spliceCLM_apply]
  by_cases hk : k<N
  · rw [dite_eq_left hk]
    unfold registerStep
    by_cases hk1 : k+1<N
    · simp only [hk1,↓reduceDIte]
    · simp only [hk1,↓reduceDIte]
      change u (k+1-N)=u 0
      exact congrArg (fun j : ℕ=>u j) (by omega)
  · simp only [hk,↓reduceDIte]
    rw [dite_eq_right (by omega : ¬k+1<N)]
    change u (k+1-N)=u (k-N+1)
    exact congrArg (fun j : ℕ=>u j) (by omega)

def instantaneous {N : ℕ} (K : NatKernel) (x : Fin N→E) (d : E) : ℝ:=
  NatKernel.eval K (fun j=>if hj : j<N then x ⟨j,hj⟩ else d) 0

theorem instantaneous_eq {N : ℕ} {K : NatKernel} (hK : K.Supported N)
    (x : Fin N→E) (u : SequenceSpace E) :
    instantaneous K x (u 0)=NatKernel.eval K (fun k=>spliceCLM N (x,u) k) 0 := by
  unfold instantaneous NatKernel.eval
  apply congrArg List.sum
  apply List.map_congr_left
  intro p hp
  have hb:=hK p hp
  simp only [Nat.zero_add,spliceCLM_apply]
  have he (j : ℕ) (hj : j≤N) :
      (if h : j<N then x ⟨j,h⟩ else u 0)=
        if h : j<N then x ⟨j,h⟩ else u (j-N) := by
    by_cases h : j<N
    · simp only [h,↓reduceDIte]
    · simp only [h,↓reduceDIte,show j-N=0 by omega]
  rw [he p.2.1 hb.1,he p.2.2 hb.2]

theorem natKernel_eval_advance (K : NatKernel) (x : SequenceSpace E) (k : ℕ) :
    NatKernel.eval K (fun j=>advanceCLM 1 x j) k=NatKernel.eval K (fun j=>x j) (k+1) := by
  unfold NatKernel.eval
  apply congrArg List.sum
  apply List.map_congr_left
  intro p _
  simp only [advanceCLM_apply]
  rw [show k+p.2.1+1=k+1+p.2.1 by omega,show k+p.2.2+1=k+1+p.2.2 by omega]

/-- Exact Bellman splitting of the infinite supply; convergence is already proved. -/
theorem halfKernel_split (K : NatKernel) (x : SequenceSpace E) :
    halfKernel K x x=NatKernel.eval K (fun j=>x j) 0+
      halfKernel K (advanceCLM 1 x) (advanceCLM 1 x) := by
  rw [halfKernel_eq_tsum,halfKernel_eq_tsum]
  simp_rw [natKernel_eval_advance]
  have hh:=(natKernel_summable K x).sum_add_tsum_nat_add 1
  simpa only [Finset.sum_range_one] using hh.symm

/-- Exact cost decomposition in the finite state and arbitrary future input. -/
theorem splice_cost_split {N : ℕ} (hN : 0<N) {K : NatKernel} (hK : K.Supported N)
    (x : Fin N→E) (u : SequenceSpace E) :
    halfKernel K (spliceCLM N (x,u)) (spliceCLM N (x,u))=
      instantaneous K x (u 0)+
        halfKernel K (spliceCLM N (registerStep x (u 0),advanceCLM 1 u))
          (spliceCLM N (registerStep x (u 0),advanceCLM 1 u)) := by
  rw [halfKernel_split,←instantaneous_eq hK,advance_splice hN]

end
end nesterov.IQC.KYP
