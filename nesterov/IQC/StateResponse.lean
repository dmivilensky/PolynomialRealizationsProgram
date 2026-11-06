import nesterov.IQC.Green

/-!
The actual stable finite-memory state response: unrestricted causal execution,
its finite Green expansion, and its scalar convolution representation.
-/
namespace nesterov.IQC
noncomputable section
open scoped BigOperators
open polyak.General.IQC
variable {d : ℕ}
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Duhamel response to one scalar input injected at coordinate l. -/
def forcedState (a : Fin d→ℝ) (b : ℝ) (l : Fin d) (input : ℕ→E)
    (n : ℕ) (i : Fin d) : E :=
  ∑ m∈Finset.range n,(b*green a (n-1-m) i l) • input m

@[simp] theorem forcedState_zero (a : Fin d→ℝ) (b : ℝ) (l : Fin d) (input : ℕ→E) (i : Fin d) :
    forcedState a b l input 0 i=0 := by simp [forcedState]

/-- The exact state equation, before any square-summability assumption. -/
theorem forcedState_succ (a : Fin d→ℝ) (b : ℝ) (l : Fin d) (input : ℕ→E)
    (n : ℕ) (i : Fin d) :
    forcedState a b l input (n+1) i=
      (if hi : i.val+1<d then forcedState a b l input n ⟨i.val+1,hi⟩
        else ∑ k,a k • forcedState a b l input n k)+
        (if i=l then b • input n else 0) := by
  unfold forcedState
  rw [Finset.sum_range_succ]
  simp only [Nat.add_sub_cancel,Nat.sub_self,green_zero]
  have hp : (∑ m∈Finset.range n,(b*green a (n-m) i l) • input m)=
      if hi : i.val+1<d then
        ∑ m∈Finset.range n,(b*green a (n-1-m) ⟨i.val+1,hi⟩ l) • input m
      else ∑ k,a k • ∑ m∈Finset.range n,(b*green a (n-1-m) k l) • input m := by
    have he (m : ℕ) (hm : m∈Finset.range n) : n-m=(n-1-m)+1 := by
      have :=Finset.mem_range.mp hm
      omega
    by_cases hi : i.val+1<d
    · simp only [hi,↓reduceDIte]
      apply Finset.sum_congr rfl
      intro m hm
      rw [he m hm,green_succ]
      simp only [hi,↓reduceDIte]
    · simp only [hi,↓reduceDIte,Finset.smul_sum,smul_smul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro m hm
      rw [he m hm,green_succ]
      simp only [hi,↓reduceDIte,Finset.mul_sum,Finset.sum_smul]
      apply Finset.sum_congr rfl
      intro k _
      congr 1
      ring
  rw [hp]
  by_cases hil : i=l <;> simp [hil]

/-- Each state coordinate is an actual strictly causal scalar convolution. -/
def stateImpulse (a : Fin d→ℝ) (b : ℝ) (i l : Fin d) : ℕ→ℝ
  | 0=>0
  | n+1=>b*green a n i l

@[simp] theorem stateImpulse_zero (a : Fin d→ℝ) (b : ℝ) (i l : Fin d) :
    stateImpulse a b i l 0=0 := rfl

theorem stateImpulse_summable (a : Fin d→ℝ) (b : ℝ) (i l : Fin d)
    (hs : Summable (fun n : ℕ=>‖companion d (fun j=>(a j:ℂ))^n‖)) :
    Summable (fun n=>|stateImpulse a b i l n|) := by
  apply (summable_nat_add_iff 1).mp
  simpa only [stateImpulse,abs_mul] using (green_abs_summable a hs i l).mul_left |b|

theorem forcedState_convolution (a : Fin d→ℝ) (b : ℝ) (l : Fin d) (input : ℕ→E)
    (n : ℕ) (i : Fin d) :
    forcedState a b l input n i=convolution (stateImpulse a b i l) input n := by
  unfold convolution
  simp only [LinearMap.coe_mk,AddHom.coe_mk]
  rw [Finset.sum_range_succ']
  simp only [stateImpulse_zero,zero_smul,add_zero]
  unfold forcedState
  rw [←Finset.sum_range_reflect]
  apply Finset.sum_congr rfl
  intro m hm
  have hm' : m<n:=Finset.mem_range.mp hm
  simp only [stateImpulse,delay,show m+1≤n by omega,↓reduceIte]
  congr 1
  · congr 2
    omega
  · congr 1
    omega

/-- The free plus forced response is the unique state solution. -/
theorem state_decomposition (a : Fin d→ℝ) (b : ℝ) (l : Fin d)
    (initial : Fin d→E) (input : ℕ→E) (x : ℕ→Fin d→E)
    (hzero : x 0=initial)
    (hstep : ∀ n i,x (n+1) i=
      (if hi : i.val+1<d then x n ⟨i.val+1,hi⟩ else ∑ k,a k • x n k)+
        (if i=l then b • input n else 0)) :
    ∀ n i,x n i=freeState a initial n i+forcedState a b l input n i := by
  intro n
  induction n with
  | zero=>simp [hzero]
  | succ n ih=>
    intro i
    rw [hstep,freeState_succ,forcedState_succ]
    simp_rw [ih]
    by_cases hi : i.val+1<d
    · simp only [hi,↓reduceDIte]
      abel
    · simp only [hi,↓reduceDIte,smul_add,Finset.sum_add_distrib]
      abel

end
end nesterov.IQC
