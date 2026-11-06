import nesterov.IQC.StateResponse

/-! Exact observations of the stable full-memory Green response. -/
namespace nesterov.IQC
noncomputable section
open scoped BigOperators
open polyak.General.IQC
variable {d : ℕ}

/-- Scalar impulse of an arbitrary linear observation of the causal state. -/
def observationImpulse (a q : Fin d→ℝ) (b : ℝ) (l : Fin d) (n : ℕ) : ℝ :=
  ∑ i,q i*stateImpulse a b i l n

@[simp] theorem observationImpulse_zero (a q : Fin d→ℝ) (b : ℝ) (l : Fin d) :
    observationImpulse a q b l 0=0 := by simp [observationImpulse]

theorem observationImpulse_summable (a q : Fin d→ℝ) (b : ℝ) (l : Fin d)
    (hs : Summable (fun n : ℕ=>‖companion d (fun j=>(a j:ℂ))^n‖)) :
    Summable (fun n=>|observationImpulse a q b l n|) := by
  have hsum : Summable (fun n : ℕ=>∑ i,|q i| *|stateImpulse a b i l n|) := by
    apply summable_sum
    intro i _
    exact (stateImpulse_summable a b i l hs).mul_left |q i|
  apply hsum.of_nonneg_of_le (fun _=>abs_nonneg _)
  intro n
  calc
    _≤∑ i,|q i*stateImpulse a b i l n|:=Finset.abs_sum_le_sum_abs _ _
    _=_:=by simp only [abs_mul]

section Vector
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def freeObservation (a q : Fin d→ℝ) (initial : Fin d→E) (n : ℕ) : E :=
  ∑ i,q i • freeState a initial n i

theorem forced_observation (a q : Fin d→ℝ) (b : ℝ) (l : Fin d) (input : ℕ→E) (n : ℕ) :
    (∑ i,q i • forcedState a b l input n i)=convolution (observationImpulse a q b l) input n := by
  simp_rw [forcedState_convolution]
  unfold convolution observationImpulse
  simp only [LinearMap.coe_mk,AddHom.coe_mk,Finset.sum_smul,Finset.smul_sum,smul_smul]
  rw [Finset.sum_comm]

/-- Shift consistency of the actual state, with input injected at its last coordinate. -/
theorem forcedState_shift {d : ℕ} (hd : 0<d) (a : Fin d→ℝ) (b : ℝ)
    (input : ℕ→E) (k : ℕ) (i : Fin d) :
    forcedState a b ⟨d-1,by omega⟩ input k i=
      forcedState a b ⟨d-1,by omega⟩ input (k+i.val) ⟨0,hd⟩ := by
  obtain ⟨i,hi⟩:=i
  induction i generalizing k with
  | zero=>simp
  | succ i ih=>
    have hi' : i<d:=by omega
    have hl : (⟨i,hi'⟩:Fin d)≠⟨d-1,by omega⟩:=by
      intro hh
      have hv:=congrArg Fin.val hh
      change i=d-1 at hv
      omega
    have hh:=forcedState_succ a b (⟨d-1,by omega⟩:Fin d) input k ⟨i,hi'⟩
    simp only [show i+1<d from hi,↓reduceDIte,hl,↓reduceIte,add_zero] at hh
    rw [←hh,ih (k+1) hi']
    simp only [Nat.add_comm,Nat.add_left_comm]

/-- Therefore the scalar causal latent response starts with D zero coordinates. -/
theorem forcedState_initial {d : ℕ} (hd : 0<d) (a : Fin d→ℝ) (b : ℝ)
    (input : ℕ→E) (j : Fin d) :
    forcedState a b ⟨d-1,by omega⟩ input j.val ⟨0,hd⟩=0 := by
  have hh:=forcedState_shift hd a b input 0 j
  simpa only [forcedState_zero,zero_add] using hh.symm

end Vector
end
end nesterov.IQC
