import nesterov.IQC.KYP.Sequence
import nesterov.IQC.KYP.QuadraticMaximum
import polyak.General.IQC.KernelL2

/-!
The bounded half-line supply form of a finite forward quadratic kernel.
Its zero-initial-history input block inherits the strict whole-line Fourier
gap, which is exactly the coercivity required by the value construction.
-/
namespace nesterov.IQC.KYP
noncomputable section
open scoped BigOperators InnerProductSpace
open polyak.General.IQC polyak.Energy

abbrev NatKernel:=List (ℝ×(ℕ×ℕ))

def NatKernel.toKernel (K : NatKernel) : Kernel:=
  K.map (fun p=>(p.1,((p.2.1:ℤ),(p.2.2:ℤ))))

def NatKernel.Supported (N : ℕ) (K : NatKernel) : Prop:=
  ∀ p∈K,p.2.1≤N ∧ p.2.2≤N

section Hilbert
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def NatKernel.eval (K : NatKernel) (x : ℕ→E) (k : ℕ) : ℝ:=
  (K.map (fun p=>p.1*inner ℝ (x (k+p.2.1)) (x (k+p.2.2)))).sum

def halfTerm (p : ℝ×(ℕ×ℕ)) : Bilinear (SequenceSpace E):=
  p.1 • ((innerSL ℝ).bilinearComp (advanceCLM p.2.1) (advanceCLM p.2.2))

/-- The actual bounded bilinear supply summed over nonnegative center times. -/
def halfKernelRaw (K : NatKernel) : Bilinear (SequenceSpace E):=
  (K.map (halfTerm (E:=E))).sum

def halfKernel (K : NatKernel) : Bilinear (SequenceSpace E):=
  (1/2:ℝ) • (halfKernelRaw K+(halfKernelRaw K).flip)

theorem halfKernel_symmetric (K : NatKernel) (x y : SequenceSpace E) :
    halfKernel K x y=halfKernel K y x := by
  simp only [halfKernel,smul_apply,add_apply,ContinuousLinearMap.flip_apply,smul_eq_mul]
  ring

theorem halfKernel_diagonal (K : NatKernel) (x : SequenceSpace E) :
    halfKernel K x x=halfKernelRaw K x x := by
  simp only [halfKernel,smul_apply,add_apply,ContinuousLinearMap.flip_apply,smul_eq_mul]
  ring

theorem natKernel_summable (K : NatKernel) (x : SequenceSpace E) :
    Summable (fun k=>NatKernel.eval K (fun j=>x j) k) := by
  induction K with
  | nil=>simp [NatKernel.eval]
  | cons p K ih=>
    have hs:= (lp.summable_inner (advanceCLM p.2.1 x) (advanceCLM p.2.2 x)).mul_left p.1
    exact hs.add ih

theorem halfKernel_eq_tsum (K : NatKernel) (x : SequenceSpace E) :
    halfKernel K x x=∑' k,NatKernel.eval K (fun j=>x j) k := by
  rw [halfKernel_diagonal]
  induction K with
  | nil=>simp [halfKernelRaw,NatKernel.eval]
  | cons p K ih=>
    have hs:= (lp.summable_inner (advanceCLM p.2.1 x) (advanceCLM p.2.2 x)).mul_left p.1
    change (halfTerm (E:=E) p+halfKernelRaw (E:=E) K) x x=_
    simp only [halfTerm,add_apply,smul_apply,ContinuousLinearMap.bilinearComp_apply,innerSL_apply_apply,
      smul_eq_mul,ih]
    have hs' : Summable (fun k=>p.1*inner ℝ (x (k+p.2.1)) (x (k+p.2.2))) := by
      simpa only [advanceCLM_apply] using hs
    change p.1*inner ℝ (advanceCLM p.2.1 x) (advanceCLM p.2.2 x)+
      (∑' k,NatKernel.eval K (fun j=>x j) k)=
        ∑' k,(p.1*inner ℝ (x (k+p.2.1)) (x (k+p.2.2))+NatKernel.eval K (fun j=>x j) k)
    rw [hs'.tsum_add (natKernel_summable K x),tsum_mul_left]
    rfl

theorem NatKernel.eval_eq_whole (K : NatKernel) (x : ℕ→E) (k : ℕ) :
    NatKernel.eval K x k=kernelEval K.toKernel (zeroExtend x) k := by
  unfold NatKernel.eval kernelEval NatKernel.toKernel
  simp only [List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro p _
  simp only [Function.comp_apply]
  rw [show (k:ℤ)+(p.2.1:ℤ)=((k+p.2.1:ℕ):ℤ) by omega,
    show (k:ℤ)+(p.2.2:ℤ)=((k+p.2.2:ℕ):ℤ) by omega,zeroExtend_nat,zeroExtend_nat]

/-- No negative-center supply remains when the complete initial window is zero. -/
theorem NatKernel.eval_negative_zero {N : ℕ} {K : NatKernel} (hK : K.Supported N)
    (x : SequenceSpace E) {k : ℤ} (hk : k<0) :
    kernelEval K.toKernel (zeroExtend (fun n=>delayCLM N x n)) k=0 := by
  unfold kernelEval NatKernel.toKernel
  simp only [List.map_map]
  apply List.sum_eq_zero
  intro y hy
  obtain ⟨p,hp,rfl⟩:=List.mem_map.mp hy
  have hpN:=hK p hp
  have hz (j : ℕ) (hj : j≤N) : zeroExtend (fun n=>delayCLM N x n) (k+j)=0 := by
    by_cases hkj : 0≤k+(j:ℤ)
    · rw [zeroExtend,ite_eq_left hkj,delayCLM_apply,ite_eq_right (by omega)]
    · exact zeroExtend_neg _ (lt_of_not_ge hkj)
  simp only [Function.comp_apply,hz p.2.1 hpN.1,hz p.2.2 hpN.2,inner_zero_left,mul_zero]

/-- Strict Fourier negativity implies a coercively negative input block of the
half-line cost, without an assumed finite-dimensional storage matrix. -/
theorem halfKernel_delay_gap {N : ℕ} {K : NatKernel} (hK : K.Supported N)
    {ε : ℝ} (hgap : ∀ θ,kernelSymbol K.toKernel θ≤ -ε) (x : SequenceSpace E) :
    halfKernel K (delayCLM N x) (delayCLM N x)≤ -ε*‖x‖^2 := by
  have hg:=kernelBilinear_le K.toKernel hgap (zeroExtendL2 (delayCLM N x))
  rw [zeroExtendL2_norm,delayCLM_norm,kernelBilinear_eq_tsum] at hg
  have he : (∑' k : ℤ,kernelEval K.toKernel (zeroExtend (fun n=>delayCLM N x n)) k)=
      ∑' n : ℕ,NatKernel.eval K (fun n=>delayCLM N x n) n := by
    have hn : Summable (fun n : ℕ=>kernelEval K.toKernel
        (zeroExtend (fun n=>delayCLM N x n)) n) := by
      simpa only [←NatKernel.eval_eq_whole] using natKernel_summable K (delayCLM N x)
    have hz : (fun n : ℕ=>kernelEval K.toKernel
        (zeroExtend (fun n=>delayCLM N x n)) (-((n:ℤ)+1)))=0 := by
      funext n
      exact NatKernel.eval_negative_zero hK x (by omega)
    have hneg : Summable (fun n : ℕ=>kernelEval K.toKernel
        (zeroExtend (fun n=>delayCLM N x n)) (-((n:ℤ)+1))) := by rw [hz]; exact summable_zero
    rw [tsum_of_nat_of_neg_add_one hn hneg,hz]
    have hzsum : tsum (0:ℕ→ℝ)=0:=tsum_zero
    rw [hzsum,add_zero]
    apply tsum_congr
    intro n
    exact (NatKernel.eval_eq_whole K _ n).symm
  rw [halfKernel_eq_tsum]
  change (∑' n : ℕ,NatKernel.eval K (fun n=>delayCLM N x n) n)≤_
  rw [←he]
  exact hg

end Hilbert
end
end nesterov.IQC.KYP
