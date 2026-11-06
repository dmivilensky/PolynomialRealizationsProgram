import nesterov.IQC.StateMass

/-! Bounded head, tail, delay and splice operators used by the KYP value proof. -/
namespace nesterov.IQC.KYP
noncomputable section
open scoped BigOperators ENNReal
open polyak.General.IQC
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def advanceL2 (n : ℕ) (x : SequenceSpace E) : SequenceSpace E:=
  toL2 (fun k=>x (k+n)) ((summable_nat_add_iff n).mpr (lp_squareSummable x))

omit [NormedSpace ℝ E] in
@[simp] theorem advanceL2_apply (n : ℕ) (x : SequenceSpace E) (k : ℕ) :
    advanceL2 n x k=x (k+n):=rfl

omit [NormedSpace ℝ E] in
theorem advanceL2_norm (n : ℕ) (x : SequenceSpace E) : ‖advanceL2 n x‖≤‖x‖ := by
  rw [lp_norm_eq_sequenceNorm,lp_norm_eq_sequenceNorm]
  unfold sequenceNorm
  apply Real.sqrt_le_sqrt
  have hh:=(lp_squareSummable x).sum_add_tsum_nat_add n
  have hn : 0≤∑ k∈Finset.range n,‖x k‖^2:=Finset.sum_nonneg (fun _ _=>sq_nonneg _)
  simpa only [advanceL2_apply] using (by linarith : (∑' k,‖x (k+n)‖^2)≤∑' k,‖x k‖^2)

def advanceLinear (n : ℕ) : SequenceSpace E→ₗ[ℝ]SequenceSpace E where
  toFun:=advanceL2 n
  map_add' x y:=by apply Subtype.ext; rfl
  map_smul' r x:=by apply Subtype.ext; rfl

def advanceCLM (n : ℕ) : SequenceSpace E→L[ℝ]SequenceSpace E:=
  (advanceLinear n).mkContinuous 1 (fun x=>by change ‖advanceL2 n x‖≤1*‖x‖; simpa only [one_mul] using advanceL2_norm n x)

@[simp] theorem advanceCLM_apply (n : ℕ) (x : SequenceSpace E) (k : ℕ) :
    advanceCLM n x k=x (k+n):=rfl

omit [NormedSpace ℝ E] in
theorem delay_squareSummable (n : ℕ) (x : SequenceSpace E) : SquareSummable (delay n x) := by
  apply squareSummable_of_prefix_bound (C:=‖x‖)
  intro N
  rw [prefixNorm_delay]
  simpa only [lp_norm_eq_sequenceNorm] using prefixNorm_le_sequenceNorm (lp_squareSummable x) (N-n)

def delayL2 (n : ℕ) (x : SequenceSpace E) : SequenceSpace E:=
  toL2 (delay n x) (delay_squareSummable n x)

omit [NormedSpace ℝ E] in
@[simp] theorem delayL2_apply (n : ℕ) (x : SequenceSpace E) (k : ℕ) :
    delayL2 n x k=delay n x k:=rfl

omit [NormedSpace ℝ E] in
theorem delayL2_norm (n : ℕ) (x : SequenceSpace E) : ‖delayL2 n x‖=‖x‖ := by
  rw [lp_norm_eq_sequenceNorm,lp_norm_eq_sequenceNorm]
  unfold sequenceNorm
  congr 1
  have hh:=(delay_squareSummable n x).sum_add_tsum_nat_add n
  have hzero : (∑ k∈Finset.range n,‖delay n (fun k=>x k) k‖^2)=0 := by
    apply Finset.sum_eq_zero
    intro k hk
    simp [delay,show ¬n≤k by have :=Finset.mem_range.mp hk; omega]
  rw [hzero,zero_add] at hh
  change (∑' k,‖delay n (fun k=>x k) k‖^2)=∑' k,‖x k‖^2
  rw [←hh]
  apply tsum_congr
  intro k
  simp [delay]

def delayLinear (n : ℕ) : SequenceSpace E→ₗ[ℝ]SequenceSpace E where
  toFun:=delayL2 n
  map_add' x y:=by apply Subtype.ext; exact delay_add n _ _
  map_smul' r x:=by apply Subtype.ext; exact delay_smul n r _

def delayCLM (n : ℕ) : SequenceSpace E→L[ℝ]SequenceSpace E:=
  (delayLinear n).mkContinuous 1 (fun x=>by change ‖delayL2 n x‖≤1*‖x‖; rw [delayL2_norm,one_mul])

@[simp] theorem delayCLM_apply (n : ℕ) (x : SequenceSpace E) (k : ℕ) :
    delayCLM n x k=if n≤k then x (k-n) else 0:=rfl

@[simp] theorem delayCLM_norm (n : ℕ) (x : SequenceSpace E) : ‖delayCLM n x‖=‖x‖:=delayL2_norm _ _

/-- Finite initial state embedded by genuine coordinate impulses. -/
def headCLM (N : ℕ) : (Fin N→E)→L[ℝ]SequenceSpace E:=
  ∑ j : Fin N,(lp.singleContinuousLinearMap ℝ (fun _ : ℕ=>E) 2 j.val).comp (ContinuousLinearMap.proj j)

@[simp] theorem headCLM_apply (N : ℕ) (x : Fin N→E) (k : ℕ) :
    headCLM N x k=if hk : k<N then x ⟨k,hk⟩ else 0 := by
  simp only [headCLM,sum_apply,ContinuousLinearMap.comp_apply,ContinuousLinearMap.proj_apply,
    lp.singleContinuousLinearMap_apply,lp.coeFn_sum,Finset.sum_apply,lp.single_apply]
  by_cases hk : k<N
  · rw [dite_eq_left hk]
    rw [Finset.sum_eq_single (⟨k,hk⟩:Fin N)]
    · simp
    · intro j _ hj
      have hjk : j.val≠k:=by intro h; exact hj (Fin.ext h)
      simp [hjk]
    · simp
  · rw [dite_eq_right hk]
    apply Finset.sum_eq_zero
    intro j _
    have hjk : k≠j.val:=by intro h; rw [h] at hk; exact hk j.isLt
    simp [hjk]

/-- Actual sequence with a finite head and an arbitrary square-summable future. -/
def spliceCLM (N : ℕ) : ((Fin N→E)×SequenceSpace E)→L[ℝ]SequenceSpace E:=
  (headCLM N).comp (ContinuousLinearMap.fst ℝ _ _)+
    (delayCLM N).comp (ContinuousLinearMap.snd ℝ _ _)

@[simp] theorem spliceCLM_apply (N : ℕ) (x : Fin N→E) (u : SequenceSpace E) (k : ℕ) :
    spliceCLM N (x,u) k=if hk : k<N then x ⟨k,hk⟩ else u (k-N) := by
  simp only [spliceCLM,add_apply,ContinuousLinearMap.comp_apply,
    lp.coeFn_add,Pi.add_apply,
    headCLM_apply,delayCLM_apply]
  by_cases hk : k<N
  · simp [hk,show ¬N≤k by omega]
  · simp [hk,show N≤k by omega]

end
end nesterov.IQC.KYP
