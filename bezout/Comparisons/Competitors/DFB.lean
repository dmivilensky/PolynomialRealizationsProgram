import bezout.Comparisons.Competitors.Averaging
import bezout.Comparisons.Competitors.Superposition

/-!
Article: bezout, Equation `eq:competitor-dfb`.
Use: literal unregularized accelerated averaging, step 1/L and momentum one,
with one actual extrapolated-query oracle call per step and the running average.
Proof: the exact constant two-state matrix identifies d_j; a telescoping matrix
geometric sum gives the accumulated physical impulse and its averaged response.
-/

namespace bezout.Comparisons.Competitors.DFB
noncomputable section
open chebyshev1 Polynomial
open scoped BigOperators Matrix
open bezout.Algorithms

/-- The fixed DFB configuration from the comparison protocol. -/
def config (L : ℝ) : Momentum where
  alpha _ := 1/L
  beta _ := 1
  extrapolated := true
  reset _ := false

/-- The constant two-by-two DFB matrix at one eigenvalue. -/
def matrix (L lam : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![2*(1-lam/L), -(1-lam/L); 1,0]

/-- The literal extrapolated-query configuration has the stated constant matrix. -/
theorem matrix_eq (L lam : ℝ) (s : ℕ) : (config L).matrix s lam = matrix L lam := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [config, Momentum.matrix, Momentum.baseMatrix, matrix] <;> ring

/-- The exact DFB nominal scalar sequence, with d_(-1)=d_0=1 encoded by its startup. -/
def d (L lam : ℝ) : ℕ → ℝ
  | 0 => 1
  | 1 => 1-lam/L
  | j+2 => (1-lam/L)*(2*d L lam (j+1)-d L lam j)

/-- The previous nominal state, including the separately prescribed d_(-1)=1. -/
def dPrevious (L lam : ℝ) (j : ℕ) : ℝ := if j=0 then 1 else d L lam (j-1)

/-- The displayed scalar recurrence includes the first oracle step. -/
theorem d_step (L lam : ℝ) (j : ℕ) :
    d L lam (j+1) = (1-lam/L)*(2*d L lam j-dPrevious L lam j) := by
  cases j with
  | zero => norm_num [d,dPrevious]
  | succ j => simp only [d,dPrevious, Nat.add_eq_zero_iff,Nat.one_ne_zero,and_false,ite_false,Nat.add_sub_cancel]

/-- The two nominal scalar states obey the actual DFB matrix recurrence. -/
theorem d_state_step (L lam : ℝ) (j : ℕ) :
    matrix L lam *ᵥ ![d L lam j,dPrevious L lam j] =
      ![d L lam (j+1),dPrevious L lam (j+1)] := by
  have hp : dPrevious L lam (j+1)=d L lam j := by simp [dPrevious]
  rw [d_step,hp]
  ext i
  fin_cases i
  · simp [matrix,Matrix.mulVec,Matrix.vecHead,Matrix.vecTail]
    ring
  · simp [matrix,Matrix.mulVec,Matrix.vecHead,Matrix.vecTail]

/-- Exact matrix-power representation of every d_j, including both startups. -/
theorem d_matrix (L lam : ℝ) (j : ℕ) :
    matrix L lam ^ j *ᵥ ![1,1] = ![d L lam j,dPrevious L lam j] := by
  induction j with
  | zero => simp [d,dPrevious]
  | succ j ih => rw [pow_succ',← Matrix.mulVec_mulVec,ih,d_state_step]

/-- The nominal terminal polynomial value of the averaged DFB configuration. -/
def terminalValue (L lam : ℝ) (N : ℕ) : ℝ :=
  (∑ j ∈ Finset.range (N+1), d L lam j)/((N:ℝ)+1)

/-- The sum of the remaining unit injections is the exact equilibrium-shift response. -/
theorem accumulated_impulse (L lam : ℝ) (hL : L≠0) (hlam : lam≠0) (k : ℕ) :
    (1/L)*(∑ j ∈ Finset.range k, (matrix L lam^j *ᵥ ![(1:ℝ),0]) 0) =
      (1-d L lam k)/lam := by
  let x : Fin 2 → ℝ := ![1/lam,1/lam]
  have hv : x-matrix L lam*ᵥ x = (1/L) • ![(1:ℝ),0] := by
    ext i
    fin_cases i <;> simp [x,matrix,Matrix.vecHead,Matrix.vecTail]
    field_simp
    ring
  have hs := congrFun (sum_power_difference (matrix L lam) x k) 0
  rw [hv] at hs
  simp only [Matrix.mulVec_smul, Pi.sub_apply, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul] at hs
  have hx : x = (1/lam) • ![(1:ℝ),1] := by ext i; fin_cases i <;> simp [x]
  rw [hx, Matrix.mulVec_smul, d_matrix] at hs
  simp only [Matrix.cons_val_zero, Pi.smul_apply, smul_eq_mul,mul_one] at hs
  rw [Finset.mul_sum]
  have hfinal : (1/lam)-(1/lam)*d L lam k=(1-d L lam k)/lam := by ring
  exact hs.trans hfinal

/-- Literal DFB execution returns the running average of its single physical trajectory. -/
def output {E : Type*} [AddCommGroup E] [Module ℝ E] (L : ℝ) (N : ℕ)
    (oracle : Fin N → E → E) (initial : E) : E := (config L).averagedOutput N oracle initial

/-- Every nominal physical DFB iterate equals its prescribed d_j. -/
theorem nominal_iterate (L lam : ℝ) (N j : ℕ) (hj : j≤N) :
    (((config L).program N).runPrefix (Momentum.scalarOracle N lam (fun _ => 0)) 1 j).vectors 0 =
      d L lam j := by
  have h := congrFun ((config L).scalarState_nominal N lam 1 j hj) 0
  simp only [Momentum.scalarState,Matrix.cons_val_zero,matrix_eq,
    orderedProduct_constant,d_matrix] at h
  exact h

/-- The actual averaged nominal output is the printed finite d_j average. -/
theorem terminalValue_actual (L lam : ℝ) (N : ℕ) :
    output L N (Momentum.scalarOracle N lam (fun _ => 0)) 1 = terminalValue L lam N := by
  rw [output,Momentum.averagedOutput_eq]
  simp only [smul_eq_mul,terminalValue,div_eq_mul_inv]
  rw [mul_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  exact nominal_iterate L lam N j (by have := Finset.mem_range.mp hj; omega)

/-- The scalar physical response is defined by the actual averaged unit-impulse run. -/
def responseValue (L lam : ℝ) (N : ℕ) (s : Fin N) : ℝ :=
  output L N (Momentum.scalarOracle N lam (fun j => if j=s then 1 else 0)) 0

/-- A physical impulse affects precisely the later iterates, with the exact matrix power. -/
theorem impulse_iterate (L lam : ℝ) (N : ℕ) (s : Fin N) (j : ℕ) (hj : j≤N) :
    (((config L).program N).runPrefix
      (Momentum.scalarOracle N lam (fun t => if t=s then 1 else 0)) 0 j).vectors 0 =
      if s.val<j then -(1/L)*(matrix L lam^(j-(s.val+1)) *ᵥ ![1,0]) 0 else 0 := by
  have hp := congrFun ((config L).scalarState_impulse N lam s j hj) 0
  simp only [Momentum.scalarState,Matrix.cons_val_zero,matrix_eq,orderedProduct_constant] at hp
  rw [hp]
  by_cases hs : s.val<j
  · rw [ite_eq_left hs]
    have hv : ![-(config L).alpha s.val,0] = (-(1/L)) • ![(1:ℝ),0] := by
      ext i; fin_cases i <;> simp [config]
    rw [hv,Matrix.mulVec_smul]
    simp only [hs,ite_true,Pi.smul_apply,smul_eq_mul]
  · simp only [hs,ite_false,Pi.zero_apply]

/-- Averaging the actual physical impulse sums exactly its remaining suffix states. -/
theorem responseValue_sum (L lam : ℝ) (N : ℕ) (s : Fin N) :
    responseValue L lam N s =
      -((1/L)*(∑ j ∈ Finset.range (N-s.val), (matrix L lam^j *ᵥ ![1,0]) 0))/((N:ℝ)+1) := by
  rw [responseValue,output,Momentum.averagedOutput_eq]
  have hs : (∑ j ∈ Finset.range (N+1),
      (((config L).program N).runPrefix
        (Momentum.scalarOracle N lam (fun t => if t=s then 1 else 0)) 0 j).vectors 0) =
      ∑ j ∈ Finset.range (N+1), if s.val<j then
        -(1/L)*(matrix L lam^(j-(s.val+1)) *ᵥ ![1,0]) 0 else 0 := by
    apply Finset.sum_congr rfl
    intro j hj
    exact impulse_iterate L lam N s j (by have := Finset.mem_range.mp hj; omega)
  rw [hs,sum_shifted_tail (fun j => -(1/L)*(matrix L lam^j *ᵥ ![1,0]) 0) N s.val,
    ← Finset.mul_sum]
  simp only [smul_eq_mul]
  ring

/-- The exact printed DFB physical response, valid at every nonzero eigenvalue. -/
theorem responseValue_eq (L lam : ℝ) (hL : L≠0) (hlam : lam≠0)
    (N : ℕ) (s : Fin N) :
    responseValue L lam N s = -(1-d L lam (N-s.val))/(lam*((N:ℝ)+1)) := by
  rw [responseValue_sum,accumulated_impulse L lam hL hlam]
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring

/-- The actual DFB variance coefficient is the sum of its physical response squares. -/
def varianceValue (L lam : ℝ) (N : ℕ) : ℝ := ∑ s : Fin N, responseValue L lam N s^2

/-- The finite variance formula in Equation `eq:competitor-dfb`. -/
theorem varianceValue_eq (L lam : ℝ) (hL : L≠0) (hlam : lam≠0) (N : ℕ) :
    varianceValue L lam N =
      (∑ j ∈ Finset.range N, (1-d L lam (j+1))^2)/(lam^2*((N:ℝ)+1)^2) := by
  simp only [varianceValue,responseValue_eq L lam hL hlam,div_pow,neg_sq,mul_pow]
  rw [← Finset.sum_div]
  congr 1
  rw [Fin.sum_univ_eq_sum_range (fun s : ℕ => (1-d L lam (N-s))^2) N]
  rw [← Finset.sum_range_reflect (fun s => (1-d L lam (N-s))^2) N]
  apply Finset.sum_congr rfl
  intro j hj
  rw [show N-(N-1-j)=j+1 by have := Finset.mem_range.mp hj; omega]

/-- Every actual scalar error stream has precisely the computed physical response.
This superposition concerns errors returned by the oracle at extrapolated queries. -/
theorem output_superposition (L lam : ℝ) (N : ℕ) (initial : ℝ) (noise : Fin N → ℝ) :
    output L N (Momentum.scalarOracle N lam noise) initial =
      terminalValue L lam N*initial+∑ s : Fin N, responseValue L lam N s*noise s := by
  have hcurrent (j : ℕ) (hj : j<N+1) :
      (((config L).program N).runPrefix (Momentum.scalarOracle N lam noise) initial j).vectors 0 =
      initial*(((config L).program N).runPrefix (Momentum.scalarOracle N lam (fun _ => 0)) 1 j).vectors 0 +
        ∑ s : Fin N, noise s*(((config L).program N).runPrefix
          (Momentum.scalarOracle N lam (fun t => if t=s then 1 else 0)) 0 j).vectors 0 := by
    have hp := congrFun ((config L).scalarState_superposition N lam initial noise j (by omega)) 0
    simpa only [Momentum.scalarState,Matrix.cons_val_zero,Pi.add_apply,Pi.smul_apply,
      Finset.sum_apply,smul_eq_mul] using hp
  rw [← terminalValue_actual L lam N]
  unfold responseValue
  simp only [output,Momentum.averagedOutput_eq,smul_eq_mul]
  have hs : (∑ j ∈ Finset.range (N+1),
      (((config L).program N).runPrefix (Momentum.scalarOracle N lam noise) initial j).vectors 0) =
      ∑ j ∈ Finset.range (N+1),
        (initial*(((config L).program N).runPrefix (Momentum.scalarOracle N lam (fun _ => 0)) 1 j).vectors 0 +
          ∑ s : Fin N, noise s*(((config L).program N).runPrefix
            (Momentum.scalarOracle N lam (fun t => if t=s then 1 else 0)) 0 j).vectors 0) := by
    apply Finset.sum_congr rfl
    intro j hj
    exact hcurrent j (Finset.mem_range.mp hj)
  rw [hs]
  simp only [Finset.sum_add_distrib,mul_add,Finset.mul_sum,Finset.sum_mul]
  rw [Finset.sum_comm]
  congr 1
  · apply Finset.sum_congr rfl
    intro j _
    ring
  · apply Finset.sum_congr rfl
    intro s _
    apply Finset.sum_congr rfl
    intro j _
    ring

/-- The accelerated running-average implementation still makes exactly N fresh calls. -/
theorem oracle_calls {E : Type*} [AddCommGroup E] [Module ℝ E] (L : ℝ) (N : ℕ)
    (oracle : Fin N → E → E) (initial : E) :
    ((config L).averagedPrefix N oracle initial N).state.calls=N :=
  Momentum.averaged_oracle_calls _ _ _ _

end
end bezout.Comparisons.Competitors.DFB
