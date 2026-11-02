import jacobi.Applications.NesterovModel
import jacobi.Applications.NesterovWave

/-!
Article: jacobi, Theorem 5.1.
The causal ordered matrix product propagates an insertion by the exact
polynomial fundamental solution after the original positive-step rescaling.
Use: NesterovKernel combines this tail with the actual forward query.
-/
namespace jacobi.Applications
noncomputable section
open Matrix chebyshev1
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-- The two entries in a nonempty actual Nesterov tail column are exactly the rescaled polynomial fundamental solutions.
Use: nesterov_tail_fundamental computes the causal propagation of one genuine Hessian insertion.
Article: jacobi, Theorem 5.1.
Proof: multiply the genuine next scalar step into the tail. Its two rational coefficients cancel the preceding positive iteration counts and yield the true fundamental-wave recurrence. -/
theorem nesterov_tail_column (r k:ℕ) (hr:1≤r) (l:ℝ) :
    let M := orderedProduct (fun i => (nesterovMethod 1).scalarStep (r+i) l) (k+1)
    M 0 0=(r:ℝ)/(r+(k+1):ℕ)*nesterovWave (k+1) l ∧
    M 1 0=(r:ℝ)/(r+k:ℕ)*nesterovWave k l := by
  -- Rescaling only divides by positive iteration indices, including an insertion at the first step.
  induction k with
  | zero =>
    simp only [orderedProduct_succ,orderedProduct_zero,mul_one,Nat.add_zero]
    rw [nesterov_scalarStep,nesterovMomentum_one (by omega)]
    constructor
    · simp only [Matrix.of_apply,Matrix.cons_val_zero,Nat.cast_add,Nat.cast_one]
      simp only [Nat.zero_add,nesterovWave_one]
      field_simp
      ring
    · simp only [Matrix.of_apply,Matrix.cons_val_zero,Matrix.cons_val_one,nesterovWave_zero,mul_one]
      rw [div_self (show (r:ℝ)≠0 by exact_mod_cast (by omega : r≠0))]
  | succ k ih =>
    dsimp only at ih ⊢
    rw [orderedProduct_succ,nesterov_scalarStep,nesterovMomentum_one (by omega)]
    constructor
    · simp only [Matrix.mul_apply,Fin.sum_univ_two,Matrix.of_apply,Matrix.cons_val_zero,
        Matrix.cons_val_one,Matrix.cons_val_fin_one,ih.1,ih.2]
      rw [show k+1+1=k+2 by omega,nesterovWave_recurrence]
      push_cast
      have hrp : 0<(r:ℝ) := by exact_mod_cast (by omega : 0<r)
      field_simp [ne_of_gt (show 0<(r:ℝ)+k by positivity)]
      ring
    · simpa only [Matrix.mul_apply,Fin.sum_univ_two,Matrix.of_apply,Matrix.cons_val_zero,
        Matrix.cons_val_one,Matrix.cons_val_fin_one,one_mul,zero_mul,add_zero] using ih.1

/-- The actual causal tail has exactly the printed wave factor, including the empty tail.
Use: nesterov_kernel obtains the full spectral-pair first variation from the generic original realization calculus.
Article: jacobi, Theorem 5.1.
Proof: the empty tail is the identity. Every nonempty tail is the proved original two-entry propagator, and its ending index is the actual horizon. -/
theorem nesterov_tail_fundamental {k r:ℕ} (hr:1≤r) (hrk:r≤k) (l:ℝ) :
    orderedProduct (fun i => (nesterovMethod 1).scalarStep (r+i) l) (k-r) 0 0=
      (r:ℝ)/(k:ℝ)*nesterovWave (k-r) l := by
  -- Treat the empty original causal product separately; its terminal normalization is nonzero.
  rcases Nat.eq_zero_or_pos (k-r) with h | h
  · have he : k=r := by omega
    rw [h,orderedProduct_zero,nesterovWave_zero,mul_one,he]
    simp [show (r:ℝ)≠0 by exact_mod_cast (by omega : r≠0)]
  · obtain ⟨j,hj⟩ := Nat.exists_eq_succ_of_ne_zero h.ne'
    have hh := (nesterov_tail_column r j hr l).1
    have he : r+(j+1)=k := by omega
    rw [he] at hh
    simpa only [hj,Nat.succ_eq_add_one] using hh

end
end jacobi.Applications
