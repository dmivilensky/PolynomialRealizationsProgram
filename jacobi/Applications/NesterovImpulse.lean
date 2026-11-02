import jacobi.Applications.NesterovKernel

/-!
Article: jacobi, Theorem 5.1.
The actual zero-mode linearized insertion state has current and previous
error coordinates. It is identified with the original realization kernel,
including causal zero padding before an insertion occurs.
Use: EndpointCovariance computes the three true squared-error recurrences.
-/
namespace jacobi.Applications
noncomputable section
open Matrix chebyshev1
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-- Every original zero-mode forward error equals its initial value.
Use: nesterovQuery_endpoint gives the exact source amplitude multiplying every actual zero-mode Hessian insertion.
Article: jacobi, Theorem 5.1.
Proof: the original initial errors are one and the recurrence has a fixed point for every momentum coefficient. -/
theorem nesterovError_endpoint (b:ℝ) (k:ℕ) : nesterovError b 0 k=1 := by
  induction k using Nat.twoStepInduction with
  | zero => rfl
  | one => simp [nesterovError]
  | more k h0 h1 => rw [nesterovError,h0,h1]; ring

/-- Every actual original zero-mode query is exactly the initial error, at every admissible or algebraic momentum parameter.
Use: each actual endpoint impulse is minus the unit current-memory vector.
Article: jacobi, Theorem 5.1.
Proof: the proved true forward memory has two unit coordinates. The original query coefficients sum to one. -/
theorem nesterovQuery_endpoint (b:ℝ) (k:ℕ) : nesterovQuery b k 0=1 := by
  rw [nesterovQuery,nesterov_forward_memory]
  simp [nesterovError_endpoint,nesterovMethod,Fin.sum_univ_two]

/-- The genuine linearized state caused by an endpoint Hessian insertion at time j, with causal zero state before it occurs.
Use: its first coordinate is the actual source kernel, and its three covariance sums give the exact endpoint gain asymptotic.
Article: jacobi, Theorem 5.1.
-/
def nesterovImpulse (b:ℝ) (j:ℕ) : ℕ → Fin 2 → ℝ
  | 0 => 0
  | k+1 => ((nesterovMethod b).scalarStep k 0).mulVec (nesterovImpulse b j k)-
      if j=k then ![1,0] else 0

/-- The actual insertion state vanishes before its original causal insertion time.
Use: endpoint covariance recurrences have exactly one new independent unit insertion at each time step.
Article: jacobi, Theorem 5.1.
Proof: before the insertion the original state is zero and the injection branch is absent. -/
theorem nesterovImpulse_before (b:ℝ) {j k:ℕ} (hk:k≤j) : nesterovImpulse b j k=0 := by
  induction k with
  | zero => rfl
  | succ k ih => simp [nesterovImpulse,ih (by omega),show j≠k by omega]

/-- After its actual insertion, the genuine linearized state is exactly the original causal tail acting on minus the current-memory unit vector.
Use: nesterovImpulse_kernel identifies the covariance calculation with the real original first variation.
Article: jacobi, Theorem 5.1.
Proof: at insertion the old causal state is zero. Every later step multiplies the same original scalar-step matrix on the left, which is precisely the earlier article's ordered causal product. -/
theorem nesterovImpulse_after (b:ℝ) {j k:ℕ} (hk:j<k) :
    nesterovImpulse b j k=
      -((orderedProduct (fun i => (nesterovMethod b).scalarStep (j+1+i) 0) (k-(j+1))).mulVec ![1,0]) := by
  -- This is the actual insertion state; no desired asymptotic kernel formula enters its definition.
  induction k with
  | zero => omega
  | succ k ih =>
    by_cases hj : j=k
    · subst j
      simp [nesterovImpulse,nesterovImpulse_before b le_rfl]
    · have hjk : j<k := by omega
      rw [nesterovImpulse,ite_eq_right hj,sub_zero,ih hjk,Matrix.mulVec_neg]
      rw [show k+1-(j+1)=(k-(j+1))+1 by omega,orderedProduct_succ,← Matrix.mulVec_mulVec]
      congr 2
      congr 1
      omega

/-- The actual original zero-mode first-variation kernel is precisely the first coordinate of the genuine causal impulse state.
Use: EndpointCovariance computes the original endpoint gain, not the gain of a surrogate recurrence.
Article: jacobi, Theorem 5.1.
Proof: the true query has unit amplitude. The generic original rank-one kernel and the exact causal impulse-tail formula therefore have the same negative first matrix entry. -/
theorem nesterovImpulse_kernel (b:ℝ) {j k:ℕ} (hk:j<k) :
    nesterovImpulse b j k 0=(nesterovMethod b).kernel k j 0 0 := by
  rw [nesterovImpulse_after b hk,nesterov_kernel_factorization,nesterovQuery_endpoint]
  simp [Matrix.mulVec,Matrix.vecHead,Matrix.vecTail]

/-- The original linearized memory update at an old insertion is the exact current-error/difference-error propagation.
Use: the genuine D, C and E covariance recurrences are finite sums of these same two identities.
Article: jacobi, Theorem 5.1.
Proof: the injection branch is absent, and the original scalar-step matrix has upper row (1+beta,-beta) and lower row (1,0). -/
theorem nesterovImpulse_old (b:ℝ) {j k:ℕ} (hj:j≠k) :
    nesterovImpulse b j (k+1) 0=nesterovImpulse b j k 0+nesterovMomentum b k*
      (nesterovImpulse b j k 0-nesterovImpulse b j k 1) ∧
    nesterovImpulse b j (k+1) 1=nesterovImpulse b j k 0 := by
  rw [nesterovImpulse,ite_eq_right hj,nesterov_scalarStep]
  simp [Matrix.vecHead,Matrix.vecTail]
  ring

/-- Each true new endpoint insertion has current value minus one and unchanged previous value zero.
Use: its squared contribution is exactly one in all three endpoint covariance recurrences.
Article: jacobi, Lemma A.2.
Proof: its preceding state is exactly zero by causality; evaluate the literal original injection. -/
theorem nesterovImpulse_new (b:ℝ) (k:ℕ) : nesterovImpulse b k (k+1)=![-1,0] := by
  simp [nesterovImpulse,nesterovImpulse_before b le_rfl]

end
end jacobi.Applications
