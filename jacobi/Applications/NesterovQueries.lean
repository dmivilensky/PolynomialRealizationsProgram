import jacobi.Applications.NesterovModel
import jacobi.Applications.NesterovWave

/-!
Article: jacobi, Theorem 5.1.
The true forward Nesterov memory and queried error are identified with
the polynomial fundamental solutions. The argument keeps the endpoint
lambda=1 and the first Landweber step, without dividing by 1-lambda.
Use: NesterovKernel combines the actual query with its causal tail.
-/
namespace jacobi.Applications
noncomputable section
open Matrix chebyshev1
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-- The actual scalar error recurrence of the original Nesterov realization.
Use: nesterov_forward_memory identifies it with the true ordered matrix product, and its rescaled formula identifies the actual queries.
Article: jacobi, Theorem 5.1.
-/
def nesterovError (b l:ℝ) : ℕ → ℝ
  | 0 => 1
  | 1 => 1-l
  | s+2 => (1-l)*((1+nesterovMomentum b (s+1))*nesterovError b l (s+1)-
      nesterovMomentum b (s+1)*nesterovError b l s)

/-- The true ordered realization product stores precisely the current and previous original Nesterov errors.
Use: the forward query in nesterov_kernel is computed from the actual method, rather than stipulated as an auxiliary polynomial.
Article: jacobi, Theorem 5.1.
Proof: the initial equal memory yields the first Landweber step; multiplication by each genuine scalar step gives exactly the two-step original error recurrence. -/
theorem nesterov_forward_memory (b l:ℝ) (n:ℕ) :
    (orderedProduct (fun s => (nesterovMethod b).scalarStep s l) n).mulVec ![1,1]=
      ![nesterovError b l n,nesterovError b l (n-1)] := by
  -- The second coordinate is the previous error, including the prescribed equal initial errors.
  induction n using Nat.twoStepInduction with
  | zero => simp [nesterovError]
  | one =>
    rw [orderedProduct_succ,orderedProduct_zero,mul_one,nesterov_scalarStep]
    ext i
    fin_cases i <;> simp [Matrix.mulVec,nesterovError]
  | more n _ h1 =>
    rw [show n+2=(n+1)+1 by omega,orderedProduct_succ,← Matrix.mulVec_mulVec,h1,nesterov_scalarStep]
    ext i
    fin_cases i <;> simp [Matrix.mulVec,nesterovError]
    ring

/-- At b=1 the genuine current error is the printed polynomial wave divided by the true iteration count.
Use: the actual query has its exact F_s/(s+1) expression, including every spectral endpoint.
Article: jacobi, Theorem 5.1.
Proof: rescale the original two-step recurrence by the positive iteration count. Its rational coefficients cancel and leave precisely the proved constant-coefficient wave recurrence. -/
theorem nesterovError_wave (s:ℕ) (l:ℝ) :
    nesterovError 1 l (s+1)=(1-l)*nesterovWave s l/((s:ℝ)+1) := by
  -- All canceled denominators are positive iteration counts; the Landweber factor is never canceled.
  induction s using Nat.twoStepInduction with
  | zero => simp [nesterovError]
  | one => simp [nesterovError,nesterovMomentum]; ring
  | more n h0 h1 =>
    rw [show n+2+1=(n+1)+2 by omega,nesterovError,nesterovMomentum_one (by omega),h1,h0,
      nesterovWave_recurrence]
    push_cast
    field_simp
    ring

/-- The actual original queried forward error, before its stepwise Hessian application.
Use: nesterov_query_wave and nesterov_kernel factor the genuine spectral-pair first variation.
Article: jacobi, Theorem 5.1.
-/
def nesterovQuery (b:ℝ) (s:ℕ) (l:ℝ) : ℝ :=
  ∑ i:Fin 2,(nesterovMethod b).q s i*
    ((orderedProduct (fun r => (nesterovMethod b).scalarStep r l) s).mulVec ![1,1]) i

/-- Every genuine b=1 query equals the polynomial wave with exactly its original step normalization.
Use: computes one factor of the actual two-spectral-variable kernel in the sharp Nesterov gain theorem.
Article: jacobi, Theorem 5.1.
Proof: substitute the genuine current and previous forward errors. For the first two steps use their exact initial values; all later steps reduce to the true wave recurrence after canceling only positive natural denominators. -/
theorem nesterov_query_wave (s:ℕ) (l:ℝ) :
    nesterovQuery 1 s l=nesterovWave s l/((s:ℝ)+1) := by
  -- Lambda=1 is retained in the same polynomial identity, so no removable spectral case is assumed.
  rw [nesterovQuery,nesterov_forward_memory]
  simp only [Fin.sum_univ_two,nesterovMethod,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one]
  cases s with
  | zero => simp [nesterovError]
  | succ s =>
    cases s with
    | zero => simp [nesterovError,nesterovMomentum]; ring
    | succ n =>
      rw [nesterovMomentum_one (by omega),show n+1+1-1=n+1 by omega,
        show n+1+1=n+2 by omega,
        nesterovError_wave,nesterovError_wave,nesterovWave_recurrence]
      push_cast
      field_simp
      ring

end
end jacobi.Applications
