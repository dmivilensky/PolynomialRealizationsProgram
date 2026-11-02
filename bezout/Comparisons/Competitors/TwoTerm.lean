import bezout.Comparisons.Competitors.Propagation
import chebyshev1.TwoTerm.Basic
import bezout.History.Realization

/-!
Article: bezout, Prefix and sine--Jacobi competitor configurations.
Use: normalized two-term Jacobi coefficients become literal current-query
momentum executions, with exact nominal terminals and physical kernels.
Proof: fixed-point normalization identifies each used two-by-two matrix;
the unused initial previous slot has zero propagated second column.
-/

namespace bezout.Comparisons.Competitors.TwoTerm
noncomputable section
open chebyshev1 Polynomial
open scoped BigOperators Matrix

/-- Convert the normalized two-term recurrence to the printed momentum form. -/
def config (S : chebyshev1.TwoTerm) : Momentum where
  alpha := S.gamma
  beta s := if s=0 then 0 else -S.b s
  extrapolated := false
  reset _ := false

/-- Fixed-point normalization identifies every used physical matrix. -/
theorem matrix_eq (S : chebyshev1.TwoTerm) (N : ℕ)
    (hf : ∀ s, 0<s → s<N → S.a s+S.b s=1) (s : ℕ) (hs : s<N) (lam : ℝ) :
    (config S).matrix s lam=S.realization.scalarStep s lam := by
  cases s with
  | zero => simp [config,Momentum.matrix,Momentum.baseMatrix,S.scalarStep_zero]
  | succ s =>
    have ha : S.a (s+1)=1-S.b (s+1) := by have := hf (s+1) (by omega) hs; linarith
    rw [S.scalarStep_succ]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [config,Momentum.matrix,Momentum.baseMatrix,ha]
    ring

/-- The initial previous component is never read by a normalized two-term method. -/
theorem product_second_column (S : chebyshev1.TwoTerm) (lam : ℝ) (n : ℕ) (i : Fin 2) :
    orderedProduct (fun s => S.realization.scalarStep s lam) (n+1) i 1=0 := by
  induction n generalizing i with
  | zero => rw [orderedProduct_succ,orderedProduct_zero,Matrix.mul_one,S.scalarStep_zero]; fin_cases i <;> simp
  | succ n ih =>
    rw [orderedProduct_succ,Matrix.mul_apply]
    simp only [Fin.sum_univ_two,ih,mul_zero,add_zero]

/-- Both initial previous-state conventions have the same nominal current output. -/
theorem product_action (S : chebyshev1.TwoTerm) (lam : ℝ) (n : ℕ) :
    (orderedProduct (fun s => S.realization.scalarStep s lam) n *ᵥ ![1,1]) 0=
      S.realization.scalarTransfer n lam := by
  rw [Realization.scalarTransfer,chebyshev1.TwoTerm.scalarContract]
  cases n with
  | zero => simp
  | succ n =>
    have hc := product_second_column S lam n 0
    simp only [Matrix.mulVec,dotProduct,Fin.sum_univ_two]
    rw [hc]
    simp

/-- The actual finite momentum terminal is precisely the existing two-term polynomial. -/
theorem terminal (S : chebyshev1.TwoTerm) (N : ℕ)
    (hf : ∀ s, 0<s → s<N → S.a s+S.b s=1) :
    ((config S).history N).terminal=S.realization.residualPolynomial N := by
  apply Polynomial.funext
  intro lam
  rw [Momentum.terminal_eval,Realization.residualPolynomial_eval]
  have hp : orderedProduct (fun s => (config S).matrix s lam) N=
      orderedProduct (fun s => S.realization.scalarStep s lam) N :=
    orderedProduct_congr (fun s hs => matrix_eq S N hf s hs lam)
  rw [hp,product_action]

/-- Every nominal query equals the corresponding exact two-term scalar prefix. -/
theorem query_eval (S : chebyshev1.TwoTerm) (N : ℕ)
    (hf : ∀ s, 0<s → s<N → S.a s+S.b s=1) (s : Fin N) (lam : ℝ) :
    (((config S).history N).query s).eval lam=S.realization.scalarTransfer s.val lam := by
  rw [Momentum.query_eval_actual,Momentum.queryAt_eq]
  simp only [Momentum.query,config,Bool.false_eq_true,ite_false]
  change (((config S).program N).runPrefix (Momentum.scalarOracle N lam (fun _ => 0)) 1 s.val).vectors 0 = _
  have hstate := congrFun ((config S).scalarState_nominal N lam 1 s.val (Nat.le_of_lt s.isLt)) 0
  simp only [Momentum.scalarState,Matrix.cons_val_zero] at hstate
  rw [hstate]
  have hp : orderedProduct (fun j => (config S).matrix j lam) s.val=
      orderedProduct (fun j => S.realization.scalarStep j lam) s.val :=
    orderedProduct_congr (fun j hj => matrix_eq S N hf j (by omega) lam)
  rw [hp,product_action]

/-- Every physical response and query product is the existing two-term insertion
kernel, so existing spectral and asymptotic theorems concern this actual oracle code. -/
theorem realization_kernel (S : chebyshev1.TwoTerm) (N : ℕ)
    (hf : ∀ s, 0<s → s<N → S.a s+S.b s=1) (s : Fin N) (x y : ℝ) :
    ((config S).history N).realization.kernel N s.val x y=S.realization.kernel N s.val x y := by
  rw [bezout.History.realization_kernel,Momentum.response_eval,query_eval S N hf]
  have hp : orderedProduct (fun i => (config S).matrix (s.val+1+i) x) (N-(s.val+1))=
      orderedProduct (fun i => S.realization.scalarStep (s.val+1+i) x) (N-(s.val+1)) := by
    apply orderedProduct_congr
    intro i hi
    exact matrix_eq S N hf _ (by omega) x
  rw [hp]
  simp [Realization.kernel,chebyshev1.TwoTerm.scalarContract,
    chebyshev1.TwoTerm.queryFactor,Realization.scalarTransfer,config,
    Matrix.mul_apply,Matrix.mulVec,dotProduct,Fin.sum_univ_two]
  ring_nf
  simp

end
end bezout.Comparisons.Competitors.TwoTerm
