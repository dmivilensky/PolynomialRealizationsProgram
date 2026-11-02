import bezout.Comparisons.Competitors.Momentum
import bezout.Risk.Lower

/-!
Article: bezout, Equation `eq:competitor-transfer`.
Use: exact physical terminal and single-answer impulse formulas for momentum,
extrapolated queries and resets, in the literal finite oracle execution.
Proof: the two-state physical loop satisfies the inhomogeneous matrix recurrence;
variation of constants and the actual history response identify every factor.
-/

namespace bezout.Comparisons.Competitors.Momentum
noncomputable section
open chebyshev1 Polynomial
open scoped BigOperators Matrix
open bezout.Algorithms

/-- The spectral two-state action is exactly the physical momentum assignment. -/
theorem matrix_mulVec (data : Momentum) (s : ℕ) (lam x p : ℝ) :
    data.matrix s lam *ᵥ ![x,p] =
      ![(1+data.beta s)*x-data.beta s*data.previous s x p-
        data.alpha s*lam*data.query s x p, x] := by
  cases he : data.extrapolated <;> cases hr : data.reset s <;>
    ext i <;> fin_cases i <;>
    simp [matrix, baseMatrix, resetMatrix, previous, query, he, hr,
      Matrix.mul_apply, Matrix.mulVec, Fin.sum_univ_two, smul_eq_mul,
      Matrix.vecHead, Matrix.vecTail, Matrix.one_apply] <;> ring

/-- The actual scalar oracle corresponding to one Hessian eigenvalue. -/
def scalarOracle (N : ℕ) (lam : ℝ) (noise : Fin N → ℝ) : Fin N → ℝ → ℝ :=
  fun s x => lam*x+noise s

/-- The current and previous components of the actual physical prefix. -/
def scalarState (data : Momentum) (N : ℕ) (lam initial : ℝ) (noise : Fin N → ℝ)
    (k : ℕ) : Fin 2 → ℝ :=
  ![((data.program N).runPrefix (scalarOracle N lam noise) initial k).vectors 0,
    ((data.program N).runPrefix (scalarOracle N lam noise) initial k).vectors 1]

/-- The signed physical answer error injected into the first state component. -/
def scalarForcing (data : Momentum) (N : ℕ) (noise : Fin N → ℝ) (s : ℕ) : Fin 2 → ℝ :=
  if hs : s<N then ![-data.alpha s*noise ⟨s,hs⟩,0] else 0

/-- One physical scalar stage has exactly the printed two-by-two propagation. -/
theorem scalarState_succ (data : Momentum) (N : ℕ) (lam initial : ℝ)
    (noise : Fin N → ℝ) (k : ℕ) (hk : k<N) :
    data.scalarState N lam initial noise (k+1) =
      data.matrix k lam *ᵥ data.scalarState N lam initial noise k + data.scalarForcing N noise k := by
  let old := (data.program N).runPrefix (scalarOracle N lam noise) initial k
  have hv : old.vectors = ![old.vectors 0,old.vectors 1,old.vectors 2] := by
    ext i; fin_cases i <;> rfl
  have hs : old = ⟨![old.vectors 0,old.vectors 1,old.vectors 2],old.calls⟩ :=
    RegisterState.ext hv rfl
  have hstep := data.stage_vectors N ⟨k,hk⟩ (scalarOracle N lam noise)
    (old.vectors 0) (old.vectors 1) (old.vectors 2) old.calls
  simp only [scalarState, RegisterProgram.runPrefix, dite_eq_left hk]
  change ![((data.program N).stage _ _ old).vectors 0,
    ((data.program N).stage _ _ old).vectors 1] = _
  rw [hs]
  simp only [hstep, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [data.matrix_mulVec]
  ext i
  fin_cases i <;> simp [scalarForcing, hk, scalarOracle, smul_eq_mul] <;> ring

/-- The actual scalar execution equals the exact inhomogeneous matrix recursion. -/
theorem scalarState_eq_linearRun (data : Momentum) (N : ℕ) (lam initial : ℝ)
    (noise : Fin N → ℝ) (k : ℕ) (hk : k≤N) :
    data.scalarState N lam initial noise k =
      linearRun (fun j => data.matrix j lam) (data.scalarForcing N noise) ![initial,initial] k := by
  induction k with
  | zero => ext i; fin_cases i <;>
      simp [scalarState, RegisterProgram.runPrefix, RegisterProgram.initialState, program, linearRun]
  | succ k ih => rw [data.scalarState_succ N lam initial noise k (by omega), linearRun, ih (by omega)]

/-- The physical output is the first component of the actual scalar state. -/
theorem scalar_output (data : Momentum) (N : ℕ) (lam initial : ℝ) (noise : Fin N → ℝ) :
    (data.program N).output (scalarOracle N lam noise) initial =
      data.scalarState N lam initial noise N 0 := rfl

/-- The actual nominal physical query evaluates the induced history query polynomial. -/
theorem query_eval_actual (data : Momentum) (N : ℕ) (s : Fin N) (lam : ℝ) :
    ((data.history N).query s).eval lam =
      (data.program N).queryAt (scalarOracle N lam (fun _ => 0)) 1 s := by
  have hq := data.query_eq_history N (scalarOracle N lam (fun _ => 0)) (1:ℝ) s
  have hn := (data.history N).nominal_query (bezout.History.scalarOperator lam) (1:ℝ)
    ((data.history N).oracleExecution (bezout.History.scalarOperator lam) 1 (fun _ => 0)) s
  simp only [bezout.History.oracleExecution, bezout.History.scalarOperator_polynomial_action,
    mul_one] at hn
  have hor : scalarOracle N lam (fun _ => 0) =
      fun j x => bezout.History.scalarOperator lam x+(0:ℝ) := by rfl
  rw [hor] at hq
  exact (hq.trans hn).symm

/-- The nominal scalar terminal of the actual causal history. -/
theorem terminal_eval (data : Momentum) (N : ℕ) (lam : ℝ) :
    (data.history N).terminal.eval lam =
      (orderedProduct (fun s => data.matrix s lam) N *ᵥ ![1,1]) 0 := by
  have hout := data.output_eq_history N (scalarOracle N lam (fun _ => 0)) (1:ℝ)
  have hor : scalarOracle N lam (fun _ => 0) =
      fun s x => bezout.History.scalarOperator lam x+(0:ℝ) := by rfl
  rw [hor, bezout.History.oracleOutput_linear, bezout.History.nominal_output,
    bezout.History.scalarOperator_polynomial_action, mul_one] at hout
  rw [← hout, ← hor, data.scalar_output, data.scalarState_eq_linearRun N lam 1 _ N le_rfl,
    linearRun_expansion]
  have hz : data.scalarForcing N (fun _ => 0) = fun _ => 0 := by
    funext j
    simp [scalarForcing]
  rw [hz]
  simp

/-- A unit physical error stream injects one signed first-component impulse. -/
theorem scalarForcing_single (data : Momentum) (N : ℕ) (s : Fin N) :
    data.scalarForcing N (fun j => if j=s then 1 else 0) =
      fun j => if j=s.val then ![-data.alpha s.val,0] else 0 := by
  funext j
  by_cases hj : j<N
  · by_cases he : j=s.val
    · subst j
      simp [scalarForcing,hj]
    · have hne : (⟨j,hj⟩:Fin N)≠s := by intro h; exact he (congrArg Fin.val h)
      simp [scalarForcing,hj,he,hne]
  · have he : j≠s.val := by have := s.isLt; omega
    simp [scalarForcing,hj,he]

/-- Every actual nominal prefix is its ordered spectral matrix product. -/
theorem scalarState_nominal (data : Momentum) (N : ℕ) (lam initial : ℝ)
    (k : ℕ) (hk : k≤N) :
    data.scalarState N lam initial (fun _ => 0) k =
      orderedProduct (fun j => data.matrix j lam) k *ᵥ ![initial,initial] := by
  rw [data.scalarState_eq_linearRun N lam initial _ k hk,linearRun_expansion]
  have hz : data.scalarForcing N (fun _ => 0) = fun _ => 0 := by
    funext j
    simp [scalarForcing]
  rw [hz]
  simp

/-- The actual state created by a single physical unit error at any finite prefix. -/
theorem scalarState_impulse (data : Momentum) (N : ℕ) (lam : ℝ)
    (s : Fin N) (k : ℕ) (hk : k≤N) :
    data.scalarState N lam 0 (fun j => if j=s then 1 else 0) k =
      if s.val<k then
        orderedProduct (fun i => data.matrix (s.val+1+i) lam) (k-(s.val+1)) *ᵥ
          ![-data.alpha s.val,0] else 0 := by
  rw [data.scalarState_eq_linearRun N lam 0 _ k hk,data.scalarForcing_single]
  have hz : ![(0:ℝ),0] = (0 : Fin 2 → ℝ) := by ext i; fin_cases i <;> rfl
  rw [hz]
  by_cases hs : s.val<k
  · rw [ite_eq_left hs,linearRun_single_impulse _ _ hs]
  · rw [ite_eq_right hs,linearRun_before_impulse _ _ (by omega)]

/-- A physical error at call s is injected after its own matrix update and
propagates only through later matrices, including subsequent stage resets. -/
theorem response_eval (data : Momentum) (N : ℕ) (s : Fin N) (lam : ℝ) :
    ((data.history N).response s).eval lam =
      -data.alpha s.val *
        (orderedProduct (fun i => data.matrix (s.val+1+i) lam) (N-(s.val+1)) *ᵥ ![1,0]) 0 := by
  let noise : Fin N → ℝ := fun j => if j=s then 1 else 0
  have hout := data.output_eq_history N (scalarOracle N lam noise) (0:ℝ)
  have hor : scalarOracle N lam noise =
      fun j x => bezout.History.scalarOperator lam x+noise j := by rfl
  rw [hor, bezout.History.oracleOutput_linear, bezout.Risk.scalar_output] at hout
  simp only [mul_zero, zero_add, noise, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true] at hout
  rw [← hout, ← hor, data.scalar_output, data.scalarState_eq_linearRun N lam 0 _ N le_rfl]
  have hf : data.scalarForcing N noise =
      fun j => if j=s.val then ![-data.alpha s.val,0] else 0 := by
    funext j
    by_cases hj : j<N
    · by_cases he : j=s.val
      · subst j
        simp [scalarForcing, hj, noise]
      · have hne : (⟨j,hj⟩:Fin N)≠s := by intro h; exact he (congrArg Fin.val h)
        simp [scalarForcing, hj, noise, he, hne]
    · have he : j≠s.val := by have := s.isLt; omega
      simp [scalarForcing, hj, he]
  rw [hf]
  have hz : ![(0:ℝ),0] = (0 : Fin 2 → ℝ) := by ext i; fin_cases i <;> rfl
  rw [hz]
  rw [linearRun_single_impulse _ _ s.isLt]
  have hv : ![-data.alpha s.val,0] = (-data.alpha s.val) • ![(1:ℝ),0] := by ext i; fin_cases i <;> simp
  rw [hv, Matrix.mulVec_smul]
  rfl

end
end bezout.Comparisons.Competitors.Momentum
