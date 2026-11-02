import krylov.Reference.CGPolynomials
import krylov.Realization.PolynomialMemory

/-!
Article: Definition B.10 [s3:def:phi] of krylov.tex.
Use: construct the printed continuation and direction polynomials from actual
frozen CG coefficients and connect them to the existing chronological transfer
calculus; offset k means the source endpoint m=j+k.
Source: measured CG residual recurrence, standard polynomial degree inequalities
and the already proved ordered physical polynomial-memory action.
-/

namespace krylov.Envelope
noncomputable section
open Polynomial Matrix krylov.Reference krylov.Realization chebyshev1
open scoped BigOperators
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The frozen gradient/direction polynomial state started at the genuine injection time.
Use: The frozen gradient/direction polynomial state started at the genuine injection time.
Article: main_krylov, s3:def:phi and apB:lem:filtration, actual continuation polynomials.
Proof: The initial impulse has residual one and direction minus one. -/
def continuationRun (α β : ℕ → ℝ) (j : ℕ) : ℕ → ℝ[X] × ℝ[X]
  | 0 => (1,-1)
  | k+1 =>
    let p := continuationRun α β j k
    let r := p.1+C (α (j+k))*X*p.2
    (r,-r+C (β (j+k))*p.2)

/-- The source continuation polynomial after k frozen steps starting at j.
Use: The source continuation polynomial after k frozen steps starting at j.
Article: main_krylov, s3:def:phi and apB:lem:filtration, actual continuation polynomials.
Proof: Its source endpoint is m=j+k; no terminal spectral data are assumed. -/
def phi (α β : ℕ → ℝ) (j k : ℕ) : ℝ[X] := (continuationRun α β j k).1

/-- The corresponding frozen direction-response polynomial.
Use: The corresponding frozen direction-response polynomial.
Article: main_krylov, s3:def:phi and apB:lem:filtration, actual continuation polynomials.
Proof: It is the second component of the same actual frozen recurrence. -/
def psi (α β : ℕ → ℝ) (j k : ℕ) : ℝ[X] := (continuationRun α β j k).2

/-- The empty continuation polynomial is one.
Use: The empty continuation polynomial is one.
Article: main_krylov, s3:def:phi and apB:lem:filtration, actual continuation polynomials.
Proof: Use the actual empty state. -/
theorem phi_zero (α β : ℕ → ℝ) (j : ℕ) : phi α β j 0=1 := rfl

/-- The initial direction response is minus one.
Use: The initial direction response is minus one.
Article: main_krylov, s3:def:phi and apB:lem:filtration, actual continuation polynomials.
Proof: Use the actual empty state. -/
theorem psi_zero (α β : ℕ → ℝ) (j : ℕ) : psi α β j 0= -1 := rfl

/-- The actual continuation has the printed gradient-update recurrence.
Use: The actual continuation has the printed gradient-update recurrence.
Article: main_krylov, s3:def:phi and apB:lem:filtration, actual continuation polynomials.
Proof: Unfold the next polynomial state. -/
theorem phi_succ (α β : ℕ → ℝ) (j k : ℕ) :
    phi α β j (k+1)=phi α β j k+C (α (j+k))*X*psi α β j k := rfl

/-- The actual direction response has the printed CG recurrence.
Use: The actual direction response has the printed CG recurrence.
Article: main_krylov, s3:def:phi and apB:lem:filtration, actual continuation polynomials.
Proof: Unfold the second component of the next state. -/
theorem psi_succ (α β : ℕ → ℝ) (j k : ℕ) :
    psi α β j (k+1)= -phi α β j (k+1)+C (β (j+k))*psi α β j k := rfl

/-- Every actual continuation is normalized to one at zero.
Use: Every actual continuation is normalized to one at zero.
Article: main_krylov, s3:def:phi and apB:lem:filtration, actual continuation polynomials.
Proof: Every residual update adds a multiple of the polynomial variable. -/
theorem phi_at_zero (α β : ℕ → ℝ) (j k : ℕ) : (phi α β j k).eval 0=1 := by
  induction k with
  | zero => simp only [phi_zero,eval_one]
  | succ k ih =>
    rw [phi_succ]
    simpa only [eval_add,eval_mul,eval_C,eval_X,mul_zero,zero_mul,add_zero] using ih

/-- Both true continuation polynomial degrees are at most their number of frozen steps.
Use: Both true continuation polynomial degrees are at most their number of frozen steps.
Article: main_krylov, s3:def:phi and apB:lem:filtration, actual continuation polynomials.
Proof: Use polynomial product and sum degree inequalities in the genuine simultaneous recurrence. -/
theorem continuation_degree (α β : ℕ → ℝ) (j k : ℕ) :
    (phi α β j k).natDegree ≤ k ∧ (psi α β j k).natDegree ≤ k := by
  -- Bound both actual state components together, including vanishing measured coefficients.
  induction k with
  | zero => simp [phi,psi,continuationRun]
  | succ k ih =>
    have hx : (C (α (j+k))*X : ℝ[X]).natDegree ≤ 1 :=
      (natDegree_C_mul_le _ _).trans (by simp only [natDegree_X,le_refl])
    have hr : (phi α β j (k+1)).natDegree ≤ k+1 := by
      rw [phi_succ]
      exact natDegree_add_le_of_degree_le (ih.1.trans (Nat.le_succ k))
        ((natDegree_mul_le.trans (Nat.add_le_add hx ih.2)).trans (by omega))
    refine ⟨hr,?_⟩
    rw [psi_succ]
    apply (natDegree_add_le _ _).trans
    rw [natDegree_neg]
    exact max_le hr ((natDegree_C_mul_le _ _).trans (ih.2.trans (Nat.le_succ k)))

/-- At injection time zero, the continuation uses exactly the genuine measured CG residual and direction polynomials.
Use: At injection time zero, the continuation uses exactly the genuine measured CG residual and direction polynomials.
Article: main_krylov, s3:def:phi and apB:lem:filtration, actual continuation polynomials.
Proof: The two actual recurrences and initial states agree. -/
theorem continuation_actual_cg (Q : E →L[ℝ] E) (g : E) (k : ℕ) :
    continuationRun (CG.length Q g) (CG.beta Q g) 0 k=CG.polynomialRun Q g k := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [continuationRun,CG.polynomialRun,ih,zero_add]

/-- The actual two-memory polynomial transition of the frozen gradient/direction pair.
Use: The actual two-memory polynomial transition of the frozen gradient/direction pair.
Article: main_krylov, s3:def:phi and apB:lem:filtration, actual continuation polynomials.
Proof: Its entries encode the measured residual and momentum updates. -/
def continuationMatrix (α β : ℕ → ℝ) (k : ℕ) : Matrix (Fin 2) (Fin 2) ℝ[X] :=
  !![1,C (α k)*X; -1,C (β k)-C (α k)*X]

/-- The continuation state is exactly the existing chronological ordered polynomial transfer of its true injection.
Use: The continuation state is exactly the existing chronological ordered polynomial transfer of its true injection.
Article: main_krylov, s3:def:phi and apB:lem:filtration, actual continuation polynomials.
Proof: Induction on the actual transfer uses the two printed polynomial updates. -/
theorem continuation_matrix (α β : ℕ → ℝ) (j k : ℕ) :
    (fun i : Fin 2 => if i=0 then phi α β j k else psi α β j k)=
      orderedProduct (fun l => continuationMatrix α β (j+l)) k *ᵥ ![1,-1] := by
  -- Keep the genuine chronological product convention already used by the physical realization dictionary.
  induction k with
  | zero => ext i;fin_cases i <;> simp [orderedProduct_zero,phi_zero,psi_zero]
  | succ k ih =>
    rw [orderedProduct_succ,← Matrix.mulVec_mulVec,← ih]
    funext i
    fin_cases i
    · simp [continuationMatrix,Matrix.mulVec,Matrix.vecHead,Matrix.vecTail,phi_succ]
    · simp [continuationMatrix,Matrix.mulVec,Matrix.vecHead,Matrix.vecTail,phi_succ,psi_succ]
      ring
end
end krylov.Envelope
