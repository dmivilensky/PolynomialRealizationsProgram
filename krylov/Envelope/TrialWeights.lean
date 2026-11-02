import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic
set_option autoImplicit false
/-!
Article: main_krylov, thm:E1, genuine bidiagonal virtual back substitution.
Use: derive the printed chronological virtual-correction weight products from true reference trial and missed-step coefficients.
Source: exact finite back substitution in the actual chronological bidiagonal stored-step basis.
-/

namespace krylov.Envelope
noncomputable section
open scoped BigOperators

/-- The genuine finite chronological back-substitution weights for relative virtual corrections.
Use: The genuine finite chronological back-substitution weights for relative virtual corrections.
Article: main_krylov, thm:E1, genuine bidiagonal virtual back substitution.
Proof: Append the newest relative correction and multiply each genuine older weight by its negative. -/
def trialWeights (e : ℕ → ℝ) : (k : ℕ) → Fin k → ℝ
  | 0 => Fin.elim0
  | k+1 => Fin.snoc (fun i => -e k*trialWeights e k i) (e k)

/-- The genuine newest back-substitution coefficient equals the actual last relative virtual correction.
Use: The genuine newest back-substitution coefficient equals the actual last relative virtual correction.
Article: main_krylov, thm:E1, genuine bidiagonal virtual back substitution.
Proof: Read the actual final coordinate of the finite back substitution. -/
theorem trialWeights_last (e : ℕ → ℝ) (k : ℕ) : trialWeights e (k+1) (Fin.last k)=e k := by
  simp [trialWeights]

/-- Every genuine older back-substitution coefficient acquires the negative actual newest relative correction.
Use: Every genuine older back-substitution coefficient acquires the negative actual newest relative correction.
Article: main_krylov, thm:E1, genuine bidiagonal virtual back substitution.
Proof: Read the original retained coordinate of the true finite back substitution. -/
theorem trialWeights_castSucc (e : ℕ → ℝ) (k : ℕ) (i : Fin k) :
    trialWeights e (k+1) i.castSucc= -e k*trialWeights e k i := by
  simp [trialWeights]

/-- The actual chronological back-substitution weights equal the printed signed product of genuine relative virtual corrections.
Use: The actual chronological back-substitution weights equal the printed signed product of genuine relative virtual corrections.
Article: main_krylov, thm:E1, genuine bidiagonal virtual back substitution.
Proof: Induct through the real appended coefficient and extend the genuine chronological interval product. -/
theorem trialWeights_product (e : ℕ → ℝ) (k : ℕ) (i : Fin k) :
    trialWeights e k i=(-1:ℝ)^(k-1-i.val)*∏ j∈Finset.Ico i.val k,e j := by
  -- Extend the actual chronological product by exactly the newest genuine relative correction.
  induction k with
  | zero => exact Fin.elim0 i
  | succ k ih =>
    refine Fin.lastCases ?_ (fun i => ?_) i
    · simp [trialWeights_last]
    · rw [trialWeights_castSucc,ih]
      have hi : i.val≤k := i.isLt.le
      simp only [Fin.val_castSucc]
      rw [Finset.prod_Ico_succ_top (f := e) hi]
      have he : k+1-1-i.val=(k-1-i.val)+1 := by omega
      rw [he,pow_succ]
      ring

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- The actual bidiagonal reference steps synthesize the genuine newest missed direction component with the true back-substitution weights.
Use: The actual bidiagonal reference steps synthesize the genuine newest missed direction component with the true back-substitution weights.
Article: main_krylov, thm:E1, genuine bidiagonal virtual back substitution.
Proof: The real preceding missed component cancels against the actual older weighted synthesis; only the genuine newest direction remains. -/
theorem trialWeights_bidiagonal_sum (tau rho : ℕ → ℝ) (ht : ∀ k,tau k≠0)
    (d : ℕ → E) (s : ℕ → E)
    (hs0 : s 0=tau 0 • d 0)
    (hs : ∀ k,s (k+1)=rho k • d k+tau (k+1) • d (k+1)) (k : ℕ) :
    ∑ i : Fin (k+1),trialWeights (fun j => rho j/tau j) (k+1) i • s i.val=rho k • d k := by
  induction k with
  | zero =>
    rw [Fin.sum_univ_one]
    change trialWeights (fun j => rho j/tau j) 1 (Fin.last 0) • s 0=rho 0 • d 0
    rw [trialWeights_last,hs0,smul_smul,div_mul_cancel₀ _ (ht 0)]
  | succ k ih =>
    -- Cancel the genuine preceding missed component before simplifying the actual newest nonzero trial.
    rw [Fin.sum_univ_castSucc]
    simp only [trialWeights_castSucc,Fin.val_castSucc,trialWeights_last,Fin.val_last,mul_smul,← Finset.smul_sum,ih,hs]
    simp only [smul_add,smul_smul,div_mul_cancel₀ _ (ht (k+1))]
    module
end
end krylov.Envelope
