import krylov.Envelope.TrialWeights
set_option autoImplicit false
/-!
Article: main_krylov, thm:E1, true finite virtual back-substitution prefixes.
Use: prove the exact printed partial weighted-step sums using only genuine finite nonzero trials and the actual bounded bidiagonal reference identities.
Source: genuine finite back substitution, chronological interval products and exact cancellation of the preceding missed component.
-/

namespace krylov.Envelope
noncomputable section
open scoped BigOperators

/-- The actual chronological back-substitution weight with zero extension outside its genuine finite horizon.
Use: The actual chronological back-substitution weight with zero extension outside its genuine finite horizon.
Article: main_krylov, thm:E1, true finite virtual back-substitution prefixes.
Proof: Read the actual finite coefficient only at a genuinely present chronological index. -/
def trialWeightAt (e : ℕ → ℝ) (k i : ℕ) : ℝ := if hi : i<k then trialWeights e k ⟨i,hi⟩ else 0

/-- Every genuine finite chronological index reads exactly its actual back-substitution coefficient.
Use: Every genuine finite chronological index reads exactly its actual back-substitution coefficient.
Article: main_krylov, thm:E1, true finite virtual back-substitution prefixes.
Proof: The original finite index satisfies its true horizon test. -/
theorem trialWeightAt_used (e : ℕ → ℝ) (k : ℕ) (i : Fin k) :
    trialWeightAt e k i.val=trialWeights e k i := by simp [trialWeightAt,i.isLt]

/-- Every true older chronological weight gains the negative actual appended relative correction.
Use: Every true older chronological weight gains the negative actual appended relative correction.
Article: main_krylov, thm:E1, true finite virtual back-substitution prefixes.
Proof: Transfer the real retained-coordinate back-substitution identity through its genuine horizon tests. -/
theorem trialWeightAt_succ (e : ℕ → ℝ) (k i : ℕ) (hi : i<k) :
    trialWeightAt e (k+1) i= -e k*trialWeightAt e k i := by
  have h := trialWeights_castSucc e k ⟨i,hi⟩
  simpa [trialWeightAt,hi,show i<k+1 by omega] using h

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- The genuine finite bidiagonal reference synthesis recovers its actual newest missed component using only real bounded trial domains.
Use: The genuine finite bidiagonal reference synthesis recovers its actual newest missed component using only real bounded trial domains.
Article: main_krylov, thm:E1, true finite virtual back-substitution prefixes.
Proof: Induct through the finite actual reference prefix and cancel the genuine preceding missed component. -/
theorem trialWeights_bidiagonal_bounded (tau rho : ℕ → ℝ) (d s : ℕ → E) (k : ℕ)
    (ht : ∀ j≤k,tau j≠0) (hs0 : s 0=tau 0 • d 0)
    (hs : ∀ j<k,s (j+1)=rho j • d j+tau (j+1) • d (j+1)) :
    ∑ i : Fin (k+1),trialWeights (fun j => rho j/tau j) (k+1) i • s i.val=rho k • d k := by
  -- Use only genuine trial domains and bidiagonal identities inside the actual bounded prefix.
  induction k with
  | zero =>
    rw [Fin.sum_univ_one]
    change trialWeights (fun j => rho j/tau j) 1 (Fin.last 0) • s 0=rho 0 • d 0
    rw [trialWeights_last,hs0,smul_smul,div_mul_cancel₀ _ (ht 0 le_rfl)]
  | succ k ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [trialWeights_castSucc,Fin.val_castSucc,trialWeights_last,Fin.val_last,mul_smul,← Finset.smul_sum]
    rw [ih (fun j hj => ht j (by omega)) (fun j hj => hs j (by omega)),hs k (by omega)]
    simp only [smul_add,smul_smul,div_mul_cancel₀ _ (ht (k+1) le_rfl)]
    module

/-- Every genuine chronological partial weighted reference-step sum equals the printed signed product times its actual final missed direction.
Use: Every genuine chronological partial weighted reference-step sum equals the printed signed product times its actual final missed direction.
Article: main_krylov, thm:E1, true finite virtual back-substitution prefixes.
Proof: The complete bounded prefix gives the initial sum; each later genuine relative correction scales that same earlier partial sum by its negative. -/
theorem trialWeights_prefix_sum (tau rho : ℕ → ℝ) (d s : ℕ → E) (k l : ℕ)
    (hl : l<k) (ht : ∀ j<k,tau j≠0) (hs0 : s 0=tau 0 • d 0)
    (hs : ∀ j,j+1<k → s (j+1)=rho j • d j+tau (j+1) • d (j+1)) :
    ∑ i∈Finset.range (l+1),trialWeightAt (fun j => rho j/tau j) k i • s i=
      ((-1:ℝ)^(k-1-l)*∏ j∈Finset.Ico (l+1) k,rho j/tau j) • (rho l • d l) := by
  -- Each later actual relative correction scales the same true earlier physical partial sum.
  induction k with
  | zero => omega
  | succ k ih =>
    by_cases he : l=k
    · subst l
      have hsum := trialWeights_bidiagonal_bounded tau rho d s k (fun j hj => ht j (by omega)) hs0
        (fun j hj => hs j (by omega))
      have heq : (∑ i : Fin (k+1),trialWeights (fun j => rho j/tau j) (k+1) i • s i.val)=
          ∑ i∈Finset.range (k+1),trialWeightAt (fun j => rho j/tau j) (k+1) i • s i := by
        rw [← Fin.sum_univ_eq_sum_range]
        apply Finset.sum_congr rfl
        intro i _
        rw [trialWeightAt_used]
      rw [← heq,hsum]
      simp
    · have hlk : l<k := by omega
      have hrec : (∑ i∈Finset.range (l+1),trialWeightAt (fun j => rho j/tau j) (k+1) i • s i)=
          (-(rho k/tau k)) • (∑ i∈Finset.range (l+1),trialWeightAt (fun j => rho j/tau j) k i • s i) := by
        rw [Finset.smul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        rw [trialWeightAt_succ _ _ _ (by have := Finset.mem_range.mp hi;omega),mul_smul]
      rw [hrec,ih hlk (fun j hj => ht j (by omega)) (fun j hj => hs j (by omega)),smul_smul]
      rw [Finset.prod_Ico_succ_top (by omega : l+1≤k) (fun j => rho j/tau j)]
      have he : k+1-1-l=(k-1-l)+1 := by omega
      rw [he,pow_succ]
      congr 1
      ring
end
end krylov.Envelope
