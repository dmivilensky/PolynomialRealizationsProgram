import krylov.Envelope.ContinuationSecondOrder
import chebyshev1.TwoTerm.Basic

set_option autoImplicit false
/-!
Article: main_krylov, prop:phi(a), actual continuation and two-term suffix transfer.
Use: identify the genuine measured gradient/direction continuation with the true causal two-memory transfer started at a real constant suffix state.
Source: the proved actual scalar continuation recurrence and the existing genuine two-term realization matrix entries, including the true causal time-zero branch.
-/

namespace krylov.Envelope
noncomputable section
open Polynomial Matrix chebyshev1
open scoped BigOperators

/-- The actual continuation and its true preceding residual are exactly the genuine constant-state two-term suffix transfer under the real measured coefficients.
Use: The actual continuation and its true preceding residual are exactly the genuine constant-state two-term suffix transfer under the real measured coefficients.
Article: main_krylov, prop:phi(a), actual continuation and two-term suffix transfer.
Proof: Match the true empty and one-step states, including causal time zero, then use the genuine scalar three-term recurrence at every actual later update. -/
theorem phi_twoTerm_suffix (α β : ℕ → ℝ) (S : TwoTerm) (j k : ℕ)
    (ha : ∀ i<k,α (j+i)≠0)
    (hγ : ∀ i<k,S.gamma (j+i)=α (j+i))
    (hfix : ∀ i<k,S.a (j+i)+S.b (j+i)=1)
    (hb : ∀ i<k,0 < i → S.b (j+i)= -α (j+i)*β (j+i-1)/α (j+i-1)) (lam : ℝ) :
    orderedProduct (fun i => S.realization.scalarStep (j+i) lam) k *ᵥ ![1,1]=
      ![(phi α β j k).eval lam,if k=0 then 1 else (phi α β j (k-1)).eval lam] := by
  -- Preserve both genuine consecutive residual coordinates while following the real chronological suffix product.
  induction k using Nat.twoStepInduction with
  | zero => simp only [orderedProduct_zero,Matrix.one_mulVec,phi_zero,eval_one,ite_true]
  | one =>
    rw [orderedProduct_succ,orderedProduct_zero,Matrix.mul_one]
    by_cases hj : j=0
    · subst j
      rw [Nat.zero_add,S.scalarStep_zero,hγ 0 (by omega),phi_one]
      ext i
      fin_cases i <;> simp [Matrix.mulVec,dotProduct,Fin.sum_univ_two,phi_zero]
    · obtain ⟨p,hp⟩ : ∃ p,j=p+1 := ⟨j-1,by omega⟩
      rw [hp] at hγ hfix ⊢
      rw [S.scalarStep_succ,hγ 0 (by omega),phi_one]
      have hsum := hfix 0 (by omega)
      simp only [Nat.add_zero] at hsum
      ext i
      fin_cases i <;> simp [Matrix.mulVec,dotProduct,Fin.sum_univ_two,phi_zero]
      linarith
  | more k _ ih =>
    -- The actual later row uses exactly the genuine measured momentum; no gradient trajectory or determinant response is assumed.
    have ih' := ih (fun i hi => ha i (by omega)) (fun i hi => hγ i (by omega))
      (fun i hi => hfix i (by omega)) (fun i hi hip => hb i (by omega) hip)
    rw [show k+2=(k+1)+1 by omega,orderedProduct_succ,← Matrix.mulVec_mulVec,ih']
    rw [show j+(k+1)=(j+k)+1 by omega,S.scalarStep_succ]
    have hgamma : S.gamma (j+k+1)=α (j+k+1) := by
      simpa only [Nat.add_assoc] using hγ (k+1) (by omega)
    rw [hgamma]
    have hsum : S.a (j+k+1)+S.b (j+k+1)=1 := by
      simpa only [Nat.add_assoc] using hfix (k+1) (by omega)
    have hbs : S.b (j+k+1)= -(α (j+k+1)*β (j+k)/α (j+k)) := by
      have hh := hb (k+1) (by omega) (by omega)
      rw [show j+(k+1)=j+k+1 by omega,Nat.add_sub_cancel] at hh
      simpa only [neg_mul,neg_div] using hh
    -- The proved actual continuation recurrence identifies the real newest transfer row.
    have hp := congrArg (fun p : ℝ[X] => p.eval lam) (phi_add_two α β j k (ha k (by omega)))
    simp only [eval_sub,eval_mul,eval_add,eval_one,eval_C,eval_X] at hp
    simp only [show ¬k+1=0 by omega,ite_false,Nat.add_sub_cancel] at ih' ⊢
    ext i
    fin_cases i
    · rw [hbs] at hsum
      have hab : S.a (j+k+1)=1+α (j+k+1)*β (j+k)/α (j+k) := by
        linarith
      rw [hab,hbs]
      simp [Matrix.mulVec,dotProduct,Fin.sum_univ_two]
      linear_combination -hp
    · simp [Matrix.mulVec,dotProduct,Fin.sum_univ_two]
end
end krylov.Envelope
