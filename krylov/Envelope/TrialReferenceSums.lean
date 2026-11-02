import krylov.Envelope.TrialWeightPrefix
set_option autoImplicit false
/-!
Article: main_krylov, thm:E1, genuine weighted and ordinary virtual reference prefixes.
Use: derive exact original trial-displacement prefix differences and their zero total from the actual chronological bidiagonal reference basis.
Source: finite real bidiagonal telescoping and the proved genuine back-substitution prefix formula.
-/

namespace krylov.Envelope
noncomputable section
open scoped BigOperators
variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- The genuine signed product of actual later relative virtual corrections after the chosen chronological step.
Use: The genuine signed product of actual later relative virtual corrections after the chosen chronological step.
Article: main_krylov, thm:E1, genuine weighted and ordinary virtual reference prefixes.
Proof: Multiply exactly the true later correction ratios and their chronological sign. -/
def trialTailFactor (tau rho : ℕ → ℝ) (k l : ℕ) : ℝ :=
  (-1:ℝ)^(k-1-l)*∏ j∈Finset.Ico (l+1) k,rho j/tau j

/-- The true evaluated bidiagonal reference prefix differs from its genuine CG prefix by exactly its negative actual last missed direction.
Use: The true evaluated bidiagonal reference prefix differs from its genuine CG prefix by exactly its negative actual last missed direction.
Article: main_krylov, thm:E1, genuine weighted and ordinary virtual reference prefixes.
Proof: Telescope the original adjacent missed components in the actual chronological physical step sums. -/
theorem trial_bidiagonal_prefix_difference (alpha tau : ℕ → ℝ) (d s : ℕ → E) (l : ℕ)
    (hs0 : s 0=tau 0 • d 0)
    (hs : ∀ j<l,s (j+1)=(alpha j-tau j) • d j+tau (j+1) • d (j+1)) :
    (∑ i∈Finset.range (l+1),s i)-(∑ i∈Finset.range (l+1),alpha i • d i)=
      -(alpha l-tau l) • d l := by
  -- Each actual preceding missed component cancels before the genuine newest trial difference is collected.
  induction l with
  | zero =>
    simp only [Nat.zero_add,Finset.sum_range_one,hs0]
    module
  | succ l ih =>
    rw [Finset.sum_range_succ (f := s) (l+1),Finset.sum_range_succ (f := fun i => alpha i • d i) (l+1)]
    have he : (∑ i∈Finset.range (l+1),s i)+s (l+1)-
        ((∑ i∈Finset.range (l+1),alpha i • d i)+alpha (l+1) • d (l+1))=
        ((∑ i∈Finset.range (l+1),s i)-(∑ i∈Finset.range (l+1),alpha i • d i))+
        s (l+1)-alpha (l+1) • d (l+1) := by abel
    rw [he,ih (fun j hj => hs j (by omega)),hs l (by omega)]
    module

/-- The genuine weighted reference prefix differs from its original CG prefix by the printed later-product-minus-one times its actual last missed direction.
Use: The genuine weighted reference prefix differs from its original CG prefix by the printed later-product-minus-one times its actual last missed direction.
Article: main_krylov, thm:E1, genuine weighted and ordinary virtual reference prefixes.
Proof: Add the true ordinary prefix difference and the exact genuine weighted back-substitution prefix synthesis. -/
theorem trial_weighted_prefix_difference (alpha tau : ℕ → ℝ) (d s : ℕ → E) (k l : ℕ)
    (hl : l<k) (ht : ∀ j<k,tau j≠0) (hs0 : s 0=tau 0 • d 0)
    (hs : ∀ j,j+1<k → s (j+1)=(alpha j-tau j) • d j+tau (j+1) • d (j+1)) :
    (∑ i∈Finset.range (l+1),((1+trialWeightAt (fun j => (alpha j-tau j)/tau j) k i) • s i-alpha i • d i))=
      (trialTailFactor tau (fun j => alpha j-tau j) k l-1) • ((alpha l-tau l) • d l) := by
  -- Combine the true ordinary and actual weighted physical prefix identities on the original finite horizon.
  have hb := trial_bidiagonal_prefix_difference alpha tau d s l hs0 (fun j hj => hs j (by omega))
  have hw := trialWeights_prefix_sum tau (fun j => alpha j-tau j) d s k l hl ht hs0 hs
  simp only [Finset.sum_sub_distrib,add_smul,one_smul,Finset.sum_add_distrib]
  rw [show (∑ i∈Finset.range (l+1),s i)+(∑ i∈Finset.range (l+1),trialWeightAt (fun j => (alpha j-tau j)/tau j) k i • s i)-
      (∑ i∈Finset.range (l+1),alpha i • d i)=
      ((∑ i∈Finset.range (l+1),s i)-(∑ i∈Finset.range (l+1),alpha i • d i))+
      (∑ i∈Finset.range (l+1),trialWeightAt (fun j => (alpha j-tau j)/tau j) k i • s i) by abel]
  rw [hb,hw]
  dsimp only [trialTailFactor]
  module

/-- The full genuine weighted bidiagonal reference displacement equals its original complete CG displacement.
Use: The full genuine weighted bidiagonal reference displacement equals its original complete CG displacement.
Article: main_krylov, thm:E1, genuine weighted and ordinary virtual reference prefixes.
Proof: At the actual last chronological site the later product is empty and equals one. -/
theorem trial_weighted_total_difference (alpha tau : ℕ → ℝ) (d s : ℕ → E) (k : ℕ)
    (ht : ∀ j<k,tau j≠0) (hs0 : s 0=tau 0 • d 0)
    (hs : ∀ j,j+1<k → s (j+1)=(alpha j-tau j) • d j+tau (j+1) • d (j+1)) :
    ∑ i∈Finset.range k,((1+trialWeightAt (fun j => (alpha j-tau j)/tau j) k i) • s i-alpha i • d i)=0 := by
  cases k with
  | zero => simp
  | succ k =>
    rw [trial_weighted_prefix_difference alpha tau d s (k+1) k (by omega) ht hs0 hs]
    simp [trialTailFactor]
end
end krylov.Envelope
