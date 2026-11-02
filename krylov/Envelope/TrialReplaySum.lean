import krylov.Envelope.TrialReferenceSums
set_option autoImplicit false
/-!
Article: main_krylov, thm:I, exact finite direction-image replay sum.
Use: unroll the actual one-step first-jet recurrence into the original signed
later-trial product, including every exact-trial zero factor.
Source: finite scalar recurrence induction and the existing original
chronological trialTailFactor definition.
-/

namespace krylov.Envelope
noncomputable section
open scoped BigOperators
variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- Appending one actual later trial multiplies every older signed tail
factor by precisely its negative relative correction.
Use: the source direction-basis replay products share the existing amplitudes.
Article: main_krylov, thm:I.
Proof: append the true upper endpoint to the finite interval product and
increment its chronological sign exponent. -/
theorem trialTailFactor_succ (tau rho : ℕ → ℝ) (k l : ℕ) (hl : l<k) :
    trialTailFactor tau rho (k+1) l= -(rho k/tau k)*trialTailFactor tau rho k l := by
  rw [trialTailFactor,trialTailFactor,Finset.prod_Ico_succ_top (by omega),
    show k+1-1-l=(k-1-l)+1 by omega,pow_succ]
  ring

/-- The genuine finite replay recurrence has exactly the printed signed
later-correction-product response at every actual bounded horizon.
Use: the actual direction-basis terminal derivative can be normalized directly
into the original XRFC amplitude sum, with no inverse oblique flags.
Article: main_krylov, thm:I.
Proof: the true initial error vanishes. Each actual next recursion subtracts
the preceding response times the negative newest relative correction;
the chronological finite-product recurrence and finite sum append exactly
the newest physical increment response. -/
theorem trial_replay_response_sum (tau rho : ℕ → ℝ) (D J : ℕ → V) (N : ℕ)
    (hJ0 : J 0=0)
    (hJ : ∀ j,j+1<N → J (j+1)=(rho j/tau (j+1)) • (D j-J j))
    (k : ℕ) (hk : k<N) :
    rho k • (D k-J k)=
      ∑ l∈Finset.range (k+1),trialTailFactor tau rho (k+1) l • (rho l • D l) := by
  induction k with
  | zero =>
    simp [hJ0,trialTailFactor]
  | succ k ih =>
    have he : rho (k+1) • (D (k+1)-J (k+1))=
        -(rho (k+1)/tau (k+1)) • (rho k • (D k-J k))+rho (k+1) • D (k+1) := by
      rw [hJ k hk]
      module
    rw [he,ih (by omega),Finset.smul_sum]
    rw [Finset.sum_range_succ (f := fun l => trialTailFactor tau rho (k+1+1) l • (rho l • D l)) (k+1)]
    have hp : (∑ x∈Finset.range (k+1),-(rho (k+1)/tau (k+1)) •
        (trialTailFactor tau rho (k+1) x • (rho x • D x)))=
        ∑ x∈Finset.range (k+1),trialTailFactor tau rho (k+1+1) x • (rho x • D x) := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [trialTailFactor_succ tau rho (k+1) x (Finset.mem_range.mp hx),smul_smul]
    rw [hp]
    congr 1
    simp only [trialTailFactor,Nat.add_sub_cancel,Nat.sub_self,pow_zero,
      Finset.Ico_self,Finset.prod_empty,one_mul,one_smul]

end
end krylov.Envelope
