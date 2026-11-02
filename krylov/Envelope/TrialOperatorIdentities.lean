import krylov.Envelope.OperatorSummation
import krylov.Envelope.TrialReferenceSums
set_option autoImplicit false
/-!
Article: main_krylov, thm:E1, exact original virtual trial operator formulas.
Use: derive printed output and effective-injection trial factors by actual operator summation by parts on the genuine bidiagonal reference steps.
Source: true chronological operator tail-prefix identities and proved ordinary and weighted physical reference prefix sums.
-/

namespace krylov.Envelope
noncomputable section
open scoped BigOperators
variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- The actual weighted output-operator tail sum equals the printed signed later-product increment action on each genuine missed reference direction.
Use: The actual weighted output-operator tail sum equals the printed signed later-product increment action on each genuine missed reference direction.
Article: main_krylov, thm:E1, exact original virtual trial operator formulas.
Proof: Exchange true physical tails with actual weighted step prefixes, then insert genuine finite back substitution. -/
theorem trial_output_increment_sum (alpha tau : ℕ → ℝ) (d s : ℕ → E) (D : ℕ → E →ₗ[ℝ] E) (N : ℕ)
    (ht : ∀ j<N,tau j≠0) (hs0 : s 0=tau 0 • d 0)
    (hs : ∀ j,j+1<N → s (j+1)=(alpha j-tau j) • d j+tau (j+1) • d (j+1)) :
    (∑ i∈Finset.range N,(∑ l∈Finset.Ico i N,D l)
      (trialWeightAt (fun j => (alpha j-tau j)/tau j) N i • s i))=
    ∑ l∈Finset.range N,trialTailFactor tau (fun j => alpha j-tau j) N l • D l ((alpha l-tau l) • d l) := by
  rw [operator_tail_prefix_sum]
  apply Finset.sum_congr rfl
  intro l hl
  rw [trialWeights_prefix_sum tau (fun j => alpha j-tau j) d s N l (Finset.mem_range.mp hl) ht hs0 hs,map_smul]
  rfl

/-- The actual difference of effective and ordinary cumulative reference injections equals the printed one-minus-later-product increment sum.
Use: The actual difference of effective and ordinary cumulative reference injections equals the printed one-minus-later-product increment sum.
Article: main_krylov, thm:E1, exact original virtual trial operator formulas.
Proof: Use the genuine zero total weighted reference displacement and exact physical operator summation by parts. -/
theorem trial_injection_increment_sum (alpha tau : ℕ → ℝ) (d s : ℕ → E) (D : ℕ → E →ₗ[ℝ] E) (N : ℕ)
    (ht : ∀ j<N,tau j≠0) (hs0 : s 0=tau 0 • d 0)
    (hs : ∀ j,j+1<N → s (j+1)=(alpha j-tau j) • d j+tau (j+1) • d (j+1)) :
    (∑ i∈Finset.range N,(∑ l∈Finset.range i,D l)
      ((1+trialWeightAt (fun j => (alpha j-tau j)/tau j) N i) • s i-alpha i • d i))=
    ∑ l∈Finset.range N,(1-trialTailFactor tau (fun j => alpha j-tau j) N l) • D l ((alpha l-tau l) • d l) := by
  rw [operator_cumulative_by_parts D _ N (trial_weighted_total_difference alpha tau d s N ht hs0 hs)]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro l hl
  rw [trial_weighted_prefix_difference alpha tau d s N l (Finset.mem_range.mp hl) ht hs0 hs,map_smul]
  module

/-- The genuine final effective-injection trial increment vanishes and may be removed from the original printed finite sum.
Use: The genuine final effective-injection trial increment vanishes and may be removed from the original printed finite sum.
Article: main_krylov, thm:E1, exact original virtual trial operator formulas.
Proof: The actual last later-correction product is empty and equals one. -/
theorem trial_injection_last_zero (tau rho : ℕ → ℝ) (d : ℕ → E) (D : ℕ → E →ₗ[ℝ] E) (N : ℕ) :
    (∑ l∈Finset.range N,(1-trialTailFactor tau rho N l) • D l (rho l • d l))=
      ∑ l∈Finset.range (N-1),(1-trialTailFactor tau rho N l) • D l (rho l • d l) := by
  cases N with
  | zero => simp
  | succ N => simp [Finset.sum_range_succ,trialTailFactor]
end
end krylov.Envelope
