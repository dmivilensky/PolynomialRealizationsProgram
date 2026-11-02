import krylov.Envelope.FrozenResponse
import krylov.Methods.StaticTermination

/-!
Article: main_krylov, apB:lem:filtration and apB:eq:tilt, actual frozen displacements.
Use: construct the true displacement continuation chi without polynomial
division by a nonunit variable, and prove the exact physical displacement
injection formula from the actual frozen executor.
Source: mathlib Polynomial.divX and X_mul_divX_add, the genuine normalized
continuation and true frozen gradient identity; reuse positive_operator_injective.
-/

namespace krylov.Envelope
noncomputable section
open Polynomial Matrix krylov.Reference krylov.Methods
open scoped BigOperators
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The genuine polynomial displacement response of a frozen gradient injection.
Use: The genuine polynomial displacement response of a frozen gradient injection.
Article: main_krylov, apB:lem:filtration and apB:eq:tilt, actual frozen displacements.
Proof: Divide the zero-constant polynomial phi-minus-one by X using actual polynomial divX. -/
def chi (α β : ℕ → ℝ) (j k : ℕ) : ℝ[X] := (phi α β j k-1).divX

/-- The true continuation equals one plus X times its genuine displacement response.
Use: The true continuation equals one plus X times its genuine displacement response.
Article: main_krylov, apB:lem:filtration and apB:eq:tilt, actual frozen displacements.
Proof: Normalization at zero makes the actual constant term vanish in the proved divX identity. -/
theorem phi_eq_one_add_X_chi (α β : ℕ → ℝ) (j k : ℕ) :
    phi α β j k=1+X*chi α β j k := by
  have hz : (phi α β j k-1).coeff 0=0 := by
    rw [coeff_zero_eq_eval_zero,eval_sub,phi_at_zero,eval_one,sub_self]
  have he := X_mul_divX_add (phi α β j k-1)
  rw [hz,C_0,add_zero] at he
  dsimp only [chi]
  rw [he]
  ring

/-- The actual empty displacement response vanishes.
Use: The actual empty displacement response vanishes.
Article: main_krylov, apB:lem:filtration and apB:eq:tilt, actual frozen displacements.
Proof: Its true continuation is one. -/
theorem chi_zero (α β : ℕ → ℝ) (j : ℕ) : chi α β j 0=0 := by simp [chi,phi_zero]

/-- The genuine displacement polynomial advances by the actual measured line length times the true direction response.
Use: The genuine displacement polynomial advances by the actual measured line length times the true direction response.
Article: main_krylov, apB:lem:filtration and apB:eq:tilt, actual frozen displacements.
Proof: Cancel the genuine nonzero polynomial X in the two actual normalized continuation recurrences. -/
theorem chi_succ (α β : ℕ → ℝ) (j k : ℕ) :
    chi α β j (k+1)=chi α β j k+C (α (j+k))*psi α β j k := by
  apply mul_left_cancel₀ (X_ne_zero : (X : ℝ[X])≠0)
  have hnext := phi_eq_one_add_X_chi α β j (k+1)
  have hprev := phi_eq_one_add_X_chi α β j k
  rw [phi_succ,hprev] at hnext
  linear_combination -hnext

/-- Every actual continuation impulse is its original physical injection plus the true operator applied to the genuine displacement response.
Use: Every actual continuation impulse is its original physical injection plus the true operator applied to the genuine displacement response.
Article: main_krylov, apB:lem:filtration and apB:eq:tilt, actual frozen displacements.
Proof: Evaluate the proved polynomial identity at the actual physical operator. -/
theorem continuation_physical_split (Q : E →L[ℝ] E) (α β : ℕ → ℝ) (j k : ℕ) (v : E) :
    (aeval Q.toLinearMap (phi α β j k)) v=v+Q ((aeval Q.toLinearMap (chi α β j k)) v) := by
  rw [phi_eq_one_add_X_chi]
  simp only [map_add,map_one,map_mul,aeval_X,LinearMap.add_apply,Module.End.one_apply,Module.End.mul_apply]
  rfl

/-- The true accumulated physical frozen displacement equals the sum of all genuine displacement-polynomial injection responses.
Use: The true accumulated physical frozen displacement equals the sum of all genuine displacement-polynomial injection responses.
Article: main_krylov, apB:lem:filtration and apB:eq:tilt, actual frozen displacements.
Proof: The actual frozen gradient has both its genuine displacement identity and its actual continuation impulse sum. Separate each true impulse and cancel the real positive physical operator using the already proved injectivity theorem. -/
theorem frozen_displacement_formula (Q : E →L[ℝ] E)
    (hpos : ∀ v : E, v≠0 → 0 < inner ℝ v (Q v))
    (α β : ℕ → ℝ) (ζ : ℕ → E) (m : ℕ) :
    frozenDisplacement Q α β ζ m=∑ j∈Finset.range m,
      (aeval Q.toLinearMap (chi α β (j+1) (m-(j+1)))) (ζ (j+1)) := by
  -- Compare two identities of the actual frozen executor before cancelling its genuine positive query operator.
  apply positive_operator_injective Q hpos
  have hG := frozen_gradient_displacement Q α β ζ m
  rw [frozen_response_formula] at hG
  simp_rw [continuation_physical_split] at hG
  rw [Finset.sum_add_distrib,← map_sum] at hG
  exact add_left_cancel (by convert hG.symm using 1;abel)
end
end krylov.Envelope
