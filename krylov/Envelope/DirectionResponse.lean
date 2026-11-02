import krylov.Envelope.FrozenResponse

set_option autoImplicit false
/-!
Article: main_krylov, apB:lem:mu(b), genuine frozen direction impulse formula.
Use: unroll the actual measured frozen direction and displacement steps
into true propagated gradient injections, for the explicit real tilt and
its absorbed-scenario and last-budget identities.
Source: genuine two-memory ordered physical transfer and actual finite
affine variation of constants, reusing the existing continuation calculus.
-/

namespace krylov.Envelope
noncomputable section
open Polynomial Matrix krylov.Reference krylov.Realization chebyshev1
open scoped BigOperators
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The actual second memory readout is exactly the true measured continuation direction polynomial.
Use: The actual second memory readout is exactly the true measured continuation direction polynomial.
Article: main_krylov, apB:lem:mu(b), genuine frozen direction impulse formula.
Proof: Read the genuine second row of the actual chronological polynomial transfer identity. -/
theorem continuation_direction_readout (α β : ℕ → ℝ) (j k : ℕ) :
    (∑ i : Fin 2, ∑ l : Fin 2, C (![0,1] i)*
      orderedProduct (fun t => continuationMatrix α β (j+t)) k i l*C (![1,-1] l))=psi α β j k := by
  have h := congrFun (continuation_matrix α β j k) 1
  simp only [Fin.sum_univ_two,Matrix.cons_val_zero,Matrix.cons_val_one,
    C_0,C_1,C_neg,one_mul,zero_mul,mul_one,mul_neg,zero_add] at ⊢
  simpa [Matrix.mulVec,Matrix.vecHead,Matrix.vecTail] using h.symm

/-- A true physical gradient impulse has exactly the actual continuation-direction polynomial response in the genuine frozen direction.
Use: A true physical gradient impulse has exactly the actual continuation-direction polynomial response in the genuine frozen direction.
Article: main_krylov, apB:lem:mu(b), genuine frozen direction impulse formula.
Proof: Reuse the proved real polynomial-memory scalar readout with the true second-memory output coordinate. -/
theorem physical_direction_continuation (Q : E →L[ℝ] E) (α β : ℕ → ℝ) (j k : ℕ) (v : E) :
    (orderedProduct (fun i => polynomialMemoryMap Q.toLinearMap (continuationMatrix α β (j+i))) k ![v,-v]) 1=
      (aeval Q.toLinearMap (psi α β j k)) v := by
  -- Use the genuine signed physical gradient impulse and actual second-memory readout.
  have hinput : (![v,-v] : Fin 2 → E)=fun i => (![1,-1] : Fin 2 → ℝ) i • v := by
    funext i
    fin_cases i <;> simp
  have h := memoryReadout_polynomialMemoryMap Q.toLinearMap
    (orderedProduct (fun t => continuationMatrix α β (j+t)) k) ![0,1] ![1,-1] v
  rw [continuation_direction_readout] at h
  rw [polynomialMemoryMap_ordered,hinput]
  simpa [memoryReadout,Fin.sum_univ_two] using h

/-- The actual measured frozen direction is exactly the true finite sum of genuine direction-polynomial injection responses.
Use: The actual measured frozen direction is exactly the true finite sum of genuine direction-polynomial injection responses.
Article: main_krylov, apB:lem:mu(b), genuine frozen direction impulse formula.
Proof: Unroll the real finite affine executor and identify each actual second-memory physical impulse response. -/
theorem frozen_direction_formula (Q : E →L[ℝ] E) (α β : ℕ → ℝ) (ζ : ℕ → E) (m : ℕ) :
    frozenResponse Q α β ζ m 1=∑ j∈Finset.range m,
      (aeval Q.toLinearMap (psi α β (j+1) (m-(j+1)))) (ζ (j+1)) := by
  -- Unroll the genuine physical executor before substituting the true continuation-direction impulse polynomials.
  unfold frozenResponse
  rw [affineRun_unroll]
  have hz : (orderedProduct (fun i => polynomialMemoryMap Q.toLinearMap (continuationMatrix α β i)) m) 0=0 := map_zero _
  rw [hz,zero_add]
  simp only [Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro j _
  exact physical_direction_continuation Q α β (j+1) (m-(j+1)) (ζ (j+1))

/-- Every actual frozen displacement increment equals its true line length times the genuine frozen direction.
Use: Every actual frozen displacement increment equals its true line length times the genuine frozen direction.
Article: main_krylov, apB:lem:mu(b), genuine frozen direction impulse formula.
Proof: Take the last real term of the actual finite displacement sum. -/
theorem frozen_displacement_step (Q : E →L[ℝ] E) (α β : ℕ → ℝ) (ζ : ℕ → E) (k : ℕ) :
    frozenDisplacement Q α β ζ (k+1)-frozenDisplacement Q α β ζ k=α k • frozenResponse Q α β ζ k 1 := by
  rw [frozenDisplacement,frozenDisplacement,Finset.sum_range_succ,add_sub_cancel_left]
end
end krylov.Envelope
