import krylov.Envelope.Continuation

/-!
Article: main_krylov, s3:def:phi and apB:lem:filtration, genuine frozen injection propagation.
Use: solve the actual physical frozen two-memory recurrence with arbitrary
additive gradient injections using exactly the previously proved transfer
calculus; identify every genuine impulse response with its source polynomial.
Source: existing affineRun_unroll, physical polynomial-memory evaluation and
the actual continuation transfer identity; no expansion is assumed.
-/

namespace krylov.Envelope
noncomputable section
open Polynomial Matrix krylov.Reference krylov.Realization chebyshev1
open scoped BigOperators
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The actual physical frozen gradient/direction run with independent genuine gradient injections.
Use: The actual physical frozen gradient/direction run with independent genuine gradient injections.
Article: main_krylov, s3:def:phi and apB:lem:filtration, genuine frozen injection propagation.
Proof: Use the existing physical affine executor with the true two-memory polynomial transition and signed gradient/direction impulse. -/
def frozenResponse (Q : E →L[ℝ] E) (α β : ℕ → ℝ) (ζ : ℕ → E) (k : ℕ) : Fin 2 → E :=
  affineRun (fun i => polynomialMemoryMap Q.toLinearMap (continuationMatrix α β i))
    (fun i => ![ζ (i+1),-ζ (i+1)]) 0 k


/-- The actual empty physical frozen response is zero.
Use: The actual empty physical frozen response is zero.
Article: main_krylov, s3:def:phi and apB:lem:filtration, genuine frozen injection propagation.
Proof: Use the actual affine initial state. -/
theorem frozenResponse_zero (Q : E →L[ℝ] E) (α β : ℕ → ℝ) (ζ : ℕ → E) :
    frozenResponse Q α β ζ 0=0 := rfl

/-- The actual physical frozen gradient has exactly the source gradient recurrence with its genuine new injection.
Use: The actual physical frozen gradient has exactly the source gradient recurrence with its genuine new injection.
Article: main_krylov, s3:def:phi and apB:lem:filtration, genuine frozen injection propagation.
Proof: Evaluate the true first row of its physical polynomial-memory transition. -/
theorem frozenResponse_gradient_succ (Q : E →L[ℝ] E) (α β : ℕ → ℝ) (ζ : ℕ → E) (k : ℕ) :
    frozenResponse Q α β ζ (k+1) 0=frozenResponse Q α β ζ k 0+
      α k • Q (frozenResponse Q α β ζ k 1)+ζ (k+1) := by
  change (polynomialMemoryMap Q.toLinearMap (continuationMatrix α β k) (frozenResponse Q α β ζ k)) 0+_=_
  simp [polynomialMemoryMap,continuationMatrix,Fin.sum_univ_two,aeval_C,aeval_X,map_mul,
    Algebra.algebraMap_eq_smul_one]

/-- The actual physical frozen direction has the source momentum recurrence.
Use: The actual physical frozen direction has the source momentum recurrence.
Article: main_krylov, s3:def:phi and apB:lem:filtration, genuine frozen injection propagation.
Proof: Evaluate the true second row and use the actual new gradient recurrence. -/
theorem frozenResponse_direction_succ (Q : E →L[ℝ] E) (α β : ℕ → ℝ) (ζ : ℕ → E) (k : ℕ) :
    frozenResponse Q α β ζ (k+1) 1= -frozenResponse Q α β ζ (k+1) 0+
      β k • frozenResponse Q α β ζ k 1 := by
  rw [frozenResponse_gradient_succ]
  change (polynomialMemoryMap Q.toLinearMap (continuationMatrix α β k) (frozenResponse Q α β ζ k)) 1+_=_
  simp [polynomialMemoryMap,continuationMatrix,Fin.sum_univ_two,aeval_C,aeval_X,map_mul,
    Algebra.algebraMap_eq_smul_one]
  module

/-- The actual accumulated physical frozen displacement.
Use: The actual accumulated physical frozen displacement.
Article: main_krylov, s3:def:phi and apB:lem:filtration, genuine frozen injection propagation.
Proof: Sum the real measured line lengths times the actual frozen directions. -/
def frozenDisplacement (Q : E →L[ℝ] E) (α β : ℕ → ℝ) (ζ : ℕ → E) (k : ℕ) : E :=
  ∑ i∈Finset.range k, α i • frozenResponse Q α β ζ i 1

/-- The genuine frozen gradient equals the true operator applied to the actual frozen displacement plus the actual accumulated injections.
Use: The genuine frozen gradient equals the true operator applied to the actual frozen displacement plus the actual accumulated injections.
Article: main_krylov, s3:def:phi and apB:lem:filtration, genuine frozen injection propagation.
Proof: Telescope the real gradient recurrence and its true line displacements. -/
theorem frozen_gradient_displacement (Q : E →L[ℝ] E) (α β : ℕ → ℝ) (ζ : ℕ → E) (k : ℕ) :
    frozenResponse Q α β ζ k 0=Q (frozenDisplacement Q α β ζ k)+∑ i∈Finset.range k, ζ (i+1) := by
  induction k with
  | zero => simp [frozenResponse_zero,frozenDisplacement]
  | succ k ih =>
    rw [frozenResponse_gradient_succ,frozenDisplacement,Finset.sum_range_succ,
      map_add,map_smul,Finset.sum_range_succ,ih]
    change _=Q (frozenDisplacement Q α β ζ k)+_+_
    abel

/-- The true polynomial readout of a frozen impulse is the actual continuation polynomial.
Use: The true polynomial readout of a frozen impulse is the actual continuation polynomial.
Article: main_krylov, s3:def:phi and apB:lem:filtration, genuine frozen injection propagation.
Proof: Contract the first row of the proved chronological polynomial state identity. -/
theorem continuation_readout (α β : ℕ → ℝ) (j k : ℕ) :
    (∑ i : Fin 2, ∑ l : Fin 2, C (![1,0] i)*
      orderedProduct (fun t => continuationMatrix α β (j+t)) k i l*C (![1,-1] l))=phi α β j k := by
  have h := congrFun (continuation_matrix α β j k) 0
  simp only [Fin.sum_univ_two,Matrix.cons_val_zero,Matrix.cons_val_one,
    C_0,C_1,C_neg,one_mul,zero_mul,mul_one,mul_neg,zero_add] at ⊢
  simpa [Matrix.mulVec,Matrix.vecHead,Matrix.vecTail] using h.symm

/-- Every real frozen impulse propagates by evaluation of the actual continuation polynomial at the true physical operator.
Use: Every real frozen impulse propagates by evaluation of the actual continuation polynomial at the true physical operator.
Article: main_krylov, s3:def:phi and apB:lem:filtration, genuine frozen injection propagation.
Proof: Reuse the existing algebra-homomorphic physical-memory transfer and scalar readout theorem. -/
theorem physical_continuation (Q : E →L[ℝ] E) (α β : ℕ → ℝ) (j k : ℕ) (v : E) :
    (orderedProduct (fun i => polynomialMemoryMap Q.toLinearMap (continuationMatrix α β (j+i))) k ![v,-v]) 0=
      (aeval Q.toLinearMap (phi α β j k)) v := by
  -- Use the same real physical impulse and real scalar input as in the existing transfer theorem.
  have hinput : (![v,-v] : Fin 2 → E)=fun i => (![1,-1] : Fin 2 → ℝ) i • v := by
    funext i
    fin_cases i <;> simp
  have h := memoryReadout_polynomialMemoryMap Q.toLinearMap
    (orderedProduct (fun t => continuationMatrix α β (j+t)) k) ![1,0] ![1,-1] v
  rw [continuation_readout] at h
  rw [polynomialMemoryMap_ordered,hinput]
  simpa [memoryReadout,Fin.sum_univ_two] using h

/-- The real frozen gradient is exactly the sum of all actual propagated gradient injections.
Use: The real frozen gradient is exactly the sum of all actual propagated gradient injections.
Article: main_krylov, s3:def:phi and apB:lem:filtration, genuine frozen injection propagation.
Proof: Apply the existing finite affine variation-of-constants theorem to the actual two-memory executor; identify each genuine physical impulse with its continuation polynomial. -/
theorem frozen_response_formula (Q : E →L[ℝ] E) (α β : ℕ → ℝ) (ζ : ℕ → E) (m : ℕ) :
    frozenResponse Q α β ζ m 0=∑ j∈Finset.range m,
      (aeval Q.toLinearMap (phi α β (j+1) (m-(j+1)))) (ζ (j+1)) := by
  -- The full physical executor is unrolled before any scalar polynomial response is substituted.
  unfold frozenResponse
  rw [affineRun_unroll]
  have hz : (orderedProduct (fun i => polynomialMemoryMap Q.toLinearMap (continuationMatrix α β i)) m) 0=0 := map_zero _
  rw [hz,zero_add]
  simp only [Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro j _
  exact physical_continuation Q α β (j+1) (m-(j+1)) (ζ (j+1))
end
end krylov.Envelope
