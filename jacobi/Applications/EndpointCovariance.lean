import jacobi.Applications.NesterovImpulse

/-!
Article: jacobi, Theorem 5.1.
Three genuine covariance sums of the actual causal impulse states obey
closed scalar recurrences. This gives a polynomial-error proof of the
endpoint limit, valid also at b=0, without a separate logarithmic case.
Use: EndpointCovarianceBounds controls the true original squared gain.
-/
namespace jacobi.Applications
noncomputable section
open Matrix chebyshev1
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-- The true difference-coordinate endpoint variance of the original Nesterov impulse states.
Use: endpointDifference_recurrence initializes the coupled polynomial-error estimate.
Article: jacobi, Theorem 5.1.
-/
def endpointDifference (b:ℝ) (k:ℕ) : ℝ :=
  ∑ j∈Finset.range k,(nesterovImpulse b j k 0-nesterovImpulse b j k 1)^2

/-- The genuine current/difference cross covariance of the original endpoint impulses.
Use: endpointCross_recurrence transfers the bounded difference-coordinate error into a linearly bounded cross error.
Article: jacobi, Theorem 5.1.
-/
def endpointCross (b:ℝ) (k:ℕ) : ℝ :=
  ∑ j∈Finset.range k,nesterovImpulse b j k 0*(nesterovImpulse b j k 0-nesterovImpulse b j k 1)

/-- The actual summed squared original endpoint impulse amplitudes.
Use: endpointEnergy_kernel identifies this exact finite sum with the squared original first-variation time norm.
Article: jacobi, Theorem 5.1.
-/
def endpointEnergy (b:ℝ) (k:ℕ) : ℝ := ∑ j∈Finset.range k,(nesterovImpulse b j k 0)^2

/-- The genuine endpoint impulse energy is exactly the original realization's squared endpoint gain.
Use: the polynomial covariance asymptotic proves the source's original gain, not a separate surrogate sequence.
Article: jacobi, Theorem 5.1.
Proof: the reused actual time norm is the square root of its squared kernel sum. Each causal impulse equals that same true kernel, and every summand is nonnegative. -/
theorem endpointEnergy_kernel (b:ℝ) (k:ℕ) :
    endpointEnergy b k=((nesterovMethod b).kernelNorm k 0 0)^2 := by
  rw [Realization.kernelNorm,Real.sq_sqrt (Finset.sum_nonneg (fun _ _ => sq_nonneg _))]
  apply Finset.sum_congr rfl
  intro j hj
  rw [nesterovImpulse_kernel b (Finset.mem_range.mp hj)]

/-- The true endpoint difference variance obeys its closed one-step recurrence.
Use: the exact rational particular solution and its bounded error are proved in EndpointCovarianceBounds.
Article: jacobi, Theorem 5.1.
Proof: an old impulse difference is multiplied by the original momentum beta. The one new independent insertion has difference minus one and contributes precisely one to the variance. -/
theorem endpointDifference_recurrence (b:ℝ) (k:ℕ) :
    endpointDifference b (k+1)=(nesterovMomentum b k)^2*endpointDifference b k+1 := by
  -- Causality separates the old impulses from the single genuine new insertion.
  rw [endpointDifference,Finset.sum_range_succ,nesterovImpulse_new]
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one,sub_zero,neg_one_sq]
  congr 1
  rw [endpointDifference,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  obtain ⟨h0,h1⟩ := nesterovImpulse_old b (show j≠k by have h:=Finset.mem_range.mp hj; omega)
  rw [h0,h1]
  ring

/-- The true endpoint cross covariance obeys its exact closed one-step recurrence.
Use: a bounded difference-variance error gives a linearly bounded mixed-covariance error.
Article: jacobi, Theorem 5.1.
Proof: expand the old current times its new difference using the actual two-coordinate update. Its finite sum is beta*C+beta squared*D, and the genuine new unit insertion adds one. -/
theorem endpointCross_recurrence (b:ℝ) (k:ℕ) :
    endpointCross b (k+1)=nesterovMomentum b k*endpointCross b k+endpointDifference b (k+1) := by
  -- The difference-variance contribution is the same exact original sequence in both recurrences.
  rw [endpointDifference_recurrence,endpointCross,Finset.sum_range_succ,nesterovImpulse_new]
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one,sub_zero,neg_mul,one_mul,neg_neg]
  have he : (∑ j∈Finset.range k,nesterovImpulse b j (k+1) 0*
      (nesterovImpulse b j (k+1) 0-nesterovImpulse b j (k+1) 1))=
      ∑ j∈Finset.range k,(nesterovMomentum b k*(nesterovImpulse b j k 0*
        (nesterovImpulse b j k 0-nesterovImpulse b j k 1))+
        (nesterovMomentum b k)^2*(nesterovImpulse b j k 0-nesterovImpulse b j k 1)^2) := by
    apply Finset.sum_congr rfl
    intro j hj
    obtain ⟨h0,h1⟩ := nesterovImpulse_old b (show j≠k by have h:=Finset.mem_range.mp hj; omega)
    rw [h0,h1]
    ring
  rw [he,Finset.sum_add_distrib,← Finset.mul_sum,← Finset.mul_sum]
  simp only [endpointCross,endpointDifference,add_assoc]

/-- The actual original endpoint squared gain obeys its exact closed covariance recurrence.
Use: EndpointCovarianceBounds controls its quadratic error around the genuine cubic leading term.
Article: jacobi, Lemma A.2.
Proof: square the real old-impulse update x+beta*(x-y), sum its three terms, and add the genuine new unit insertion. The beta squared difference variance plus one is exactly the next difference variance. -/
theorem endpointEnergy_recurrence (b:ℝ) (k:ℕ) :
    endpointEnergy b (k+1)=endpointEnergy b k+2*nesterovMomentum b k*endpointCross b k+
      endpointDifference b (k+1) := by
  -- Every term comes from the finite sum of actual original first-variation amplitudes.
  rw [endpointDifference_recurrence,endpointEnergy,Finset.sum_range_succ,nesterovImpulse_new]
  simp only [Matrix.cons_val_zero,neg_one_sq]
  have he : (∑ j∈Finset.range k,(nesterovImpulse b j (k+1) 0)^2)=
      ∑ j∈Finset.range k,((nesterovImpulse b j k 0)^2+
        2*nesterovMomentum b k*(nesterovImpulse b j k 0*(nesterovImpulse b j k 0-nesterovImpulse b j k 1))+
        (nesterovMomentum b k)^2*(nesterovImpulse b j k 0-nesterovImpulse b j k 1)^2) := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [(nesterovImpulse_old b (show j≠k by have h:=Finset.mem_range.mp hj; omega)).1]
    ring
  rw [he,Finset.sum_add_distrib,Finset.sum_add_distrib,← Finset.mul_sum,← Finset.mul_sum]
  simp only [endpointEnergy,endpointCross,endpointDifference,add_assoc]

/-- The three original endpoint covariances have the genuine unit one-step initial values.
Use: starts the uniform polynomial-error induction at the first actual Nesterov query.
Article: jacobi, Lemma A.2.
Proof: there is exactly one causal insertion, with current value minus one and previous value zero. -/
theorem endpointCovariance_initial (b:ℝ) :
    endpointDifference b 1=1 ∧ endpointCross b 1=1 ∧ endpointEnergy b 1=1 := by
  simp [endpointDifference,endpointCross,endpointEnergy,nesterovImpulse_new]

end
end jacobi.Applications
