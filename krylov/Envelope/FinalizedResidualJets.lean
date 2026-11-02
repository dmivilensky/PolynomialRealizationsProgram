import krylov.Envelope.FinalizedProjectedJets
import krylov.Envelope.RecordedResidualJet
import krylov.Envelope.TiltSplitting

set_option autoImplicit false
/-!
Article: main_krylov, apB:lem:mu(a), actual final Galerkin residual variation.
Use: annihilate every genuine own-recorded-step residual first derivative
and the true residual-variation vector after one actual appended model solve.
Source: proved real full-basis projection cancellation, exact unchanged
earlier steps and genuine total correction-jet Krylov orthogonality.
-/

namespace krylov.Envelope
noncomputable section
open krylov.Reference krylov.Methods krylov.Stability
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Every genuine recorded-step final-gradient residual derivative vanishes after the real latest-information correction of any smooth source method.
Use: Every genuine recorded-step final-gradient residual derivative vanishes after the real latest-information correction of any smooth source method.
Article: main_krylov, apB:lem:mu(a), actual final Galerkin residual variation.
Proof: Actual earlier steps are unchanged full-basis columns. For the genuine last step, the real direction projection vanishes and the true total correction jet is in the next Krylov flag, orthogonal to the actual final reference gradient. -/
theorem finalized_recorded_residual_deriv_zero (M : SmoothProbedClass E)
    (A B : ℝ → ℕ → E →L[ℝ] E) (g : E) (k : ℕ)
    (hA : ∀ i<k+1, ContDiffAt ℝ 2 (fun t => A t i) 0)
    (hB : ∀ i<k+1, ContDiffAt ℝ 2 (fun t => B t i) 0)
    (Q : E →L[ℝ] E) (hA0 : A 0=fun _ => Q) (hB0 : B 0=fun _ => Q)
    (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v : E, v≠0 → 0 < inner ℝ v (Q v))
    (hpre : ∀ i<k+1, CG.gradient Q g i≠0) (i : ℕ) (hi : i<k+1) :
    deriv (fun t => inner ℝ (probedStep (finalizedMethod M.policy (k+1)) (A t) (B t) g i)
      (probedGradient (finalizedMethod M.policy (k+1)) (A t) (B t) g (k+1))) 0=0 := by
  -- Preserve the exact earlier actual steps and handle the genuine combined last step through its proved correction-jet filtration.
  have hp := finalized_projected_residual_deriv_zero M A B g k hA hB Q hA0 hB0 hQ hpos hpre
  by_cases hik : i=k
  · subst i
    apply recorded_residual_deriv_zero_of_direction (finalizedSmoothClass M (k+1))
      A B g k hA hB Q hA0 hB0 hQ hpos hpre
    change deriv (fun t => inner ℝ (probedDirection (finalizedMethod M.policy (k+1)) (A t) (B t) g k)
      (probedGradient (finalizedMethod M.policy (k+1)) (A t) (B t) g (k+1))) 0=0
    simp_rw [finalizedMethod_direction_last]
    exact hp 0
  · have hil : i<k := by omega
    have hj : k-1-i<k := by omega
    have hindex : k-1-(k-1-i)=i := by omega
    have hz := hp (Fin.succ ⟨k-1-i,hj⟩)
    simp only [probedStepBasis,Fin.cons_succ,hindex] at hz
    simpa only [finalizedMethod_step_before M.policy (k+1) _ _ g i (by omega)] using hz

/-- The true observed residual-variation vector of the actual finalized smooth method is zero on every genuine active prefix, including the empty horizon.
Use: The true observed residual-variation vector of the actual finalized smooth method is zero on every genuine active prefix, including the empty horizon.
Article: main_krylov, apB:lem:mu(a), actual final Galerkin residual variation.
Proof: Every real recorded-step residual derivative is zero, so its genuine finite normalized CG expansion vanishes. -/
theorem finalized_residualVariation_zero {n : ℕ}
    (M : SmoothProbedClass (EuclideanSpace ℝ (Fin n)))
    (base : Matrix (Fin n) (Fin n) ℝ) (g : EuclideanSpace ℝ (Fin n))
    (A B : ℝ → ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (N : ℕ) (hA : ∀ i<N, ContDiffAt ℝ 2 (fun t => A t i) 0)
    (hB : ∀ i<N, ContDiffAt ℝ 2 (fun t => B t i) 0)
    (Q : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hA0 : A 0=fun _ => Q) (hB0 : B 0=fun _ => Q)
    (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v, v≠0 → 0 < inner ℝ v (Q v))
    (hpre : ∀ i<N, CG.gradient Q g i≠0) :
    residualVariation base g (finalizedMethod M.policy N) A B N=0 := by
  cases N with
  | zero => simp only [residualVariation,Finset.univ_eq_empty,Finset.sum_empty]
  | succ k =>
    unfold residualVariation
    apply Finset.sum_eq_zero
    intro i _
    rw [finalized_recorded_residual_deriv_zero M A B g k hA hB Q hA0 hB0 hQ hpos hpre i.val i.isLt,zero_div,zero_smul]
end
end krylov.Envelope
