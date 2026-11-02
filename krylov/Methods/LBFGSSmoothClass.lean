import krylov.Methods.EmptyCompilation
import krylov.Methods.LBFGSObserved

set_option autoImplicit false
/-!
Article: main_krylov, cor:lm and s3:cor:qn, actual smooth BFGS/L-BFGS class membership.
Use: prove full primitive smooth source-class membership for true
scalar-initialized BFGS and every positive newest-retaining L-BFGS window.
Source: KoldaEtAl98, Corollary 2.5; proved actual quadratic transcripts,
positive retained curvature pivots and concrete genuine two-loop observed coefficients.
-/

namespace krylov.Methods
noncomputable section
open krylov.Reference krylov.Stability
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Every actual retained nonstagnating quadratic CG secant pair has strictly positive true curvature.
Use: Every actual retained nonstagnating quadratic CG secant pair has strictly positive true curvature.
Article: main_krylov, cor:lm and s3:cor:qn, actual smooth BFGS/L-BFGS class membership.
Proof: The genuine retained conjugacy matrix is positive definite, so its actual selected diagonal is positive; use real inner-product symmetry. -/
theorem retained_reference_curvature_pos (Q : E →L[ℝ] E) (hQ : Q.toLinearMap.IsSymmetric)
    (hpos : ∀ v : E, v≠0 → 0 < inner ℝ v (Q v)) (g : E) (k m : ℕ)
    (hg : ∀ i<k, CG.gradient Q g i≠0) (p : E × E) (hp : p∈(referencePairs Q g k).take m) :
    0 < inner ℝ p.1 p.2 := by
  obtain ⟨i,hi⟩ := List.mem_iff_get.mp hp
  have hd := (retainedConjugacy_posDef Q hQ hpos g k m hg).diag_pos (i := i)
  change 0 < inner ℝ (((referencePairs Q g k).take m).get i).2 (((referencePairs Q g k).take m).get i).1 at hd
  simpa only [hi,real_inner_comm] using hd

/-- The actual positive-scalar-initialized BFGS/L-BFGS policy has genuine primitive smooth-cycle membership at every order on every true active quadratic reference.
Use: The actual positive-scalar-initialized BFGS/L-BFGS policy has genuine primitive smooth-cycle membership at every order on every true active quadratic reference.
Article: main_krylov, cor:lm and s3:cor:qn, actual smooth BFGS/L-BFGS class membership.
Proof: Compile its concrete actual observed two-loop coefficients and empty corrections. Recover the true retained reference pairs from the genuine quadratic execution and derive every real primitive curvature pivot. -/
theorem lbfgsMethod_smoothCycleAt (memory : ℕ → ℕ) (hm : ∀ k, 0<k → 0<memory k)
    (c : ℝ) (hc : 0<c) (Q : E →L[ℝ] E) (hQ : Q.toLinearMap.IsSymmetric)
    (hpos : ∀ v : E, v≠0 → 0 < inner ℝ v (Q v)) (g : E)
    (N : ℕ) (hpre : ∀ k<N, CG.gradient Q g k≠0) (r : WithTop ℕ∞) :
    SmoothProbedCycleAt (lbfgsMethod memory (fun _ => c)) r Q g N := by
  -- Compile the actual finite two-loop observation coefficients and derive all genuine primitive pivots from the true retained CG transcript.
  apply emptyCompiled_smoothCycleAt (lbfgsMethod memory (fun _ => c)) (fun _ _ => rfl)
    (lbfgsObservedRule memory c) (lbfgsObservedRule_evaluate memory c) Q g N r
  intro k hk
  apply lbfgsObservedRule_regular
  intro p hp
  have hW : chartWindow memory (methodRun (lbfgsMethod memory (fun _ => c)) (fun _ => Q) (fun _ => Q) g k).queryShape
      (observedArray (methodRun (lbfgsMethod memory (fun _ => c)) (fun _ => Q) (fun _ => Q) g k).observationList.length
        (methodRun (lbfgsMethod memory (fun _ => c)) (fun _ => Q) (fun _ => Q) g k).observationList)=
      (referencePairs Q g k).take (memory k) := by
    unfold chartWindow selectedWindow
    rw [ofFn_observedArray,historyFromObservations_actual,methodRun_length,
      (lbfgsMethod_static memory (fun _ => c) (fun _ => hc) Q hQ hpos g (fun k _ => hm k) k).2]
  rw [hW] at hp
  exact (retained_reference_curvature_pos Q hQ hpos g k (memory k)
    (fun i hi => hpre i (hi.trans hk)) p hp).ne'

/-- The actual L-BFGS executor with positive scalar initialization and any positive newest-retaining memory as a genuine smooth globally CG-consistent source information-class member.
Use: The actual L-BFGS executor with positive scalar initialization and any positive newest-retaining memory as a genuine smooth globally CG-consistent source information-class member.
Article: main_krylov, cor:lm and s3:cor:qn, actual smooth BFGS/L-BFGS class membership.
Proof: Combine actual all-history information admissibility, genuine quadratic CG consistency and the proved true finite primitive smooth-cycle representation. -/
def smoothLBFGSClass (memory : ℕ → ℕ) (hm : ∀ k, 0<k → 0<memory k)
    (c : ℝ) (hc : 0<c) : SmoothProbedClass E where
  memory := memory
  policy := lbfgsMethod memory (fun _ => c)
  admissible := lbfgsMethod_spanRestricted memory (fun _ => c)
  consistent := lbfgsMethod_consistent memory hm (fun _ => c) (fun _ => hc)
  smooth := fun Q hQ hpos g N hpre => lbfgsMethod_smoothCycleAt memory hm c hc Q hQ hpos g N hpre 2

/-- The actual full-memory BFGS executor with positive scalar initialization as a genuine smooth globally CG-consistent source information-class member.
Use: The actual full-memory BFGS executor with positive scalar initialization as a genuine smooth globally CG-consistent source information-class member.
Article: main_krylov, cor:lm and s3:cor:qn, actual smooth BFGS/L-BFGS class membership.
Proof: Specialize the actual L-BFGS class to full true memory. -/
def smoothBFGSClass (c : ℝ) (hc : 0<c) : SmoothProbedClass E :=
  smoothLBFGSClass fullMemory (fun _ hk => hk) c hc
end
end krylov.Methods
