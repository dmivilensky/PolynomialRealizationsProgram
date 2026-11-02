import krylov.Methods.LBFGSReference

set_option autoImplicit false
/-!
Article: main_krylov, thm:select and apB:lem:mu(a), actual generic quadratic stored-pair transcript.
Use: recover the genuine complete CG pair history for every actual
globally CG-consistent method before constructing its real final
latest-information model.
Source: genuine exact-search direction-scale cancellation and actual
zero corrections in the proved full-history reference advance theorem.
-/

namespace krylov.Methods
noncomputable section
open krylov.Reference
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Every actual globally CG-consistent method has exactly the true CG stored step/secant pair transcript on every positive quadratic reference, including stopped tails.
Use: Every actual globally CG-consistent method has exactly the true CG stored step/secant pair transcript on every positive quadratic reference, including stopped tails.
Article: main_krylov, thm:select and apB:lem:mu(a), actual generic quadratic stored-pair transcript.
Proof: Induct through genuine actual histories. Real global consistency supplies the positive direction scale and zero correction phase; the proved true scaled quadratic advance appends exactly the actual reference pair. -/
theorem cgConsistent_reference_pairs (m : ProbedMethod E) (hm : CGConsistent m)
    (Q : E →L[ℝ] E) (hQ : Q.toLinearMap.IsSymmetric)
    (hpos : ∀ v : E, v≠0 → 0 < inner ℝ v (Q v)) (g : E) (k : ℕ) :
    (methodRun m (fun _ => Q) (fun _ => Q) g k).pairs=referencePairs Q g k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    obtain ⟨c,hc,hd,hzero⟩ := hm Q hQ hpos g k
    exact (reference_advance_scaled m Q g k _ (quadratic_gradient_eq_cg m hm Q hQ hpos g k) ih hc.ne' hd hzero).2
end
end krylov.Methods
