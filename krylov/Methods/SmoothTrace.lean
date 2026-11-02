import krylov.Methods.SmoothClasses

/-!
Article: main_krylov, def:classes and lem:U(d), full actual smooth raw-policy traces.
Use: retain every genuine intermediate observation for arbitrary locally
compiled smooth raw methods, so step, direction and terminal-output regularity
are all derived from their true primitive coefficient representations.
Source: actual local complete-history compilation, real reference curvature
transfer from raw CG consistency and genuine finite observation charts.
-/

namespace krylov.Methods
noncomputable section
open Filter Topology krylov.Stability krylov.Reference
open scoped InnerProductSpace
variable {E X : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- Every actual primitive smooth CG-consistent raw probed cycle has a genuine C-r chart of its complete observed history.
Use: Every actual primitive smooth CG-consistent raw probed cycle has a genuine C-r chart of its complete observed history.
Article: main_krylov, def:classes and lem:U(d), full actual smooth raw-policy traces.
Proof: Choose the true local primitive coefficient representation. Actual raw CG consistency supplies every real compiled curvature; real execution induction and genuine local history equality transfer the entire actual observation chart. -/
theorem smoothProbed_trace_regular (m : ProbedMethod E) (hconsistent : CGConsistent m)
    (A B : X → ℕ → E →L[ℝ] E) (g : X → E) (x : X) (N : ℕ) {r : WithTop ℕ∞}
    (hA : ∀ k<N, ContDiffAt ℝ r (fun p => A p k) x)
    (hB : ∀ k<N, ContDiffAt ℝ r (fun p => B p k) x) (hg : ContDiffAt ℝ r g x)
    (Q : E →L[ℝ] E) (hAx : A x=fun _ => Q) (hBx : B x=fun _ => Q)
    (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v : E, v≠0 → 0 < inner ℝ v (Q v))
    (hpre : ∀ k<N, CG.gradient Q (g x) k≠0) (hsmooth : SmoothProbedCycleAt m r Q (g x) N) :
    SmoothListAt r (fun p => (methodRun m (A p) (B p) (g p) N).observationList) x := by
  -- Transfer the complete actual history chart, retaining all genuine intermediate correction observations.
  obtain ⟨P,hcoef,hlocal⟩ := hsmooth
  have hcurv := localCompiled_quadratic_curvatures m P Q hQ hpos (g x) N hconsistent hpre hlocal
  have hcoef' : ∀ k<N, P.CoefficientsRegularAt r (methodRun P.method (A x) (B x) (g x) k) (A x k) (B x k) := by
    simpa only [hAx,hBx] using hcoef
  have hcurv' : ∀ k<N, inner ℝ (P.method.direction (methodRun P.method (A x) (B x) (g x) k))
      (A x k (P.method.direction (methodRun P.method (A x) (B x) (g x) k)))≠0 := by
    simpa only [hAx,hBx] using hcurv
  have hlocal' : ∀ k<N, LocalCompiledAt m P (methodRun P.method (A x) (B x) (g x) k)
      (A x k (P.method.direction (methodRun P.method (A x) (B x) (g x) k))) := by
    simpa only [hAx,hBx] using hlocal
  have htrace := P.run_regular A B g x N hA hB hg hcoef' hcurv'
  have heq := localCompiled_methodRun m P A B g x N hA hB hg hcoef' hcurv' hlocal'
  obtain ⟨k,data,hd,he⟩ := htrace
  refine ⟨k,data,hd,?_⟩
  filter_upwards [heq,he] with p hp hobs
  rw [hp,hobs]

end
end krylov.Methods
