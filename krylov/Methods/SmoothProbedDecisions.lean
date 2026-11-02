import krylov.Methods.SmoothProbedFields

set_option autoImplicit false
/-!
Article: main_krylov, apB:lem:filtration, genuine local raw-policy decisions.
Use: recover actual primitive smooth direction and complete correction-tree
representations along the true raw execution, retaining its real observed
history rather than replacing the algorithm by a presumed response map.
Source: actual local finite-policy history equality, genuine fixed query
shape and real primitive observed coefficient regularity.
-/

namespace krylov.Methods
noncomputable section
open Filter Topology krylov.Stability krylov.Reference
variable {E X : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- Every actual smooth CG-consistent raw nonstagnating prefix admits primitive regular compiled decisions on its true executed histories in a genuine neighborhood.
Use: Every actual smooth CG-consistent raw nonstagnating prefix admits primitive regular compiled decisions on its true executed histories in a genuine neighborhood.
Article: main_krylov, apB:lem:filtration, genuine local raw-policy decisions.
Proof: Choose the real primitive local policy and derive its genuine reference domains. Local complete-history equality fixes the actual query shape; primitive observed locality then gives actual direction and full correction-tree agreement along the true raw history. -/
theorem smoothProbed_decisions (m : ProbedMethod E) (hconsistent : CGConsistent m)
    (A B : X → ℕ → E →L[ℝ] E) (g : X → E) (x : X) (N : ℕ) {r : WithTop ℕ∞}
    (hA : ∀ k < N, ContDiffAt ℝ r (fun p => A p k) x)
    (hB : ∀ k < N, ContDiffAt ℝ r (fun p => B p k) x) (hg : ContDiffAt ℝ r g x)
    (Q : E →L[ℝ] E) (hAx : A x=fun _ => Q) (hBx : B x=fun _ => Q)
    (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v : E, v≠0 → 0 < inner ℝ v (Q v))
    (hpre : ∀ k < N, CG.gradient Q (g x) k≠0) (hsmooth : SmoothProbedCycleAt m r Q (g x) N)
    (k : ℕ) (hk : k < N) :
    ∃ P : CompiledProbedPolicy E,
      P.CoefficientsRegularAt r (methodRun m (A x) (B x) (g x) k) (A x k) (B x k) ∧
      ∀ᶠ p in 𝓝 x,
        m.direction (methodRun m (A p) (B p) (g p) k)=
          P.method.direction (methodRun m (A p) (B p) (g p) k) ∧
        m.correction (methodRun m (A p) (B p) (g p) k) (probedProbe m (A p) (B p) (g p) k)=
          P.method.correction (methodRun m (A p) (B p) (g p) k) (probedProbe m (A p) (B p) (g p) k) := by
  -- The real primitive local policy supplies its own coefficient charts, independently of a trajectory expansion.
  obtain ⟨P,hcoef,hlocal⟩ := hsmooth
  have hcurv := localCompiled_quadratic_curvatures m P Q hQ hpos (g x) N hconsistent hpre hlocal
  have hcoef' : ∀ i<N, P.CoefficientsRegularAt r (methodRun P.method (A x) (B x) (g x) i) (A x i) (B x i) := by
    simpa only [hAx,hBx] using hcoef
  have hcurv' : ∀ i<N, inner ℝ (P.method.direction (methodRun P.method (A x) (B x) (g x) i))
      (A x i (P.method.direction (methodRun P.method (A x) (B x) (g x) i)))≠0 := by
    simpa only [hAx,hBx] using hcurv
  have hlocal' : ∀ i<N, LocalCompiledAt m P (methodRun P.method (A x) (B x) (g x) i)
      (A x i (P.method.direction (methodRun P.method (A x) (B x) (g x) i))) := by
    simpa only [hAx,hBx] using hlocal
  have heq := localCompiled_methodRun m P A B g x k (fun i hi => hA i (hi.trans hk))
    (fun i hi => hB i (hi.trans hk)) hg (fun i hi => hcoef' i (hi.trans hk))
    (fun i hi => hcurv' i (hi.trans hk)) (fun i hi => hlocal' i (hi.trans hk))
  have he0 := heq.self_of_nhds
  have hm0 := (hlocal' k hk).self
  have hcoeff : P.CoefficientsRegularAt r (methodRun m (A x) (B x) (g x) k) (A x k) (B x k) := by
    rw [he0]
    exact hcoef' k hk
  have hloc : LocalCompiledAt m P (methodRun m (A x) (B x) (g x) k)
      (probedProbe m (A x) (B x) (g x) k) := by
    dsimp only [probedProbe,probedDirection]
    rw [he0,hm0.1]
    exact hlocal' k hk
  have htrace := smoothProbed_trace_regular m hconsistent A B g x k
    (fun i hi => hA i (hi.trans hk)) (fun i hi => hB i (hi.trans hk)) hg Q hAx hBx hQ hpos
    (fun i hi => hpre i (hi.trans hk)) (by exact ⟨P,fun i hi => hcoef i (hi.trans hk),fun i hi => hlocal i (hi.trans hk)⟩)
  have hz := (smoothProbed_fields_regular m hconsistent A B g x N hA hB hg Q hAx hBx hQ hpos hpre
    ⟨P,hcoef,hlocal⟩ k hk).2.1
  -- The true compiled query count fixes the raw history shape on the actual execution neighborhood.
  have hshape : ∀ᶠ p in 𝓝 x,
      (methodRun m (A p) (B p) (g p) k).queryShape=(methodRun m (A x) (B x) (g x) k).queryShape := by
    filter_upwards [heq] with p hp
    rw [hp,he0]
    exact P.run_queryShape (A p) (B p) (A x) (B x) (g p) (g x) k
  exact ⟨P,hcoeff,observedLocal_eventually _ _ x htrace hz.continuousAt hshape _ hloc⟩
end
end krylov.Methods
