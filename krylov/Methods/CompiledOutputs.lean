import krylov.Methods.CompiledProbed

/-!
Article: main_krylov, def:classes and lem:U(d), genuine compiled method outputs.
Use: extract actual physical step regularity and genuine unevaluated output
and semantic output-gradient regularity from the complete executed history.
Source: true observation-coordinate extraction, actual data-only terminal
coefficient rules and the real final operator evaluation identity.
-/

namespace krylov.Methods
noncomputable section
open Filter Topology krylov.Stability krylov.Reference
variable {E X : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- The actual recorded physical step of a genuinely smooth compiled probed prefix is C-r.
Use: The actual recorded physical step of a genuinely smooth compiled probed prefix is C-r.
Article: main_krylov, def:classes and lem:U(d), genuine compiled method outputs.
Proof: Read its genuine coordinate in the actual next observed iteration record. -/
theorem CompiledProbedPolicy.step_regular (P : CompiledProbedPolicy E)
    (A B : X → ℕ → E →L[ℝ] E) (g : X → E) (x : X) (k : ℕ) {r : WithTop ℕ∞}
    (htrace : SmoothListAt r (fun p => (methodRun P.method (A p) (B p) (g p) (k+1)).observationList) x) :
    ContDiffAt ℝ r (fun p => probedStep P.method (A p) (B p) (g p) k) x := by
  exact htrace.getD 4

/-- A primitive smooth data-only final output has a genuine C-r unevaluated displacement and semantic output gradient.
Use: A primitive smooth data-only final output has a genuine C-r unevaluated displacement and semantic output gradient.
Article: main_krylov, def:classes and lem:U(d), genuine compiled method outputs.
Proof: Compose the actual terminal observed coefficient decision and use the genuine returned gradient plus the actual output operator action; the output itself performs no query. -/
theorem CompiledProbedPolicy.output_regular (P : CompiledProbedPolicy E)
    (output : ∀ m, ObservedRule E m) (A B : X → ℕ → E →L[ℝ] E) (g : X → E)
    (C : X → E →L[ℝ] E) (x : X) (N : ℕ) {r : WithTop ℕ∞}
    (htrace : SmoothListAt r (fun p => (methodRun P.method (A p) (B p) (g p) N).observationList) x)
    (hout : ContDiffAt ℝ r (output (methodRun P.method (A x) (B x) (g x) N).observationList.length).coefficient
      (observedArray (methodRun P.method (A x) (B x) (g x) N).observationList.length
        (methodRun P.method (A x) (B x) (g x) N).observationList)) (hC : ContDiffAt ℝ r C x) :
    let u := fun p => listDecision output (methodRun P.method (A p) (B p) (g p) N).observationList
    ContDiffAt ℝ r u x ∧ ContDiffAt ℝ r (fun p => probedGradient P.method (A p) (B p) (g p) N+C p (u p)) x := by
  have hu := listDecision_contDiffAt output _ x htrace hout
  exact ⟨hu,(P.gradient_regular A B g x N htrace).add (hC.clm_apply hu)⟩
end
end krylov.Methods
