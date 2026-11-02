import krylov.OneGradient.CompletionCG
import krylov.Methods.QuadraticConsistency
import krylov.Methods.RFC
set_option autoImplicit false
/-!
Article: main_krylov, s5:moment(c), zero error of the actual probed methods.
Use: compare the positive physical one-gradient obstruction with the genuine
FC/RFC outputs on precisely the same constant-prefix information fibres.
Source: the proved actual CG-consistent probe-history theorem and genuine
full-atom termination of every positive physical Lanczos completion.
-/

namespace krylov.OneGradient
noncomputable section
open Matrix krylov.Reference krylov.Secant krylov.Methods
variable {n : ℕ}

/-- Every actual CG-consistent probed policy terminates exactly on each positive
physical last-Jacobi-pivot completion, even with arbitrary correction operators.
Use: the one-gradient obstruction is absent when the last true direction action
is probed before its actual exact-search step is selected.
Article: main_krylov, s5:moment(c).
Proof: genuine constant-prefix probe equality identifies the whole true method
history with its actual quadratic reference; every completion retains the full
active atom count, where the real CG residual vanishes. -/
theorem probed_fibre_terminal
    (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin (n+1))) (hg : g≠0)
    (hc : (activeSpectralValues A hA.1 g).card=n+1) (b : ℝ)
    (hb : (lanczosCompletion A hA g hg hc b).PosDef)
    (method : ProbedMethod (EuclideanSpace ℝ (Fin (n+1)))) (hm : CGConsistent method)
    (B : ℕ → EuclideanSpace ℝ (Fin (n+1)) →L[ℝ] EuclideanSpace ℝ (Fin (n+1))) :
    (methodRun method (fun _ => cgOperator (lanczosCompletion A hA g hg hc b)) B g (n+1)).gradient=0 := by
  let C := lanczosCompletion A hA g hg hc b
  have hp := cgOperator_positive C hb
  have hhist := cgConsistent_shadow method hm (cgOperator C) hp.1 hp.2
    (fun _ => cgOperator C) B g (n+1) (fun _ _ => rfl) (n+1) le_rfl
  rw [hhist,quadratic_gradient_eq_cg method hm _ hp.1 hp.2]
  have hcount := completion_full_atoms A hA g hg hc b hb
  change referenceAtomCount C hb g=n+1 at hcount
  have ht := cg_terminates C hb g
  rw [hcount] at ht
  exact ht

/-- The actual normalized full-memory FC error on every positive physical
one-gradient fibre scenario is exactly zero.
Use: the comparison uses the same genuine last-CG-error denominator as the
one-gradient minimax theorem, rather than a different reference normalization.
Article: main_krylov, s5:moment(c).
Proof: apply genuine probed fibre termination to the implemented consistent
full-memory FC policy, then evaluate its actual canonical zero residual. -/
theorem fc_fibre_error_zero
    (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin (n+1))) (hg : g≠0)
    (hc : (activeSpectralValues A hA.1 g).card=n+1) (b : ℝ)
    (hb : (lanczosCompletion A hA g hg hc b).PosDef)
    (B : ℕ → EuclideanSpace ℝ (Fin (n+1)) →L[ℝ] EuclideanSpace ℝ (Fin (n+1))) :
    let C := lanczosCompletion A hA g hg hc b
    ‖cgOperator (metricRoot C)⁻¹ (methodRun (fcMethod fullMemory)
      (fun _ => cgOperator C) B g (n+1)).gradient‖/‖cgCanonicalError C g n‖=0 := by
  dsimp only
  rw [probed_fibre_terminal A hA g hg hc b hb (fcMethod fullMemory) fullFC_consistent B,
    map_zero,norm_zero,zero_div]

/-- Every finite repeated full-memory RFC implementation has exactly zero
normalized physical error on the same constant-prefix fibre scenarios.
Use: the comparison includes ordinary RFC, all finite correction counts and
arbitrary actual correction operators, without charging an unevaluated output query.
Article: main_krylov, s5:moment(c).
Proof: the implemented RFC policy's proved true CG consistency gives actual
probed fibre termination and hence an exactly zero real canonical error. -/
theorem rfc_fibre_error_zero
    (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin (n+1))) (hg : g≠0)
    (hc : (activeSpectralValues A hA.1 g).card=n+1) (b : ℝ)
    (hb : (lanczosCompletion A hA g hg hc b).PosDef) (count : ℕ)
    (B : ℕ → EuclideanSpace ℝ (Fin (n+1)) →L[ℝ] EuclideanSpace ℝ (Fin (n+1))) :
    let C := lanczosCompletion A hA g hg hc b
    ‖cgOperator (metricRoot C)⁻¹ (methodRun (rfcMethod fullMemory count)
      (fun _ => cgOperator C) B g (n+1)).gradient‖/‖cgCanonicalError C g n‖=0 := by
  dsimp only
  rw [probed_fibre_terminal A hA g hg hc b hb (rfcMethod fullMemory count)
    (rfcMethod_consistent fullMemory (fun _ hi => hi) count) B,map_zero,norm_zero,zero_div]

end
end krylov.OneGradient
