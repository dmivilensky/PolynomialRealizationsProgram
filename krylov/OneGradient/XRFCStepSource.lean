import krylov.OneGradient.CanonicalMatrixPath
import krylov.OneGradient.XRFCStepTaylor
set_option autoImplicit false
/-!
Article: main_krylov, thm:I, literal canonical-source step-basis expansion.
Use: state the actual XRFC output expansion on the original source E_l
matrices, with the printed real response and a genuine quadratic remainder.
Source: proved actual physical varying-prefix expansion and the exact reused
canonicalFCPath matrix/operator and normalized-increment dictionaries.
-/

namespace krylov.OneGradient
noncomputable section
open Matrix krylov.Methods krylov.Reference krylov.Secant krylov.Stability krylov.Variation
open scoped Matrix.Norms.L2Operator
variable {n : ℕ}

/-- The original canonical source scenario gives the literal printed step-basis
XRFC amplitude response, with a true quadratic output remainder.
Use: the canonical E_l are exactly the supplied actual real symmetric source
matrices, including the final unevaluated output segment increment.
Article: main_krylov, thm:I, step-basis formula on the original canonical source.
Proof: instantiate the proved genuine physical varying-prefix expansion by
the actual matrix realization of the existing canonicalFCPath. Its true
affine calculus and exact root cancellations identify each normalized
operator derivative increment with the original supplied E_l. -/
theorem xrfc_step_canonical_expansion
    (trial : History (EuclideanSpace ℝ (Fin n)) → ℝ)
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (hc : referenceAtomCount base hb g=n) (hn : 0<n)
    (E : ℕ → Matrix (Fin n) (Fin n) ℝ) (hE : ∀ l,(E l).IsSymm)
    (ht : ∀ i<n,trial (oneGradientRun (xrfcMethod fullMemory trial) (fun _ => cgOperator base) g i)≠0)
    (hT : ∀ k<n,ContDiffAt ℝ 2 (trialCoordinate trial k)
      (oneGradientData (xrfcMethod fullMemory trial) (fun _ => cgOperator base) g k)) :
    let m := xrfcMethod fullMemory trial
    let R := cgOperator (metricRoot base)⁻¹
    ∃ delta C : ℝ,0<delta ∧ 0≤C ∧ ∀ t : ℝ,|t|≤delta →
      ‖R (m.outputGradient (canonicalFCPath base E t n)
        (oneGradientRun m (canonicalFCPath base E t) g n))-
          t • xrfcStepResponse trial base g (fun l => cgOperator (E l))‖≤C*t^2 := by
  have h := xrfc_step_output_quadratic_remainder trial base hb g hc hn (canonicalMatrixPath base E)
    (canonical_matrix_path_contDiff base E) (canonical_matrix_path_symmetric base hb E hE)
    (canonical_matrix_path_zero base E) ht hT
  simp only [canonical_matrix_path_operator] at h
  have hinc (l : ℕ) :
      cgOperator (metricRoot base)⁻¹*(deriv (fun t => canonicalFCPath base E t (l+1)) 0-
        deriv (fun t => canonicalFCPath base E t l) 0)*cgOperator (metricRoot base)⁻¹=cgOperator (E l) := by
    simpa only [canonical_matrix_path_operator] using canonical_matrix_path_normalized_increment base hb E l
  simpa only [hinc] using h

/-- Exact original reference trials give a genuine quadratic actual step-basis
XRFC error on every original canonical matrix source path.
Use: the source's exact-trial improvement concerns the real semantic output,
not merely a vanishing formal coefficient.
Article: main_krylov, thm:I, exact reference trials imply O(omega^2).
Proof: the genuine original canonical expansion has its actual printed
response, and the proved exact-reference-trial identity makes that real
finite response zero coefficient by coefficient. -/
theorem xrfc_step_exact_canonical_quadratic
    (trial : History (EuclideanSpace ℝ (Fin n)) → ℝ)
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (hc : referenceAtomCount base hb g=n) (hn : 0<n)
    (E : ℕ → Matrix (Fin n) (Fin n) ℝ) (hE : ∀ l,(E l).IsSymm)
    (ht : ∀ i<n,trial (oneGradientRun (xrfcMethod fullMemory trial) (fun _ => cgOperator base) g i)≠0)
    (hT : ∀ k<n,ContDiffAt ℝ 2 (trialCoordinate trial k)
      (oneGradientData (xrfcMethod fullMemory trial) (fun _ => cgOperator base) g k))
    (hexact : ∀ i<n,trial (oneGradientRun (xrfcMethod fullMemory trial) (fun _ => cgOperator base) g i)=
      CG.length (cgOperator base) g i) :
    let m := xrfcMethod fullMemory trial
    let R := cgOperator (metricRoot base)⁻¹
    ∃ delta C : ℝ,0<delta ∧ 0≤C ∧ ∀ t : ℝ,|t|≤delta →
      ‖R (m.outputGradient (canonicalFCPath base E t n)
        (oneGradientRun m (canonicalFCPath base E t) g n))‖≤C*t^2 := by
  have h := xrfc_step_canonical_expansion trial base hb g hc hn E hE ht hT
  have hz := (xrfc_exact_trial_responses trial base g hexact (fun l => cgOperator (E l))).2
  simpa only [hz,smul_zero,sub_zero] using h

end
end krylov.OneGradient
