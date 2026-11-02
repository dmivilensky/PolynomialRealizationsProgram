import krylov.OneGradient.CanonicalMatrixPath
import krylov.OneGradient.XRFCDirectionTaylor
import krylov.Methods.XRFCBasisHistory
set_option autoImplicit false
/-!
Article: Theorem C.1 [thm:I] of krylov.tex.
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

/-- The original canonical source scenario gives the literal printed direction-basis
XRFC amplitude response, with a true quadratic output remainder.
Use: the canonical E_l are exactly the supplied actual real symmetric source
matrices, including the final unevaluated output segment increment.
Article: main_krylov, thm:I, direction-basis formula on the original canonical source.
Proof: instantiate the proved genuine physical varying-prefix expansion by
the actual matrix realization of the existing canonicalFCPath. Its true
affine calculus and exact root cancellations identify each normalized
operator derivative increment with the original supplied E_l. -/
theorem xrfc_direction_canonical_expansion
    (trial : History (EuclideanSpace ℝ (Fin n)) → ℝ)
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (hc : referenceAtomCount base hb g=n) (hn : 0<n)
    (E : ℕ → Matrix (Fin n) (Fin n) ℝ)
    (ht : ∀ i<n,trial (oneGradientRun (xrfcDMethod fullMemory trial) (fun _ => cgOperator base) g i)≠0)
    (hT : ∀ k<n,ContDiffAt ℝ 2 (trialCoordinate trial k)
      (oneGradientData (xrfcDMethod fullMemory trial) (fun _ => cgOperator base) g k)) :
    let m := xrfcDMethod fullMemory trial
    let R := cgOperator (metricRoot base)⁻¹
    ∃ delta C : ℝ,0<delta ∧ 0≤C ∧ ∀ t : ℝ,|t|≤delta →
      ‖R (m.outputGradient (canonicalFCPath base E t n)
        (oneGradientRun m (canonicalFCPath base E t) g n))-
          t • xrfcDirectionResponse trial base g (fun l => cgOperator (E l))‖≤C*t^2 := by
  have h := xrfc_direction_output_quadratic_remainder trial base hb g hc hn (canonicalMatrixPath base E)
    (canonical_matrix_path_contDiff base E) (canonical_matrix_path_zero base E) ht hT
  simp only [canonical_matrix_path_operator] at h
  have hinc (l : ℕ) :
      cgOperator (metricRoot base)⁻¹*(deriv (fun t => canonicalFCPath base E t (l+1)) 0-
        deriv (fun t => canonicalFCPath base E t l) 0)*cgOperator (metricRoot base)⁻¹=cgOperator (E l) := by
    simpa only [canonical_matrix_path_operator] using canonical_matrix_path_normalized_increment base hb E l
  simpa only [hinc] using h

/-- Exact original reference trials give a genuine quadratic actual direction-basis
XRFC error on every original canonical matrix source path.
Use: the source's exact-trial improvement concerns the real semantic output,
not merely a vanishing formal coefficient.
Article: main_krylov, thm:I, exact reference trials imply O(omega^2).
Proof: the genuine original canonical expansion has its actual printed
response, and the proved exact-reference-trial identity makes that real
finite response zero coefficient by coefficient. -/
theorem xrfc_direction_exact_canonical_quadratic
    (trial : History (EuclideanSpace ℝ (Fin n)) → ℝ)
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (hc : referenceAtomCount base hb g=n) (hn : 0<n)
    (E : ℕ → Matrix (Fin n) (Fin n) ℝ)
    (ht : ∀ i<n,trial (oneGradientRun (xrfcDMethod fullMemory trial) (fun _ => cgOperator base) g i)≠0)
    (hT : ∀ k<n,ContDiffAt ℝ 2 (trialCoordinate trial k)
      (oneGradientData (xrfcDMethod fullMemory trial) (fun _ => cgOperator base) g k))
    (hexact : ∀ i<n,trial (oneGradientRun (xrfcDMethod fullMemory trial) (fun _ => cgOperator base) g i)=
      CG.length (cgOperator base) g i) :
    let m := xrfcDMethod fullMemory trial
    let R := cgOperator (metricRoot base)⁻¹
    ∃ delta C : ℝ,0<delta ∧ 0≤C ∧ ∀ t : ℝ,|t|≤delta →
      ‖R (m.outputGradient (canonicalFCPath base E t n)
        (oneGradientRun m (canonicalFCPath base E t) g n))‖≤C*t^2 := by
  have h := xrfc_direction_canonical_expansion trial base hb g hc hn E ht hT
  have hp := cgOperator_positive base hb
  have hpre (i : ℕ) (hi : i<n) : CG.gradient (cgOperator base) g i≠0 :=
    cg_nonstagnation base hb g i (by rw [hc];exact hi)
  have hsExact : ∀ i<n,trial (oneGradientRun (xrfcMethod fullMemory trial) (fun _ => cgOperator base) g i)=
      CG.length (cgOperator base) g i := by
    intro i hi
    rw [← xrfc_quadratic_basis_histories_of_direction trial (cgOperator base) hp.1 hp.2 g n hpre ht i hi.le]
    exact hexact i hi
  have hz := (xrfc_exact_trial_responses trial base g hsExact (fun l => cgOperator (E l))).1
  simpa only [hz,smul_zero,sub_zero] using h

end
end krylov.OneGradient
