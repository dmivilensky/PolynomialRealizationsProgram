import krylov.OneGradient.XRFCObservedSpectral
import krylov.OneGradient.XRFCTwoBasisOutput
set_option autoImplicit false
/-!
Article: main_krylov, cor:quant(a), genuine uniform two-basis XRFC attainment.
Use: one history-only endpoint policy gives the original uniform spectral
guarantee for all real constant-prefix references and physical output matrices.
Source: original observed harmonic policy, true equality of the two executed
quadratic basis histories and actual attained physical output maxima.
-/

namespace krylov.OneGradient
noncomputable section
open Matrix krylov.Reference krylov.Methods krylov.Secant
variable {m : ℕ}

/-- Either genuine full-memory XRFC implementation using the single original
history-only spectral harmonic trial rule.
Use: the choice of basis captures no unobserved reference or information fibre.
Article: main_krylov, cor:quant(a). -/
def spectralXRFCMethod (directions : Bool) (N : ℕ) (mu upper : ℝ)
    (earlier : History (EuclideanSpace ℝ (Fin m)) → ℝ) : OneGradientMethod (EuclideanSpace ℝ (Fin m)) :=
  xrfcBasisMethod directions (xrfcSpectralTrial N mu upper earlier)

/-- One actual observed harmonic policy attains the uniform original spectral
error guarantee in either XRFC basis, for arbitrary positive earlier trials.
Use: the bound holds simultaneously for every actual positive full-atom
reference in the known class and every real admissible unobserved output
matrix; the same decision functions are used for every such reference.
Article: main_krylov, cor:quant(a), uniform attainment by XRFC.
Proof: true native observed-window feasibility gives the harmonic trial bound
at the final query. The two bases have identical genuine quadratic histories,
so their final scalar decisions agree. Each implemented executor has the
proved actual physical output-ball maximum. Divide it by the true positive
last CG error norm and apply the same known-data trial bound. -/
theorem xrfc_spectral_output_upper (directions : Bool)
    (A : Matrix (Fin m) (Fin m) ℝ) (hA : A.PosDef) (g : EuclideanSpace ℝ (Fin m))
    (N : ℕ) (hN : referenceAtomCount A hA g=N+1)
    (mu upper : ℝ) (hmu : 0 < mu) (hmuL : mu≤upper)
    (hlo : (A-mu • 1).PosSemidef) (hhi : (upper • 1-A).PosSemidef)
    (earlier : History (EuclideanSpace ℝ (Fin m)) → ℝ) (he : ∀ H,0 < earlier H)
    {omega : ℝ} (homega : 0≤omega)
    (B : Matrix (Fin m) (Fin m) ℝ) (hB : B.IsSymm) (hbudget : relativeBudget A (B-A)≤omega) :
    let method := spectralXRFCMethod directions N mu upper earlier
    let H := oneGradientRun method (fun _ => cgOperator A) g (N+1)
    ‖cgOperator (metricRoot A)⁻¹ (method.outputGradient (cgOperator B) H)‖/‖cgCanonicalError A g N‖≤
      ((upper-mu)/(upper+mu))*omega := by
  let Q := cgOperator A
  let trial := xrfcSpectralTrial N mu upper earlier
  have ht (K : History (EuclideanSpace ℝ (Fin m))) : trial K≠0 :=
    (xrfc_spectral_trial_positive N mu upper earlier he K).ne'
  have hraw := xrfc_prior_harmonic_reference_bound A hA g N hN mu upper hmu hmuL hlo hhi trial
    (fun _ _ => ht _)
  have hlast : trial (oneGradientRun (xrfcMethod fullMemory trial) (fun _ => Q) g N)=
      xrfcPriorHarmonic mu upper (oneGradientRun (xrfcMethod fullMemory trial) (fun _ => Q) g N) := by
    change xrfcSpectralTrial N mu upper earlier _=_
    rw [xrfcSpectralTrial,oneGradientRun_length,ite_eq_left rfl,ite_eq_left hraw.1]
  have hS : |1-trial (oneGradientRun (xrfcMethod fullMemory trial) (fun _ => Q) g N)/CG.length Q g N|≤
      (upper-mu)/(upper+mu) := by
    rw [hlast]
    exact hraw.2
  exact xrfc_two_basis_output_upper directions A hA g N hN trial ht
    ((upper-mu)/(upper+mu)) hS homega B hB hbudget

end
end krylov.OneGradient
