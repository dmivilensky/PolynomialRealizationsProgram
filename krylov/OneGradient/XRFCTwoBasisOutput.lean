import krylov.OneGradient.XRFCOutputMaximum
import krylov.Methods.XRFCBasisHistory
set_option autoImplicit false
/-!
Article: main_krylov, cor:quant, shared genuine two-basis output transfer.
Use: pass one actual last observed trial bound to either native XRFC basis,
without repeating the physical output-maximization proof for each prior.
Source: original executed quadratic basis-history equality and true attained
physical output maxima, including the genuine positive last-error denominator.
-/

namespace krylov.OneGradient
noncomputable section
open Matrix krylov.Reference krylov.Methods krylov.Secant
variable {m : ℕ}

/-- The actual full-memory XRFC executor in either original stored basis.
Use: prior policies share one physical output-transfer theorem.
Article: main_krylov, cor:quant. -/
def xrfcBasisMethod (directions : Bool) (trial : History (EuclideanSpace ℝ (Fin m)) → ℝ) :
    OneGradientMethod (EuclideanSpace ℝ (Fin m)) :=
  if directions then xrfcDMethod fullMemory trial else xrfcMethod fullMemory trial

/-- A true bound on the last actual observed trial of step-basis XRFC gives
the original normalized physical output bound for either implemented basis.
Use: spectral and relative-ball policies reuse the actual executor and real
output-ball analysis, with arbitrary earlier nonzero observed trials.
Article: main_krylov, cor:quant.
Proof: the real quadratic basis histories coincide, so the last decisions
are identical. Each native executor has its genuine physical output maximum.
Divide that maximum by the true positive last CG error norm. -/
theorem xrfc_two_basis_output_upper (directions : Bool)
    (A : Matrix (Fin m) (Fin m) ℝ) (hA : A.PosDef) (g : EuclideanSpace ℝ (Fin m))
    (N : ℕ) (hN : referenceAtomCount A hA g=N+1)
    (trial : History (EuclideanSpace ℝ (Fin m)) → ℝ) (ht : ∀ H,trial H≠0)
    (coefficient : ℝ)
    (htrial : |1-trial (oneGradientRun (xrfcMethod fullMemory trial) (fun _ => cgOperator A) g N)/
      CG.length (cgOperator A) g N|≤coefficient)
    {omega : ℝ} (homega : 0≤omega)
    (B : Matrix (Fin m) (Fin m) ℝ) (hB : B.IsSymm) (hbudget : relativeBudget A (B-A)≤omega) :
    let method := xrfcBasisMethod directions trial
    let H := oneGradientRun method (fun _ => cgOperator A) g (N+1)
    ‖cgOperator (metricRoot A)⁻¹ (method.outputGradient (cgOperator B) H)‖/‖cgCanonicalError A g N‖≤coefficient*omega := by
  let Q := cgOperator A
  let method := xrfcBasisMethod directions trial
  let H := oneGradientRun method (fun _ => Q) g (N+1)
  have hp := cgOperator_positive A hA
  have hpre (i : ℕ) (hi : i<N+1) : CG.gradient Q g i≠0 :=
    cg_nonstagnation A hA g i (by rw [hN];exact hi)
  have hhist := xrfc_quadratic_basis_histories trial Q hp.1 hp.2 g N
    (fun i hi => hpre i (by omega)) (fun _ _ => ht _) N le_rfl
  have htlast : |1-trial (oneGradientRun method (fun _ => Q) g N)/CG.length Q g N|≤coefficient := by
    cases directions with
    | false => exact htrial
    | true =>
      change |1-trial (oneGradientRun (xrfcDMethod fullMemory trial) (fun _ => Q) g N)/CG.length Q g N|≤_
      rw [hhist]
      exact htrial
  have hmax : IsGreatest {x : ℝ | ∃ C : Matrix (Fin m) (Fin m) ℝ,C.IsSymm ∧
      relativeBudget A (C-A)≤omega ∧ x=‖cgOperator (metricRoot A)⁻¹ (method.outputGradient (cgOperator C) H)‖}
      (omega*|1-trial (oneGradientRun method (fun _ => Q) g N)/CG.length Q g N| *‖cgCanonicalError A g N‖) := by
    cases directions with
    | false => exact xrfc_last_output_maximum A hA g N hN trial (fun _ _ => ht _) homega
    | true =>
      exact xrfcD_last_output_maximum A hA g N hN fullMemory trial (fun _ _ hi => hi)
        (fun _ _ => ht _) homega
  apply (div_le_iff₀ (last_reference_denominator A hA g N hN).1).mpr
  calc
    _ ≤ omega*|1-trial (oneGradientRun method (fun _ => Q) g N)/CG.length Q g N| *‖cgCanonicalError A g N‖ :=
      hmax.2 ⟨B,hB,hbudget,rfl⟩
    _ ≤ omega*coefficient*‖cgCanonicalError A g N‖ :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left htlast homega) (norm_nonneg _)
    _ = (coefficient*omega)*‖cgCanonicalError A g N‖ := by ring

end
end krylov.OneGradient
