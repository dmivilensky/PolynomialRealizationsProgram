import krylov.OneGradient.LastEvaluation
import krylov.Methods.XRFC
import krylov.Methods.XRFCDTermination
set_option autoImplicit false
/-!
Article: main_krylov, thm:exact, full-cycle XRFC attainment.
Use: compute the exact attained physical output error of the actual one-gradient
XRFC executor after genuine CG exhaustion, in both stored bases.
Source: the proved true virtual CG trajectory, actual final correction and the
attained symmetric physical output-ball image theorem.
-/

namespace krylov.OneGradient
noncomputable section
open Matrix krylov.Reference krylov.Secant krylov.Methods
variable {m : ℕ}

/-- At a genuine solved virtual output the exact physical robust error is
omega times the true canonical output displacement.
Use: transfer the physical output maximum to either implemented XRFC basis.
Article: main_krylov, thm:exact.
Proof: the actual reference semantic gradient vanishes; the true inverse-root
reference action cancels the deterministic residual in the output maximum. -/
theorem solved_output_maximum (A : Matrix (Fin m) (Fin m) ℝ) (hA : A.PosDef)
    (r u : EuclideanSpace ℝ (Fin m)) (hsolved : r+cgOperator A u=0)
    {omega : ℝ} (homega : 0≤omega) :
    IsGreatest {x : ℝ | ∃ B : Matrix (Fin m) (Fin m) ℝ,B.IsSymm ∧
      relativeBudget A (B-A)≤omega ∧ x=‖cgOperator (metricRoot A)⁻¹ (r+cgOperator B u)‖}
      (omega*‖cgOperator (metricRoot A) u‖) := by
  have he : cgOperator (metricRoot A)⁻¹ r+cgOperator (metricRoot A) u=0 := by
    have hbase : cgOperator (metricRoot A)⁻¹ (cgOperator A u)=cgOperator (metricRoot A) u :=
      canonical_reference_action A hA u
    rw [← hbase,← map_add,hsolved,map_zero]
  simpa only [he,norm_zero,zero_add] using physical_output_maximum A hA r u homega

/-- The true missing-line correction has exactly the relative-trial-error
multiple of the genuine last CG error norm.
Use: the normalization is the actual physical denominator, including all scalar signs.
Article: main_krylov, thm:exact.
Proof: pull its actual scalar through the true metric root and use the proved
positive last reference line and last error identity. -/
theorem last_correction_norm (A : Matrix (Fin m) (Fin m) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin m)) (N : ℕ) (hN : referenceAtomCount A hA g=N+1) (t : ℝ) :
    ‖cgOperator (metricRoot A) ((CG.length (cgOperator A) g N-t) • CG.direction (cgOperator A) g N)‖=
      |1-t/CG.length (cgOperator A) g N| *‖cgCanonicalError A g N‖ := by
  let a := CG.length (cgOperator A) g N
  have hp := cgOperator_positive A hA
  have hlt : N<referenceAtomCount A hA g := by omega
  have hi := CG.invariant _ hp.1 hp.2 g N (fun j hj => cg_nonstagnation A hA g j (hj.trans hlt))
  have ha : 0<a := (CG.invariant_line_pos _ hp.2 g N hi (cg_nonstagnation A hA g N hlt)).2.1
  rw [map_smul,norm_smul,Real.norm_eq_abs,(last_reference_denominator A hA g N hN).2,← mul_assoc]
  change |a-t| * _=(|1-t/a| * a)*_
  have he : 1-t/a=(a-t)/a := by field_simp
  rw [he,abs_div,abs_of_pos ha,div_mul_cancel₀ _ ha.ne']

/-- Actual full-memory step-basis XRFC has the exact attained robust output
maximum printed in the one-gradient minimax proof.
Use: arbitrary data-dependent nonzero earlier trials affect neither the final
virtual solution nor its exact physical output-ball error formula.
Article: main_krylov, thm:exact.
Proof: the implemented full-cycle virtual output really solves the reference;
the implemented next correction is its actual missed line component. Insert
these identities into the attained physical symmetric output maximum. -/
theorem xrfc_last_output_maximum (A : Matrix (Fin m) (Fin m) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin m)) (N : ℕ) (hN : referenceAtomCount A hA g=N+1)
    (trial : History (EuclideanSpace ℝ (Fin m)) → ℝ)
    (ht : ∀ i<N+1,trial (oneGradientRun (xrfcMethod fullMemory trial) (fun _ => cgOperator A) g i)≠0)
    {omega : ℝ} (homega : 0≤omega) :
    let method := xrfcMethod fullMemory trial
    let H := oneGradientRun method (fun _ => cgOperator A) g (N+1)
    let t := trial (oneGradientRun method (fun _ => cgOperator A) g N)
    IsGreatest {x : ℝ | ∃ B : Matrix (Fin m) (Fin m) ℝ,B.IsSymm ∧
      relativeBudget A (B-A)≤omega ∧ x=‖cgOperator (metricRoot A)⁻¹ (method.outputGradient (cgOperator B) H)‖}
      (omega*|1-t/CG.length (cgOperator A) g N| *‖cgCanonicalError A g N‖) := by
  let method := xrfcMethod fullMemory trial
  let H := oneGradientRun method (fun _ => cgOperator A) g (N+1)
  have hp := cgOperator_positive A hA
  have hpre (i : ℕ) (hi : i<N+1) : CG.gradient (cgOperator A) g i≠0 :=
    cg_nonstagnation A hA g i (by omega)
  have hterm := (xrfc_full_terminates A hA g trial (by simpa only [hN] using ht)).2.1
  rw [hN] at hterm
  have hc := xrfc_full_next_correction trial (cgOperator A) hp.1 hp.2 g (N+1) hpre ht N (Nat.lt_succ_self N)
  have hmax := solved_output_maximum A hA H.gradient (method.output H) hterm homega
  have hcn := congrArg (fun u => ‖cgOperator (metricRoot A) u‖) hc
  rw [last_correction_norm A hA g N hN] at hcn
  rw [hcn] at hmax
  simpa only [mul_assoc,OneGradientMethod.outputGradient] using hmax

/-- Actual direction-basis XRFC has the same exact attained physical full-cycle
output maximum, for every newest-retaining positive direction memory.
Use: in particular full-memory XRFC-D attains the one-gradient minimax formula
with the same final harmonic trial.
Article: main_krylov, thm:exact.
Proof: use the proved real direction-window executor's solution and its genuine
missed-line correction in the same physical attained output maximum. -/
theorem xrfcD_last_output_maximum (A : Matrix (Fin m) (Fin m) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin m)) (N : ℕ) (hN : referenceAtomCount A hA g=N+1)
    (memory : ℕ → ℕ) (trial : History (EuclideanSpace ℝ (Fin m)) → ℝ)
    (hm : ∀ i≤N+1,0 < i → 0 < memory i)
    (ht : ∀ i<N+1,trial (oneGradientRun (xrfcDMethod memory trial) (fun _ => cgOperator A) g i)≠0)
    {omega : ℝ} (homega : 0≤omega) :
    let method := xrfcDMethod memory trial
    let H := oneGradientRun method (fun _ => cgOperator A) g (N+1)
    let t := trial (oneGradientRun method (fun _ => cgOperator A) g N)
    IsGreatest {x : ℝ | ∃ B : Matrix (Fin m) (Fin m) ℝ,B.IsSymm ∧
      relativeBudget A (B-A)≤omega ∧ x=‖cgOperator (metricRoot A)⁻¹ (method.outputGradient (cgOperator B) H)‖}
      (omega*|1-t/CG.length (cgOperator A) g N| *‖cgCanonicalError A g N‖) := by
  let method := xrfcDMethod memory trial
  let H := oneGradientRun method (fun _ => cgOperator A) g (N+1)
  have hp := cgOperator_positive A hA
  have hpre (i : ℕ) (hi : i<N+1) : CG.gradient (cgOperator A) g i≠0 :=
    cg_nonstagnation A hA g i (by omega)
  have hterm := (xrfcD_terminates A hA g memory trial (by simpa only [hN] using hm)
    (by simpa only [hN] using ht)).2.1
  rw [hN] at hterm
  have hc := xrfcD_next_correction memory trial (cgOperator A) hp.1 hp.2 g (N+1) hpre hm ht N (Nat.lt_succ_self N)
  have hmax := solved_output_maximum A hA H.gradient (method.output H) hterm homega
  have hcn := congrArg (fun u => ‖cgOperator (metricRoot A) u‖) hc
  rw [last_correction_norm A hA g N hN] at hcn
  rw [hcn] at hmax
  simpa only [mul_assoc,OneGradientMethod.outputGradient] using hmax

end
end krylov.OneGradient
