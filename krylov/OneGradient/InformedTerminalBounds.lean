import krylov.OneGradient.InformedDirectionError
import krylov.Stability.ContDiffXRFC
set_option autoImplicit false
/-!
Article: main_krylov, thm:local(a), genuine informed terminal launch bounds.
Use: derive the actual last evaluated gradient's first-order vanishing in
both native bases from primitive data, before the full second-order output.
Source: exact informed reference CG trial, actual quadratic termination,
true S/D reference histories and primitive native C-one execution calculus.
-/

namespace krylov.OneGradient
noncomputable section
open krylov.Methods krylov.Reference krylov.Stability
open Filter Topology Asymptotics
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {n : ℕ}

/-- The actual full-cycle informed last evaluated gradient vanishes at
the true known quadratic reference in either original native basis.
Use: the genuine incoming gradient has zero reference value, rather than
only a postulated small launch residual or an unevaluated-output zero.
Article: main_krylov, thm:local(a).
Proof: the original informed last trial equals the actual CG length, so
the genuine last virtual correction is zero. Actual quadratic full-cycle
termination then makes the real last evaluated gradient zero. The proved
true S/D history identity transfers the same real gradient to either basis. -/
theorem informed_terminal_gradient_zero (directions : Bool)
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (hc : referenceAtomCount base hb g=n) (hn : 0< n) :
    oneGradientGradient (xrfcBasisMethod directions (informedTrial (cgOperator base)))
      (fun _ => cgOperator base) g n=0 := by
  let trial := informedTrial (cgOperator base)
  have hp := cgOperator_positive base hb
  have hpre : ∀ i< n,CG.gradient (cgOperator base) g i≠0 :=
    fun i hi => cg_nonstagnation base hb g i (by rw [hc];exact hi)
  have ht : ∀ i< n,trial (oneGradientRun (xrfcMethod fullMemory trial) (fun _ => cgOperator base) g i)≠0 :=
    fun _ _ => (informed_trial_positive (cgOperator base) _).ne'
  have hout := xrfc_full_next_correction trial (cgOperator base) hp.1 hp.2 g n hpre ht (n-1) (by omega)
  rw [show n-1+1=n by omega] at hout
  have hcal := (informed_trial_step_reference (cgOperator base) hp.1 hp.2 g n hpre (n-1) (by omega)).2
  change (xrfcMethod fullMemory trial).output (oneGradientRun (xrfcMethod fullMemory trial) (fun _ => cgOperator base) g n)=_ at hout
  change trial (oneGradientRun (xrfcMethod fullMemory trial) (fun _ => cgOperator base) g (n-1))=CG.length (cgOperator base) g (n-1) at hcal
  rw [hcal,sub_self,zero_smul] at hout
  have hterm := (xrfc_full_terminates base hb g trial (fun _ _ => (informed_trial_positive (cgOperator base) _).ne')).2.1
  rw [hc] at hterm
  change (oneGradientRun (xrfcMethod fullMemory trial) (fun _ => cgOperator base) g n).gradient+
    cgOperator base ((xrfcMethod fullMemory trial).output (oneGradientRun (xrfcMethod fullMemory trial) (fun _ => cgOperator base) g n))=0 at hterm
  rw [hout,map_zero,add_zero] at hterm
  cases directions with
  | false => exact hterm
  | true =>
    change (oneGradientRun (xrfcDMethod fullMemory trial) (fun _ => cgOperator base) g n).gradient=0
    rw [xrfc_quadratic_basis_histories trial (cgOperator base) hp.1 hp.2 g n hpre ht n le_rfl]
    exact hterm

/-- The actual full-cycle informed last evaluated gradient has first
order in the full perturbation parameter in either native basis, with
every real trial chart and reference execution domain derived.
Use: the native quadratic image/model errors contribute only cubic order
when applied to this real incoming gradient in the known-base expansion.
Article: main_krylov, thm:local(a).
Proof: true informed coefficient charts give genuine primitive C-one
execution regularity. The proved actual evaluated-gradient zero turns
the standard differentiability increment bound into first-order vanishing. -/
theorem informed_terminal_gradient_first_order (directions : Bool)
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (hc : referenceAtomCount base hb g=n) (hn : 0< n)
    (A : X → ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hA : ∀ i,ContDiffAt ℝ 1 (fun z => A z i) 0)
    (hA0 : A 0=fun _ => cgOperator base) :
    (fun z => oneGradientGradient (xrfcBasisMethod directions (informedTrial (cgOperator base))) (A z) g n)
      =O[𝓝 0] (fun z => ‖z‖) := by
  let trial := informedTrial (cgOperator base)
  have hp := cgOperator_positive base hb
  have hpre : ∀ i< n,CG.gradient (cgOperator base) g i≠0 :=
    fun i hi => cg_nonstagnation base hb g i (by rw [hc];exact hi)
  have hreg : ContDiffAt ℝ 1 (fun z => oneGradientGradient (xrfcBasisMethod directions trial) (A z) g n) 0 := by
    cases directions with
    | false =>
      exact (quadraticXRFC_prefix_contDiffAt trial A (fun _ => g) 0 hA contDiffAt_const
        (cgOperator base) hA0 hp.1 hp.2 n hpre
        (fun _ _ => (informed_trial_positive (cgOperator base) _).ne') (fun i hi => by
          rw [hA0]
          exact informed_trial_reference_contDiff false base hb base hb g n hpre i hi 1)).1 n le_rfl
    | true =>
      exact (quadraticXRFCD_prefix_contDiffAt trial A (fun _ => g) 0 hA contDiffAt_const
        (cgOperator base) hA0 hp.1 hp.2 n hpre
        (fun _ _ => (informed_trial_positive (cgOperator base) _).ne') (fun i hi => by
          rw [hA0]
          exact informed_trial_reference_contDiff true base hb base hb g n hpre i hi 1)).1 n le_rfl
  have hz : oneGradientGradient (xrfcBasisMethod directions trial) (A 0) g n=0 := by
    rw [hA0]
    exact informed_terminal_gradient_zero directions base hb g hc hn
  simpa only [hz,sub_zero] using (hreg.differentiableAt (by norm_num)).isBigO_sub.norm_right

end
end krylov.OneGradient
