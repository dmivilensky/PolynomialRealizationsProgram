import krylov.OneGradient.DirectionTerminalJet
import krylov.OneGradient.CanonicalOperatorLine
import krylov.Envelope.TrialReplaySum
import krylov.Methods.XRFCBasisHistory
set_option autoImplicit false
/-!
Article: main_krylov, thm:I, actual complete direction-basis XRFC first variation.
Use: identify the genuine full varying-prefix native output derivative with
the printed original measured-amplitude response, without oblique flags.
Source: actual primitive direction replay calculus, real terminal native solve,
proved image-error jet recurrence, exact finite replay unrolling and genuine
positive-root/CG-energy normalization. No response or trajectory jet is assumed.
-/

namespace krylov.OneGradient
noncomputable section
open Matrix krylov.Methods krylov.Reference krylov.Secant krylov.Stability krylov.Envelope
open scoped BigOperators
variable {n : ℕ}

/-- The original full-memory direction-basis XRFC semantic output has exactly
the printed measured-amplitude first derivative on every primitive C1 physical
operator path through its genuine full-atom reference.
Use: the response contains the actual original E_l and no oblique projector;
all trial and trajectory regularity is derived from primitive observed charts.
Article: main_krylov, thm:I, direction-basis first variation.
Proof: true native terminal pairing reconstruction gives the actual newest
image-error output jet. Its genuine one-step replay recurrence unrolls into
the original signed later-trial factors. Actual complete quadratic histories
identify measured trials in both implementations; the true positive root and
CG energy dictionary normalize each physical increment into the printed sum. -/
theorem xrfc_direction_output_first_jet
    (trial : History (EuclideanSpace ℝ (Fin n)) → ℝ)
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (hc : referenceAtomCount base hb g=n) (hn : 0<n)
    (A : ℝ → ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hA : ∀ k,ContDiffAt ℝ 1 (fun t => A t k) 0) (hA0 : A 0=fun _ => cgOperator base)
    (ht : ∀ i<n,trial (oneGradientRun (xrfcDMethod fullMemory trial) (fun _ => cgOperator base) g i)≠0)
    (hT : ∀ k<n,ContDiffAt ℝ 1 (trialCoordinate trial k)
      (oneGradientData (xrfcDMethod fullMemory trial) (fun _ => cgOperator base) g k)) :
    let m := xrfcDMethod fullMemory trial
    let R := cgOperator (metricRoot base)⁻¹
    let E := fun l => R*(deriv (fun t => A t (l+1)) 0-deriv (fun t => A t l) 0)*R
    HasDerivAt (fun t => R (m.outputGradient (A t n) (oneGradientRun m (A t) g n)))
      (xrfcDirectionResponse trial base g E) 0 := by
  let Q := cgOperator base
  let m := xrfcDMethod fullMemory trial
  let R := cgOperator (metricRoot base)⁻¹
  let tau := fun j => trial (oneGradientRun (xrfcMethod fullMemory trial) (fun _ => Q) g j)
  let rho := fun j => CG.length Q g j-tau j
  let C := fun l => deriv (fun t => A t (l+1)) 0-deriv (fun t => A t l) 0
  let D := fun l => C l (CG.direction Q g l)
  let J := fun l => deriv (fun t => xrfcDImageError trial (A t) g l) 0
  let out := fun t => m.outputGradient (A t n) (oneGradientRun m (A t) g n)
  have hp := cgOperator_positive base hb
  have hpre (i : ℕ) (hi : i<n) : CG.gradient Q g i≠0 := cg_nonstagnation base hb g i (by rw [hc];exact hi)
  have hTau (k : ℕ) (hk : k≤n) : trial (oneGradientRun m (fun _ => Q) g k)=tau k :=
    congrArg trial (xrfc_quadratic_basis_histories_of_direction trial Q hp.1 hp.2 g n hpre ht k hk)
  have hJ0 : J 0=0 := xrfcD_image_error_zero_jet trial A hA Q hA0 hp.1 hp.2 g n hn hpre ht hT
  have hJ (k : ℕ) (hk : k+1<n) : J (k+1)=(rho k/tau (k+1)) • (D k-J k) := by
    have h := xrfcD_image_error_successor_jet trial A hA Q hA0 hp.1 hp.2 g n hpre ht hT k hk
    rw [hTau k (by omega),hTau (k+1) hk.le] at h
    exact h
  have hsum := trial_replay_response_sum tau rho D J n hJ0 hJ (n-1) (by omega)
  rw [show n-1+1=n by omega] at hsum
  have hterm := xrfcD_terminal_output_first_jet trial base hb g hc hn A hA hA0 ht hT
  dsimp only at hterm
  rw [hTau (n-1) (by omega)] at hterm
  have hraw : deriv out 0=∑ l∈Finset.range n,trialTailFactor tau rho n l • (rho l • D l) := by
    have hlast : deriv out 0=rho (n-1) • (D (n-1)-J (n-1)) := by
      change deriv out 0=rho (n-1) •
        ((deriv (fun t => A t (n-1+1)) 0-deriv (fun t => A t (n-1)) 0)
          (CG.direction Q g (n-1))-J (n-1))
      rw [show n-1+1=n by omega]
      exact hterm
    exact hlast.trans hsum
  have hout := (quadraticXRFCD_output_contDiffAt trial A (fun t => A t n) (fun _ => g) 0 hA (hA n)
    contDiffAt_const Q hA0 hp.1 hp.2 n hpre ht (by rw [hA0];exact hT)).2
  have hnorm := R.hasFDerivAt.comp_hasDerivAt 0 (hout.differentiableAt (by norm_num)).hasDerivAt
  change HasDerivAt (fun t => R (out t)) (R (deriv out 0)) 0 at hnorm
  rw [hraw,canonical_direction_response_sum trial base hb g hc C] at hnorm
  exact hnorm

end
end krylov.OneGradient
