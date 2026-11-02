import krylov.OneGradient.ObservedPriorHarmonic
import krylov.OneGradient.XRFCTwoBasisOutput
import krylov.Methods.DirectionInformation
set_option autoImplicit false
/-!
Article: main_krylov, cor:quant, uniform known-prior harmonic attainment.
Use: one genuine history-only policy attains the sharp guarantee on every
physical fibre meeting the known prior, in either implemented XRFC basis.
Source: actual observed prior endpoint dictionary, true complete-history
nonanticipation, physical reciprocal-pivot interval and native output maximum.
-/

namespace krylov.OneGradient
noncomputable section
open Matrix krylov.Reference krylov.Methods krylov.Secant
variable {n : ℕ}

/-- The single original known-prior endpoint policy is the exact harmonic
trial on the whole original physical information interval and attains its
true sharp output guarantee in either native XRFC basis.
Use: the same method is chosen before the original reference and information
fibre. Only known prior membership and genuine observed history enter its
decisions; arbitrary earlier positive observed trials remain allowed.
Article: main_krylov, cor:quant.
Proof: the actual reference transcript determines the true prior endpoints.
All original completions give the identical complete incoming history before
the last query, so the one implemented decision equals the same actual
harmonic trial everywhere on the fibre. Genuine last CG lengths lie in the
real reciprocal interval; scalar equioscillation and the shared two-basis
physical output theorem prove the original normalized scenario bound. -/
theorem xrfc_observed_prior_fibre_upper (directions : Bool)
    (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin (n+1))) (hg : g≠0)
    (hc : (activeSpectralValues A hA.1 g).card=n+1)
    (prior : Set (Matrix (Fin (n+1)) (Fin (n+1)) ℝ)) (lo hi : ℝ)
    (hlo : lastJacobiPivot A hA g hg hc-(lastInversePivot A hA g hg hc)⁻¹ < lo)
    (horder : lo≤hi)
    (hprior : ∀ b : ℝ,lanczosCompletion A hA g hg hc b∈prior ↔ b∈Set.Icc lo hi)
    (earlier : History (EuclideanSpace ℝ (Fin (n+1))) → ℝ) (he : ∀ H,0 < earlier H)
    {omega : ℝ} (homega : 0≤omega) :
    let sigma := lastJacobiPivot A hA g hg hc-(lastInversePivot A hA g hg hc)⁻¹
    let trial := observedPriorLastTrial n prior earlier
    let method := xrfcBasisMethod directions trial
    ∀ b∈Set.Icc lo hi,∀ B : Matrix (Fin (n+1)) (Fin (n+1)) ℝ,B.IsSymm →
      relativeBudget (lanczosCompletion A hA g hg hc b)
        (B-lanczosCompletion A hA g hg hc b)≤omega →
      fibreScenarioError A hA g hg hc method b B≤
        omega*intervalMinimaxValue (1/(hi-sigma)) (1/(lo-sigma)) := by
  let Q := cgOperator A
  let sigma := lastJacobiPivot A hA g hg hc-(lastInversePivot A hA g hg hc)⁻¹
  let trial := observedPriorLastTrial n prior earlier
  let mS := xrfcMethod fullMemory trial
  let H := oneGradientRun mS (fun _ => Q) g n
  have ht (K : History (EuclideanSpace ℝ (Fin (n+1)))) : trial K≠0 :=
    (observed_prior_last_trial_positive n prior earlier he K).ne'
  have hraw := xrfc_observed_prior_harmonic A hA g hg hc trial (fun _ _ => ht _)
    prior lo hi hlo horder hprior
  have htrialA : trial H=harmonicTrial (1/(hi-sigma)) (1/(lo-sigma)) := by
    change observedPriorLastTrial n prior earlier H=_
    rw [observedPriorLastTrial,oneGradientRun_length,ite_eq_left rfl,ite_eq_left hraw.1]
    exact hraw.2
  have ha : 0 < 1/(hi-sigma) := one_div_pos.mpr (sub_pos.mpr (hlo.trans_le horder))
  have hab : 1/(hi-sigma)≤1/(lo-sigma) :=
    one_div_le_one_div_of_le (sub_pos.mpr hlo) (sub_le_sub_right horder sigma)
  dsimp only
  intro b hb B hB hbudget
  let C := lanczosCompletion A hA g hg hc b
  have hC : C.PosDef := (lanczos_completion_positive_iff A hA g hg hc b).mpr (hlo.trans_le hb.1)
  have hcount := completion_full_atoms A hA g hg hc b hC
  have hhistory : oneGradientRun mS (fun _ => cgOperator C) g n=H :=
    one_gradient_information_history mS (xrfcMethod_spanRestricted fullMemory trial) Q (cgOperator C) g n
      (lanczos_completion_information A hA g hg hc b) n le_rfl
  have hscalar := trial_error_le_endpoints ha
    (fibre_length_interval A hA g hg hc lo hi b hlo hb).1
    (fibre_length_interval A hA g hg hc lo hi b hlo hb).2
    (harmonicTrial (1/(hi-sigma)) (1/(lo-sigma)))
  rw [(harmonic_trial_attains ha hab).2] at hscalar
  have hlast : |1-trial (oneGradientRun mS (fun _ => cgOperator C) g n)/CG.length (cgOperator C) g n|≤
      intervalMinimaxValue (1/(hi-sigma)) (1/(lo-sigma)) := by
    rw [hhistory,htrialA]
    exact hscalar
  have hout := xrfc_two_basis_output_upper directions C hC g n hcount trial ht
    (intervalMinimaxValue (1/(hi-sigma)) (1/(lo-sigma))) hlast homega B hB hbudget
  change ‖cgOperator (metricRoot C)⁻¹ ((xrfcBasisMethod directions trial).outputGradient (cgOperator B)
    (oneGradientRun (xrfcBasisMethod directions trial) (fun _ => cgOperator C) g (n+1)))‖/‖cgCanonicalError C g n‖≤
      omega*intervalMinimaxValue (1/(hi-sigma)) (1/(lo-sigma))
  simpa only [mul_comm] using hout

end
end krylov.OneGradient
