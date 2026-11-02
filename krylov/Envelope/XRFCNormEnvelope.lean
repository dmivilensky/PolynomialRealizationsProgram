import krylov.Envelope.XRFCNormPairing
import krylov.Stability.CanonicalContinuity
set_option autoImplicit false
/-!
Article: main_krylov, thm:E1, genuine virtual-launch norm envelope and quadratic remainder.
Use: conclude the actual unevaluated XRFC canonical gradient norm expansion from primitive C-two trial charts before real active-spectrum exhaustion.
Source: genuine actual output regularity, proved full virtual frozen norm pairing and the existing weighted compact Taylor norm theorem.
-/

namespace krylov.Envelope
noncomputable section
open Matrix krylov.Methods krylov.Reference krylov.Secant krylov.Stability
open scoped BigOperators
variable {n : ℕ}

/-- The actual semantic unevaluated full-memory XRFC canonical gradient norm has the true virtual-launch first variation and a genuine weighted quadratic remainder on a real nonexhausted quadratic reference.
Use: The actual semantic unevaluated full-memory XRFC canonical gradient norm has the true virtual-launch first variation and a genuine weighted quadratic remainder on a real nonexhausted quadratic reference.
Article: main_krylov, thm:E1, genuine virtual-launch norm envelope and quadratic remainder.
Proof: Derive true output C-two regularity from primitive trial rules, identify its actual CG reference and virtual frozen derivative pairing, then apply the proved compact weighted norm Taylor theorem on the genuine reference singleton. -/
theorem xrfc_norm_envelope (trial : History (EuclideanSpace ℝ (Fin n)) → ℝ)
    (A : ℝ → ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (B : ℝ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef) (g : EuclideanSpace ℝ (Fin n)) (N : ℕ)
    (hcount : N<referenceAtomCount base hb g)
    (hA0 : A 0=fun _ => cgOperator base) (hB0 : B 0=cgOperator base)
    (hA : ∀ i,ContDiffAt ℝ 2 (fun t => A t i) 0) (hB : ContDiffAt ℝ 2 B 0)
    (ht : ∀ i<N,trial (oneGradientRun (xrfcMethod fullMemory trial) (fun _ => cgOperator base) g i)≠0)
    (hT : ∀ k<N,ContDiffAt ℝ 2 (trialCoordinate trial k)
      (oneGradientData (xrfcMethod fullMemory trial) (A 0) g k)) :
    let m := xrfcMethod fullMemory trial
    let R := Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base)⁻¹
    let e := cgCanonicalError base g N
    let e0 := ‖R g‖
    ∃ delta C : ℝ,0<delta ∧ 0≤C ∧ ∀ t : ℝ,|t|≤delta →
      |‖R (m.outputGradient (B t) (oneGradientRun m (A t) g N))‖-‖e‖-
        t*inner ℝ e (xrfcEnvelopeResponse trial A B base g N)/‖e‖|≤
        C*t^2*e0*(1+e0/‖e‖) := by
  dsimp only
  let m := xrfcMethod fullMemory trial
  let Q := cgOperator base
  let R := Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base)⁻¹
  let Phi := fun t => R (m.outputGradient (B t) (oneGradientRun m (A t) g N))
  let e := cgCanonicalError base g N
  let e0 := ‖R g‖
  have hp := cgOperator_positive base hb
  have hpre (i : ℕ) (hi : i≤N) : CG.gradient Q g i≠0 := cg_nonstagnation base hb g i (hi.trans_lt hcount)
  -- The true semantic output is C-two by real primitive execution, before any norm remainder is estimated.
  have hout := (quadraticXRFC_output_contDiffAt trial A B (fun _ => g) 0 hA hB contDiffAt_const
    Q hA0 hp.1 hp.2 N (fun i hi => hpre i hi.le) ht hT).2
  have hPhi : ContDiffAt ℝ 2 Phi 0 := R.contDiff.contDiffAt.comp 0 hout
  have hbase : Phi 0=e := by
    dsimp only [Phi]
    rw [hA0,hB0]
    have h := xrfc_virtual_output_balance trial (fun _ => Q) Q g N
    dsimp only at h
    have hz : virtualOutputDefect m (fun _ => Q) Q g N=0 := by simp [virtualOutputDefect]
    rw [hz,add_zero] at h
    rw [h]
    change R (virtualGradient (selectedWindow fullMemory (oneGradientRun m (fun _ => Q) g N))
      (oneGradientRun m (fun _ => Q) g N).gradient)=e
    rw [selectedWindow_full,(xrfc_full_reference trial Q hp.1 hp.2 g N (fun i hi => hpre i hi.le) ht N le_rfl).2.1]
    rfl
  have he0 : 0<e0 := canonical_error_pos base hb g (hpre 0 (Nat.zero_le N))
  have he : 0<‖e‖ := canonical_error_pos base hb (CG.gradient Q g N) (hpre N le_rfl)
  -- Use the actual weighted Taylor bound and retain the genuine remaining-error denominator before substituting the proved virtual first variation.
  obtain ⟨delta,C,hd,hC,hbound⟩ := compact_weighted_norm_variation Phi (fun _ => e0)
    ({0} : Set ℝ) isCompact_singleton (by intro x hx;simpa only [Set.mem_singleton_iff.mp hx] using hPhi)
    continuousOn_const (by intro _ _;exact he0)
  refine ⟨delta,C,hd,hC,?_⟩
  intro t ht'
  have h := hbound 0 (Set.mem_singleton 0) t (by simpa only [Real.norm_eq_abs] using ht') (by rw [hbase];exact he)
  have hpair := xrfc_norm_first_jet_pairing trial A B base hb g N hcount hA0 hB0 hA hB ht hT
  have hderiv : deriv Phi 0=R (deriv (fun t => m.outputGradient (B t) (oneGradientRun m (A t) g N)) 0) :=
    (R.hasFDerivAt.comp_hasDerivAt 0 (hout.differentiableAt (by norm_num)).hasDerivAt).deriv
  have hinner : inner ℝ e (deriv Phi 0)=inner ℝ e (xrfcEnvelopeResponse trial A B base g N) := by
    rw [hderiv]
    exact hpair
  simpa only [zero_add,hbase,fderiv_eq_smul_deriv,real_inner_smul_right,hinner,Real.norm_eq_abs,sq_abs] using h
end
end krylov.Envelope
