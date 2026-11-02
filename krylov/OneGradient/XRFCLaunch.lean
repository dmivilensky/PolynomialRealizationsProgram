import krylov.OneGradient.XRFCProjector
set_option autoImplicit false
/-!
Article: main_krylov, prop:launch(b), actual full-cycle virtual-launch distance.
Use: identify the genuine evaluated endpoint error and exactly telescope the
original compression response into the printed measured trial amplitudes.
Source: actual quadratic XRFC termination and last output correction, genuine
metric-root CG energy dictionary and actual oblique-prefix synthesis.
-/

namespace krylov.OneGradient
noncomputable section
open Matrix krylov.Methods krylov.Reference krylov.Secant krylov.Stability krylov.Envelope
open scoped BigOperators
variable {n : ℕ}

/-- The actual canonical evaluated endpoint of a full XRFC reference cycle
has precisely the last-trial extrapolation error of the original source.
Use: the launch distance is derived from the original real executor rather
than supplied as an abstract vector with the desired coefficients.
Article: main_krylov, prop:launch(b), he=-a_(n-1) shat_(n-1).
Proof: actual quadratic termination makes the true evaluated gradient the
negative true reference operator on its last virtual correction. The genuine
missed-line root identity gives its printed original trial amplitude. -/
theorem xrfc_reference_launch_error
    (trial : History (EuclideanSpace ℝ (Fin n)) → ℝ)
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (hc : referenceAtomCount base hb g=n) (hn : 0<n)
    (ht : ∀ i<n,trial (oneGradientRun (xrfcMethod fullMemory trial) (fun _ => cgOperator base) g i)≠0) :
    let H := oneGradientRun (xrfcMethod fullMemory trial) (fun _ => cgOperator base) g n
    cgOperator (metricRoot base)⁻¹ H.gradient=
      -(xrfcTrialCoefficient trial base g n (n-1) • canonicalCGUnitStep base g (n-1)) := by
  let Q := cgOperator base
  let m := xrfcMethod fullMemory trial
  let H := oneGradientRun m (fun _ => Q) g n
  let tau := fun i => trial (oneGradientRun m (fun _ => Q) g i)
  let rho := CG.length Q g (n-1)-tau (n-1)
  have hp := cgOperator_positive base hb
  have hterm := (xrfc_full_terminates base hb g trial (fun i hi => ht i (by rw [← hc];exact hi))).2.1
  rw [hc] at hterm
  change H.gradient+Q (m.output H)=0 at hterm
  have hout := xrfc_full_next_correction trial Q hp.1 hp.2 g n
    (fun i hi => cg_nonstagnation base hb g i (by rw [hc];exact hi)) ht (n-1) (by omega)
  rw [show n-1+1=n by omega] at hout
  change m.output H=rho • CG.direction Q g (n-1) at hout
  have hgrad : H.gradient= -Q (rho • CG.direction Q g (n-1)) := by
    rw [hout] at hterm
    exact eq_neg_of_add_eq_zero_left hterm
  change cgOperator (metricRoot base)⁻¹ H.gradient=_
  rw [hgrad,map_neg]
  have hroot : cgOperator (metricRoot base)⁻¹ (Q (rho • CG.direction Q g (n-1)))=
      cgOperator (metricRoot base) (rho • CG.direction Q g (n-1)) := canonical_reference_action base hb _
  rw [hroot]
  have hline := canonical_missed_line base hb g (n-1) (by rw [hc];omega) rho
  change cgOperator (metricRoot base) (rho • CG.direction Q g (n-1))=_ at hline
  rw [hline]
  have htail : trialTailFactor tau (fun j => CG.length Q g j-tau j) n (n-1)=1 := by
    simp only [trialTailFactor,show n-1+1=n by omega,Finset.Ico_self,Finset.prod_empty,Nat.sub_self,pow_zero,one_mul]
  dsimp only [xrfcTrialCoefficient]
  change -((rho/CG.length Q g (n-1)*Real.sqrt (cgEnergy base g (n-1))) • canonicalCGUnitStep base g (n-1))=
    -((trialTailFactor tau (fun j => CG.length Q g j-tau j) n (n-1)*
      (rho/CG.length Q g (n-1))*Real.sqrt (cgEnergy base g (n-1))) • canonicalCGUnitStep base g (n-1))
  rw [htail,one_mul]

/-- The actual virtual-launch compression response is exactly the source's
step-basis XRFC amplitude sum for every real canonical increment family.
Use: this is the algebraic specialization of the general launch compression
formula to the true evaluated endpoint and actual chronological XRFC projectors.
Article: main_krylov, prop:launch(b), sum a_l Pi_l transpose E_l shat_l.
Proof: distribute the original genuine compressed matrix sum, substitute the
proved actual last-column amplitude identity and move the real scalar through
the true matrix actions. Vanishing amplitudes require no separate division. -/
theorem xrfc_virtual_launch_compressions
    (trial : History (EuclideanSpace ℝ (Fin n)) → ℝ)
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (hc : referenceAtomCount base hb g=n)
    (ht : ∀ i<n,trial (oneGradientRun (xrfcMethod fullMemory trial) (fun _ => cgOperator base) g i)≠0)
    (E : ℕ → Matrix (Fin n) (Fin n) ℝ) :
    let P := fun l => transportedFlag (xrfcCanonicalColumns trial base g) l
    let he := -(xrfcTrialCoefficient trial base g n (n-1) • canonicalCGUnitStep base g (n-1));
    -cgOperator (∑ l∈Finset.range n,(P l)ᵀ*E l*P l) he=
      ∑ l∈Finset.range n,xrfcTrialCoefficient trial base g n l •
        cgOperator (P l)ᵀ (cgOperator (E l) (canonicalCGUnitStep base g l)) := by
  dsimp only
  rw [map_neg,neg_neg]
  simp only [cgOperator,map_sum,_root_.sum_apply,map_mul,mul_apply_eq_comp]
  apply Finset.sum_congr rfl
  intro l hl
  have h := xrfc_projector_last_amplitude trial base hb g hc ht l (Finset.mem_range.mp hl)
  dsimp only [cgOperator] at h
  rw [h,map_smul,map_smul]

end
end krylov.OneGradient
