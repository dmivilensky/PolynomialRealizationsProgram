import krylov.OneGradient.XRFCColumns
set_option autoImplicit false
/-!
Article: main_krylov, apE:Pi and prop:launch(b), genuine virtual-launch telescoping.
Use: prove the original endpoint projector/amplitude identity on the actual
full-memory XRFC trajectory, including exact or zero-error reference trials.
Source: actual chronological virtual weights, real prefix selection, genuine
CG energy normalization and original signed later-correction products.
-/

namespace krylov.OneGradient
noncomputable section
open Matrix krylov.Methods krylov.Reference krylov.Secant krylov.Stability krylov.Envelope
open scoped BigOperators
variable {n : ℕ}

/-- The genuine metric-root image of a missed reference line is its true
relative missed length times the original square-root energy and unit CG step.
Use: no division by a trial error or an amplitude is needed in the projector identities.
Article: main_krylov, apE:Pi.
Proof: specialize the proved canonical increment dictionary to the actual identity
increment; the genuine positive root square and inverse cancel exactly. -/
theorem canonical_missed_line (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (k : ℕ) (hk : k<referenceAtomCount base hb g) (rho : ℝ) :
    cgOperator (metricRoot base) (rho • CG.direction (cgOperator base) g k)=
      (rho/CG.length (cgOperator base) g k*Real.sqrt (cgEnergy base g k)) • canonicalCGUnitStep base g k := by
  have h := canonical_missed_direction_action base hb g k hk rho 1
  rw [Matrix.mul_one,metricRoot_square base hb,canonical_reference_action base hb] at h
  simpa only [cgOperator,map_one,one_apply_eq_self] using h

/-- The actual weighted prefix of canonical evaluated XRFC steps is exactly
its printed true trial amplitude times the actual unit CG step.
Use: connect the source's amplitude products to genuine oblique prefix coordinates.
Article: main_krylov, apE:Pi.
Proof: apply the actual metric root to the already proved physical weighted-prefix
identity, then use the actual positive CG line and square-root energy dictionary. -/
theorem xrfc_canonical_weighted_prefix (trial : History (EuclideanSpace ℝ (Fin n)) → ℝ)
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef) (g : EuclideanSpace ℝ (Fin n))
    (N : ℕ) (hcount : N≤referenceAtomCount base hb g)
    (ht : ∀ i<N,trial (oneGradientRun (xrfcMethod fullMemory trial) (fun _ => cgOperator base) g i)≠0)
    (l : ℕ) (hl : l<N) :
    let m := xrfcMethod fullMemory trial
    let tau := fun j => trial (oneGradientRun m (fun _ => cgOperator base) g j)
    let rho := fun j => CG.length (cgOperator base) g j-tau j
    (∑ i∈Finset.range (l+1),trialWeightAt (fun j => rho j/tau j) N i •
      cgOperator (metricRoot base) (oneGradientStep m (fun _ => cgOperator base) g i))=
      xrfcTrialCoefficient trial base g N l • canonicalCGUnitStep base g l := by
  have hp := cgOperator_positive base hb
  have h := xrfc_reference_weighted_prefix trial (cgOperator base) hp.1 hp.2 g N
    (fun i hi => cg_nonstagnation base hb g i (hi.trans_le hcount)) ht N l le_rfl hl
  dsimp only at h ⊢
  have he := congrArg (cgOperator (metricRoot base)) h
  rw [map_sum] at he
  simp only [map_smul] at he
  rw [← map_smul (cgOperator (metricRoot base))] at he
  rw [canonical_missed_line base hb g l (hl.trans_le hcount)] at he
  simpa only [smul_smul,mul_assoc,xrfcTrialCoefficient] using he

/-- The actual full-cycle oblique old flag selects its genuine chronological
weighted prefix, with every inverse domain derived from the original execution.
Use: apply the real source projector to the true last virtual correction.
Article: main_krylov, apE:Pi.
Proof: the canonical column matrix is truly nonsingular. Its transported
selector keeps exactly the actual prefix columns, and the finite selected
chronological sum is the original prefix sum. -/
theorem xrfc_projector_weighted_prefix (trial : History (EuclideanSpace ℝ (Fin n)) → ℝ)
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef) (g : EuclideanSpace ℝ (Fin n))
    (hc : referenceAtomCount base hb g=n)
    (ht : ∀ i<n,trial (oneGradientRun (xrfcMethod fullMemory trial) (fun _ => cgOperator base) g i)≠0)
    (l : ℕ) (hl : l<n) (w : ℕ → ℝ) :
    let m := xrfcMethod fullMemory trial
    let P := transportedFlag (xrfcCanonicalColumns trial base g) l
    cgOperator P (∑ i∈Finset.range n,w i •
      cgOperator (metricRoot base) (oneGradientStep m (fun _ => cgOperator base) g i))=
      ∑ i∈Finset.range (l+1),w i •
        cgOperator (metricRoot base) (oneGradientStep m (fun _ => cgOperator base) g i) := by
  let m := xrfcMethod fullMemory trial
  let T := xrfcCanonicalColumns trial base g
  have hT := (xrfc_columns_nonsingular trial base hb g hc ht).2
  dsimp only
  rw [map_sum]
  have he : (∑ i∈Finset.range n,cgOperator (transportedFlag T l)
      (w i • cgOperator (metricRoot base) (oneGradientStep m (fun _ => cgOperator base) g i)))=
      ∑ i∈Finset.range n,if i≤l then w i •
        cgOperator (metricRoot base) (oneGradientStep m (fun _ => cgOperator base) g i) else 0 := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [map_smul]
    have hc' := transported_flag_column T hT l ⟨i,Finset.mem_range.mp hi⟩
    rw [xrfc_canonical_column] at hc'
    rw [hc']
    split_ifs
    · rfl
    · simp only [smul_zero]
  change _=_ at he
  rw [he,← Finset.sum_filter]
  have hf : (Finset.range n).filter (fun i => i≤l)=Finset.range (l+1) := by
    ext i
    simp only [Finset.mem_filter,Finset.mem_range]
    omega
  rw [hf]

/-- The actual oblique XRFC projector and genuine printed trial amplitudes
satisfy the original last-column telescoping identity without any nonzero-error premise.
Use: obtain the source's virtual-launch response even when some exact trials
make intermediate or final amplitudes vanish.
Article: main_krylov, apE:Pi, a_(n-1) Pi_l shat_(n-1)=a_l shat_l.
Proof: synthesize the actual last virtual correction in the original true
canonical step basis, select its real chronological prefix and use the proved
weighted-prefix amplitude identity. Only original nonzero trials are divided by. -/
theorem xrfc_projector_last_amplitude (trial : History (EuclideanSpace ℝ (Fin n)) → ℝ)
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef) (g : EuclideanSpace ℝ (Fin n))
    (hc : referenceAtomCount base hb g=n)
    (ht : ∀ i<n,trial (oneGradientRun (xrfcMethod fullMemory trial) (fun _ => cgOperator base) g i)≠0)
    (l : ℕ) (hl : l<n) :
    let P := transportedFlag (xrfcCanonicalColumns trial base g) l
    cgOperator P (xrfcTrialCoefficient trial base g n (n-1) • canonicalCGUnitStep base g (n-1))=
      xrfcTrialCoefficient trial base g n l • canonicalCGUnitStep base g l := by
  let m := xrfcMethod fullMemory trial
  let tau := fun j => trial (oneGradientRun m (fun _ => cgOperator base) g j)
  let rho := fun j => CG.length (cgOperator base) g j-tau j
  let w := trialWeightAt (fun j => rho j/tau j) n
  have hcount : n≤referenceAtomCount base hb g := hc.symm.le
  have hlast := xrfc_canonical_weighted_prefix trial base hb g n hcount ht (n-1) (by omega)
  have hpref := xrfc_canonical_weighted_prefix trial base hb g n hcount ht l hl
  have hselect := xrfc_projector_weighted_prefix trial base hb g hc ht l hl w
  dsimp only at hlast hpref hselect ⊢
  rw [show n-1+1=n by omega] at hlast
  rw [← hlast,← hpref]
  exact hselect

end
end krylov.OneGradient
