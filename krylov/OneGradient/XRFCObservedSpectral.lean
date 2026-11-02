import krylov.Completion.ObservedHarmonicTrial
import krylov.Completion.QuadraticObservedWindow
import krylov.OneGradient.XRFCOutputMaximum
set_option autoImplicit false
/-!
Article: main_krylov, cor:quant(a), one actual spectral-prior XRFC policy.
Use: implement one real history-only harmonic rule using the original
observed window and known class bounds, before the last gradient query.
Source: genuine native XRFC virtual CG/basis theorem and actual physical
observed curvature minimax; all inverse and feasibility domains are derived.
-/

namespace krylov.OneGradient
noncomputable section
open Matrix krylov.Reference krylov.Methods krylov.Completion krylov.Secant
open scoped InnerProductSpace
variable {m : ℕ}

/-- Original physical columns of the full observed XRFC step window.
Use: the prior policy receives only actually observed vectors.
Article: main_krylov, cor:quant(a). -/
def xrfcPriorColumns (H : History (EuclideanSpace ℝ (Fin m))) : Matrix (Fin m) (Fin H.pairs.length) ℝ :=
  fun i j => windowSteps H.pairs j i

/-- The actual XRFC virtual direction, computed solely from the old transcript.
Use: no unobserved last curvature enters the harmonic rule.
Article: main_krylov, cor:quant(a). -/
def xrfcPriorDirection (H : History (EuclideanSpace ℝ (Fin m))) : EuclideanSpace ℝ (Fin m) :=
  windowDirection H.pairs (virtualGradient H.pairs H.gradient)

/-- One original harmonic trial read from the actual observed full window.
Use: the same rule covers every reference in the known spectral prior.
Article: main_krylov, cor:quant(a). -/
def xrfcPriorHarmonic (mu upper : ℝ) (H : History (EuclideanSpace ℝ (Fin m))) : ℝ :=
  observedHarmonicTrial (xrfcPriorColumns H) (WithLp.ofLp (xrfcPriorDirection H)) (windowModel H.pairs)
    mu upper (-inner ℝ (virtualGradient H.pairs H.gradient) (xrfcPriorDirection H))

/-- One globally positive history-only spectral rule with arbitrary earlier
positive trials and the original observed harmonic rule at the final query.
Use: no representative reference or fibre-dependent constant is captured by
the policy. The harmless positive fallback totalizes infeasible histories.
Article: main_krylov, cor:quant(a). -/
def xrfcSpectralTrial (N : ℕ) (mu upper : ℝ)
    (earlier : History (EuclideanSpace ℝ (Fin m)) → ℝ) (H : History (EuclideanSpace ℝ (Fin m))) : ℝ :=
  if H.records.length=N then
    if 0 < xrfcPriorHarmonic mu upper H then xrfcPriorHarmonic mu upper H else 1
  else earlier H

/-- The actual original spectral trial policy is positive on every history.
Use: all genuine native XRFC basis and inverse domains follow automatically.
Article: main_krylov, cor:quant(a).
Proof: the earlier rule is positive; the last rule uses its positive observed
harmonic value on feasible data and the positive totalization elsewhere. -/
theorem xrfc_spectral_trial_positive (N : ℕ) (mu upper : ℝ)
    (earlier : History (EuclideanSpace ℝ (Fin m)) → ℝ) (he : ∀ H,0 < earlier H)
    (H : History (EuclideanSpace ℝ (Fin m))) : 0 < xrfcSpectralTrial N mu upper earlier H := by
  unfold xrfcSpectralTrial
  split_ifs with _ hh
  · exact hh
  · norm_num
  · exact he H

/-- The original observed harmonic rule has the true spectral trial bound on
every actual nonstagnating native XRFC reference history.
Use: one policy handles the whole original prior; its physical rank, new
direction, descent and completion domains are all proved from the actual run.
Article: main_krylov, cor:quant(a).
Proof: the genuine XRFC basis and virtual CG theorem identify its actual
window and direction. True CG descent is positive. The shared quadratic
window theorem supplies physical feasibility, and the original observed
harmonic matrix maximum bounds the actual reference's exact line. -/
theorem xrfc_prior_harmonic_reference_bound (A : Matrix (Fin m) (Fin m) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin m)) (N : ℕ) (hN : referenceAtomCount A hA g=N+1)
    (mu upper : ℝ) (hmu : 0 < mu) (hmuL : mu≤upper)
    (hlo : (A-mu • 1).PosSemidef) (hhi : (upper • 1-A).PosSemidef)
    (trial : History (EuclideanSpace ℝ (Fin m)) → ℝ)
    (ht : ∀ i<N,trial (oneGradientRun (xrfcMethod fullMemory trial) (fun _ => cgOperator A) g i)≠0) :
    let H := oneGradientRun (xrfcMethod fullMemory trial) (fun _ => cgOperator A) g N
    0 < xrfcPriorHarmonic mu upper H ∧
      |1-xrfcPriorHarmonic mu upper H/CG.length (cgOperator A) g N|≤(upper-mu)/(upper+mu) := by
  let Q := cgOperator A
  let method := xrfcMethod fullMemory trial
  let H := oneGradientRun method (fun _ => Q) g N
  let r := virtualGradient H.pairs H.gradient
  let d := xrfcPriorDirection H
  let S := xrfcPriorColumns H
  let q := -inner ℝ r d
  have hp := cgOperator_positive A hA
  have hpre (i : ℕ) (hi : i<N+1) : CG.gradient Q g i≠0 :=
    cg_nonstagnation A hA g i (by rw [hN];exact hi)
  have hb := xrfc_full_basis trial Q hp.1 hp.2 g N (fun i hi => hpre i (by omega)) ht N le_rfl
  obtain ⟨_,hr,hd⟩ := xrfc_full_reference trial Q hp.1 hp.2 g N
    (fun i hi => hpre i (by omega)) ht N le_rfl
  change r=CG.gradient Q g N at hr
  change d=CG.direction Q g N at hd
  have hi := CG.invariant Q hp.1 hp.2 g N (fun i hi => hpre i (by omega))
  have hq : 0 < q := by
    change 0 < -inner ℝ r d
    rw [hr,hd,real_inner_comm,hi.search_pair,neg_neg]
    exact sq_pos_of_pos (norm_pos_iff.mpr (hpre N (Nat.lt_succ_self N)))
  have hd0 : d≠0 := by
    intro hz
    have hh : q=0 := by simp only [q,hz,inner_zero_right,neg_zero]
    exact hq.ne' hh
  have hy : ∀ j,windowImages H.pairs j=Q (windowSteps H.pairs j) := fun j =>
    oneGradientRun_pairs_quadratic method Q g N (H.pairs.get j) (List.get_mem _ j)
  obtain ⟨hS,hnew,hfeasible⟩ := quadratic_observed_window_feasible H.pairs A hA mu upper hlo hhi r hy hb.1 hd0
  have hout := observed_harmonic_trial_bound S hS (WithLp.ofLp d) hnew (windowModel H.pairs)
    mu upper q hmu hmuL hq ⟨A,hfeasible⟩
  have hlen : physicalTrialLength (WithLp.ofLp d) q A=CG.length Q g N := by
    unfold physicalTrialLength
    rw [← Matrix.inner_toEuclideanCLM]
    change -inner ℝ r d/inner ℝ d (Q d)=CG.length Q g N
    rw [hr,hd]
    change -inner ℝ (CG.gradient Q g N) (CG.direction Q g N)/
      inner ℝ (CG.direction Q g N) (Q (CG.direction Q g N))=
      -inner ℝ (CG.direction Q g N) (CG.gradient Q g N)/
        inner ℝ (CG.direction Q g N) (Q (CG.direction Q g N))
    rw [real_inner_comm]
  have hbound := hout.2.2.1.2 ⟨A,hfeasible,rfl⟩
  change |1-xrfcPriorHarmonic mu upper H/physicalTrialLength (WithLp.ofLp d) q A|≤_ at hbound
  rw [hlen] at hbound
  exact ⟨hout.1,hbound.trans hout.2.2.2⟩

end
end krylov.OneGradient
