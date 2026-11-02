import krylov.OneGradient.SchurHarmonic
import krylov.Cancellation.DCSchurReferenceRegularity
import krylov.Completion.PhysicalBandForms
set_option autoImplicit false
/-!
Article: main_krylov, thm:radau and lem:U(d), native harmonic reference domains.
Use: derive the actual continued harmonic policy's smooth primitive chart
from genuine quadratic XRFC observations, including physical class endpoints.
Source: actual virtual CG geometry, strict proper-Krylov pencils and original
physical feasibility; no policy or trajectory regularity is assumed. -/

namespace krylov.OneGradient
noncomputable section
open Matrix krylov.Methods krylov.Reference krylov.Stability krylov.Completion krylov.Cancellation
open scoped InnerProductSpace
variable {n : ℕ}

/-- Genuine quadratic full-window observations provide every actual
primitive domain of the virtual-direction harmonic Schur trial.
Use: native harmonic regularity requires no additional determinant or endpoint
positivity hypotheses, even at physical spectral endpoints.
Article: main_krylov, thm:radau and lem:U(d).
Proof: the actual virtual solve gives the genuine active CG direction.
The true physical window is feasible and its old flag has strictly interior
Ritz values. Exact getter coordinates transfer all derived positive domains
to the original primitive history chart. -/
theorem xrfc_schur_actual_chart_domain
    (H : History (EuclideanSpace ℝ (Fin n)))
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (k : ℕ) (hpre : ∀ i<k+1,CG.gradient (cgOperator base) g i≠0)
    (mu upper : ℝ) (hmu : 0<mu) (hmuL : mu≤upper)
    (hlo : (base-mu • 1).PosSemidef) (hhi : (upper • 1-base).PosSemidef)
    (hloform : ∀ v : EuclideanSpace ℝ (Fin n),mu*‖v‖^2≤ inner ℝ v (cgOperator base v))
    (hhiform : ∀ v : EuclideanSpace ℝ (Fin n),inner ℝ v (cgOperator base v)≤upper*‖v‖^2)
    (hbal : H.gradient=g+cgOperator base H.displacement)
    (hy : ∀ j,windowImages H.pairs j=cgOperator base (windowSteps H.pairs j))
    (hLI : LinearIndependent ℝ (windowSteps H.pairs)) (hspan : pairSpan H.pairs=directionFlag (cgOperator base) g k) :
    xrfcSchurChartDomain H.queryShape (observedArray H.observationList.length H.observationList) mu upper := by
  have hflag : ∀ j,windowSteps H.pairs j∈directionFlag (cgOperator base) g k := by
    intro j
    rw [← hspan]
    exact Submodule.subset_span ⟨j,rfl⟩
  let shape := H.queryShape
  let data := observedArray H.observationList.length H.observationList
  let p := min (fullMemory shape.length) shape.length
  let W := H.pairs
  let s := chartSteps fullMemory shape data
  let y := chartImages fullMemory shape data
  let T := pairModel s y
  let S : Matrix (Fin n) (Fin p) ℝ := fun a i => s i a
  let gv := chartGradient shape data+combine y (modelCoefficients s T (chartGradient shape data))
  let d := WithLp.ofLp (conjugacyDirection s y gv)
  have hW : chartWindow fullMemory shape data=W := by
    dsimp only [chartWindow,shape,data]
    rw [ofFn_observedArray,historyFromObservations_actual,selectedWindow_full]
  have hlen : W.length=p := by rw [← hW];exact chartWindow_length fullMemory shape data
  have hs : s=(fun i : Fin p => (W.getD i.val (0,0)).1) := by
    funext i
    dsimp only [s,chartSteps]
    rw [hW]
  have hyc : y=(fun i : Fin p => (W.getD i.val (0,0)).2) := by
    funext i
    dsimp only [y,chartImages]
    rw [hW]
  have hsW : windowSteps W=s ∘ finCongr hlen := by
    rw [hs]
    exact windowSteps_getD_array W p hlen
  have hyW : windowImages W=y ∘ finCongr hlen := by
    rw [hyc]
    exact windowImages_getD_array W p hlen
  have hsa : LinearIndependent ℝ s := by
    have h := hLI.comp (finCongr hlen).symm (finCongr hlen).symm.injective
    rw [hsW] at h
    simpa only [Function.comp_def,Equiv.apply_symm_apply] using h
  have hya : y=fun i => cgOperator base (s i) := by
    funext i
    have h := hy ((finCongr hlen).symm i)
    rw [hsW,hyW] at h
    simpa only [Function.comp_apply,Equiv.apply_symm_apply] using h
  have hfa (i : Fin p) : s i∈directionFlag (cgOperator base) g k := by
    have h := hflag ((finCongr hlen).symm i)
    rw [hsW] at h
    simpa only [Function.comp_apply,Equiv.apply_symm_apply] using h
  have hp := cgOperator_positive base hb
  have hT : T=crossGram (fun i => cgOperator base (s i)) s := by
    dsimp only [T]
    rw [hya,pairModel_quadratic s (cgOperator base) hp.1]
    ext i j
    exact (hp.1 (s i) (s j)).symm
  have hmodel := operatorGram_posDef (cgOperator base) hp.1 hp.2 hsa
  have hshifts := proper_directionFlag_gram_shifts (cgOperator base) hp.1 hp.2 g k hpre mu upper
    hloform hhiform s hsa hfa
  have hG : Sᵀ*S=crossGram s s := by
    ext i j
    change (∑ a : Fin n,s i a*s j a)=inner ℝ (s i) (s j)
    rw [real_inner_comm]
    rfl
  have hgrad : chartGradient shape data=H.gradient := by
    dsimp only [chartGradient,shape,data]
    rw [ofFn_observedArray,historyFromObservations_actual]
  have hv := virtual_reference_basis H (cgOperator base) hp.1 hp.2 g k
    (fun i hi => hpre i (by omega)) hbal hy hLI hspan
  have hgv : virtualGradient W H.gradient=gv := by
    rw [← hgrad]
    exact (virtualWindow_coordinates W hlen s y hsW hyW (chartGradient shape data)).2
  have hdir : xrfcPriorDirection H=d := by
    unfold xrfcPriorDirection
    rw [hgv,windowDirection_getD_array W _ hlen,← hs,← hyc]
  have hd0 : windowDirection W (virtualGradient W H.gradient)≠0 := by
    rw [hv.2.2]
    exact (CG.invariant_line_pos (cgOperator base) hp.2 g k
      (CG.invariant (cgOperator base) hp.1 hp.2 g k (fun i hi => hpre i (by omega))) (hpre k (by omega))).1
  have hphys := quadratic_observed_window_feasible W base hb mu upper hlo hhi
    (virtualGradient W H.gradient) hy hLI hd0
  have hproper := proper_observed_window_pencils W base hb g k hpre mu upper hloform hhiform hy hLI hflag
  have hC := Set.nonempty_of_mem hphys.2.2
  have hend := observed_endpoints_schur_extension _ hphys.1 _ hphys.2.1 _ mu upper hmu hmuL
    hproper.1 hproper.2 hC
  have hrange := observed_window_curvature_range _ hphys.1 _ hphys.2.1 _ mu upper hmu hmuL hC
  have hlow : 0<schurLowerCurvature (xrfcPriorColumns H) (xrfcPriorDirection H)
      (windowModel W) mu := hend.1 ▸ hrange.1
  have hhigh : 0<schurUpperCurvature (xrfcPriorColumns H) (xrfcPriorDirection H)
      (windowModel W) upper := hend.2 ▸ hrange.1.trans_le hrange.2.1
  have hcast := schur_endpoints_window_coordinates W p hlen (xrfcPriorDirection H) mu upper
  dsimp only at hcast
  change 0<schurLowerCurvature (fun a j => windowSteps W j a)
    (xrfcPriorDirection H) (windowModel W) mu at hlow
  change 0<schurUpperCurvature (fun a j => windowSteps W j a)
    (xrfcPriorDirection H) (windowModel W) upper at hhigh
  rw [hcast.1] at hlow
  rw [hcast.2] at hhigh
  rw [← hs,← hyc,hdir] at hlow hhigh
  have hSc : (fun a (j : Fin p) => (W.getD j.val (0,0)).1 a)=S := by
    ext a j
    exact congrArg (fun v : EuclideanSpace ℝ (Fin n) => v a) (congrFun hs j).symm
  rw [hSc] at hlow hhigh
  change T.det≠0 ∧ (crossGram y s).det≠0 ∧ (T-mu • (Sᵀ*S)).det≠0 ∧
    (upper • (Sᵀ*S)-T).det≠0 ∧ 0<schurLowerCurvature S d T mu ∧ 0<schurUpperCurvature S d T upper
  refine ⟨?_,?_,?_,?_,hlow,hhigh⟩
  · rw [hT]
    exact hmodel.det_pos.ne'
  · rw [hya]
    exact hmodel.det_pos.ne'
  · rw [hT,hG]
    exact hshifts.1.det_pos.ne'
  · rw [hT,hG]
    exact hshifts.2.det_pos.ne'

/-- On every genuine active quadratic history, the smooth virtual-direction
continuation equals the original observed harmonic trial and is positive.
Use: the continuation preserves the true physical minimax choice, including
collapsed feasible intervals and physical class endpoint references.
Article: main_krylov, thm:radau and cor:quant(a).
Proof: actual virtual CG geometry derives the nonzero new direction and its
positive descent pairing. The genuine feasible window and strict proper-flag
pencils identify both real endpoints; original harmonic minimax gives positivity. -/
theorem xrfc_schur_actual_reference_values
    (H : History (EuclideanSpace ℝ (Fin n)))
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (k : ℕ) (hpre : ∀ i<k+1,CG.gradient (cgOperator base) g i≠0)
    (mu upper : ℝ) (hmu : 0<mu) (hmuL : mu≤upper)
    (hlo : (base-mu • 1).PosSemidef) (hhi : (upper • 1-base).PosSemidef)
    (hbal : H.gradient=g+cgOperator base H.displacement)
    (hy : ∀ j,windowImages H.pairs j=cgOperator base (windowSteps H.pairs j))
    (hLI : LinearIndependent ℝ (windowSteps H.pairs)) (hspan : pairSpan H.pairs=directionFlag (cgOperator base) g k) :
    xrfcSchurHarmonic mu upper H=xrfcPriorHarmonic mu upper H ∧ 0<xrfcSchurHarmonic mu upper H := by
  have hp := cgOperator_positive base hb
  have hv := virtual_reference_basis H (cgOperator base) hp.1 hp.2 g k
    (fun i hi => hpre i (by omega)) hbal hy hLI hspan
  have hInv := CG.invariant (cgOperator base) hp.1 hp.2 g k (fun i hi => hpre i (by omega))
  have hd0 : windowDirection H.pairs (virtualGradient H.pairs H.gradient)≠0 := by
    rw [hv.2.2]
    exact (CG.invariant_line_pos (cgOperator base) hp.2 g k hInv (hpre k (by omega))).1
  have hq : 0 < -inner ℝ (virtualGradient H.pairs H.gradient) (xrfcPriorDirection H) := by
    change 0 < -inner ℝ (virtualGradient H.pairs H.gradient)
      (windowDirection H.pairs (virtualGradient H.pairs H.gradient))
    rw [hv.2.2,hv.2.1,real_inner_comm,hInv.search_pair,neg_neg]
    exact sq_pos_of_pos (norm_pos_iff.mpr (hpre k (by omega)))
  have hform := physical_band_operator_forms base mu upper hlo hhi
  have hf : ∀ j,windowSteps H.pairs j∈directionFlag (cgOperator base) g k := by
    intro j
    rw [← hspan]
    exact Submodule.subset_span ⟨j,rfl⟩
  have hproper := proper_observed_window_pencils H.pairs base hb g k hpre mu upper hform.1 hform.2 hy hLI hf
  have hphys := quadratic_observed_window_feasible H.pairs base hb mu upper hlo hhi
    (virtualGradient H.pairs H.gradient) hy hLI hd0
  have hC := Set.nonempty_of_mem hphys.2.2
  have he := (observed_rules_schur_extension _ hphys.1 _ hphys.2.1 _ mu upper (-inner ℝ (virtualGradient H.pairs H.gradient) (xrfcPriorDirection H)) hmu hmuL
    hproper.1 hproper.2 hC).2
  have hpos := (observed_harmonic_trial_bound _ hphys.1 _ hphys.2.1 _ mu upper (-inner ℝ (virtualGradient H.pairs H.gradient) (xrfcPriorDirection H)) hmu hmuL hq hC).1
  change xrfcPriorHarmonic mu upper H=xrfcSchurHarmonic mu upper H at he
  exact ⟨he.symm,he ▸ (show 0<xrfcPriorHarmonic mu upper H from hpos)⟩

/-- The actual positive harmonic policy has a C-r complete observed-history
chart on every genuine active quadratic full-window reference.
Use: all primitive positive smooth trial hypotheses are derived for the
literal executable continuation, without a supplied smooth policy premise.
Article: main_krylov, thm:radau and lem:U(d).
Proof: physical quadratic geometry supplies the genuine chart domain and
positive value. The rational harmonic calculus gives C-r regularity, whose
continuity keeps the real positive branch selected in a true neighborhood. -/
theorem xrfc_schur_actual_reference_regular
    (H : History (EuclideanSpace ℝ (Fin n)))
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (k : ℕ) (hpre : ∀ i<k+1,CG.gradient (cgOperator base) g i≠0)
    (mu upper : ℝ) (hmu : 0<mu) (hmuL : mu≤upper)
    (hlo : (base-mu • 1).PosSemidef) (hhi : (upper • 1-base).PosSemidef)
    (hbal : H.gradient=g+cgOperator base H.displacement)
    (hy : ∀ j,windowImages H.pairs j=cgOperator base (windowSteps H.pairs j))
    (hLI : LinearIndependent ℝ (windowSteps H.pairs)) (hspan : pairSpan H.pairs=directionFlag (cgOperator base) g k)
    (r : WithTop ℕ∞) :
    ContDiffAt ℝ r (historyEstimateChart (xrfcSchurTrial mu upper) H.queryShape H.observationList.length)
      (observedArray H.observationList.length H.observationList) := by
  have hform := physical_band_operator_forms base mu upper hlo hhi
  have hd := xrfc_schur_actual_chart_domain H base hb g k hpre mu upper hmu hmuL hlo hhi
    hform.1 hform.2 hbal hy hLI hspan
  have hr := xrfc_schur_harmonic_chart_regular H.queryShape _ mu upper r hd
  have hp := (xrfc_schur_actual_reference_values H base hb g k hpre mu upper hmu hmuL hlo hhi hbal hy hLI hspan).2
  have hpchart : 0<historyEstimateChart (xrfcSchurHarmonic mu upper) H.queryShape H.observationList.length
      (observedArray H.observationList.length H.observationList) := by
    simpa only [historyEstimateChart,ofFn_observedArray,historyFromObservations_actual] using hp
  apply hr.congr_of_eventuallyEq
  filter_upwards [hr.continuousAt.eventually (isOpen_Ioi.mem_nhds hpchart)] with z hz
  exact ite_eq_left hz

end
end krylov.OneGradient
