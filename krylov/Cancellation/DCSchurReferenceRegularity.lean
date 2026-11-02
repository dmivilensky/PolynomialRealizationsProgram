import krylov.Cancellation.DCSchurEstimate
import krylov.Cancellation.DCPhysicalWindow
import krylov.Completion.ProperObservedPencils
set_option autoImplicit false
/-!
Article: main_krylov, s8:dcsdef and lem:U(d), derived native Schur regularity.
Use: discharge the real primitive estimate chart domain from genuine
quadratic observations in a proper CG flag, including boundary references.
Source: original physical feasibility, actual strict Krylov pencils and exact
full-history/getter coordinate dictionaries; no estimate regularity is assumed.
-/

namespace krylov.Cancellation
noncomputable section
open Matrix krylov.Methods krylov.Reference krylov.Stability krylov.Completion
open scoped InnerProductSpace
variable {n : ℕ}

/-- Both actual Schur endpoints have their genuine fixed getter-array
coordinates under a true window length equality.
Use: transfer proved physical positivity into primitive observed charts.
Article: main_krylov, s8:dcsdef and lem:U(d).
Proof: after the pure index length cast, exact getter identities identify
both observed vector families and the original latest-information model. -/
theorem schur_endpoints_window_coordinates
    (W : List (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)))
    (p : ℕ) (hp : W.length=p) (d : Fin n → ℝ) (mu upper : ℝ) :
    let S : Matrix (Fin n) (Fin W.length) ℝ := fun a j => windowSteps W j a
    let s := fun j : Fin p => (W.getD j.val (0,0)).1
    let y := fun j : Fin p => (W.getD j.val (0,0)).2
    let U : Matrix (Fin n) (Fin p) ℝ := fun a j => s j a
    schurLowerCurvature S d (windowModel W) mu=schurLowerCurvature U d (pairModel s y) mu ∧
      schurUpperCurvature S d (windowModel W) upper=schurUpperCurvature U d (pairModel s y) upper := by
  subst p
  have hs : windowSteps W=(fun j : Fin W.length => (W.getD j.val (0,0)).1) :=
    windowSteps_getD_array W W.length rfl
  have hy : windowImages W=(fun j : Fin W.length => (W.getD j.val (0,0)).2) :=
    windowImages_getD_array W W.length rfl
  dsimp only
  rw [← pairModel_window,hs,hy]
  exact ⟨rfl,rfl⟩

/-- The genuine quadratic retained window supplies every actual determinant
and positive endpoint of its primitive observed Schur chart.
Use: share the native geometric domain between arithmetic and harmonic rules.
Article: main_krylov, thm:radau and s8:dcsdef.
Proof: physical feasibility gives the positive endpoints, proper active Krylov
geometry gives both positive pencils, and exact getter casts transfer these
real domains to the original fixed-shape observed coordinate array. -/
theorem dc_schur_actual_chart_domain (memory : ℕ → ℕ)
    (H : History (EuclideanSpace ℝ (Fin n)))
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (k : ℕ) (hpre : ∀ i<k+1,CG.gradient (cgOperator base) g i≠0)
    (mu upper : ℝ) (hmu : 0<mu) (hmuL : mu≤upper)
    (hlo : (base-mu • 1).PosSemidef) (hhi : (upper • 1-base).PosSemidef)
    (hloform : ∀ v : EuclideanSpace ℝ (Fin n),mu*‖v‖^2≤ inner ℝ v (cgOperator base v))
    (hhiform : ∀ v : EuclideanSpace ℝ (Fin n),inner ℝ v (cgOperator base v)≤upper*‖v‖^2)
    (hy : ∀ j,windowImages (selectedWindow memory H) j=
      cgOperator base (windowSteps (selectedWindow memory H) j))
    (hLI : LinearIndependent ℝ (windowSteps (selectedWindow memory H)))
    (hflag : ∀ j,windowSteps (selectedWindow memory H) j∈directionFlag (cgOperator base) g k)
    (hq : 0<dcCurvatureSlope memory H) :
    dcSchurChartDomain memory H.queryShape
      (observedArray H.observationList.length H.observationList) mu upper := by
  let shape := H.queryShape
  let data := observedArray H.observationList.length H.observationList
  let p := min (memory shape.length) shape.length
  let W := selectedWindow memory H
  let s := chartSteps memory shape data
  let y := chartImages memory shape data
  let T := pairModel s y
  let S : Matrix (Fin n) (Fin p) ℝ := fun a i => s i a
  let d := WithLp.ofLp (conjugacyDirection s y (chartGradient shape data))
  have hW : chartWindow memory shape data=W := by
    dsimp only [chartWindow,shape,data]
    rw [ofFn_observedArray,historyFromObservations_actual]
  have hlen : W.length=p := by rw [← hW];exact chartWindow_length memory shape data
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
  have hdir : dcObservedUntilted memory H=d := by
    unfold dcObservedUntilted
    rw [windowDirection_getD_array W p hlen,← hs,← hyc,← hgrad]
  have hphys := dc_quadratic_window_feasible memory H base hb mu upper hlo hhi hy hLI hq
  have hproper := proper_observed_window_pencils W base hb g k hpre mu upper hloform hhiform hy hLI hflag
  have hC := Set.nonempty_of_mem hphys.2.2
  have hend := observed_endpoints_schur_extension _ hphys.1 _ hphys.2.1 _ mu upper hmu hmuL
    hproper.1 hproper.2 hC
  have hrange := observed_window_curvature_range _ hphys.1 _ hphys.2.1 _ mu upper hmu hmuL hC
  have hlow : 0<schurLowerCurvature (dcObservedColumns memory H) (dcObservedUntilted memory H)
      (windowModel W) mu := hend.1 ▸ hrange.1
  have hhigh : 0<schurUpperCurvature (dcObservedColumns memory H) (dcObservedUntilted memory H)
      (windowModel W) upper := hend.2 ▸ hrange.1.trans_le hrange.2.1
  have hcast := schur_endpoints_window_coordinates W p hlen (dcObservedUntilted memory H) mu upper
  dsimp only at hcast
  change 0<schurLowerCurvature (fun a j => windowSteps W j a)
    (dcObservedUntilted memory H) (windowModel W) mu at hlow
  change 0<schurUpperCurvature (fun a j => windowSteps W j a)
    (dcObservedUntilted memory H) (windowModel W) upper at hhigh
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


/-- Genuine quadratic observations in a proper active CG flag supply all
actual primitive Schur estimate domains and its full observed C-r regularity.
Use: native DC implementations can apply their original smooth-cycle and
compact remainder theorems without a supplied smooth estimate hypothesis.
Article: main_krylov, s8:dcsdef and lem:U(d).
Proof: physical feasibility gives positive true curvature endpoints. Actual
proper-Krylov geometry gives both positive shifted pencils. Genuine independent
window arrays have positive model/cross-Gram domains; exact full-history
reconstruction and pure getter reindexing transfer everything to the original
primitive estimate chart, whose regularity has already been proved algebraically. -/
theorem dc_schur_actual_reference_regular (memory : ℕ → ℕ)
    (H : History (EuclideanSpace ℝ (Fin n)))
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (k : ℕ) (hpre : ∀ i<k+1,CG.gradient (cgOperator base) g i≠0)
    (mu upper : ℝ) (hmu : 0<mu) (hmuL : mu≤upper)
    (hlo : (base-mu • 1).PosSemidef) (hhi : (upper • 1-base).PosSemidef)
    (hloform : ∀ v : EuclideanSpace ℝ (Fin n),mu*‖v‖^2≤ inner ℝ v (cgOperator base v))
    (hhiform : ∀ v : EuclideanSpace ℝ (Fin n),inner ℝ v (cgOperator base v)≤upper*‖v‖^2)
    (hy : ∀ j,windowImages (selectedWindow memory H) j=
      cgOperator base (windowSteps (selectedWindow memory H) j))
    (hLI : LinearIndependent ℝ (windowSteps (selectedWindow memory H)))
    (hflag : ∀ j,windowSteps (selectedWindow memory H) j∈directionFlag (cgOperator base) g k)
    (hq : 0<dcCurvatureSlope memory H) (r : WithTop ℕ∞) :
    ContDiffAt ℝ r (historyEstimateChart (dcSchurGaussRadauEstimate memory mu upper)
      H.queryShape H.observationList.length) (observedArray H.observationList.length H.observationList) := by
  exact dc_schur_estimate_chart_regular memory H.queryShape _ mu upper r
    (dc_schur_actual_chart_domain memory H base hb g k hpre mu upper hmu hmuL
      hlo hhi hloform hhiform hy hLI hflag hq)

end
end krylov.Cancellation
