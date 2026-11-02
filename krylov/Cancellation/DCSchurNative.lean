import krylov.Cancellation.DCSchurReferenceRegularity
import krylov.Cancellation.DCReferenceInputs
import krylov.Cancellation.DCNativeSmooth
import krylov.Completion.PhysicalBandForms
set_option autoImplicit false
/-!
Article: main_krylov, s8:dcsdef and lem:U(d), actual smooth Gauss--Radau DC.
Use: derive positive smooth estimates in actual exact-search and one-gradient
executions from the original physical spectral class and active CG data.
Source: genuine native quadratic inputs, strict proper-Krylov pencils and
the proved physical Schur continuation/observed-coordinate calculus.
-/

namespace krylov.Cancellation
noncomputable section
open Matrix krylov.Methods krylov.Reference krylov.Stability krylov.Completion
open scoped InnerProductSpace
variable {n : ℕ}

/-- Every genuine proper-flag quadratic window gives the actual continued
arithmetic estimate a positive value and its primitive C-r history chart.
Use: native cycle regularity has its estimate hypotheses derived entirely.
Article: main_krylov, s8:dcsdef and lem:U(d).
Proof: the physical class supplies actual Hilbert-space bounds and genuine
window feasibility. Proper-Krylov geometry makes both pencils positive;
the continuation equals the original positive observed arithmetic rule.
The original primitive chart regularity theorem then applies. -/
theorem dc_schur_reference_estimate (memory : ℕ → ℕ)
    (H : History (EuclideanSpace ℝ (Fin n)))
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (k : ℕ) (hpre : ∀ i<k+1,CG.gradient (cgOperator base) g i≠0)
    (mu upper : ℝ) (hmu : 0<mu) (hmuL : mu≤upper)
    (hlo : (base-mu • 1).PosSemidef) (hhi : (upper • 1-base).PosSemidef)
    (hy : ∀ j,windowImages (selectedWindow memory H) j=
      cgOperator base (windowSteps (selectedWindow memory H) j))
    (hLI : LinearIndependent ℝ (windowSteps (selectedWindow memory H)))
    (hflag : ∀ j,windowSteps (selectedWindow memory H) j∈directionFlag (cgOperator base) g k)
    (hq : 0<dcCurvatureSlope memory H) (r : WithTop ℕ∞) :
    0<dcSchurGaussRadauEstimate memory mu upper H ∧
      ContDiffAt ℝ r (historyEstimateChart (dcSchurGaussRadauEstimate memory mu upper)
        H.queryShape H.observationList.length) (observedArray H.observationList.length H.observationList) := by
  have hform := physical_band_operator_forms base mu upper hlo hhi
  have hproper := proper_observed_window_pencils (selectedWindow memory H) base hb g k hpre mu upper
    hform.1 hform.2 hy hLI hflag
  have hphys := dc_quadratic_window_feasible memory H base hb mu upper hlo hhi hy hLI hq
  have heq := dc_schur_estimate_original memory mu upper H hmu hmuL hphys.1 hphys.2.1
    hproper.1 hproper.2 (Set.nonempty_of_mem hphys.2.2)
  have hpos := (dc_quadratic_gauss_radau_bound memory H base hb mu upper hmu hmuL hlo hhi hy hLI hq).1
  refine ⟨heq ▸ hpos,?_⟩
  exact dc_schur_actual_reference_regular memory H base hb g k hpre mu upper hmu hmuL hlo hhi
    hform.1 hform.2 hy hLI hflag hq r

/-- The actual exact-search native Schur Gauss--Radau DC procedure belongs
to its genuine smooth source cycle class at every positive active reference
in the original physical spectral band.
Use: all native DC derivative, Taylor and compact theorems now have their
positive smooth estimate hypotheses proved for this literal implementation.
Article: main_krylov, s8:dcsdef, thm:dcs(c) and lem:U(d).
Proof: actual exact-search DC inputs are derived independently of its estimate.
The proved genuine observed Schur rule supplies positive C-r primitive
estimate charts at every queried history; reuse the original native compiler. -/
theorem dc_schur_slide_smoothCycleAt (memory : ℕ → ℕ) (hm : ∀ k,0<k → 0<memory k)
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef) (mu upper : ℝ) (hmu : 0<mu) (hmuL : mu≤upper)
    (hlo : (base-mu • 1).PosSemidef) (hhi : (upper • 1-base).PosSemidef)
    (g : EuclideanSpace ℝ (Fin n)) (N : ℕ) (hpre : ∀ k<N,CG.gradient (cgOperator base) g k≠0)
    (r : WithTop ℕ∞) :
    SmoothProbedCycleAt (dcSlideMethod memory (dcSchurGaussRadauEstimate memory mu upper))
      r (cgOperator base) g N := by
  let estimate := dcSchurGaussRadauEstimate memory mu upper (n := n)
  have hp := cgOperator_positive base hb
  have hest (k : ℕ) (hk : k<N) :
      let H := methodRun (dcSlideMethod memory estimate) (fun _ => cgOperator base) (fun _ => cgOperator base) g k
      0<estimate H ∧ ContDiffAt ℝ r (historyEstimateChart estimate H.queryShape H.observationList.length)
        (observedArray H.observationList.length H.observationList) := by
    have hprefix : ∀ i<k+1,CG.gradient (cgOperator base) g i≠0 := fun i hi => hpre i (by omega)
    have hi := dc_reference_inputs memory hm estimate (cgOperator base) hp.1 hp.2 g k hprefix
    exact dc_schur_reference_estimate memory _ base hb g k hprefix mu upper hmu hmuL hlo hhi
      hi.2.1 hi.1 hi.2.2.1 hi.2.2.2 r
  exact dc_slide_smoothCycleAt memory hm estimate (cgOperator base) hp.1 hp.2 g N hpre r
    (fun k hk => (hest k hk).2) (fun k hk => (hest k hk).1)

/-- The actual full-memory one-gradient Schur Gauss--Radau DC procedure
selects positive estimates and has primitive C-r full observed-history charts
on its entire true nonstagnating quadratic prefix.
Use: all original trial, model and Schur domains are derived by genuine
execution induction, not assumed for an estimate sequence.
Article: main_krylov, s8:dcsdef, thm:dcs(b) and lem:U(d).
Proof: already proved earlier positive decisions give the actual independent
CG flag and true virtual/untilted inputs. Their original observed slope is
the positive incoming factor times the true CG residual norm squared. The
genuine physical Schur estimate theorem proves the next positive smooth rule. -/
theorem dc_schur_one_gradient_estimates
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef) (mu upper : ℝ) (hmu : 0<mu) (hmuL : mu≤upper)
    (hlo : (base-mu • 1).PosSemidef) (hhi : (upper • 1-base).PosSemidef)
    (g : EuclideanSpace ℝ (Fin n)) (N : ℕ) (hpre : ∀ k<N,CG.gradient (cgOperator base) g k≠0)
    (r : WithTop ℕ∞) :
    ∀ k<N,
      let estimate := dcSchurGaussRadauEstimate fullMemory mu upper (n := n)
      let H := oneGradientRun (dcSlideOneGradient fullMemory estimate) (fun _ => cgOperator base) g k
      0<estimate H ∧ ContDiffAt ℝ r (historyEstimateChart estimate H.queryShape H.observationList.length)
        (observedArray H.observationList.length H.observationList) := by
  let Q := cgOperator base
  let estimate := dcSchurGaussRadauEstimate fullMemory mu upper (n := n)
  let method := dcSlideOneGradient fullMemory estimate
  have hp := cgOperator_positive base hb
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro hk
    have ht : ∀ j<k,0<estimate (oneGradientRun method (fun _ => Q) g j) :=
      fun j hj => (ih j hj (hj.trans hk)).1
    have hprefix : ∀ j<k,CG.gradient Q g j≠0 := fun j hj => hpre j (hj.trans hk)
    have hstate := dc_one_gradient_state estimate Q hp.1 hp.2 g k hprefix ht k le_rfl
    have hinputs := dc_one_gradient_curvature_inputs estimate Q hp.1 hp.2 g k hprefix ht k le_rfl
    let H := oneGradientRun method (fun _ => Q) g k
    have hInv := CG.invariant Q hp.1 hp.2 g k hprefix
    have hq : 0<dcCurvatureSlope fullMemory H := by
      have he : dcCurvatureSlope fullMemory H=dcIncomingFactor estimate Q g k*‖CG.gradient Q g k‖^2 := by
        have hpair : inner ℝ (CG.gradient Q g k) (CG.direction Q g k)= -‖CG.gradient Q g k‖^2 :=
          (real_inner_comm _ _).trans hInv.search_pair
        unfold dcCurvatureSlope
        rw [hinputs.1,hinputs.2,real_inner_smul_right,hpair]
        ring
      rw [he]
      exact mul_pos hstate.1 (sq_pos_of_pos (norm_pos_iff.mpr (hpre k hk)))
    have hy : ∀ j,windowImages (selectedWindow fullMemory H) j=Q (windowSteps (selectedWindow fullMemory H) j) := by
      rw [selectedWindow_full]
      exact fun j => oneGradientRun_pairs_quadratic method Q g k (H.pairs.get j) (List.get_mem _ j)
    have hLI : LinearIndependent ℝ (windowSteps (selectedWindow fullMemory H)) := by
      rw [selectedWindow_full]
      exact hstate.2.1
    have hflag : ∀ j,windowSteps (selectedWindow fullMemory H) j∈directionFlag Q g k := by
      rw [selectedWindow_full]
      intro j
      rw [← hstate.2.2.1]
      exact Submodule.subset_span ⟨j,rfl⟩
    exact dc_schur_reference_estimate fullMemory H base hb g k (fun i hi => hpre i (by omega))
      mu upper hmu hmuL hlo hhi hy hLI hflag hq r

end
end krylov.Cancellation
