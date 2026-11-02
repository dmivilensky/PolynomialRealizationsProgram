import krylov.Convergence.ObservableRFCGate
import krylov.Convergence.ObservableAppend

/-!
Article: main_krylov, apG:Dunif, accepted actual RFC invariant step.
Use: prove that a passed observed energy gate forces value acceptance,
retains actual secant conditioning and propagates the cubic residual.
Source: genuine scalar Taylor bounds and the true two-segment secant
identity. All statements concern the literal proposed physical query.
-/
namespace krylov.Convergence
noncomputable section
open Set Metric Matrix krylov.Methods krylov.Functions krylov.Nonlinear krylov.Reference
  krylov.Correction chebyshev1.Nonlinear
open scoped InnerProductSpace Matrix.Norms.L2Operator NNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The genuine value test passes and the actual accepted record
preserves every component of the running RFC invariant. No value
acceptance, secant accuracy or residual bound is assumed at the new
point. Article: main_krylov, apG:Dunif. -/
theorem ObservableLocalSource.rfc_accepted {T : E ≃L[ℝ] E} {f : E → ℝ} {G : E → E}
    {H : E → E →L[ℝ] E} {r : ℝ} {L : ℝ≥0} (S : ObservableLocalSource T f G H r L)
    (x₀ : E) (B : History E) (N : ℕ) (epsilon bar : ℝ) (queried : Bool)
    (I : ObservableRFCInvariant T f G x₀ N epsilon bar B)
    (P : ObservableRFCPrepared T f G H r x₀ B epsilon)
    (hn : 1≤N) (hsize : B.records.length<N) (he : 0≤epsilon) (hb : 0≤bar)
    (hsmall : (N:ℝ)*epsilon≤1/128) (hbar : (N:ℝ)*bar≤1/16)
    (hstart : ‖T x₀‖<r/4) (hsource : 3*(L:ℝ)*‖T x₀‖≤epsilon)
    (hgate : observableCorrectionRatio T f G r x₀ B≤bar) :
    let y := rfcFunctionLinePoint T f fullMemory r x₀ B
    let u := rfcFunctionCorrectionStep T f G fullMemory r x₀ B
    f (y+u)≤f y ∧
      ObservableRFCInvariant T f G x₀ N epsilon bar
        ⟨B.initial,observableRecord T f G r x₀ B u queried::B.records⟩ := by
  let e := ‖T x₀‖
  let y := rfcFunctionLinePoint T f fullMemory r x₀ B
  let u := rfcFunctionCorrectionStep T f G fullMemory r x₀ B
  let line := T (rfcFunctionLineStep T f fullMemory r x₀ B)
  let c := T u
  let A := observableRFCSearchOperator T f H r x₀ B
  let Bc := averagedDerivative (coordinateDerivative T H) (T y) c
  let record := observableRecord T f G r x₀ B u queried
  let B' : History E := ⟨B.initial,record::B.records⟩
  have hN : (1:ℝ)≤N := by exact_mod_cast hn
  have hep : epsilon≤1/128 := by nlinarith only [mul_le_mul_of_nonneg_right hN he,hsmall]
  have hbp : bar≤1/16 := by nlinarith only [mul_le_mul_of_nonneg_right hN hb,hbar]
  have hc : ‖c‖≤(3/2:ℝ)*bar*‖line‖ := P.passed S.inverse_symmetric (by linarith) hb hgate
  have hcl : ‖c‖≤(3/8:ℝ)*e := by
    have hh := mul_le_mul_of_nonneg_left P.length (show 0≤(3/2:ℝ)*bar by positivity)
    have hb' := mul_le_mul_of_nonneg_right hbp (norm_nonneg (T x₀))
    exact hc.trans (by nlinarith only [hh,hb'])
  have hy : ‖T y‖≤2*e := P.point
  have hline : line=lineLength (T.symm B.gradient) (T (rfcFunctionDirection fullMemory B))
    (A (T (rfcFunctionDirection fullMemory B))) • T (rfcFunctionDirection fullMemory B) := P.line
  have hz : ‖T y+c‖≤3*e := (norm_add_le _ _).trans (by linarith only [hy,hcl,norm_nonneg (T x₀)])
  have hr := S.radius_pos
  have hR : 3*e<r := by dsimp only [e];linarith
  have hlocal : (L:ℝ)*(3*e)≤1/8 := by nlinarith only [hsource,hep]
  have hvalue := S.rfc_value_accept (T y) c (3*e)
    (observableRFCModelEnergy T f G H r x₀ B)
    (P.point.trans (by nlinarith only [norm_nonneg (T x₀)])) hz hR hlocal
    (by simpa only [coordinateGradient,T.symm_apply_apply,←P.correction,
      observableRFCLineGradient] using P.slope)
    (by simpa only [←P.correction] using P.move_energy)
  have hval : f (y+u)≤f y := by
    change coordinateObjective T f (T y+T u)≤coordinateObjective T f (T y) at hvalue
    rw [←map_add,coordinateObjective_apply,coordinateObjective_apply] at hvalue
    exact hvalue
  have hsegment := S.segment_data (T y) (T y+c) (3*e)
    (P.point.trans (by nlinarith only [norm_nonneg (T x₀)])) hz hR
  have hBc : ‖Bc-ContinuousLinearMap.id ℝ E‖≤epsilon := by
    dsimp only [Bc]
    convert hsegment.2.2.trans (show (L:ℝ)*(3*e)≤epsilon by nlinarith only [hsource]) using 1
    rw [add_sub_cancel_left]
  have hgnew : T.symm (G (y+u))=observableRFCLineGradient T f G r x₀ B+Bc c := by
    have hh := hsegment.1
    rw [add_sub_cancel_left] at hh
    have heq : coordinateGradient T G (T y+c)=T.symm (G (y+u)) := by
      dsimp only [c,coordinateGradient]
      rw [←map_add,T.symm_apply_apply]
    rw [heq] at hh
    simp only [coordinateGradient,T.symm_apply_apply] at hh
    change T.symm (G (y+u))-observableRFCLineGradient T f G r x₀ B=Bc c at hh
    exact sub_eq_iff_eq_add.mp hh |>.trans (add_comm _ _)
  have hlength := observable_rfc_accepted_length line c bar hb hbp P.step hc
  have hstep : T record.step=line+c := by
    change T (rfcFunctionLineStep T f fullMemory r x₀ B+u)=_
    exact map_add T _ _
  have hgradient : record.gradient=G (y+u) := rfl
  have hfullerror : ‖T.symm (record.gradient-B.gradient)-T record.step‖≤(2*epsilon)*‖T record.step‖ := by
    rw [hstep,hgradient,map_sub,hgnew,P.searched]
    have hh := observable_rfc_recorded_error A Bc line c he P.operator hBc hlength.2
    have hs : searchedGradient (T.symm B.gradient) (T (rfcFunctionDirection fullMemory B))
        (A (T (rfcFunctionDirection fullMemory B)))-T.symm B.gradient=A line := by
      rw [hline,map_smul,searchedGradient,add_sub_cancel_left]
    have heq : searchedGradient (T.symm B.gradient) (T (rfcFunctionDirection fullMemory B))
        (A (T (rfcFunctionDirection fullMemory B)))+Bc c-T.symm B.gradient-(line+c)=
        A line+Bc c-(line+c) := by rw [←hs];module
    rw [heq]
    exact hh
  have hdomains := I.domains S.inverse_symmetric hn hsize.le he hb hsmall hbar
  have ho (i : Fin B.pairs.length) : inner ℝ (observableDual T B i)
      (T (rfcFunctionDirection fullMemory B))=0 :=
    observable_direction_conjugate T S.inverse_symmetric B hdomains.1 i
  have hang (i : Fin B.pairs.length) :
      |inner ℝ (unitWindow (observablePrimal T B) i) (‖T record.step‖⁻¹ • T record.step)|≤2*epsilon+3*bar := by
    have hpair := unitWindow_pair_error (observablePrimal T B) (observableDual T B) I.steps I.pairs i
    have horth : inner ℝ (unitWindowImages (observablePrimal T B) (observableDual T B) i) line=0 := by
      change inner ℝ (‖observablePrimal T B i‖⁻¹ • observableDual T B i) line=0
      rw [hline,real_inner_smul_left,real_inner_smul_right,ho,mul_zero,mul_zero]
    have hh := recorded_step_observed_angle
      (unitWindow (observablePrimal T B) i)
      (unitWindowImages (observablePrimal T B) (observableDual T B) i) line c
      (unitWindow_norm (observablePrimal T B) I.steps i) hpair horth
      (norm_pos_iff.mpr P.step) (by linarith : (3/2:ℝ)*bar<1) hc
    rw [hstep]
    simpa only [NormedSpace.normalize,show (2:ℝ)*((3/2)*bar)=3*bar by ring] using hh
  have hcurv : inner ℝ (T (rfcFunctionDirection fullMemory B))
      (A (T (rfcFunctionDirection fullMemory B)))≠0 := by
    have hh := observable_operator_form A epsilon P.operator (T (rfcFunctionDirection fullMemory B))
    have hnz := norm_pos_iff.mpr P.direction
    have hp : 0 < inner ℝ (T (rfcFunctionDirection fullMemory B))
        (A (T (rfcFunctionDirection fullMemory B))) := by nlinarith only [hh.1,hep,sq_pos_of_pos hnz]
    exact hp.ne'
  have hdim : B.pairs.length+1≤N := by rw [History.pairs_length];omega
  have hrel : ‖observableRFCModelMove T f G H r x₀ B‖≤
      (3/2:ℝ)*(1/16)*‖line‖ := by rw [←P.correction];exact hc.trans (by gcongr)
  have hnext := observable_rfc_projected_step (observablePrimal T B) (observableDual T B) I.steps
    A Bc (T.symm B.gradient) (T (rfcFunctionDirection fullMemory B)) N epsilon e
    hdim he (norm_nonneg _) P.operator hBc I.pairs ho hcurv P.gram hsmall
    (by rw [←P.line];exact P.length)
    (by
      rw [←P.searched]
      change ‖observableRFCModelMove T f G H r x₀ B‖≤_
      rw [←P.line]
      exact hrel)
    (by rw [←P.line];exact P.step)
  have hnext' : ‖projectedResidual (unitWindow (Fin.cons (T record.step) (observablePrimal T B)))
      (T.symm record.gradient)‖≤
      64*(N:ℝ)*epsilon*‖projectedResidual (unitWindow (observablePrimal T B)) (T.symm B.gradient)‖+
        1024*(N:ℝ)*Real.sqrt N*epsilon^2*e := by
    rw [hstep,hgradient,hgnew]
    rw [←P.line,←P.searched] at hnext
    change ‖projectedResidual (unitWindow (Fin.cons
      (T (rfcFunctionLineStep T f fullMemory r x₀ B)+observableRFCModelMove T f G H r x₀ B)
      (observablePrimal T B))) (observableRFCLineGradient T f G r x₀ B+
        Bc (observableRFCModelMove T f G H r x₀ B))‖≤_ at hnext
    rw [←P.correction] at hnext
    exact hnext
  have hres : ‖projectedResidual (unitWindow (Fin.cons (T record.step) (observablePrimal T B)))
      (T.symm record.gradient)‖≤observableRFCResidualBudget N epsilon e := by
    have hcoef : 64*(N:ℝ)*epsilon≤1/2 := by nlinarith only [hsmall]
    have hterm := mul_le_mul_of_nonneg_left I.residual (show 0≤64*(N:ℝ)*epsilon by positivity)
    have hcontract := mul_le_mul_of_nonneg_right hcoef
      (show 0≤observableRFCResidualBudget N epsilon e by dsimp only [observableRFCResidualBudget,e];positivity)
    dsimp only [observableRFCResidualBudget] at hterm hcontract ⊢
    exact hnext'.trans (by nlinarith only [hterm,hcontract])
  have hendpoint : x₀+B'.displacement=y+u := by
    have hh := observableRecord_endpoint T f G r x₀ B u queried
    change x₀+(record.step+B.displacement)=_
    rw [←hh]
    abel
  have hvalues : f (x₀+B'.displacement)≤f x₀ := by rw [hendpoint];exact hval.trans (P.value.trans I.value)
  have hpoint : ‖T (x₀+B'.displacement)‖≤2*e := by
    have hf z (hz : z∈closedBall (0:E) r) := S.coordinate_f z
      (by simpa only [mem_closedBall,dist_zero_right] using hz)
    have hg z (hz : z∈closedBall (0:E) r) := S.coordinate_g z
      (by simpa only [mem_closedBall,dist_zero_right] using hz)
    have hgzero : coordinateGradient T G 0=0 := by simp only [coordinateGradient,map_zero,S.gradient_zero]
    have hzball : T (y+u)∈closedBall (0:E) r := by
      rw [mem_closedBall,dist_zero_right,map_add]
      exact hz.trans hR.le
    have hh := local_sublevel_search_bounds _ _ _ S.radius_pos hgzero S.hessian_zero
      S.small S.lipschitz hf hg (T x₀) (T (y+u)) (by linarith) hzball
      (by simpa only [coordinateObjective_apply] using hval.trans (P.value.trans I.value))
    rw [hendpoint]
    exact hh.1.trans (mul_le_mul_of_nonneg_right (Real.sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩ : Real.sqrt (3:ℝ)≤2) (norm_nonneg _))
  exact ⟨hval,I.append record (observableRecord_append_gradient T f G r x₀ B u queried)
    hpoint hvalues (by rw [hstep];exact hlength.1) hfullerror hang hres⟩

end
end krylov.Convergence
