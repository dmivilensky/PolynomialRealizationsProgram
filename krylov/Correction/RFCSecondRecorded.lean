import krylov.Correction.RFCSecondSearch
import krylov.Correction.RFCInitialShadow
import krylov.Correction.RFCUniformParameters
import krylov.Correction.RFCContamination
import krylov.Correction.RecordedPrefixReindex
import krylov.Correction.ObservedPrefixModels
import krylov.Stability.ActualObservedSearch

/-!
Article: main_krylov, thm:UCq, exceptional genuine second recorded pair.
Use: Propagate the exact first reference data through the true second search,
correction, recorded displacement and observed secant without condition (N).
Source: exact actual initial histories, relative true second-search geometry,
the measured relative-residual step and genuine correction noncancellation.
-/

namespace krylov.Correction
noncomputable section
open Matrix krylov.Methods krylov.Reference krylov.Secant krylov.Stability
open scoped InnerProductSpace Matrix.Norms.L2Operator
variable {n : ℕ}

set_option maxHeartbeats 1200000 in
/-- One numerical tube controls both actual recorded-prefix bounds, complete ordinary/gated histories and quadratic relative measured-secant contamination through the second iteration, even when its true CG energy is arbitrarily small.
Use: Supply the original three-dimensional exceptional induction without a nonstagnation or minimum-step premise.
Article: main_krylov, thm:UCq.
Proof: The unchanged first probe yields exact true CG data and identically zero old projected residual. The actual second direction is exactly CG, so its real line has a relative error at most twice the operator allowance. Apply the proved relative-residual angle step to the actual canonical gated phase. Real recorded-step noncancellation and exact oracle balance give quadratic secant contamination; true CG energy monotonicity gives the absolute step bound. The actual measured spectral test extends complete ordinary/gated history equality.
-/
theorem gated_second_recorded_prefix :
    ∃ δ a C D Cξ : ℝ, 0<δ ∧ 0<a ∧ 0<C ∧ 0<D ∧ 0<Cξ ∧
      ∀ (base : Matrix (Fin n) (Fin n) ℝ) (_hb : base.PosDef)
        (A B : ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
        (g : EuclideanSpace ℝ (Fin n)) (ε : ℝ),
      A 0=cgOperator base → 0<ε → ε≤δ → ‖cgCanonicalError base g 0‖≤1 →
      (∀ i≤1, CG.gradient (cgOperator base) g i≠0) →
      (∀ i<3, ‖canonicalOperator base (A i)-ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))‖≤ε) →
      (∀ i<3, ‖canonicalOperator base (B i)-ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))‖≤ε) →
      let m := gatedMethod fullMemory (1/2) (E := EuclideanSpace ℝ (Fin n))
      let R := cgOperator (metricRoot base)
      let J := cgOperator (metricRoot base)⁻¹
      (∀ j≤2, recordedPrefixBound (a*ε) C ε
        (primalWindow base (windowSteps (selectedWindow fullMemory (methodRun m A B g j))))
        (J (probedGradient m A B g j))) ∧
      (∀ j≤2, methodRun m A B g j=methodRun (rfcMethod fullMemory 1) A B g j) ∧
      ∀ i<2, ‖R (probedStep m A B g i)-canonicalCGStep base g i‖≤D*ε ∧
        ‖J (probedSecant m A B g i)-canonicalOperator base (A i) (R (probedStep m A B g i))‖≤
          Cξ*ε^2*‖R (probedStep m A B g i)‖ := by
  obtain ⟨K,C,L,M,δ,hK,hC,hL,hM,hδ,hgrowth,hallow,hMg,hMs,hsmall⟩ :=
    rfc_uniform_prefix_parameters 3 1 (1/2) (by norm_num) (by norm_num) (by norm_num)
  have hK0 : 0≤K := by rw [hK]; exact mul_nonneg (by norm_num) (gatedCorrectionConstant_nonneg 3 (1/2))
  let a := rfcLinearAngleConstant 3 K C
  let Q := rfcRelativeCorrectionConstant 3 K C
  have ha : 0<a := rfcLinearAngleConstant_pos 3 hK0 hC.le
  have hQ : 0≤Q := rfcRelativeCorrectionConstant_nonneg 3 hK0 hC.le
  refine ⟨min δ (1/(2*(Q+1))),a,C,3+2*Q,4*Q+1,
    lt_min hδ (by positivity),ha,hC,by positivity,by positivity,?_⟩
  intro base hb A B g ε hA0 hε he hinit hpre hA hB
  obtain ⟨hhalf,hrecord,hangle,hF,hProj⟩ := hsmall ε hε.le (he.trans (min_le_left _ _))
  have heQ : ε*(2*(Q+1))≤1 := (le_div_iff₀ (by positivity : 0<2*(Q+1))).mp (he.trans (min_le_right _ _))
  have hqhalf : Q*ε≤1/2 := by nlinarith only [heQ,hε.le]
  let m := gatedMethod fullMemory (1/2) (E := EuclideanSpace ℝ (Fin n))
  let mo := rfcMethod fullMemory 1 (E := EuclideanSpace ℝ (Fin n))
  let R := cgOperator (metricRoot base)
  let J := cgOperator (metricRoot base)⁻¹
  let W := selectedWindow fullMemory (methodRun m A B g 1)
  let s := primalWindow base (windowSteps W)
  let y := dualWindow base (windowImages W)
  let G := J (probedGradient m A B g 1)
  let d := R (m.direction (methodRun m A B g 1))
  let Ac := canonicalOperator base (A 1)
  let Bc := canonicalOperator base (B 1)
  let P := gatedArrayPhase (1/2) s y G d (Ac d) Bc
  let line := lineLength G d (Ac d) • d
  -- The first real history is exactly quadratic, independently of its correction operator.
  have hshadow : methodRun m A B g 1=methodRun mo A B g 1 := gated_initial_history_eq_rfc (1/2) A B g
  have hp := cgOperator_positive base hb
  have hpair := ordinary_initial_pair A B (cgOperator base) hp.1 hp.2 g hA0
  have hS0 : probedStep m A B g 0=referenceStep (cgOperator base) g 0 :=
    (congrArg (fun H : History (EuclideanSpace ℝ (Fin n)) => H.observationList.getD 4 0) hshadow).trans hpair.1
  have hY0 : probedSecant m A B g 0=cgOperator base (referenceStep (cgOperator base) g 0) :=
    (congrArg (fun H : History (EuclideanSpace ℝ (Fin n)) => H.gradient-g) hshadow).trans hpair.2
  have hW : W=[(referenceStep (cgOperator base) g 0,cgOperator base (referenceStep (cgOperator base) g 0))] := by
    dsimp only [W]
    rw [fullWindow_methodRun]
    change [(probedStep m A B g 0,probedSecant m A B g 0)]=_
    rw [hS0,hY0]
  have hlen : W.length=1 := by rw [hW]; rfl
  have hs (i : Fin W.length) : s i=canonicalCGStep base g 0 := by
    have hi : i.val=0 := by have ht : i.val<1 := i.isLt.trans_eq hlen; omega
    change R (W[i.val]).1=_
    simp only [hi,hW,List.getElem_cons_zero]
    rfl
  have hy (i : Fin W.length) : y i=s i := by
    have hi : i.val=0 := by have ht : i.val<1 := i.isLt.trans_eq hlen; omega
    change J (W[i.val]).2=R (W[i.val]).1
    simp only [hi,hW,List.getElem_cons_zero]
    exact canonical_reference_action base hb _
  have hG : G=cgCanonicalError base g 1 := by
    have hh := hshadow.trans (ordinary_initial_history A B (cgOperator base) g hA0)
    have hg := (congrArg History.gradient hh).trans
      (rfcMethod_static fullMemory 1 (cgOperator base) hp.1 hp.2 g (fun _ _ hj => hj) 1).1
    change J ((methodRun m A B g 1).gradient)=_
    rw [hg]
    rfl
  have hres : projectedResidual (unitWindow s) G=0 := by
    ext i
    change inner ℝ (NormedSpace.normalize (s i)) G=0
    rw [hs,hG]
    exact canonicalCG_old_step_orth base hb g 2 (canonicalCGUnitStep_orthonormal base hb g 2 (fun j hj => hpre j (by omega)))
      ⟨0,by omega⟩ 1 (by omega) (by norm_num)
  -- Its zero old residual is relative to every positive second line, however small.
  have hsne (i : Fin W.length) : s i≠0 := by rw [hs]; exact canonicalCGStep_ne_zero base hb g 0 (fun j hj => hpre j (by omega))
  have hangles (i j : Fin W.length) (hij : i≠j) : |inner ℝ (unitWindow s i) (unitWindow s j)|≤a*ε := by
    have hi : i.val<1 := i.isLt.trans_eq hlen
    have hj : j.val<1 := j.isLt.trans_eq hlen
    exact (hij (Fin.ext (by omega))).elim
  have hprefix : recordedPrefixBound (a*ε) C ε s G := by
    refine ⟨hsne,hangles,?_⟩
    rw [hres,norm_zero]
    positivity
  have hpairBound (i : Fin W.length) : ‖y i-s i‖≤((1+K)*ε)*‖s i‖ := by rw [hy,sub_self,norm_zero]; positivity
  have hdphys : m.direction (methodRun m A B g 1)≠0 := by
    have ho : m.direction (methodRun m A B g 1)=mo.direction (methodRun mo A B g 1) := by
      change windowDirection W _=windowDirection (selectedWindow fullMemory (methodRun mo A B g 1)) _
      dsimp only [W]
      rw [hshadow]
    rw [ho,ordinary_second_direction A B (cgOperator base) hp.1 hp.2 g hA0]
    intro hz
    exact (canonicalCG_direction_ne base hb g 1 hpre) (by rw [hz,map_zero])
  have hcurv : inner ℝ (m.direction (methodRun m A B g 1)) (A 1 (m.direction (methodRun m A B g 1)))≠0 :=
    (canonical_curvature_positive base hb (A 1) _ hdphys ((hA 1 (by omega)).trans hhalf)).ne'
  have hc : inner ℝ d (Ac d)≠0 := by
    dsimp only [d,Ac,R,cgOperator]
    rw [canonicalOperator_primal base hb,← canonical_search_pairing base hb]
    exact hcurv
  have hmodel := observed_prefix_model_conditioning base hb W (probedGradient m A B g 1) (A 1)
    (N := 3) (a := a*ε) (η := (1+K)*ε) (ε := ε) (γ := 1/2)
    (by omega) (by rw [hlen]; omega) (mul_nonneg ha.le hε.le) (by positivity)
    (by nlinarith) (by dsimp only [a,rfcLinearAngleConstant]; change (1+K)*ε≤(2*(1+K)+2*Q)*ε/2; nlinarith)
    (by norm_num) (by norm_num) hangle hsne hangles hpairBound hdphys (hA 1 (by omega))
  have ho (i : Fin W.length) : inner ℝ (y i) d=0 :=
    canonical_window_image_conjugacy base hb W (probedGradient m A B g 1) hmodel.1 i
  have hfields := probedGated_canonical_window_fields base hb fullMemory (1/2) A B g 1
  change P.movement=R (probedPhase m A B g 1).movement ∧
    P.gradient=J (probedGradient m A B g 2) ∧ line+P.movement=R (probedStep m A B g 1) at hfields
  have hlineeq : line=R (gatedObservedLineStep (1/2) A B g 1) := by
    dsimp only [line,Ac,d,R,cgOperator,G,J]
    rw [canonicalOperator_primal base hb,canonical_lineLength base hb]
    change _=R (lineLength (probedGradient m A B g 1) (m.direction (methodRun m A B g 1))
      (A 1 (m.direction (methodRun m A B g 1))) • m.direction (methodRun m A B g 1))
    rw [map_smul]
    rfl
  have hlineordinary : gatedObservedLineStep (1/2) A B g 1=fullLineStep 1 A B g 1 := by
    unfold gatedObservedLineStep fullLineStep
    dsimp only
    rw [hshadow]
    rfl
  have hlineCG := ordinary_second_line_relative base hb A B g hA0 hpre (hA 1 (by omega)) hhalf
  have hlineCG' : ‖line-canonicalCGStep base g 1‖≤2*ε*‖canonicalCGStep base g 1‖ := by
    rw [hlineeq,hlineordinary]
    exact hlineCG.1
  have hlinepos : 0<‖line‖ := by
    rw [hlineeq,hlineordinary]
    exact norm_pos_iff.mpr hlineCG.2
  have hrelative : ‖P.movement‖≤K*‖line+P.movement‖ := by
    rw [hfields.2.2,hfields.1]
    have hr := gated_uniform_recorded_bounds base hb fullMemory (1/2) (by norm_num) A B g 3 hε.le hA hB
      (by simpa only [hK] using hrecord.1) (by simpa only [hK] using hrecord.2.1) (by simpa only [hK] using hrecord.2.2)
    apply (hr.1 1 (by omega)).trans
    apply mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    rw [hK]
    have ht := gatedCorrectionConstant_nonneg 3 (1/2)
    linarith
  have hLone : 1≤L := by
    have hgr : 1≤gatedGrowthConstant 3 (1/2) := by norm_num [gatedGrowthConstant]
    exact (one_le_pow₀ hgr).trans hgrowth
  have hgnorm : ‖G‖≤L := by rw [hG]; exact ((cgError_antitone base hb g (show 0≤1 by omega)).trans hinit).trans hLone
  have hnext := recordedPrefixBound_linear_step_of_relative_residual s y Ac Bc G d
    (N := 3) (by rw [hlen]; omega) (by omega) (by rw [hlen]; omega)
    (by norm_num : (0 : ℝ)≤1/2) (by norm_num : (1/2 : ℝ)<1) hC.le hε hK0 hgnorm
    hprefix (hA 1 (by omega)) (hB 1 (by omega)) hpairBound ho hc hangle hF hallow hlinepos
    (by rw [hres,norm_zero]; positivity) hrelative
  -- The actual passed decision preserves the complete recorded ordinary history.
  have hshadow2 : methodRun m A B g 2=methodRun mo A B g 2 :=
    gated_rfc_next_history_eq_of_gate (1/2) A B g 1 hshadow hmodel.2.1
  have href : ‖canonicalCGStep base g 1‖≤1 := by
    have he := cgEnergy_drop base hb g 1
    rw [cgEnergy_eq_norm_sq base hb g 1] at he
    have hm := (cgError_antitone base hb g (show 0≤1 by omega)).trans hinit
    nlinarith [sq_nonneg ‖cgCanonicalError base g 2‖,norm_nonneg (canonicalCGStep base g 1),norm_nonneg (cgCanonicalError base g 1)]
  have hlineNorm : ‖line‖≤2*‖canonicalCGStep base g 1‖ := by
    have ht := (norm_le_norm_sub_add line (canonicalCGStep base g 1)).trans (add_le_add hlineCG' (le_refl _))
    nlinarith [norm_nonneg (canonicalCGStep base g 1)]
  have hχ : ‖P.movement‖≤2*Q*ε*‖canonicalCGStep base g 1‖ :=
    hnext.2.trans ((mul_le_mul_of_nonneg_left hlineNorm (mul_nonneg hQ hε.le)).trans_eq (by ring))
  -- Transfer the true phase fields and convert its relative correction to measured xi.
  dsimp only
  refine ⟨?_,?_,?_⟩
  · intro j hj
    have hcases : j=0 ∨ j=1 ∨ j=2 := by omega
    rcases hcases with rfl | rfl | rfl
    · have he : primalWindow base (windowSteps (selectedWindow fullMemory (methodRun m A B g 0)))=
          (fun i : Fin 0 => Fin.elim0 i) := by funext i; exact Fin.elim0 i
      rw [he]
      exact recordedPrefixBound_empty (a*ε) C ε hC.le (J g)
    · exact hprefix
    · rw [show selectedWindow fullMemory (methodRun m A B g 2)=
          (probedStep m A B g 1,probedSecant m A B g 1)::W from full_observed_window_next m A B g 1,windowSteps_cons]
      have hm : primalWindow base (Fin.cons (probedStep m A B g 1) (windowSteps W))=
          Fin.cons (R (probedStep m A B g 1)) s := by
        funext i
        exact Fin.cases rfl (fun _ => rfl) i
      rw [hm,← hfields.2.2,← hfields.2.1]
      exact hnext.1
  · intro j hj
    have hcases : j=0 ∨ j=1 ∨ j=2 := by omega
    rcases hcases with rfl | rfl | rfl
    · rfl
    · exact hshadow
    · exact hshadow2
  · intro i hi
    have hi' : i=0 ∨ i=1 := by omega
    rcases hi' with rfl | rfl
    · have hsref : R (probedStep m A B g 0)=canonicalCGStep base g 0 := by rw [hS0]; rfl
      refine ⟨?_,?_⟩
      · rw [hsref,sub_self,norm_zero]; positivity
      · have hzero : J (probedSecant m A B g 0)-canonicalOperator base (A 0) (R (probedStep m A B g 0))=0 := by
          rw [hY0,hS0,hA0]
          dsimp only [R,J,cgOperator]
          rw [canonicalOperator_primal base hb,sub_self]
        rw [hzero,norm_zero]
        positivity
    · refine ⟨?_,?_⟩
      · rw [← hfields.2.2]
        have heq : line+P.movement-canonicalCGStep base g 1=(line-canonicalCGStep base g 1)+P.movement := by abel
        rw [heq]
        have ht := (norm_add_le _ _).trans (add_le_add hlineCG' hχ)
        calc
          _ ≤ (2+2*Q)*ε*‖canonicalCGStep base g 1‖ := ht.trans_eq (by ring)
          _ ≤ (2+2*Q)*ε := by nlinarith [mul_nonneg (by positivity : 0≤(2+2*Q)*ε) (sub_nonneg.mpr href)]
          _ ≤ (3+2*Q)*ε := by nlinarith only [hε.le]
      · have hr := correction_line_to_recorded_bound line P.movement (mul_nonneg hQ hε.le) hqhalf hnext.2
        rw [hfields.2.2,hfields.1] at hr
        have hχrec : ‖R (probedPhase m A B g 1).movement‖≤(2*Q)*ε*‖R (probedStep m A B g 1)‖ := hr.trans_eq (by ring)
        have ht := probed_canonical_contamination_bound base hb m A B g 1 hε.le (hA 1 (by omega)) (hB 1 (by omega)) hχrec
        have hcoef : 2*(2*Q)≤4*Q+1 := by linarith
        exact ht.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcoef (sq_nonneg ε)) (norm_nonneg _))

end
end krylov.Correction
