import krylov.Correction.RFCSecondRecorded
import krylov.Correction.UniformModelBounds

/-!
Article: main_krylov, thm:UCq, complete exceptional three-step observed tube.
Use: Obtain every actual ordinary observed model, inverse and measured test,
true terminal old angles/residual, step errors and quadratic contamination
without a lower intermediate CG energy or condition (N).
Source: the genuine second recorded-pair induction, true measured recording
allowances and the existing observed-prefix model-conditioning theorem.
-/

namespace krylov.Correction
noncomputable section
open Matrix krylov.Methods krylov.Reference krylov.Secant krylov.Stability
open scoped InnerProductSpace Matrix.Norms.L2Operator
variable {n : ℕ}

set_option maxHeartbeats 1200000 in
/-- One genuine three-step ordinary-RFC prefix tube derives all active observed models and both measured gates, exact complete shadow histories and the full terminal recorded-prefix estimates without condition (N).
Use: Supply every actual preterminal input of the three-dimensional exceptional uniform cubic theorem.
Article: main_krylov, thm:UCq.
Proof: Choose the real second-pair constants and measured-recording radius before the reference. A smaller numerical angle margin makes the existing observed-model conditioning theorem apply to each true prefix. Complete accepted histories transfer all real models, steps, secants and gradients to ordinary RFC. The genuine chronological reindexing preserves the old projected residual and angle bounds.
-/
theorem ordinary_three_step_terminal_prefix :
    ∃ δ a C D Cξ Cₘ : ℝ, 0<δ ∧ 0<a ∧ 0<C ∧ 0<D ∧ 0<Cξ ∧ 0<Cₘ ∧
      ∀ (base : Matrix (Fin n) (Fin n) ℝ) (_hb : base.PosDef)
        (A B : ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
        (g : EuclideanSpace ℝ (Fin n)) (ε : ℝ),
      A 0=cgOperator base → 0<ε → ε≤δ → ‖cgCanonicalError base g 0‖≤1 →
      (∀ i≤1, CG.gradient (cgOperator base) g i≠0) →
      (∀ i<3, ‖canonicalOperator base (A i)-ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))‖≤ε) →
      (∀ i<3, ‖canonicalOperator base (B i)-ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))‖≤ε) →
      let m := rfcMethod fullMemory 1 (E := EuclideanSpace ℝ (Fin n))
      let R := cgOperator (metricRoot base)
      let J := cgOperator (metricRoot base)⁻¹
      activeObservedModelBounds base m A B g 3 (1/2) Cₘ ε ∧
      (∀ j≤2, methodRun (gatedMethod fullMemory (1/2)) A B g j=methodRun m A B g j) ∧
      recordedPrefixBound (a*ε) C ε (fun i : Fin 2 => R (probedStep m A B g i.val))
        (J (probedGradient m A B g 2)) ∧
      ∀ i<2, ‖R (probedStep m A B g i)-canonicalCGStep base g i‖≤D*ε ∧
        ‖J (probedSecant m A B g i)-canonicalOperator base (A i) (R (probedStep m A B g i))‖≤
          Cξ*ε^2*‖R (probedStep m A B g i)‖ := by
  obtain ⟨δ,a,C,D,Cξ,hδ,ha,hC,hD,hCξ,hprefix⟩ := gated_second_recorded_prefix (n := n)
  obtain ⟨δr,hδr,hrecord⟩ := gated_recording_radius 3 (1/2) (by norm_num)
  let K := 1+2*gatedCorrectionConstant 3 (1/2)
  have hK : 1≤K := by dsimp only [K]; nlinarith [gatedCorrectionConstant_nonneg 3 (1/2)]
  have hK0 : 0≤K := by linarith
  let a' := a+2*K+1
  have ha' : 0<a' := by dsimp only [a']; positivity
  have haa' : a≤a' := by dsimp only [a']; linarith
  let Cm := 3*(a'+K)+1
  have hCm : 0<Cm := by dsimp only [Cm]; positivity
  refine ⟨min δ (min δr (1/(48*(a'+1)))),a',C,D,Cξ,Cm,
    lt_min hδ (lt_min hδr (by positivity)),ha',hC,hD,hCξ,hCm,?_⟩
  intro base hb A B g ε hA0 hε he hinit hpre hA hB
  have hp := hprefix base hb A B g ε hA0 hε (he.trans (min_le_left _ _)) hinit hpre hA hB
  dsimp only at hp
  let mg := gatedMethod fullMemory (1/2) (E := EuclideanSpace ℝ (Fin n))
  let m := rfcMethod fullMemory 1 (E := EuclideanSpace ℝ (Fin n))
  let R := cgOperator (metricRoot base)
  let J := cgOperator (metricRoot base)⁻¹
  let W := fun j => selectedWindow fullMemory (methodRun mg A B g j)
  have hlen j : (W j).length=j := by dsimp only [W]; rw [fullWindow_methodRun,executedPairs_length]
  obtain ⟨hhalf,hrsmall,hrsize⟩ := hrecord ε hε.le (he.trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hrec := gated_uniform_recorded_bounds base hb fullMemory (1/2) (by norm_num) A B g 3 hε.le hA hB
    hhalf hrsmall hrsize
  have hsmall : ε*(48*(a'+1))≤1 := (le_div_iff₀ (by positivity : 0<48*(a'+1))).mp
    (he.trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hangle : (3 : ℝ)*(a'*ε)≤(1-1/2)/8 := by nlinarith only [hsmall,hε.le]
  have hmodelsG : activeObservedModelBounds base mg A B g 3 (1/2) Cm ε := by
    dsimp only [activeObservedModelBounds]
    intro j hj hd
    have hj2 : j≤2 := by omega
    have hpr := hp.1 j hj2
    have haε : a*ε≤a'*ε := mul_le_mul_of_nonneg_right haa' hε.le
    have hy (i : Fin (W j).length) : ‖dualWindow base (windowImages (W j)) i-primalWindow base (windowSteps (W j)) i‖≤
        (K*ε)*‖primalWindow base (windowSteps (W j)) i‖ :=
      selectedWindow_pair_bound fullMemory mg A B g j R J (K*ε) (fun i hi => hrec.2 i (by omega)) i
    have ht := observed_prefix_model_conditioning base hb (W j) (probedGradient mg A B g j) (A j)
      (N := 3) (a := a'*ε) (η := K*ε) (ε := ε) (γ := 1/2)
      (by omega) (by rw [hlen]; omega) (mul_nonneg ha'.le hε.le) (mul_nonneg hK0 hε.le)
      (by nlinarith) (by dsimp only [a']; nlinarith)
      (by norm_num) (by norm_num) hangle hpr.1 (fun i j hij => (hpr.2.1 i j hij).trans haε) hy hd (hA j hj)
    refine ⟨ht.1,ht.2.1,ht.2.2.1,?_⟩
    rw [canonicalObservedModel_augmented base hb]
    apply ht.2.2.2.trans
    have hj' : (((W j).length+1 : ℕ) : ℝ)≤3 := by rw [hlen]; exact_mod_cast (show j+1≤3 by omega)
    calc
      _ = (((W j).length+1 : ℕ) : ℝ)*(a'+K)*ε := by ring
      _ ≤ 3*(a'+K)*ε := by gcongr
      _ ≤ Cm*ε := by dsimp only [Cm]; nlinarith only [hε.le]
  have heq := hp.2.1
  have hgrad j (hj : j≤2) : probedGradient mg A B g j=probedGradient m A B g j := congrArg History.gradient (heq j hj)
  have hstep j (hj : j<2) : probedStep mg A B g j=probedStep m A B g j :=
    congrArg (fun H : History (EuclideanSpace ℝ (Fin n)) => H.observationList.getD 4 0) (heq (j+1) (by omega))
  have hsecant j (hj : j<2) : probedSecant mg A B g j=probedSecant m A B g j := by
    rw [probedSecant,probedSecant,hgrad (j+1) (by omega),hgrad j (by omega)]
  dsimp only
  refine ⟨?_,heq,?_,?_⟩
  · dsimp only [activeObservedModelBounds] at hmodelsG ⊢
    intro j hj hd
    have ht := hmodelsG j hj
    rw [heq j (by omega)] at ht
    exact ht hd
  · have ht := hp.1 2 le_rfl
    rw [heq 2 le_rfl,hgrad 2 le_rfl,fullWindow_methodRun] at ht
    have hchrono := (recordedPrefixBound_executed_chronological (probedStep m A B g) (probedSecant m A B g)
      R (J (probedGradient m A B g 2)) 2 (a*ε) C ε).mp ht
    exact ⟨hchrono.1,fun i j hij => (hchrono.2.1 i j hij).trans (mul_le_mul_of_nonneg_right haa' hε.le),hchrono.2.2⟩
  · intro i hi
    have ht := hp.2.2 i hi
    rw [hstep i hi,hsecant i hi] at ht
    exact ht

end
end krylov.Correction
