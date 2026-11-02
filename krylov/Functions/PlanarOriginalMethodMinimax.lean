import krylov.Functions.PlanarOriginalMinimax
import krylov.Functions.PlanarCentreAdmission

/-!
Article: main_krylov, thm:Fplanar, original one-correction class minimax.
Use: take the infimum over actual retained-span, globally quadratic-consistent
one-correction value rules, and retain their complete actual search transcript
and the original independent base interval in the source supremum.
The lower comparison allows every rich-transcript decision. The matching
upper is witnessed by the concrete endpoint-only budgeted centre method.
Source: exact scalar information fibres and the genuine admitted final rule.
This is the article's finite planar model; native full-dimensional scalar
execution and true-minimizer sharpness are proved in ReferencePlane*.
-/
namespace krylov.Functions
noncomputable section
open krylov.Methods krylov.Tensor.BinaryCubic
open scoped InnerProductSpace ENNReal

set_option maxHeartbeats 800000 in
/-- Equal binary information gives identical complete true planar search
transcripts, including actual scalar values, gradients and whole line
objectives. Article: main_krylov, thm:Fplanar. -/
theorem planeCycleTranscript_fibre_equal (p r : ℝ) (t u : krylov.Tensor.BinaryCubic)
    (hobs : observe r t=observe r u) :
    planeCycleTranscript p r (planeCubicObjective p r u)=
      planeCycleTranscript p r (planeCubicObjective p r t) := by
  let e := planeOfPair (1,0)
  let h := planeOfPair (0,1)
  have hproject (x : Plane) : hilbertPlaneProject e h x=x := by
    ext i
    fin_cases i <;> simp [hilbertPlaneProject,e,h,planeOfPair,PiLp.inner_apply,Fin.sum_univ_two]
  have hf (v : krylov.Tensor.BinaryCubic) :
      hilbertPlaneObjective e h 0 p r v=planeCubicObjective p r v := by
    funext x
    simp [hilbertPlaneObjective,hproject]
  have hpoints i (_ : i≤2) :
      (inner ℝ e (planeCycleNode p r i)=0 ∧ inner ℝ h (planeCycleNode p r i)=0) ∨
      (inner ℝ e (planeCycleNode p r i)=p ∧ inner ℝ h (planeCycleNode p r i)=0) ∨
      (inner ℝ e (planeCycleNode p r i)=p ∧ inner ℝ h (planeCycleNode p r i)=r*p) := by
    by_cases hi : i=0
    · subst i
      simp [planeCycleNode]
    · by_cases hi₁ : i=1
      · subst i
        simp [planeCycleNode,e,h,planeOfPair,PiLp.inner_apply,Fin.sum_univ_two]
      · simp [planeCycleNode,hi,hi₁,e,h,planeOfPair,PiLp.inner_apply,Fin.sum_univ_two]
  have hlines i (hi : i<2) :
      (inner ℝ h (planeCycleNode p r i)=0 ∧ inner ℝ h (planeCycleStep p r i)=0) ∨
      (inner ℝ e (planeCycleNode p r i)=p ∧ inner ℝ e (planeCycleStep p r i)=0) := by
    have hs : i=0 ∨ i=1 := by omega
    rcases hs with rfl|rfl <;>
      simp [planeCycleNode,planeCycleStep,e,h,planeOfPair,PiLp.inner_apply,Fin.sum_univ_two]
  have ht := hilbertPlaneObjective_transcript_equal e h 0 p r t u hobs
    (planeCycleNode p r) (planeCycleStep p r) 2 hpoints hlines
  simpa only [hf,planeCycleTranscript] using! ht

/-- The actual original retained-span final value decision in the finite
planar model, using its complete true observed transcript. Article: thm:Fplanar. -/
def planeValueMethodOutput (M : OneCorrectionValueMethod Plane 2) (H : History Plane)
    (p r : ℝ) (f : Plane → ℝ) : Plane :=
  observedSpanFinalPolicy (by decide) M.coefficients H (planeCycleTranscript p r f)

/-- Full original-base source risk of a genuine admitted one-correction
value method. Article: main_krylov, thm:Fplanar, original method supremum. -/
def planeOriginalMethodWorst (B r p L : ℝ) (H : History Plane)
    (M : OneCorrectionValueMethod Plane 2) : ℝ≥0∞ :=
  ⨆ t : {t : krylov.Tensor.BinaryCubic // t.InBall},
    ⨆ β : {β : ℝ // |β|≤L*p},
      let f := planeUnknownBaseObjective p r β.val (scaleBinaryCubic B t.val)
      ENNReal.ofReal ‖gradient f (planeValueMethodOutput M H p r f)‖

/-- The infimum over the original one-correction value rules of their
actual full independent-base planar risks. Article: thm:Fplanar. -/
def planeOriginalMethodMinimax (B r p L : ℝ) (H : History Plane) : ℝ≥0∞ :=
  ⨅ M : OneCorrectionValueMethod Plane 2, planeOriginalMethodWorst B r p L H M

/-- Every actual retained-span method has the sharp information lower
coefficient, even when it can inspect the whole true search transcript.
Article: main_krylov, thm:Fplanar, original-class lower bound. -/
theorem planeOriginalMethodWorst_lower (B r L : ℝ) (hB : 0<B) (hr : 0<r)
    (hL : B/2*Real.sqrt (1+r^2)≤L) :
    ∃ C : ℝ, 0<C ∧ ∀ p : ℝ, 0<p → B*p≤1 → ∀ H : History Plane,
      ∀ M : OneCorrectionValueMethod Plane 2,
      ENNReal.ofReal (B^2*(r^2/4*Real.sqrt (1+4*r^2)*fibreMinimax r)*p^3-C*p^4)≤
        planeOriginalMethodWorst B r p L H M := by
  obtain ⟨C,hC,hlower⟩ := planeBetaPolicyWorst_lower B r hB hr
  refine ⟨C,hC,?_⟩
  intro p hp hp₁ H M
  let output := fun t : krylov.Tensor.BinaryCubic=>planeValueMethodOutput M H p r (planeCubicObjective p r t)
  obtain ⟨policy,hpolicy⟩ := binary_observation_policy r output (by
    intro t u hobs
    dsimp only [output,planeValueMethodOutput]
    rw [planeCycleTranscript_fibre_equal p r t u hobs])
  apply (hlower p 0 hp hp₁ le_rfl policy).trans
  apply iSup_le
  intro t
  apply iSup_le
  intro β
  have hz : β.val=0 := by
    have hb := β.property
    simp only [zero_mul] at hb
    exact abs_nonpos_iff.mp hb
  let q := scaleBinaryCubic B t.val
  let b := -(p*(q.t2+r*q.t3)/2)
  have hq : |q.t2+r*q.t3|≤B*Real.sqrt (1+r^2) := by
    have he : q.t2+r*q.t3=B*(t.val.t2+r*t.val.t3) := by dsimp only [q,scaleBinaryCubic]; ring
    rw [he,abs_mul,abs_of_pos hB]
    exact mul_le_mul_of_nonneg_left (binary_last_base_bound r t.val t.property) hB.le
  have hb : |b|≤L*p := by
    dsimp only [b]
    rw [abs_neg,abs_div,abs_mul,abs_of_pos hp,show |(2:ℝ)|=2 by norm_num]
    have hh := mul_le_mul_of_nonneg_left hq hp.le
    have hl := mul_le_mul_of_nonneg_right hL hp.le
    nlinarith only [hh,hl]
  apply le_iSup_of_le t
  apply le_iSup_of_le ⟨b,hb⟩
  have hf : planeUnknownBaseObjective p r b q=planeCubicObjective p r q := by
    funext x
    simp only [planeUnknownBaseObjective,b,neg_add_cancel,planeBetaCubicObjective,zero_div,zero_mul,add_zero]
  change ENNReal.ofReal ‖gradient (planeBetaCubicObjective p r β.val q) (policy (observe r q))‖≤
    ENNReal.ofReal ‖gradient (planeUnknownBaseObjective p r b q)
      (planeValueMethodOutput M H p r (planeUnknownBaseObjective p r b q))‖
  rw [hz,hpolicy,hf]
  simp only [planeBetaCubicGradient_actual,zero_mul,zero_smul,add_zero]
  exact le_rfl

/-- The admitted original endpoint-only method controls every tensor and
every independent original base. Article: thm:Fplanar, attained class upper. -/
theorem planeOriginalMethodWorst_centre_upper (B r L : ℝ) (hB : 0<B) (hr : 0<r) (hL : 0≤L) :
    ∃ C : ℝ, 0<C ∧ ∀ p : ℝ, 0<p → B*p≤1 → ∀ H : History Plane,
      planeOriginalMethodWorst B r p L H
        (budgetedCentreValueMethod (ContinuousLinearEquiv.refl ℝ Plane) B (by decide))≤
        ENNReal.ofReal (B^2*(r^2/4*Real.sqrt (1+4*r^2)*fibreMinimax r)*p^3+C*p^4) := by
  obtain ⟨C,hC,hupper⟩ := planeBudgetObservedCentreOutput_beta_gradient_upper
    B r (L+B/2*Real.sqrt (1+r^2)) hB hr.ne' (by positivity)
  refine ⟨C,hC,?_⟩
  intro p hp hp₁ H
  apply iSup_le
  intro t
  apply iSup_le
  intro β
  let q := scaleBinaryCubic B t.val
  let b := β.val+p*(q.t2+r*q.t3)/2
  have hq : |q.t2+r*q.t3|≤B*Real.sqrt (1+r^2) := by
    have he : q.t2+r*q.t3=B*(t.val.t2+r*t.val.t3) := by dsimp only [q,scaleBinaryCubic]; ring
    rw [he,abs_mul,abs_of_pos hB]
    exact mul_le_mul_of_nonneg_left (binary_last_base_bound r t.val t.property) hB.le
  have hb : |b|≤(L+B/2*Real.sqrt (1+r^2))*p := by
    apply (abs_add_le _ _).trans
    rw [abs_div,abs_mul,abs_of_pos hp,show |(2:ℝ)|=2 by norm_num]
    have hh := mul_le_mul_of_nonneg_left hq hp.le
    nlinarith only [β.property,hh]
  change ENNReal.ofReal ‖gradient (planeBetaCubicObjective p r b q)
    (observedSpanFinalPolicy (by decide)
      (budgetedCentreValueMethod (ContinuousLinearEquiv.refl ℝ Plane) B (by decide)).coefficients
      H (planeCycleTranscript p r (planeBetaCubicObjective p r b q)))‖≤_
  rw [planeBudgetObservedCentreOutput_admitted B p r b hp hr q H]
  exact ENNReal.ofReal_le_ofReal (hupper p hp hp₁ b hb t.val t.property)

/-- The original one-correction method infimum of full independent-base
source suprema has exactly the sharp printed information coefficient.
One genuine globally quadratic-consistent endpoint-only method attains
the upper bound. Constants precede the actual history and all competitors.
Article: main_krylov, thm:Fplanar, complete original-class planar minimax. -/
theorem planeOriginalMethodMinimax_bounds (B r L : ℝ) (hB : 0<B) (hr : 0<r)
    (hL : B/2*Real.sqrt (1+r^2)≤L) :
    ∃ C : ℝ, 0<C ∧ ∀ p : ℝ, 0<p → B*p≤1 → ∀ H : History Plane,
      ENNReal.ofReal (B^2*(r^2/4*Real.sqrt (1+4*r^2)*fibreMinimax r)*p^3-C*p^4)≤
        planeOriginalMethodMinimax B r p L H ∧
      planeOriginalMethodMinimax B r p L H≤
        planeOriginalMethodWorst B r p L H
          (budgetedCentreValueMethod (ContinuousLinearEquiv.refl ℝ Plane) B (by decide)) ∧
      planeOriginalMethodWorst B r p L H
          (budgetedCentreValueMethod (ContinuousLinearEquiv.refl ℝ Plane) B (by decide))≤
        ENNReal.ofReal (B^2*(r^2/4*Real.sqrt (1+4*r^2)*fibreMinimax r)*p^3+C*p^4) := by
  have hL₀ : 0≤L := (mul_nonneg (div_nonneg hB.le (by norm_num)) (Real.sqrt_nonneg _)).trans hL
  obtain ⟨Cl,hCl,hlower⟩ := planeOriginalMethodWorst_lower B r L hB hr hL
  obtain ⟨Cu,hCu,hupper⟩ := planeOriginalMethodWorst_centre_upper B r L hB hr hL₀
  refine ⟨Cl+Cu,by positivity,?_⟩
  intro p hp hp₁ H
  refine ⟨?_,iInf_le _ _,?_⟩
  · apply le_iInf
    intro M
    apply (ENNReal.ofReal_le_ofReal (sub_le_sub_left
      (mul_le_mul_of_nonneg_right (by linarith only [hCu] : Cl≤Cl+Cu) (pow_nonneg hp.le 4)) _)).trans
    exact hlower p hp hp₁ H M
  · exact (hupper p hp hp₁ H).trans (ENNReal.ofReal_le_ofReal (add_le_add le_rfl
      (mul_le_mul_of_nonneg_right (by linarith only [hCl] : Cu≤Cl+Cu) (pow_nonneg hp.le 4))))

/-- The printed planar minimax equality in relative-error form, with the
original independent beta interval and original one-correction class.
The known tensor budget is exactly 2(1-delta); its sharp coefficient is
(1-delta)^2 r^2 sqrt(1+4r^2) M_F(r). The same actual centre is the upper
attainer throughout the source class. Article: main_krylov, thm:Fplanar. -/
theorem planeOriginalMethodMinimax_printed_equality (r L δ : ℝ) (hr : 0<r) (hδ : δ<1)
    (hL : (1-δ)*Real.sqrt (1+r^2)≤L) :
    ∃ C : ℝ, 0<C ∧ ∀ p : ℝ, 0<p → 2*(1-δ)*p≤1 → ∀ H : History Plane,
      let K := (1-δ)^2*r^2*Real.sqrt (1+4*r^2)*fibreMinimax r
      ENNReal.ofReal (K*p^3*(1-C*p))≤planeOriginalMethodMinimax (2*(1-δ)) r p L H ∧
      planeOriginalMethodMinimax (2*(1-δ)) r p L H≤
        planeOriginalMethodWorst (2*(1-δ)) r p L H
          (budgetedCentreValueMethod (ContinuousLinearEquiv.refl ℝ Plane) (2*(1-δ)) (by decide)) ∧
      planeOriginalMethodWorst (2*(1-δ)) r p L H
          (budgetedCentreValueMethod (ContinuousLinearEquiv.refl ℝ Plane) (2*(1-δ)) (by decide))≤
        ENNReal.ofReal (K*p^3*(1+C*p)) := by
  have ha : 0<1-δ := sub_pos.mpr hδ
  have hL' : (2*(1-δ))/2*Real.sqrt (1+r^2)≤L := by
    convert hL using 1
    ring
  obtain ⟨C,hC,hbound⟩ := planeOriginalMethodMinimax_bounds (2*(1-δ)) r L (by positivity) hr hL'
  let K := (1-δ)^2*r^2*Real.sqrt (1+4*r^2)*fibreMinimax r
  have hK : 0<K := by
    have hM := binaryFibreMinimax_pos r
    dsimp only [K]
    positivity
  refine ⟨C/K,div_pos hC hK,?_⟩
  intro p hp hp₁ H
  dsimp only
  have hb := hbound p hp hp₁ H
  have heq : (2*(1-δ))^2*(r^2/4*Real.sqrt (1+4*r^2)*fibreMinimax r)=K := by dsimp only [K]; ring
  rw [heq] at hb
  have hlo : K*p^3*(1-(C/K)*p)=K*p^3-C*p^4 := by field_simp [hK.ne']
  have hhi : K*p^3*(1+(C/K)*p)=K*p^3+C*p^4 := by field_simp [hK.ne']
  change ENNReal.ofReal (K*p^3*(1-(C/K)*p))≤_ ∧ _ ∧
    _≤ENNReal.ofReal (K*p^3*(1+(C/K)*p))
  rw [hlo,hhi]
  exact hb

end
end krylov.Functions
