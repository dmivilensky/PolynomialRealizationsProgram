import krylov.Correction.RFCSOperatorTube
import krylov.Correction.RFCSLineStep
import krylov.Stability.CompactFirstOrder

/-!
Article: main_krylov, thm:RFCS, actual search-field perturbation control.
Use: Derive joint regularity and compact uniform first-order changes of real
RFC-S search lengths, predicted line displacements and physical corrections.
Source: genuine measured-prefix analyticity, exact positive quadratic search
curvature, the original zero-correction CG transcript and compact Taylor tubes.
-/

namespace krylov.Correction
noncomputable section
open Set krylov.Methods krylov.Reference krylov.Stability
open scoped InnerProductSpace
variable {k : ℕ}

/-- The actual data-only secant-predicted search length in the genuine finite direct-source RFC-S run.
Use: Compare the real nonlinear probe length to its actual predicted search length.
Article: main_krylov, thm:RFCS, actual uniform search and correction control.
-/
def rfcsDirectAlpha (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (i : ℕ)
    (z : EuclideanSpace ℝ (Fin (k+1)) × RFCSOperatorParameters (k+1)) : ℝ :=
  let d := rfcSDirection fullMemory (rfcsDirectProbe base z) (rfcsDirectLine base z) (rfcsDirectLine base z) z.1 i
  lineLength (rfcSGradient fullMemory (rfcsDirectProbe base z) (rfcsDirectLine base z) (rfcsDirectLine base z) z.1 i)
    d (rfcsDirectProbe base z i d)

/-- The genuine predicted line displacement of the actual direct-source RFC-S run.
Use: Separate the actual line/probe mismatch from the full evaluated step.
Article: main_krylov, thm:RFCS, actual uniform search and correction control.
-/
def rfcsDirectLineStep (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (i : ℕ)
    (z : EuclideanSpace ℝ (Fin (k+1)) × RFCSOperatorParameters (k+1)) :=
  rfcSLineStep fullMemory (rfcsDirectProbe base z) (rfcsDirectLine base z) (rfcsDirectLine base z) z.1 i

/-- The actual physical correction displacement in the genuine direct-source RFC-S run.
Use: Retain the true correction term when comparing real probe and full-step averaged Hessians.
Article: main_krylov, thm:RFCS, actual uniform search and correction control.
-/
def rfcsDirectCorrection (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (i : ℕ)
    (z : EuclideanSpace ℝ (Fin (k+1)) × RFCSOperatorParameters (k+1)) :=
  rfcSStep fullMemory (rfcsDirectProbe base z) (rfcsDirectLine base z) (rfcsDirectLine base z) z.1 i-
    rfcsDirectLineStep base i z

/-- On the original quadratic reference, the genuine RFC-S search length and line step are the true CG quantities and its actual correction is zero, including stopped tails.
Use: Identify the actual unperturbed search fields without a nonstagnation premise.
Article: main_krylov, thm:RFCS, actual uniform search and correction control.
Proof: Use exact-probe transcript equality, the real CG direction and gradient, and the proved reference identity for the actual total recorded step.
-/
theorem rfcs_direct_alpha_reference (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin (k+1))) (i : ℕ) :
    rfcsDirectAlpha base i (g,0)=CG.length (cgOperator base) g i ∧
      rfcsDirectLineStep base i (g,0)=referenceStep (cgOperator base) g i ∧
      rfcsDirectCorrection base i (g,0)=0 := by
  let Q := cgOperator base
  have hQ := cgOperator_positive base hb
  have hz := rfcs_direct_operators_zero base g
  have hm : ∀ j, CG.gradient Q g j≠0 → 0<j → 0<fullMemory j := fun _ _ hj => hj
  have hd : rfcSDirection fullMemory (fun _ => Q) (fun _ => Q) (fun _ => Q) g i=CG.direction Q g i := by
    rw [(rfcSFields_exact fullMemory (fun _ => Q) (fun _ => Q) g i).2.1]
    exact rfc_reference_direction fullMemory 1 Q hQ.1 hQ.2 g hm i
  have hg : rfcSGradient fullMemory (fun _ => Q) (fun _ => Q) (fun _ => Q) g i=CG.gradient Q g i :=
    (rfcSRun_static fullMemory Q hQ.1 hQ.2 g hm i).1
  have ha : rfcsDirectAlpha base i (g,0)=CG.length Q g i := by
    unfold rfcsDirectAlpha
    dsimp only
    rw [hz.1,hz.2,hd,hg]
  have hl : rfcsDirectLineStep base i (g,0)=referenceStep Q g i := by
    unfold rfcsDirectLineStep rfcSLineStep
    dsimp only
    rw [hz.1,hz.2,hd,hg]
    rfl
  refine ⟨ha,hl,?_⟩
  unfold rfcsDirectCorrection
  rw [hl,hz.1,hz.2,(rfcSFields_exact fullMemory (fun _ => Q) (fun _ => Q) g i).2.2.1,
    (rfc_reference_pair fullMemory 1 Q hQ.1 hQ.2 g hm i).1,sub_self]

/-- The genuine search length, predicted line step and actual correction are jointly analytic near every full-active reference initial gradient.
Use: Derive actual nonlinear line and correction perturbation bounds on genuine search domains.
Article: main_krylov, thm:RFCS, actual uniform search and correction control.
Proof: The real prefix supplies analytic gradient and direction fields. Positive actual CG curvature justifies the genuine search quotient; multiplying by the actual direction and subtracting from the true total step gives the remaining fields.
-/
theorem rfcs_direct_search_fields_analytic (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin (k+1))) (hN : k+1≤referenceAtomCount base hb g)
    (i : ℕ) (hi : i<k+1) :
    AnalyticAt ℝ (rfcsDirectAlpha base i) (g,0) ∧
      AnalyticAt ℝ (rfcsDirectLineStep base i) (g,0) ∧
      AnalyticAt ℝ (rfcsDirectCorrection base i) (g,0) := by
  let Q := cgOperator base
  have hQ := cgOperator_positive base hb
  have hz := rfcs_direct_operators_zero base g
  have ht := rfcs_direct_prefix_analytic base hb g (k+1) hN
  have hg := (rfcs_direct_prefix_analytic base hb g i (hi.le.trans hN)).1
  let d := fun z => rfcSDirection fullMemory (rfcsDirectProbe base z) (rfcsDirectLine base z) (rfcsDirectLine base z) z.1 i
  have hd : AnalyticAt ℝ d (g,0) := (ht.2 i hi).1
  have hp := analytic_operator_apply ((rfcs_direct_operators_analytic base g).2 i) hd
  have hdx : d (g,0)=CG.direction Q g i := by
    dsimp only [d]
    rw [hz.1,hz.2,(rfcSFields_exact fullMemory (fun _ => Q) (fun _ => Q) g i).2.1]
    exact rfc_reference_direction fullMemory 1 Q hQ.1 hQ.2 g (fun _ _ hj => hj) i
  have hcurv : inner ℝ (d (g,0)) (rfcsDirectProbe base (g,0) i (d (g,0)))≠0 := by
    rw [hz.2,hdx]
    exact (hQ.2 _ (CG.invariant_line_pos Q hQ.2 g i
      (CG.invariant Q hQ.1 hQ.2 g i (fun j hj => cg_nonstagnation base hb g j (hj.trans_le (hi.le.trans hN))))
      (cg_nonstagnation base hb g i (hi.trans_le hN))).1).ne'
  have ha : AnalyticAt ℝ (rfcsDirectAlpha base i) (g,0) :=
    (analytic_inner hd hg).neg.div (analytic_inner hd hp) hcurv
  have hl : AnalyticAt ℝ (rfcsDirectLineStep base i) (g,0) := ha.smul hd
  exact ⟨ha,hl,((ht.2 i hi).2.1).sub hl⟩


/-- One compact-reference tube uniformly controls the changes of every genuine RFC-S search length and predicted line step and bounds every actual correction to first order in the real input perturbations.
Use: Obtain quadratic physical correction and line-step errors after actual nonlinear cycle scaling.
Article: main_krylov, thm:RFCS, actual uniform search and correction control.
Proof: Apply the proved compact first-order Taylor bound to the entire finite product of true search fields and identify its actual reference coordinates with CG and zero corrections.
-/
theorem compact_rfcs_search_field_changes (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (hb : base.PosDef)
    (K : Set (EuclideanSpace ℝ (Fin (k+1)))) (hK : IsCompact K)
    (hN : ∀ g∈K, k+1≤referenceAtomCount base hb g) :
    ∃ δ C : ℝ, 0<δ ∧ 0<C ∧ ∀ g∈K, ∀ v : EuclideanSpace ℝ (Fin (k+1)),
      ∀ Θ : RFCSOperatorParameters (k+1), ‖(v,Θ)‖≤δ → ∀ i<k+1,
      |rfcsDirectAlpha base i (g+v,Θ)-CG.length (cgOperator base) g i|≤C*‖(v,Θ)‖ ∧
      ‖rfcsDirectLineStep base i (g+v,Θ)-referenceStep (cgOperator base) g i‖≤C*‖(v,Θ)‖ ∧
      ‖rfcsDirectCorrection base i (g+v,Θ)‖≤C*‖(v,Θ)‖ := by
  let f := fun z => fun i : Fin (k+1) =>
    (rfcsDirectAlpha base i.val z,rfcsDirectLineStep base i.val z,rfcsDirectCorrection base i.val z)
  have hf (g) (hg : g∈K) : AnalyticAt ℝ f (g,0) := by
    apply AnalyticAt.pi
    intro i
    have h := rfcs_direct_search_fields_analytic base hb g (hN g hg) i.val i.isLt
    exact h.1.prod (h.2.1.prod h.2.2)
  obtain ⟨δ,C,hδ,hC,hbound⟩ := compact_reference_full_first_order f K hK hf
  refine ⟨δ,C,hδ,hC,?_⟩
  intro g hg v Θ hΘ i hi
  have h := hbound g hg v Θ hΘ
  have he := (norm_le_pi_norm (f (g+v,Θ)-f (g,0)) (⟨i,hi⟩ : Fin (k+1))).trans h
  have ha := (norm_fst_le ((f (g+v,Θ)-f (g,0)) ⟨i,hi⟩)).trans he
  have hl := (norm_fst_le ((f (g+v,Θ)-f (g,0)) ⟨i,hi⟩).2).trans
    ((norm_snd_le ((f (g+v,Θ)-f (g,0)) ⟨i,hi⟩)).trans he)
  have hc := (norm_snd_le ((f (g+v,Θ)-f (g,0)) ⟨i,hi⟩).2).trans
    ((norm_snd_le ((f (g+v,Θ)-f (g,0)) ⟨i,hi⟩)).trans he)
  dsimp only [f,Pi.sub_apply,Prod.mk_sub_mk] at ha hl hc
  rw [(rfcs_direct_alpha_reference base hb g i).1,Real.norm_eq_abs] at ha
  rw [(rfcs_direct_alpha_reference base hb g i).2.1] at hl
  rw [(rfcs_direct_alpha_reference base hb g i).2.2,sub_zero] at hc
  exact ⟨ha,hl,hc⟩

end
end krylov.Correction
