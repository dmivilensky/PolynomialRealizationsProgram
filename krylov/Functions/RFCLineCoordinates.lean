import krylov.Functions.RFCFinalDomains

/-!
Article: main_krylov, prop:Fcycle, the actual current-line coordinate scale.
Use: derive one genuine compact inverse-scale bound and first-order change
of its square, before normalizing actual value defects in the probed basis.
Source: positive true CG line quotients, actual RFC prefix analyticity and
the compact full reference/source first-order theorem.
-/
namespace krylov.Functions
noncomputable section
open Matrix Set Filter Asymptotics Topology krylov.Reference krylov.Methods krylov.Stability
  krylov.Correction krylov.Envelope krylov.Secant krylov.Variation
open scoped InnerProductSpace BigOperators Matrix.Norms.L2Operator
variable {k : ℕ}

/-- The actual last searched-segment scale in the complete physical source chart.
Article: main_krylov, prop:Fcycle, current raw-direction coordinate. -/
def rfcPhysicalLineScale (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ)
    (p : EuclideanSpace ℝ (Fin (k+1)) × RFCPhysicalData k) : ℝ :=
  let A := rfcPhysicalSearch base p.2
  let B := rfcPhysicalCorrection base p.2
  let m := rfcMethod fullMemory 1
  let H := methodRun m A B p.1 k
  let d := m.direction H
  lineLength H.gradient d (A k d)

/-- The real source-chart line quotient is precisely the actual positive CG quotient at zero perturbation.
Article: main_krylov, prop:Fcycle. -/
theorem rfcPhysicalLineScale_reference
    (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin (k+1))) :
    rfcPhysicalLineScale base (g,0)=CG.length (cgOperator base) g k := by
  obtain ⟨hQ,hpos⟩ := cgOperator_positive base hb
  dsimp only [rfcPhysicalLineScale]
  rw [(rfcPhysicalPaths_zero base).1,(rfcPhysicalPaths_zero base).2]
  have hd := rfc_reference_direction fullMemory 1 (cgOperator base) hQ hpos g (fun _ _ ha=>ha) k
  change (rfcMethod fullMemory 1).direction (methodRun _ _ _ _ _)=_ at hd
  rw [(rfcMethod_static fullMemory 1 (cgOperator base) hQ hpos g (fun _ _ ha=>ha) k).1,hd]

set_option maxHeartbeats 800000 in
/-- The actual source-chart last line quotient is analytic on its genuine nondegenerate quadratic domain.
Article: main_krylov, prop:Fcycle and lem:U. -/
theorem rfcPhysicalLineScale_analyticAt
    (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin (k+1)))
    (hpre : ∀ i≤k,CG.gradient (cgOperator base) g i≠0) :
    AnalyticAt ℝ (rfcPhysicalLineScale base) (g,0) := by
  let P := EuclideanSpace ℝ (Fin (k+1)) × RFCPhysicalData k
  let A := fun p : P=>rfcPhysicalSearch base p.2
  let B := fun p : P=>rfcPhysicalCorrection base p.2
  have hA i : AnalyticAt ℝ (fun p=>A p i) (g,0) := by
    simpa only [A,Function.comp_def] using (rfcPhysicalSearch_analyticAt base (0 : RFCPhysicalData k) i).comp
      (f := fun p : P=>p.2) (x := (g,0)) analyticAt_snd
  have hB i : AnalyticAt ℝ (fun p=>B p i) (g,0) := by
    simpa only [B,Function.comp_def] using (rfcPhysicalCorrection_analyticAt base (0 : RFCPhysicalData k) i).comp
      (f := fun p : P=>p.2) (x := (g,0)) analyticAt_snd
  obtain ⟨hQ,hpos⟩ := cgOperator_positive base hb
  have hAx : A (g,0)=fun _=>cgOperator base := (rfcPhysicalPaths_zero base).1
  have hBx : B (g,0)=fun _=>cgOperator base := (rfcPhysicalPaths_zero base).2
  have ht := quadraticRFC_prefix_analytic fullMemory 1 A B Prod.fst (g,0) hA hB analyticAt_fst
    (cgOperator base) hAx hBx hQ hpos (fun _ _ ha=>ha) (k+1) (fun i hi=>hpre i (by omega))
  have hG := (quadraticRFC_prefix_analytic fullMemory 1 A B Prod.fst (g,0) hA hB analyticAt_fst
    (cgOperator base) hAx hBx hQ hpos (fun _ _ ha=>ha) k (fun i hi=>hpre i hi.le)).1
  let d := fun p : P=>(rfcMethod fullMemory 1).direction (methodRun (rfcMethod fullMemory 1) (A p) (B p) p.1 k)
  have hd : AnalyticAt ℝ d (g,0) := (ht.2 k (by omega)).1
  have hz := analytic_operator_apply (hA k) hd
  have hdx : d (g,0)=CG.direction (cgOperator base) g k := by
    dsimp only [d]
    rw [hAx,hBx]
    exact rfc_reference_direction fullMemory 1 (cgOperator base) hQ hpos g (fun _ _ ha=>ha) k
  have hc : inner ℝ (d (g,0)) (A (g,0) k (d (g,0)))≠0 := by
    rw [hdx,hAx]
    exact (hpos _ (CG.invariant_line_pos (cgOperator base) hpos g k
      (CG.invariant (cgOperator base) hQ hpos g k (fun i hi=>hpre i hi.le)) (hpre k le_rfl)).1).ne'
  exact (analytic_inner hd hG).neg.div (analytic_inner hd hz) hc

set_option maxHeartbeats 800000 in
/-- The original actual last gate passes on one compact physical source tube.
Article: main_krylov, prop:Fcycle, genuine observed branch domain. -/
theorem compact_rfc_physical_gate
    (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (hb : base.PosDef) (hk : 0<k)
    (K : Set (EuclideanSpace ℝ (Fin (k+1)))) (hK : IsCompact K)
    (hpre : ∀ g∈K,∀ i≤k,CG.gradient (cgOperator base) g i≠0) :
    ∃ δ : ℝ, 0<δ ∧ ∀ g∈K,∀ v : EuclideanSpace ℝ (Fin (k+1)),∀ Θ : RFCPhysicalData k,
      ‖(v,Θ)‖≤δ → rfcFunctionGate fullMemory
        (methodRun (rfcMethod fullMemory 1) (rfcPhysicalSearch base Θ) (rfcPhysicalCorrection base Θ) (g+v) k) := by
  let P := EuclideanSpace ℝ (Fin (k+1)) × RFCPhysicalData k
  let A := fun p : P=>rfcPhysicalSearch base p.2
  let B := fun p : P=>rfcPhysicalCorrection base p.2
  refine compact_reference_eventual_tube
    (fun p : P=>rfcFunctionGate fullMemory (methodRun (rfcMethod fullMemory 1) (A p) (B p) p.1 k)) K hK ?_
  intro g hg
  have hA i : AnalyticAt ℝ (fun p=>A p i) (g,0) := by
    simpa only [A,Function.comp_def] using (rfcPhysicalSearch_analyticAt base (0 : RFCPhysicalData k) i).comp
      (f := fun p : P=>p.2) (x := (g,0)) analyticAt_snd
  have hB i : AnalyticAt ℝ (fun p=>B p i) (g,0) := by
    simpa only [B,Function.comp_def] using (rfcPhysicalCorrection_analyticAt base (0 : RFCPhysicalData k) i).comp
      (f := fun p : P=>p.2) (x := (g,0)) analyticAt_snd
  exact rfcFunctionGate_eventually A B Prod.fst (g,0) hA hB analyticAt_fst (cgOperator base)
    (rfcPhysicalPaths_zero base).1 (rfcPhysicalPaths_zero base).2 (cgOperator_positive base hb).1
    (cgOperator_positive base hb).2 k hk (hpre g hg)

set_option maxHeartbeats 800000 in
/-- The true inverse current-line scale and its square have compact-uniform bounds and a true first-order source change.
Article: main_krylov, prop:Fcycle, normalization of actual observed defects.
Proof: use the actual analytic positive CG quotient, compact first-order
control of its inverse square and boundedness of its actual reference values. -/
theorem compact_rfc_line_inverse_square
    (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (hb : base.PosDef)
    (K : Set (EuclideanSpace ℝ (Fin (k+1)))) (hK : IsCompact K)
    (hpre : ∀ g∈K,∀ i≤k,CG.gradient (cgOperator base) g i≠0) :
    ∃ δ C M : ℝ, 0<δ ∧ 0<C ∧ 0<M ∧ ∀ g∈K,
      ∀ v : EuclideanSpace ℝ (Fin (k+1)),∀ Θ : RFCPhysicalData k, ‖(v,Θ)‖≤δ →
        rfcPhysicalLineScale base (g+v,Θ)≠0 ∧
        |(rfcPhysicalLineScale base (g+v,Θ))⁻¹^2|≤M ∧
        |(rfcPhysicalLineScale base (g+v,Θ))⁻¹^2-(CG.length (cgOperator base) g k)⁻¹^2|≤C*‖(v,Θ)‖ := by
  let F := fun p : EuclideanSpace ℝ (Fin (k+1)) × RFCPhysicalData k=> (rfcPhysicalLineScale base p)⁻¹^2
  have hn g (hg : g∈K) : rfcPhysicalLineScale base (g,0)≠0 := by
    rw [rfcPhysicalLineScale_reference base hb g]
    exact (CG.invariant_line_pos (cgOperator base) (cgOperator_positive base hb).2 g k
      (CG.invariant (cgOperator base) (cgOperator_positive base hb).1 (cgOperator_positive base hb).2 g k
        (fun i hi=>hpre g hg i hi.le)) (hpre g hg k le_rfl)).2.1.ne'
  have ha g (hg : g∈K) : AnalyticAt ℝ F (g,0) :=
    ((rfcPhysicalLineScale_analyticAt base hb g (hpre g hg)).inv (hn g hg)).pow 2
  obtain ⟨δ,C,hδ,hC,hbound⟩ := compact_reference_full_first_order F K hK ha
  obtain ⟨δn,hδn,hnonzero⟩ := compact_reference_eventual_tube
    (fun p=>rfcPhysicalLineScale base p≠0) K hK
      (fun g hg=>(rfcPhysicalLineScale_analyticAt base hb g (hpre g hg)).continuousAt.eventually_ne (hn g hg))
  have hc : ContinuousOn (fun g=>F (g,0)) K := by
    intro g hg
    have hh : ContinuousAt (fun q : EuclideanSpace ℝ (Fin (k+1))=>F (q,0)) g :=
      (ha g hg).continuousAt.comp
        (f := fun q : EuclideanSpace ℝ (Fin (k+1))=>(q,(0 : RFCPhysicalData k)))
        (continuousAt_id.prodMk continuousAt_const)
    exact hh.continuousWithinAt
  obtain ⟨M,hM⟩ := hK.exists_bound_of_continuousOn hc
  refine ⟨min δ δn,C,max M 0+C*δ+1,lt_min hδ hδn,hC,by positivity,?_⟩
  intro g hg v Θ hnorm
  have he := hbound g hg v Θ (hnorm.trans (min_le_left _ _))
  have he' : |F (g+v,Θ)-F (g,0)|≤C*‖(v,Θ)‖ := by
    simpa only [Real.norm_eq_abs,Prod.add_def,add_zero] using he
  refine ⟨hnonzero g hg v Θ (hnorm.trans (min_le_right _ _)),?_,?_⟩
  · calc
      _ ≤ |F (g+v,Θ)-F (g,0)|+|F (g,0)| := by simpa only [Real.norm_eq_abs] using norm_le_norm_sub_add (F (g+v,Θ)) (F (g,0))
      _ ≤ C*‖(v,Θ)‖+M := add_le_add he' (by simpa only [Real.norm_eq_abs] using hM g hg)
      _ ≤ max M 0+C*δ+1 := by
        have hb' := mul_le_mul_of_nonneg_left (hnorm.trans (min_le_left δ δn)) hC.le
        linarith [le_max_left M 0]
  · simpa only [F,rfcPhysicalLineScale_reference base hb g] using he'

end
end krylov.Functions
