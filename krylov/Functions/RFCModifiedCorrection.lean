import krylov.Functions.RFCModifiedPhysical

/-!
Article: main_krylov, prop:Fcycle, the actual changed final-query bootstrap.
Use: bound the genuine modified last correction before enclosing its new
Hessian-average query. The unchanged ordinary prefix and an independent
observed model change form the original finite source chart.
Source: actual analytic inverse solves, full-dimensional CG termination and
compact analytic flatness at order one.
-/

namespace krylov.Functions
noncomputable section
open Matrix Set Filter Asymptotics Topology krylov.Reference krylov.Methods krylov.Stability
  krylov.Correction krylov.Envelope krylov.Secant krylov.Variation
open scoped InnerProductSpace BigOperators Matrix.Norms.L2Operator
variable {k : ℕ}

/-- The real changed last correction vanishes at every genuine full quadratic reference.
Article: main_krylov, prop:Fcycle, the reference point of the query bootstrap. -/
theorem rfcModifiedCorrection_reference_zero
    (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin (k+1))) :
    rfcModifiedCorrection (k := k) (fun _=>cgOperator base) (fun _=>cgOperator base) g 0=0 := by
  let Q := cgOperator base
  obtain ⟨hQ,hpos⟩ := cgOperator_positive base hb
  have hg : fullPostSearch 1 (fun _=>Q) (fun _=>Q) g k=0 := by
    dsimp only [fullPostSearch]
    rw [show (methodRun (rfcMethod fullMemory 1) (fun _=>Q) (fun _=>Q) g k).gradient=
      CG.gradient Q g k from (rfcMethod_static fullMemory 1 Q hQ hpos g (fun _ _ ha=>ha) k).1]
    have hd : (rfcMethod fullMemory 1).direction
        (methodRun (rfcMethod fullMemory 1) (fun _=>Q) (fun _=>Q) g k)=CG.direction Q g k :=
      rfc_reference_direction fullMemory 1 Q hQ hpos g (fun _ _ ha=>ha) k
    rw [hd]
    change CG.gradient Q g (k+1)=0
    simpa only [finrank_euclideanSpace, Fintype.card_fin] using cg_gradient_finrank_zero Q hQ hpos g
  change combine _ (modelCoefficients _ _ (fullPostSearch 1 (fun _=>Q) (fun _=>Q) g k))=0
  rw [hg]
  rw [modelCoefficients_zero _ _ 0 (by ext i; exact inner_zero_right _)]
  simp [krylov.Methods.combine]

/-- The genuine changed final correction in its complete independent physical source chart.
Article: main_krylov, prop:Fcycle. -/
def rfcModifiedCorrectionField (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ)
    (p : EuclideanSpace ℝ (Fin (k+1)) ×
      (EuclideanSpace ℝ (Fin (k+1)) × (RFCPhysicalData k × Matrix (Fin (k+1)) (Fin (k+1)) ℝ))) :
    EuclideanSpace ℝ (Fin (k+1)) :=
  rfcModifiedCorrection (rfcPhysicalSearch base p.2.2.1) (rfcPhysicalCorrection base p.2.2.1)
    (p.1+p.2.1) p.2.2.2

set_option maxHeartbeats 800000 in
/-- Every actual changed final query is analytic at its true nondegenerate full reference.
Article: main_krylov, prop:Fcycle and lem:U. -/
theorem rfcModifiedCorrectionField_analyticAt
    (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin (k+1)))
    (hpre : ∀ i≤k, CG.gradient (cgOperator base) g i≠0) :
    AnalyticAt ℝ (rfcModifiedCorrectionField base) (g,0) := by
  let P := EuclideanSpace ℝ (Fin (k+1)) ×
    (EuclideanSpace ℝ (Fin (k+1)) × (RFCPhysicalData k × Matrix (Fin (k+1)) (Fin (k+1)) ℝ))
  let A := fun p : P => rfcPhysicalSearch base p.2.2.1
  let B := fun p : P => rfcPhysicalCorrection base p.2.2.1
  let D := fun p : P => p.2.2.2
  let γ := fun p : P => p.1+p.2.1
  have hp : AnalyticAt ℝ (fun p : P => p.2.2.1) (g,0) :=
    analyticAt_fst.comp (analyticAt_snd.comp analyticAt_snd)
  have hA i : AnalyticAt ℝ (fun p => A p i) (g,0) := by
    simpa only [A,Function.comp_def] using (rfcPhysicalSearch_analyticAt base (0 : RFCPhysicalData k) i).comp
      (f := fun p : P => p.2.2.1) (x := (g,0)) hp
  have hB i : AnalyticAt ℝ (fun p => B p i) (g,0) := by
    simpa only [B,Function.comp_def] using (rfcPhysicalCorrection_analyticAt base (0 : RFCPhysicalData k) i).comp
      (f := fun p : P => p.2.2.1) (x := (g,0)) hp
  have hD : AnalyticAt ℝ D (g,0) := analyticAt_snd.comp (analyticAt_snd.comp analyticAt_snd)
  have hγ : AnalyticAt ℝ γ (g,0) := analyticAt_fst.add (analyticAt_fst.comp analyticAt_snd)
  have hAz : A (g,0)=fun _=>cgOperator base := (rfcPhysicalPaths_zero base).1
  have hBz : B (g,0)=fun _=>cgOperator base := (rfcPhysicalPaths_zero base).2
  exact rfcModifiedCorrection_analyticAt A B γ D (g,0) hA hB hγ hD rfl base hb hAz hBz
    (by simpa only [γ,Prod.fst_zero,add_zero] using hpre)

/-- A genuine compact reference family has one uniform linear bound on the
changed final query in all actual physical source coordinates.
Article: main_krylov, prop:Fcycle, final-query bootstrap.
Proof: the true query is analytic and its quadratic-reference value is zero;
compact analytic flatness derives the common bound, including initial drift. -/
theorem compact_rfc_modified_correction
    (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (hb : base.PosDef)
    (K : Set (EuclideanSpace ℝ (Fin (k+1)))) (hK : IsCompact K)
    (hpre : ∀ g∈K, ∀ i≤k, CG.gradient (cgOperator base) g i≠0) :
    ∃ δ C : ℝ, 0<δ ∧ 0≤C ∧ ∀ g∈K,
      ∀ v : EuclideanSpace ℝ (Fin (k+1)), ∀ Θ : RFCPhysicalData k,
      ∀ D : Matrix (Fin (k+1)) (Fin (k+1)) ℝ, ‖(v,(Θ,D))‖≤δ →
        ‖rfcModifiedCorrection (rfcPhysicalSearch base Θ) (rfcPhysicalCorrection base Θ)
          (g+v) D‖≤C*‖(v,(Θ,D))‖ := by
  have hzero g : rfcModifiedCorrectionField base (g,0)=0 := by
    simpa only [rfcModifiedCorrectionField,Prod.fst_zero,Prod.snd_zero,add_zero,
      (rfcPhysicalPaths_zero base).1,(rfcPhysicalPaths_zero base).2] using
      rfcModifiedCorrection_reference_zero base hb g
  have horder g (hg : g∈K) : (fun z=>rfcModifiedCorrectionField base (g,z)) =O[𝓝 0] (fun z=>‖z‖^1) := by
    have ha := (rfcModifiedCorrectionField_analyticAt base hb g (hpre g hg)).comp
      (f := fun z=> (g,z)) (x := 0) (analyticAt_const.prod analyticAt_id)
    simpa only [hzero,sub_zero,pow_one] using
      analytic_reference_order (fun z=>rfcModifiedCorrectionField base (g,z)) ha
  obtain ⟨δ,C,hδ,hC,hbound⟩ := compact_analytic_flat_fibres (rfcModifiedCorrectionField base) K hK 1 (by norm_num)
    (fun g hg=>rfcModifiedCorrectionField_analyticAt base hb g (hpre g hg)) horder
  exact ⟨δ,C,hδ,hC,fun g hg v Θ D hnorm=>by simpa only [rfcModifiedCorrectionField,pow_one] using hbound g hg (v,(Θ,D)) hnorm⟩

end
end krylov.Functions
