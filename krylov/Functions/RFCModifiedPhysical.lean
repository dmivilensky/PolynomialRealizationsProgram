import krylov.Functions.RFCBilinear
import krylov.Correction.ModifiedExpansion

/-!
Article: main_krylov, prop:Fcycle and apD:lem-model, actual last-model changes.
Use: place the genuine modified last correction in one complete physical
source chart, including its first secant, initial gradient and independent
observed model change. The source expansion is derived from the actual
ordinary RFC prefix and actual modified inverse solve.
Source: the previously proved full modified physical expansion and the true
analytic reference inverse domains.
-/

namespace krylov.Functions
noncomputable section
open Matrix Set Filter Asymptotics Topology krylov.Reference krylov.Methods krylov.Stability
  krylov.Correction krylov.Envelope krylov.Secant krylov.Variation
open scoped InnerProductSpace BigOperators Matrix.Norms.L2Operator
variable {k : ℕ}
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- The true physical frozen coefficient with an arbitrary actual last-model change.
Article: main_krylov, prop:Fcycle, the factor L-Delta_H. -/
def rfcModifiedQuadratic (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ)
    (g : EuclideanSpace ℝ (Fin (k+1)))
    (A B : ℕ → EuclideanSpace ℝ (Fin (k+1)) →L[ℝ] EuclideanSpace ℝ (Fin (k+1)))
    (D : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) : EuclideanSpace ℝ (Fin (k+1)) :=
  let U := referenceModelBasis base g k
  let H := pairModel U (fun i => cgOperator base (U i))
  let R := fullBasisMatrix U
  let L := Matrix.of fun i j : Fin (k+1) => inner ℝ (U i)
    ((B k-A (k-(min i j).val)) (U j))
  cgOperator (Rᵀ⁻¹*((L-D)*H⁻¹)) (frozenIncoming (cgOperator base) g A k)

/-- The actual changed last-model correction query after the genuine RFC prefix.
Article: main_krylov, prop:Fcycle, before its gradient is evaluated. -/
def rfcModifiedCorrection {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {k : ℕ}
    (A B : ℕ → E →L[ℝ] E) (g : E)
    (D : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) : E :=
  let m := rfcMethod fullMemory 1
  let U := probedStepBasis m A B g k
  combine U (modelCoefficients U (pairModel U (probedImageBasis m A B g k)+D)
    (fullPostSearch 1 A B g k))

set_option maxHeartbeats 800000 in
/-- The actual modified terminal inverse solve is analytic on its genuine quadratic reference domain.
Article: main_krylov, prop:Fcycle and lem:U.
Proof: the actual ordinary RFC prefix supplies its observed basis and
incoming searched gradient. Quadratic consistency supplies the true model
inverse, and the real modified model retains it at the base point. -/
theorem modifiedTerminalData_analyticAt
    (A B : X → ℕ → EuclideanSpace ℝ (Fin (k+1)) →L[ℝ] EuclideanSpace ℝ (Fin (k+1)))
    (g : X → EuclideanSpace ℝ (Fin (k+1)))
    (D : X → Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (x : X)
    (hA : ∀ i, AnalyticAt ℝ (fun z => A z i) x)
    (hB : ∀ i, AnalyticAt ℝ (fun z => B z i) x) (hg : AnalyticAt ℝ g x)
    (hD : AnalyticAt ℝ D x) (hD0 : D x=0)
    (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (hb : base.PosDef)
    (hAx : A x=fun _=>cgOperator base) (hBx : B x=fun _=>cgOperator base)
    (hpre : ∀ i≤k, CG.gradient (cgOperator base) (g x) i≠0) :
    AnalyticAt ℝ (fun z => rfcModifiedCorrection (A z) (B z) (g z) (D z)) x ∧
    AnalyticAt ℝ (fun z => modifiedTerminalGradient (A z) (B z) (g z) k (D z)) x := by
  let Q := cgOperator base
  let m := rfcMethod fullMemory 1 (E := EuclideanSpace ℝ (Fin (k+1)))
  let d := fun z => m.direction (methodRun m (A z) (B z) (g z) k)
  let U := fun z => probedStepBasis m (A z) (B z) (g z) k
  let Z := fun z => probedImageBasis m (A z) (B z) (g z) k
  let H := fun z => pairModel (U z) (Z z)
  let gp := fun z => fullPostSearch 1 (A z) (B z) (g z) k
  obtain ⟨hQ,hpos⟩ := cgOperator_positive base hb
  have ht := quadraticRFC_prefix_analytic fullMemory 1 A B g x hA hB hg Q hAx hBx hQ hpos
    (fun _ _ ha => ha) (k+1) (fun i hi => hpre i (by omega))
  have hG := (quadraticRFC_prefix_analytic fullMemory 1 A B g x hA hB hg Q hAx hBx hQ hpos
    (fun _ _ ha => ha) k (fun i hi => hpre i hi.le)).1
  have hd : AnalyticAt ℝ d x := (ht.2 k (by omega)).1
  have hz := analytic_operator_apply (hA k) hd
  have hdx : d x=CG.direction Q (g x) k := by
    dsimp only [d]
    rw [hAx,hBx]
    exact rfc_reference_direction fullMemory 1 Q hQ hpos (g x) (fun _ _ ha => ha) k
  have hc : inner ℝ (d x) (A x k (d x))≠0 := by
    rw [hdx,hAx]
    exact (hpos _ (CG.invariant_line_pos Q hpos (g x) k
      (CG.invariant Q hQ hpos (g x) k (fun i hi => hpre i hi.le)) (hpre k le_rfl)).1).ne'
  have hgp : AnalyticAt ℝ gp x := by
    exact hG.add ((((analytic_inner hd hG).neg.div (analytic_inner hd hz) hc).smul hz))
  have hU i : AnalyticAt ℝ (fun z => U z i) x := by
    refine Fin.cases hd (fun j => (ht.2 (k-1-j.val) (by omega)).2.1) i
  have hZ i : AnalyticAt ℝ (fun z => Z z i) x := by
    refine Fin.cases (analytic_operator_apply (hA k) (hU 0))
      (fun j => (ht.2 (k-1-j.val) (by omega)).2.2) i
  have hH : AnalyticAt ℝ H x := analytic_spectral_matrix _ x fun i j => analytic_inner (hU _) (hZ _)
  have hu : (H x+D x).det≠0 := by
    rw [hD0,add_zero]
    dsimp only [H,U,Z]
    rw [hAx,hBx]
    exact (quadratic_probedModel_posDef m (rfcMethod_consistent fullMemory (fun _ ha => ha) 1)
      Q hQ hpos (g x) k (fun i hi => hpre i (by omega))).det_pos.ne'
  have hχ := analytic_modelCorrection U (fun z => H z+D z) gp x hU
    (fun i j => analytic_matrix_entry (hH.add hD) i j) hgp hu
  exact ⟨hχ,hgp.add (analytic_operator_apply (hB k) hχ)⟩

set_option maxHeartbeats 800000 in
/-- The genuine changed last correction is analytic on its actual reference domain.
Article: main_krylov, prop:Fcycle, actual correction-query regularity. -/
theorem rfcModifiedCorrection_analyticAt
    (A B : X → ℕ → EuclideanSpace ℝ (Fin (k+1)) →L[ℝ] EuclideanSpace ℝ (Fin (k+1)))
    (g : X → EuclideanSpace ℝ (Fin (k+1)))
    (D : X → Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (x : X)
    (hA : ∀ i, AnalyticAt ℝ (fun z => A z i) x)
    (hB : ∀ i, AnalyticAt ℝ (fun z => B z i) x) (hg : AnalyticAt ℝ g x)
    (hD : AnalyticAt ℝ D x) (hD0 : D x=0)
    (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (hb : base.PosDef)
    (hAx : A x=fun _=>cgOperator base) (hBx : B x=fun _=>cgOperator base)
    (hpre : ∀ i≤k, CG.gradient (cgOperator base) (g x) i≠0) :
    AnalyticAt ℝ (fun z => rfcModifiedCorrection (A z) (B z) (g z) (D z)) x :=
  (modifiedTerminalData_analyticAt A B g D x hA hB hg hD hD0 base hb hAx hBx hpre).1

set_option maxHeartbeats 800000 in
/-- The actual returned modified gradient is analytic on its derived reference domain.
Article: main_krylov, prop:Fcycle and lem:U. -/
theorem modifiedTerminalGradient_analyticAt
    (A B : X → ℕ → EuclideanSpace ℝ (Fin (k+1)) →L[ℝ] EuclideanSpace ℝ (Fin (k+1)))
    (g : X → EuclideanSpace ℝ (Fin (k+1)))
    (D : X → Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (x : X)
    (hA : ∀ i, AnalyticAt ℝ (fun z => A z i) x)
    (hB : ∀ i, AnalyticAt ℝ (fun z => B z i) x) (hg : AnalyticAt ℝ g x)
    (hD : AnalyticAt ℝ D x) (hD0 : D x=0)
    (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (hb : base.PosDef)
    (hAx : A x=fun _=>cgOperator base) (hBx : B x=fun _=>cgOperator base)
    (hpre : ∀ i≤k, CG.gradient (cgOperator base) (g x) i≠0) :
    AnalyticAt ℝ (fun z => modifiedTerminalGradient (A z) (B z) (g z) k (D z)) x :=
  (modifiedTerminalData_analyticAt A B g D x hA hB hg hD hD0 base hb hAx hBx hpre).2

/-- The true modified physical remainder in its complete independent finite source chart.
Article: main_krylov, prop:Fcycle. -/
def rfcModifiedRemainder (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ)
    (p : EuclideanSpace ℝ (Fin (k+1)) ×
      (EuclideanSpace ℝ (Fin (k+1)) × (RFCPhysicalData k × Matrix (Fin (k+1)) (Fin (k+1)) ℝ))) :
    EuclideanSpace ℝ (Fin (k+1)) :=
  modifiedTerminalGradient (rfcPhysicalSearch base p.2.2.1) (rfcPhysicalCorrection base p.2.2.1)
      (p.1+p.2.1) k p.2.2.2+
    rfcModifiedQuadratic base p.1 (rfcPhysicalSearch base p.2.2.1)
      (rfcPhysicalCorrection base p.2.2.1) p.2.2.2

set_option maxHeartbeats 800000 in
/-- The genuine modified last correction has cubic physical remainder in all original source variables.
Article: main_krylov, prop:Fcycle, source of the native cubic function response.
Proof: the complete physical scenario space makes every real search,
correction and model-change input analytic. Instantiate the proved actual
modified physical expansion, including the drifting first search secant. -/
theorem rfcModifiedRemainder_order
    (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin (k+1))) (hk : 0<k)
    (hpre : ∀ i≤k, CG.gradient (cgOperator base) g i≠0) :
    (fun z => rfcModifiedRemainder base (g,z)) =O[𝓝 0] (fun z => ‖z‖^3) := by
  let P := EuclideanSpace ℝ (Fin (k+1)) × (RFCPhysicalData k × Matrix (Fin (k+1)) (Fin (k+1)) ℝ)
  let A := fun z : P => rfcPhysicalSearch base z.2.1
  let B := fun z : P => rfcPhysicalCorrection base z.2.1
  have hp : AnalyticAt ℝ (fun z : P => z.2.1) 0 := analyticAt_fst.comp analyticAt_snd
  have hA i : AnalyticAt ℝ (fun z => A z i) 0 := by
    simpa only [A,Function.comp_def] using (rfcPhysicalSearch_analyticAt base (0 : RFCPhysicalData k) i).comp
      (f := fun z : P => z.2.1) (x := 0) hp
  have hB i : AnalyticAt ℝ (fun z => B z i) 0 := by
    simpa only [B,Function.comp_def] using (rfcPhysicalCorrection_analyticAt base (0 : RFCPhysicalData k) i).comp
      (f := fun z : P => z.2.1) (x := 0) hp
  have hAz : A 0=fun _=>cgOperator base := (rfcPhysicalPaths_zero base).1
  have hBz : B 0=fun _=>cgOperator base := (rfcPhysicalPaths_zero base).2
  have hsym z i : (A z i).toLinearMap.IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr
    (hb.1.add (symmetricScenario_increment_symm z.2.1 i))
  have hD : AnalyticAt ℝ (fun z : P => z.2.2) 0 := analyticAt_snd.comp analyticAt_snd
  have ho := full_modified_physical_second_order A B (fun z => g+z.1) hA hB
    (analyticAt_const.add analyticAt_fst) hsym (cgOperator base) hAz hBz
    (cgOperator_positive base hb).1 (cgOperator_positive base hb).2 hk
    (by simpa only [Prod.fst_zero,add_zero] using hpre) (fun z : P => z.2.2) hD rfl
  simpa only [rfcModifiedRemainder,rfcModifiedQuadratic,Prod.fst_zero,Prod.snd_zero,add_zero,
    hAz,hBz,quadratic_imageBasis,referenceModelBasis,A,B,cgOperator] using ho

set_option maxHeartbeats 800000 in
/-- The actual modified frozen coefficient is jointly analytic on its genuine reference domain.
Article: main_krylov, prop:Fcycle and lem:U.
Proof: retain the true reference inverses, the actual model change and the
actual incoming factor, rather than assigning regularity to a response field. -/
theorem rfcModifiedQuadratic_analyticAt
    (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (hb : base.PosDef)
    (g : X → EuclideanSpace ℝ (Fin (k+1)))
    (A B : X → ℕ → EuclideanSpace ℝ (Fin (k+1)) →L[ℝ] EuclideanSpace ℝ (Fin (k+1)))
    (D : X → Matrix (Fin (k+1)) (Fin (k+1)) ℝ)
    (x : X) (hg : AnalyticAt ℝ g x)
    (hA : ∀ i, AnalyticAt ℝ (fun p => A p i) x)
    (hB : ∀ i, AnalyticAt ℝ (fun p => B p i) x) (hD : AnalyticAt ℝ D x)
    (hpre : ∀ i≤k, CG.gradient (cgOperator base) (g x) i≠0) :
    AnalyticAt ℝ (fun p => rfcModifiedQuadratic base (g p) (A p) (B p) (D p)) x := by
  let U := fun p => referenceModelBasis base (g p) k
  let H := fun p => pairModel (U p) (fun i => cgOperator base (U p i))
  let R := fun p => fullBasisMatrix (U p)
  let L := fun p => Matrix.of fun i j : Fin (k+1) =>
    inner ℝ (U p i) ((B p k-A p (k-(min i j).val)) (U p j))
  have hd := reference_model_data_analyticAt (fun _ : X => base) g x analyticAt_const hb hg hpre
  have hL : AnalyticAt ℝ L x := analytic_spectral_matrix _ x fun i j =>
    analytic_inner (hd.1 i) (analytic_operator_apply ((hB k).sub (hA _)) (hd.1 j))
  have hHi : AnalyticAt ℝ (fun p => (H p)⁻¹) x := analytic_spectral_matrix_inv H x
    (fun i j => analytic_matrix_entry hd.2.1 i j) (isUnit_iff_ne_zero.mp hd.2.2.2.1)
  have hRi : AnalyticAt ℝ (fun p => (R p)ᵀ⁻¹) x := analytic_spectral_matrix_inv _ x
    (fun i j => analytic_matrix_entry hd.2.2.1 j i)
    (by simpa only [det_transpose] using isUnit_iff_ne_zero.mp hd.2.2.2.2)
  have hr := frozenIncoming_variable_analyticAt (fun _ : X => cgOperator base) g A x analyticAt_const hg hA
    (cgOperator_positive base hb).1 (cgOperator_positive base hb).2 k hpre
  exact analytic_operator_apply
    (matrixOperator_contDiffAt _ x (hRi.mul ((hL.sub hD).mul hHi)).contDiffAt).analyticAt hr

set_option maxHeartbeats 800000 in
/-- The complete genuine modified physical remainder is analytic at every actual nondegenerate reference.
Article: main_krylov, prop:Fcycle and lem:U. -/
theorem rfcModifiedRemainder_analyticAt
    (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin (k+1)))
    (hpre : ∀ i≤k, CG.gradient (cgOperator base) g i≠0) :
    AnalyticAt ℝ (rfcModifiedRemainder base) (g,0) := by
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
  have hmod := modifiedTerminalGradient_analyticAt A B γ D (g,0) hA hB hγ hD rfl base hb hAz hBz
    (by simpa only [γ,Prod.fst_zero,add_zero] using hpre)
  have hquad := rfcModifiedQuadratic_analyticAt base hb Prod.fst A B D (g,0)
    analyticAt_fst hA hB hD hpre
  exact hmod.add hquad

omit [NormedAddCommGroup X] [NormedSpace ℝ X] in
/-- The true changed last model has one compact-uniform cubic remainder in all its actual physical source variables.
Article: main_krylov, prop:Fcycle and lem:cycle-transfer.
Proof: actual analyticity and the genuine pointwise modified physical
expansion determine the vanishing low Taylor coefficients. The existing
compact analytic-flatness theorem then supplies a common true tube. -/
theorem compact_rfc_modified_quadratic
    (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (hb : base.PosDef) (hk : 0<k)
    (K : Set (EuclideanSpace ℝ (Fin (k+1)))) (hK : IsCompact K)
    (hpre : ∀ g∈K, ∀ i≤k, CG.gradient (cgOperator base) g i≠0) :
    ∃ δ C : ℝ, 0<δ ∧ 0≤C ∧ ∀ g∈K,
      ∀ v : EuclideanSpace ℝ (Fin (k+1)), ∀ Θ : RFCPhysicalData k,
      ∀ D : Matrix (Fin (k+1)) (Fin (k+1)) ℝ, ‖(v,(Θ,D))‖≤δ →
        ‖modifiedTerminalGradient (rfcPhysicalSearch base Θ) (rfcPhysicalCorrection base Θ)
          (g+v) k D+rfcModifiedQuadratic base g (rfcPhysicalSearch base Θ)
            (rfcPhysicalCorrection base Θ) D‖≤C*‖(v,(Θ,D))‖^3 := by
  obtain ⟨δ,C,hδ,hC,hbound⟩ := compact_analytic_flat_fibres (rfcModifiedRemainder base) K hK 3 (by norm_num)
    (fun g hg => rfcModifiedRemainder_analyticAt base hb g (hpre g hg))
    (fun g hg => rfcModifiedRemainder_order base hb g hk (hpre g hg))
  exact ⟨δ,C,hδ,hC,fun g hg v Θ D hnorm=>hbound g hg (v,(Θ,D)) hnorm⟩

end
end krylov.Functions
