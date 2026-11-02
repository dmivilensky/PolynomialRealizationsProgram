import krylov.Functions.RFCPhysicalQuadratic

/-!
Article: main_krylov, lem:cycle-transfer and thm:Htransfer, the true compact RFC quadratic tube.
Use: a single cubic remainder bound covers all actual initial-gradient
drifts and all symmetric physical query perturbations, including the first
secant. This avoids assuming a native output expansion or its second jet.
Source: the genuine physical RFC expansion, actual reference inverse domains
and the existing analytic-flatness compact Taylor theorem.
-/

namespace krylov.Functions
noncomputable section
open Matrix Set Filter Asymptotics Topology krylov.Reference krylov.Methods krylov.Stability
  krylov.Correction krylov.Envelope krylov.Secant krylov.Variation
open scoped InnerProductSpace BigOperators Matrix.Norms.L2Operator
variable {k : ℕ}
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- The genuine frozen physical quadratic coefficient is analytic with its actual reference gradient and query operators.
Article: main_krylov, lem:U and thm:Htransfer.
Proof: actual quadratic reference data supply the independent basis and
positive model; their true inverse domains permit analytic reconstruction. -/
theorem rfcPhysicalQuadratic_analyticAt
    (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (hb : base.PosDef)
    (g : X → EuclideanSpace ℝ (Fin (k+1)))
    (A B : X → ℕ → EuclideanSpace ℝ (Fin (k+1)) →L[ℝ] EuclideanSpace ℝ (Fin (k+1)))
    (x : X) (hg : AnalyticAt ℝ g x)
    (hA : ∀ i, AnalyticAt ℝ (fun p => A p i) x)
    (hB : ∀ i, AnalyticAt ℝ (fun p => B p i) x)
    (hpre : ∀ i ≤ k, CG.gradient (cgOperator base) (g x) i ≠ 0) :
    AnalyticAt ℝ (fun p => rfcPhysicalQuadratic base (g p) (A p) (B p)) x := by
  let U := fun p => referenceModelBasis base (g p) k
  let H := fun p => pairModel (U p) (fun i => cgOperator base (U p i))
  let R := fun p => fullBasisMatrix (U p)
  let L := fun p => Matrix.of fun i j : Fin (k+1) =>
    inner ℝ (U p i) ((B p k - A p (k-(min i j).val)) (U p j))
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
    (matrixOperator_contDiffAt _ x (hRi.mul (hL.mul hHi)).contDiffAt).analyticAt hr

/-- The entire actual physical remainder is jointly analytic around each genuine nondegenerate quadratic reference.
Article: main_krylov, lem:U and thm:Htransfer.
Proof: original independent finite symmetric query coordinates supply the
real analytic ordinary RFC execution; the same actual reference gives its
true analytic frozen quadratic coefficient. -/
theorem rfcPhysicalRemainder_analyticAt
    (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin (k+1)))
    (hpre : ∀ i ≤ k, CG.gradient (cgOperator base) g i ≠ 0) :
    AnalyticAt ℝ (rfcPhysicalRemainder base) (g,0) := by
  let A := fun p : EuclideanSpace ℝ (Fin (k+1)) × (EuclideanSpace ℝ (Fin (k+1)) × RFCPhysicalData k) =>
    rfcPhysicalSearch base p.2.2
  let B := fun p : EuclideanSpace ℝ (Fin (k+1)) × (EuclideanSpace ℝ (Fin (k+1)) × RFCPhysicalData k) =>
    rfcPhysicalCorrection base p.2.2
  let γ := fun p : EuclideanSpace ℝ (Fin (k+1)) × (EuclideanSpace ℝ (Fin (k+1)) × RFCPhysicalData k) =>
    p.1+p.2.1
  have hp : AnalyticAt ℝ
      (fun p : EuclideanSpace ℝ (Fin (k+1)) × (EuclideanSpace ℝ (Fin (k+1)) × RFCPhysicalData k) => p.2.2)
      (g,0) := analyticAt_snd.comp analyticAt_snd
  have hA i : AnalyticAt ℝ (fun p => A p i) (g,0) := by
    simpa only [A, Function.comp_def] using
      (rfcPhysicalSearch_analyticAt base (0 : RFCPhysicalData k) i).comp
        (f := fun p : EuclideanSpace ℝ (Fin (k+1)) × (EuclideanSpace ℝ (Fin (k+1)) × RFCPhysicalData k) => p.2.2)
        (x := (g,0)) hp
  have hB i : AnalyticAt ℝ (fun p => B p i) (g,0) := by
    simpa only [B, Function.comp_def] using
      (rfcPhysicalCorrection_analyticAt base (0 : RFCPhysicalData k) i).comp
        (f := fun p : EuclideanSpace ℝ (Fin (k+1)) × (EuclideanSpace ℝ (Fin (k+1)) × RFCPhysicalData k) => p.2.2)
        (x := (g,0)) hp
  have hγ : AnalyticAt ℝ γ (g,0) := analyticAt_fst.add (analyticAt_fst.comp analyticAt_snd)
  have hAz : A (g,0) = fun _ => cgOperator base := (rfcPhysicalPaths_zero base).1
  have hBz : B (g,0) = fun _ => cgOperator base := (rfcPhysicalPaths_zero base).2
  have hgrad := (quadraticRFC_prefix_analytic fullMemory 1 A B γ (g,0) hA hB hγ
    (cgOperator base) hAz hBz (cgOperator_positive base hb).1 (cgOperator_positive base hb).2
    (fun _ _ ha => ha) (k+1) (by simpa only [γ, Prod.fst_zero, add_zero] using fun i hi => hpre i (by omega))).1
  have hquad := rfcPhysicalQuadratic_analyticAt base hb Prod.fst A B (g,0) analyticAt_fst hA hB hpre
  exact hgrad.add hquad

omit [NormedAddCommGroup X] [NormedSpace ℝ X] in
/-- A single genuine compact tube controls ordinary RFC with its drifting first search secant and initial gradient.
Article: main_krylov, lem:cycle-transfer and thm:Htransfer.
Proof: the true physical remainder is jointly analytic, and the already
proved physical expansion gives cubic order in the entire original source
space. Analytic coefficient uniqueness and the compact Taylor theorem
derive the uniform radius and constant. -/
theorem compact_rfc_physical_quadratic
    (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (hb : base.PosDef) (hk : 0 < k)
    (K : Set (EuclideanSpace ℝ (Fin (k+1)))) (hK : IsCompact K)
    (hpre : ∀ g ∈ K, ∀ i ≤ k, CG.gradient (cgOperator base) g i ≠ 0) :
    ∃ δ C : ℝ, 0 < δ ∧ 0 ≤ C ∧ ∀ g ∈ K,
      ∀ v : EuclideanSpace ℝ (Fin (k+1)), ∀ Θ : RFCPhysicalData k, ‖(v,Θ)‖ ≤ δ →
        ‖probedGradient (rfcMethod fullMemory 1) (rfcPhysicalSearch base Θ)
            (rfcPhysicalCorrection base Θ) (g+v) (k+1) +
          rfcPhysicalQuadratic base g (rfcPhysicalSearch base Θ) (rfcPhysicalCorrection base Θ)‖ ≤
            C * ‖(v,Θ)‖ ^ 3 := by
  obtain ⟨δ,C,hδ,hC,hbound⟩ := compact_analytic_flat_fibres (rfcPhysicalRemainder base) K hK 3 (by norm_num)
    (fun g hg => rfcPhysicalRemainder_analyticAt base hb g (hpre g hg))
    (fun g hg => rfcPhysicalRemainder_order base hb g hk (hpre g hg))
  exact ⟨δ,C,hδ,hC,fun g hg v Θ hΘ => hbound g hg (v,Θ) hΘ⟩

end
end krylov.Functions
