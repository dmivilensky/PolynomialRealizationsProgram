import krylov.Functions.NativeRFCJetCoordinates
import krylov.Stability.CompactFirstOrder

/-!
Article: main_krylov, thm:Htransfer, original moving first-secant reference.
Use: replace the minimizer-Hessian reference in the actual physical quadratic
coefficient by the true first search secant and true normalized initial
gradient. Source: genuine joint reference analyticity, compact first-order
Taylor control and exact degree-two homogeneity in the physical source.
-/
namespace krylov.Functions
noncomputable section
open Set Metric Matrix NormedSpace krylov.Methods krylov.Reference krylov.Stability krylov.Correction
  krylov.Nonlinear krylov.Variation krylov.Secant krylov.Envelope
open scoped InnerProductSpace NNReal Matrix.Norms.L2Operator
variable {k : ℕ}
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

set_option maxHeartbeats 800000 in
/-- The literal physical quadratic response is jointly analytic in its true
base, initial gradient, search operators and correction operators.
Article: main_krylov, thm:Htransfer and lem:U. -/
theorem rfcPhysicalQuadratic_variable_analyticAt
    (base : X → Matrix (Fin (k+1)) (Fin (k+1)) ℝ)
    (g : X → EuclideanSpace ℝ (Fin (k+1)))
    (A B : X → ℕ → EuclideanSpace ℝ (Fin (k+1)) →L[ℝ] EuclideanSpace ℝ (Fin (k+1)))
    (x : X) (hb : AnalyticAt ℝ base x) (hpos : (base x).PosDef) (hg : AnalyticAt ℝ g x)
    (hA : ∀ i, AnalyticAt ℝ (fun p=>A p i) x)
    (hB : ∀ i, AnalyticAt ℝ (fun p=>B p i) x)
    (hpre : ∀ j≤k, CG.gradient (cgOperator (base x)) (g x) j≠0) :
    AnalyticAt ℝ (fun p=>rfcPhysicalQuadratic (base p) (g p) (A p) (B p)) x := by
  let U := fun p=>referenceModelBasis (base p) (g p) k
  let H := fun p=>pairModel (U p) (fun i=>cgOperator (base p) (U p i))
  let R := fun p=>fullBasisMatrix (U p)
  let L := fun p=>Matrix.of fun i j : Fin (k+1)=>inner ℝ (U p i)
    ((B p k-A p (k-(min i j).val)) (U p j))
  have hd := reference_model_data_analyticAt base g x hb hpos hg hpre
  have hL : AnalyticAt ℝ L x := analytic_spectral_matrix _ x fun i j=>
    analytic_inner (hd.1 i) (analytic_operator_apply ((hB k).sub (hA _)) (hd.1 j))
  have hHi : AnalyticAt ℝ (fun p=>(H p)⁻¹) x := analytic_spectral_matrix_inv H x
    (fun i j=>analytic_matrix_entry hd.2.1 i j) (isUnit_iff_ne_zero.mp hd.2.2.2.1)
  have hRi : AnalyticAt ℝ (fun p=>(R p)ᵀ⁻¹) x := analytic_spectral_matrix_inv _ x
    (fun i j=>analytic_matrix_entry hd.2.2.1 j i)
    (by simpa only [det_transpose] using isUnit_iff_ne_zero.mp hd.2.2.2.2)
  have hQa := (matrixOperator_contDiffAt base x hb.contDiffAt).analyticAt
  have hQ := cgOperator_positive (base x) hpos
  have hr := frozenIncoming_variable_analyticAt (fun p=>cgOperator (base p)) g A x hQa hg hA
    hQ.1 hQ.2 k hpre
  exact analytic_operator_apply
    (matrixOperator_contDiffAt _ x (hRi.mul (hL.mul hHi)).contDiffAt).analyticAt hr

set_option maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency false in
/-- Moving the true reference by Δ changes its actual quadratic response by
O(norm(Δ)*norm(source)²), uniformly on compact nonstagnating references.
The source is unrestricted; its quadratic factor follows from genuine
homogeneity, not an assumed derivative bound.
Article: main_krylov, thm:Htransfer, actual own-A₀ reference replacement. -/
theorem compact_rfcPhysicalQuadratic_reference_change
    (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (hb : base.PosDef)
    (K : Set (EuclideanSpace ℝ (Fin (k+1)))) (hK : IsCompact K)
    (hpre : ∀ g∈K, ∀ i≤k, CG.gradient (cgOperator base) g i≠0) :
    ∃ δ C : ℝ, 0<δ ∧ 0<C ∧ ∀ g∈K,
      ∀ Δ : Matrix (Fin (k+1)) (Fin (k+1)) ℝ,
      ∀ v : EuclideanSpace ℝ (Fin (k+1)), ‖(Δ,v)‖≤δ → ∀ Θ : RFCPhysicalData k,
      ‖rfcPhysicalQuadratic (base+Δ) (g+v) (rfcPhysicalSearch (base+Δ) Θ) (rfcPhysicalCorrection (base+Δ) Θ)-
        rfcPhysicalQuadratic base g (rfcPhysicalSearch base Θ) (rfcPhysicalCorrection base Θ)‖≤
        C*‖(Δ,v)‖*‖Θ‖^2 := by
  let F := fun p : (EuclideanSpace ℝ (Fin (k+1)) × RFCPhysicalData k) ×
      (Matrix (Fin (k+1)) (Fin (k+1)) ℝ × EuclideanSpace ℝ (Fin (k+1)))=>
    rfcPhysicalQuadratic (base+p.2.1) (p.1.1+p.2.2)
      (rfcPhysicalSearch (base+p.2.1) p.1.2) (rfcPhysicalCorrection (base+p.2.1) p.1.2)
  let S := K ×ˢ closedBall (0 : RFCPhysicalData k) 1
  have hS : IsCompact S := hK.prod (isCompact_closedBall _ _)
  have ha z (hz : z∈S) : AnalyticAt ℝ F (z,0) := by
    have hbase : AnalyticAt ℝ (fun p : (EuclideanSpace ℝ (Fin (k+1)) × RFCPhysicalData k) ×
        (Matrix (Fin (k+1)) (Fin (k+1)) ℝ × EuclideanSpace ℝ (Fin (k+1)))=>base+p.2.1) (z,0) :=
      analyticAt_const.add (analyticAt_fst.comp analyticAt_snd)
    have hg : AnalyticAt ℝ (fun p : (EuclideanSpace ℝ (Fin (k+1)) × RFCPhysicalData k) ×
        (Matrix (Fin (k+1)) (Fin (k+1)) ℝ × EuclideanSpace ℝ (Fin (k+1)))=>p.1.1+p.2.2) (z,0) :=
      (analyticAt_fst.comp analyticAt_fst).add (analyticAt_snd.comp analyticAt_snd)
    have hΩ : AnalyticAt ℝ (fun p : (EuclideanSpace ℝ (Fin (k+1)) × RFCPhysicalData k) ×
        (Matrix (Fin (k+1)) (Fin (k+1)) ℝ × EuclideanSpace ℝ (Fin (k+1)))=>p.1.2) (z,0) :=
      analyticAt_snd.comp analyticAt_fst
    have hA i : AnalyticAt ℝ (fun p : (EuclideanSpace ℝ (Fin (k+1)) × RFCPhysicalData k) ×
        (Matrix (Fin (k+1)) (Fin (k+1)) ℝ × EuclideanSpace ℝ (Fin (k+1)))=>
        rfcPhysicalSearch (base+p.2.1) p.1.2 i) (z,0) := by
      simp only [rfcPhysicalSearch,←rfcSearchDeviationL_apply]
      exact (matrixOperator_contDiffAt _ (z,0) (hbase.add ((rfcSearchDeviationL k i).analyticAt _ |>.comp hΩ)).contDiffAt).analyticAt
    have hB i : AnalyticAt ℝ (fun p : (EuclideanSpace ℝ (Fin (k+1)) × RFCPhysicalData k) ×
        (Matrix (Fin (k+1)) (Fin (k+1)) ℝ × EuclideanSpace ℝ (Fin (k+1)))=>
        rfcPhysicalCorrection (base+p.2.1) p.1.2 i) (z,0) := by
      simp only [rfcPhysicalCorrection,←rfcCorrectionDeviationL_apply]
      exact (matrixOperator_contDiffAt _ (z,0) (hbase.add ((rfcCorrectionDeviationL k i).analyticAt _ |>.comp hΩ)).contDiffAt).analyticAt
    exact rfcPhysicalQuadratic_variable_analyticAt _ _ _ _ (z,0) hbase
      (by simpa only [Prod.fst_zero,add_zero] using hb) hg hA hB
      (by simpa only [Prod.fst_zero,Prod.snd_zero,add_zero] using hpre z.1 hz.1)
  obtain ⟨δ,C,hδ,hC,hbound⟩ := compact_reference_full_first_order F S hS ha
  refine ⟨δ,C,hδ,hC,?_⟩
  intro g hg Δ v hΔ Θ
  by_cases hΘ : Θ=0
  · subst Θ
    have hz (b : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (w : EuclideanSpace ℝ (Fin (k+1))) :
        rfcPhysicalQuadratic b w (rfcPhysicalSearch b 0) (rfcPhysicalCorrection b 0)=0 := by
      have hh := rfcPhysicalQuadratic_source_smul b w (0 : RFCPhysicalData k) 0
      simpa only [zero_smul,zero_pow (by decide : 2≠0)] using hh
    rw [hz,hz,sub_self,norm_zero,norm_zero,zero_pow (by decide : 2≠0),mul_zero]
  · let Ω := NormedSpace.normalize Θ
    have hΩ : Ω∈closedBall (0 : RFCPhysicalData k) 1 := by
      simp only [mem_closedBall,dist_zero_right,Ω,norm_normalize hΘ,le_refl]
    have hin : ‖((0 : EuclideanSpace ℝ (Fin (k+1)) × RFCPhysicalData k),(Δ,v))‖=‖(Δ,v)‖ := by simp
    have hh := hbound (g,Ω) ⟨hg,hΩ⟩ 0 (Δ,v) (hin ▸ hΔ)
    simp only [add_zero,F,Prod.fst_zero,Prod.snd_zero] at hh
    have hΘeq : ‖Θ‖ • Ω=Θ := norm_smul_normalize Θ
    have he (b : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (w : EuclideanSpace ℝ (Fin (k+1))) :
        rfcPhysicalQuadratic b w (rfcPhysicalSearch b Θ) (rfcPhysicalCorrection b Θ)=
          ‖Θ‖^2 • rfcPhysicalQuadratic b w (rfcPhysicalSearch b Ω) (rfcPhysicalCorrection b Ω) := by
      rw [←rfcPhysicalQuadratic_source_smul,hΘeq]
    rw [he,he,←smul_sub,norm_smul,Real.norm_of_nonneg (sq_nonneg _)]
    exact (mul_le_mul_of_nonneg_left hh (sq_nonneg _)).trans_eq (by rw [hin]; ring)

end
end krylov.Functions
