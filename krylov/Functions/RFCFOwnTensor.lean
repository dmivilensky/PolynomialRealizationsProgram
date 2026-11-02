import krylov.Functions.RFCOwnTensor
import krylov.Functions.NativeRFCFTensorTransfer

/-!
Article: main_krylov, prop:Fcycle(i), original-first-secant RFC-F response.
Use: retain the independently observed initial gradient and the genuine
current-CG-line raw value diagonal when the observed first secant varies.
Source: actual CG rational regularity, genuine full modified coefficient,
and compact joint Taylor estimates on nonstagnating references.
-/
namespace krylov.Functions
noncomputable section
open Set Metric Matrix Finset krylov.Methods krylov.Reference krylov.Stability krylov.Correction
  krylov.Nonlinear krylov.Variation krylov.Secant krylov.Envelope
open scoped InnerProductSpace BigOperators Matrix.Norms.L2Operator
variable {k : ℕ}
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

set_option maxHeartbeats 800000 in
/-- The literal physical quadratic response is jointly analytic in its true
base, initial gradient, search operators and correction operators.
Article: main_krylov, thm:Htransfer and lem:U. -/
theorem rfcModifiedQuadratic_variable_analyticAt
    (base : X → Matrix (Fin (k+1)) (Fin (k+1)) ℝ)
    (g : X → EuclideanSpace ℝ (Fin (k+1)))
    (A B : X → ℕ → EuclideanSpace ℝ (Fin (k+1)) →L[ℝ] EuclideanSpace ℝ (Fin (k+1)))
    (D : X → Matrix (Fin (k+1)) (Fin (k+1)) ℝ)
    (x : X) (hb : AnalyticAt ℝ base x) (hpos : (base x).PosDef) (hg : AnalyticAt ℝ g x)
    (hA : ∀ i, AnalyticAt ℝ (fun p=>A p i) x)
    (hB : ∀ i, AnalyticAt ℝ (fun p=>B p i) x)
    (hD : AnalyticAt ℝ D x)
    (hpre : ∀ j≤k, CG.gradient (cgOperator (base x)) (g x) j≠0) :
    AnalyticAt ℝ (fun p=>rfcModifiedQuadratic (base p) (g p) (A p) (B p) (D p)) x := by
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
    (matrixOperator_contDiffAt _ x (hRi.mul ((hL.sub hD).mul hHi)).contDiffAt).analyticAt hr

/-- The original reference diagonal uses the independently measured gradient
and the genuine current CG line scale. Article: main_krylov, prop:Fcycle(i). -/
def rfcFOwnReferenceRawValueChange
    (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ)
    (D : EuclideanSpace ℝ (Fin (k+1)) →L[ℝ]
      EuclideanSpace ℝ (Fin (k+1)) →L[ℝ] EuclideanSpace ℝ (Fin (k+1)))
    (g : EuclideanSpace ℝ (Fin (k+1))) : Matrix (Fin (k+1)) (Fin (k+1)) ℝ :=
  Matrix.diagonal (fun i =>
    ((1/2 : ℝ)*inner ℝ (D (referenceStep (cgOperator base) g i.rev.val)
      (referenceStep (cgOperator base) g i.rev.val))
      (referenceStep (cgOperator base) g i.rev.val)) *
    ((Fin.cons (CG.length (cgOperator base) g k) (fun _ : Fin k => (1 : ℝ)) : Fin (k+1) → ℝ) i)⁻¹^2)

/-- The true own-first-secant RFC-F physical coefficient, including its actual
half-split value-model change. Article: main_krylov, prop:Fcycle(i). -/
def rfcFOwnTensorPhysicalCoefficient
    (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ)
    (D : EuclideanSpace ℝ (Fin (k+1)) →L[ℝ]
      EuclideanSpace ℝ (Fin (k+1)) →L[ℝ] EuclideanSpace ℝ (Fin (k+1)))
    (g u : EuclideanSpace ℝ (Fin (k+1))) : EuclideanSpace ℝ (Fin (k+1)) :=
  rfcModifiedQuadratic base g (rfcOwnTensorSearch base D g u)
    (rfcOwnTensorCorrection base D g u) (rfcFOwnReferenceRawValueChange base D g)

/-- The true own coefficient agrees with the actual fixed-Hessian tensor
coefficient at the quadratic reference. Article: main_krylov, prop:Fcycle(i). -/
theorem rfcFOwnTensorPhysicalCoefficient_quadratic
    (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ)
    (D : EuclideanSpace ℝ (Fin (k+1)) →L[ℝ]
      EuclideanSpace ℝ (Fin (k+1)) →L[ℝ] EuclideanSpace ℝ (Fin (k+1)))
    (u : EuclideanSpace ℝ (Fin (k+1))) :
    rfcFOwnTensorPhysicalCoefficient base D (cgOperator base u) u=rfcFTensorPhysicalCoefficient base D u := by
  unfold rfcFOwnTensorPhysicalCoefficient rfcFTensorPhysicalCoefficient
  apply rfcModifiedQuadratic_congr_prefix
  · intro j hj
    simp only [rfcOwnTensorSearch,ite_eq_left (by omega : j<k+1),rfcTensorSearch,
      fcOwnReferenceMidpoint,rfcReferenceSearchMidpoint,fcQuadraticReferencePoint]
  · simp only [rfcOwnTensorCorrection,ite_eq_left (by omega : k<k+1),rfcTensorCorrection,fcQuadraticReferencePoint]

set_option maxHeartbeats 1000000 in
/-- The genuine raw value diagonal is jointly analytic in the true base
and independently measured gradient. Article: main_krylov, prop:Fcycle(i). -/
theorem rfcFOwnReferenceRawValueChange_variable_analyticAt
    (base : X → Matrix (Fin (k+1)) (Fin (k+1)) ℝ)
    (g : X → EuclideanSpace ℝ (Fin (k+1)))
    (D : EuclideanSpace ℝ (Fin (k+1)) →L[ℝ]
      EuclideanSpace ℝ (Fin (k+1)) →L[ℝ] EuclideanSpace ℝ (Fin (k+1)))
    (x : X) (hb : AnalyticAt ℝ base x) (hpos : (base x).PosDef)
    (hg : AnalyticAt ℝ g x)
    (hpre : ∀ j≤k, CG.gradient (cgOperator (base x)) (g x) j≠0) :
    AnalyticAt ℝ (fun p=>rfcFOwnReferenceRawValueChange (base p) D (g p)) x := by
  have hQa := (matrixOperator_contDiffAt base x hb.contDiffAt).analyticAt
  have hQ := cgOperator_positive (base x) hpos
  have hs j (hj : j≤k) := referenceStep_analyticAt (fun p=>cgOperator (base p)) g x hQa hg
    hQ.1 hQ.2 j (fun l hl=>hpre l (hl.trans hj))
  have hcg := cg_prefix_analytic (fun p=>cgOperator (base p)) g x hQa hg hQ.1 hQ.2 k (fun j hj=>hpre j hj.le)
  have hline := CG.invariant_line_pos (cgOperator (base x)) hQ.2 (g x) k
    (CG.invariant _ hQ.1 hQ.2 _ k (fun j hj=>hpre j hj.le)) (hpre k le_rfl)
  have hlen : AnalyticAt ℝ (fun p=>CG.length (cgOperator (base p)) (g p) k) x :=
    (analytic_inner hcg.2 hcg.1).neg.div
      (analytic_inner hcg.2 (analytic_operator_apply hQa hcg.2)) (hQ.2 _ hline.1).ne'
  have hscale i : AnalyticAt ℝ (fun p=>
      ((Fin.cons (CG.length (cgOperator (base p)) (g p) k) (fun _ : Fin k=>(1:ℝ)) : Fin (k+1) → ℝ) i)⁻¹^2) x := by
    refine Fin.cases ?_ (fun j=>?_) i
    · exact (hlen.inv hline.2.1.ne').pow 2
    · simp only [Fin.cons_succ,inv_one,one_pow]
      exact analyticAt_const
  apply analytic_spectral_matrix
  intro i j
  by_cases hij : i=j
  · subst j
    simp only [rfcFOwnReferenceRawValueChange,Matrix.diagonal_apply_eq]
    have hsi := hs i.rev.val (by omega)
    exact (analyticAt_const.mul (analytic_inner
      (analytic_operator_apply ((D.analyticAt _).comp hsi) hsi) hsi)).mul (hscale i)
  · simp only [rfcFOwnReferenceRawValueChange,Matrix.diagonal_apply_ne _ hij]
    exact analyticAt_const

set_option maxHeartbeats 1000000 in
/-- The actual own-reference tensor coefficient is jointly analytic in the
original base, independently observed gradient and starting position.
Article: main_krylov, thm:Htransfer and lem:U. -/
theorem rfcFOwnTensorPhysicalCoefficient_variable_analyticAt
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (base : X → Matrix (Fin (k+1)) (Fin (k+1)) ℝ)
    (g u : X → EuclideanSpace ℝ (Fin (k+1)))
    (D : EuclideanSpace ℝ (Fin (k+1)) →L[ℝ]
      EuclideanSpace ℝ (Fin (k+1)) →L[ℝ] EuclideanSpace ℝ (Fin (k+1)))
    (x : X) (hb : AnalyticAt ℝ base x) (hpos : (base x).PosDef)
    (hg : AnalyticAt ℝ g x) (hu : AnalyticAt ℝ u x)
    (hpre : ∀ j≤k, CG.gradient (cgOperator (base x)) (g x) j≠0) :
    AnalyticAt ℝ (fun p=>rfcFOwnTensorPhysicalCoefficient (base p) D (g p) (u p)) x := by
  have hQa := (matrixOperator_contDiffAt base x hb.contDiffAt).analyticAt
  have hQ := cgOperator_positive (base x) hpos
  have hs j (hj : j≤k) : AnalyticAt ℝ (fun p=>referenceStep (cgOperator (base p)) (g p) j) x :=
    referenceStep_analyticAt _ g x hQa hg hQ.1 hQ.2 j (fun l hl=>hpre l (hl.trans hj))
  have hd j (hj : j≤k+1) : AnalyticAt ℝ (fun p=>CG.displacement (cgOperator (base p)) (g p) j) x := by
    have hh := (range j).analyticAt_fun_sum (fun l hl=>hs l (by simp only [Finset.mem_range] at hl; omega))
    simpa only [CG.displacement,referenceStep,Finset.sum_apply] using hh
  have hA i : AnalyticAt ℝ (fun p=>rfcOwnTensorSearch (base p) D (g p) (u p) i) x := by
    by_cases hi : i<k+1
    · simp only [rfcOwnTensorSearch,ite_eq_left hi,fcOwnReferenceMidpoint]
      exact hQa.add (D.analyticAt _ |>.comp ((hu.add (hd i (by omega))).add ((hs i (by omega)).const_smul (c:=(1/2:ℝ)))))
    · simp only [rfcOwnTensorSearch,ite_eq_right hi]
      exact hQa
  have hB i : AnalyticAt ℝ (fun p=>rfcOwnTensorCorrection (base p) D (g p) (u p) i) x := by
    by_cases hi : i<k+1
    · simp only [rfcOwnTensorCorrection,ite_eq_left hi]
      exact hQa.add (D.analyticAt _ |>.comp (hu.add (hd (i+1) (by omega))))
    · simp only [rfcOwnTensorCorrection,ite_eq_right hi]
      exact hQa
  exact rfcModifiedQuadratic_variable_analyticAt base g _ _ _ x hb hpos hg hA hB
    (rfcFOwnReferenceRawValueChange_variable_analyticAt base g D x hb hpos hg hpre) hpre

set_option maxHeartbeats 1000000 in
/-- The true own-reference tensor response differs by a uniform first-order
amount when the measured first secant and initial gradient drift together.
Article: main_krylov, thm:Htransfer, original reference coefficient control. -/
theorem compact_rfcFOwnTensorPhysicalCoefficient_reference_change
    (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (hb : base.PosDef)
    (D : EuclideanSpace ℝ (Fin (k+1)) →L[ℝ]
      EuclideanSpace ℝ (Fin (k+1)) →L[ℝ] EuclideanSpace ℝ (Fin (k+1)))
    (K : Set (EuclideanSpace ℝ (Fin (k+1)))) (hK : IsCompact K)
    (hpre : ∀ g∈K, ∀ i≤k, CG.gradient (cgOperator base) g i≠0)
    (R : ℝ) :
    ∃ δ C : ℝ, 0<δ ∧ 0<C ∧ ∀ g∈K, ∀ u : EuclideanSpace ℝ (Fin (k+1)), ‖u‖≤R →
      ∀ Δ : Matrix (Fin (k+1)) (Fin (k+1)) ℝ,
      ∀ v : EuclideanSpace ℝ (Fin (k+1)), ‖(Δ,v)‖≤δ →
      ‖rfcFOwnTensorPhysicalCoefficient (base+Δ) D (g+v) u-
        rfcFOwnTensorPhysicalCoefficient base D g u‖≤C*‖(Δ,v)‖ := by
  let F := fun p : (EuclideanSpace ℝ (Fin (k+1)) × EuclideanSpace ℝ (Fin (k+1))) ×
      (Matrix (Fin (k+1)) (Fin (k+1)) ℝ × EuclideanSpace ℝ (Fin (k+1)))=>
    rfcFOwnTensorPhysicalCoefficient (base+p.2.1) D (p.1.1+p.2.2) p.1.2
  have ha z (hz : z∈K ×ˢ closedBall (0 : EuclideanSpace ℝ (Fin (k+1))) R) : AnalyticAt ℝ F (z,0) := by
    apply rfcFOwnTensorPhysicalCoefficient_variable_analyticAt
    · exact analyticAt_const.add (analyticAt_fst.comp analyticAt_snd)
    · simpa only [Prod.fst_zero,add_zero] using hb
    · exact (analyticAt_fst.comp analyticAt_fst).add (analyticAt_snd.comp analyticAt_snd)
    · exact analyticAt_snd.comp analyticAt_fst
    · simpa only [Prod.fst_zero,Prod.snd_zero,add_zero] using hpre z.1 hz.1
  obtain ⟨δ,C,hδ,hC,hbound⟩ := compact_reference_full_first_order F _ (hK.prod (isCompact_closedBall _ _)) ha
  refine ⟨δ,C,hδ,hC,?_⟩
  intro g hg u hu Δ v hΔ
  have hin : ‖((0 : EuclideanSpace ℝ (Fin (k+1)) × EuclideanSpace ℝ (Fin (k+1))),(Δ,v))‖=‖(Δ,v)‖ := by simp
  have hh := hbound (g,u) ⟨hg,by simpa only [mem_closedBall,dist_zero_right] using hu⟩ 0 (Δ,v) (hin ▸ hΔ)
  simpa only [F,add_zero,Prod.fst_zero,Prod.snd_zero,hin] using hh

end
end krylov.Functions
