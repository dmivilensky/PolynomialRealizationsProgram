import krylov.Functions.RFCReferenceGeometryChange
import krylov.Functions.NativeRFCSpatialResponse

/-!
Article: main_krylov, thm:Htransfer, actual first-secant tensor response.
Use: retain the true initial observed gradient independently of the initial
position in every compatible reference midpoint. Source: joint analyticity
of genuine CG steps, exact finite prefix dependence and compact Taylor bounds.
-/
namespace krylov.Functions
noncomputable section
open Set Metric Matrix Finset krylov.Methods krylov.Reference krylov.Stability krylov.Correction
open scoped InnerProductSpace BigOperators Matrix.Norms.L2Operator
variable {k : ℕ}

/-- Genuine finite reference search slices for an independently observed
initial gradient. The unexecuted tail is harmlessly constant.
Article: main_krylov, thm:Htransfer, original-A₀ tensor inputs. -/
def rfcOwnTensorSearch
    (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ)
    (D : EuclideanSpace ℝ (Fin (k+1)) →L[ℝ]
      EuclideanSpace ℝ (Fin (k+1)) →L[ℝ] EuclideanSpace ℝ (Fin (k+1)))
    (g u : EuclideanSpace ℝ (Fin (k+1))) (i : ℕ) :
    EuclideanSpace ℝ (Fin (k+1)) →L[ℝ] EuclideanSpace ℝ (Fin (k+1)) :=
  if i<k+1 then cgOperator base+D (fcOwnReferenceMidpoint (cgOperator base) g u i) else cgOperator base

/-- Genuine finite reference correction slices at the next own-reference nodes.
Article: main_krylov, thm:Htransfer. -/
def rfcOwnTensorCorrection
    (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ)
    (D : EuclideanSpace ℝ (Fin (k+1)) →L[ℝ]
      EuclideanSpace ℝ (Fin (k+1)) →L[ℝ] EuclideanSpace ℝ (Fin (k+1)))
    (g u : EuclideanSpace ℝ (Fin (k+1))) (i : ℕ) :
    EuclideanSpace ℝ (Fin (k+1)) →L[ℝ] EuclideanSpace ℝ (Fin (k+1)) :=
  if i<k+1 then cgOperator base+D (u+CG.displacement (cgOperator base) g (i+1)) else cgOperator base

/-- The real physical tensor response of the original independently measured
first secant and gradient. Article: main_krylov, thm:Htransfer. -/
def rfcOwnTensorPhysicalCoefficient
    (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ)
    (D : EuclideanSpace ℝ (Fin (k+1)) →L[ℝ]
      EuclideanSpace ℝ (Fin (k+1)) →L[ℝ] EuclideanSpace ℝ (Fin (k+1)))
    (g u : EuclideanSpace ℝ (Fin (k+1))) : EuclideanSpace ℝ (Fin (k+1)) :=
  rfcPhysicalQuadratic base g (rfcOwnTensorSearch base D g u) (rfcOwnTensorCorrection base D g u)

/-- At the genuine minimizer-Hessian reference the own-reference coefficient
is exactly the proved native tensor coefficient.
Article: main_krylov, thm:Htransfer, both reference conventions agree. -/
theorem rfcOwnTensorPhysicalCoefficient_quadratic
    (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ)
    (D : EuclideanSpace ℝ (Fin (k+1)) →L[ℝ]
      EuclideanSpace ℝ (Fin (k+1)) →L[ℝ] EuclideanSpace ℝ (Fin (k+1)))
    (u : EuclideanSpace ℝ (Fin (k+1))) :
    rfcOwnTensorPhysicalCoefficient base D (cgOperator base u) u=rfcTensorPhysicalCoefficient base D u := by
  apply rfcPhysicalQuadratic_congr_prefix
  · intro j hj
    simp only [rfcOwnTensorSearch,ite_eq_left (by omega : j<k+1),rfcTensorSearch,
      fcOwnReferenceMidpoint,rfcReferenceSearchMidpoint,fcQuadraticReferencePoint]
  · simp only [rfcOwnTensorCorrection,ite_eq_left (by omega : k<k+1),rfcTensorCorrection,fcQuadraticReferencePoint]

set_option maxHeartbeats 1000000 in
/-- The actual own-reference tensor coefficient is jointly analytic in the
original base, independently observed gradient and starting position.
Article: main_krylov, thm:Htransfer and lem:U. -/
theorem rfcOwnTensorPhysicalCoefficient_variable_analyticAt
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (base : X → Matrix (Fin (k+1)) (Fin (k+1)) ℝ)
    (g u : X → EuclideanSpace ℝ (Fin (k+1)))
    (D : EuclideanSpace ℝ (Fin (k+1)) →L[ℝ]
      EuclideanSpace ℝ (Fin (k+1)) →L[ℝ] EuclideanSpace ℝ (Fin (k+1)))
    (x : X) (hb : AnalyticAt ℝ base x) (hpos : (base x).PosDef)
    (hg : AnalyticAt ℝ g x) (hu : AnalyticAt ℝ u x)
    (hpre : ∀ j≤k, CG.gradient (cgOperator (base x)) (g x) j≠0) :
    AnalyticAt ℝ (fun p=>rfcOwnTensorPhysicalCoefficient (base p) D (g p) (u p)) x := by
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
  exact rfcPhysicalQuadratic_variable_analyticAt base g _ _ x hb hpos hg hA hB hpre

set_option maxHeartbeats 1000000 in
/-- The true own-reference tensor response differs by a uniform first-order
amount when the measured first secant and initial gradient drift together.
Article: main_krylov, thm:Htransfer, original reference coefficient control. -/
theorem compact_rfcOwnTensorPhysicalCoefficient_reference_change
    (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (hb : base.PosDef)
    (D : EuclideanSpace ℝ (Fin (k+1)) →L[ℝ]
      EuclideanSpace ℝ (Fin (k+1)) →L[ℝ] EuclideanSpace ℝ (Fin (k+1)))
    (K : Set (EuclideanSpace ℝ (Fin (k+1)))) (hK : IsCompact K)
    (hpre : ∀ g∈K, ∀ i≤k, CG.gradient (cgOperator base) g i≠0)
    (R : ℝ) :
    ∃ δ C : ℝ, 0<δ ∧ 0<C ∧ ∀ g∈K, ∀ u : EuclideanSpace ℝ (Fin (k+1)), ‖u‖≤R →
      ∀ Δ : Matrix (Fin (k+1)) (Fin (k+1)) ℝ,
      ∀ v : EuclideanSpace ℝ (Fin (k+1)), ‖(Δ,v)‖≤δ →
      ‖rfcOwnTensorPhysicalCoefficient (base+Δ) D (g+v) u-
        rfcOwnTensorPhysicalCoefficient base D g u‖≤C*‖(Δ,v)‖ := by
  let F := fun p : (EuclideanSpace ℝ (Fin (k+1)) × EuclideanSpace ℝ (Fin (k+1))) ×
      (Matrix (Fin (k+1)) (Fin (k+1)) ℝ × EuclideanSpace ℝ (Fin (k+1)))=>
    rfcOwnTensorPhysicalCoefficient (base+p.2.1) D (p.1.1+p.2.2) p.1.2
  have ha z (hz : z∈K ×ˢ closedBall (0 : EuclideanSpace ℝ (Fin (k+1))) R) : AnalyticAt ℝ F (z,0) := by
    apply rfcOwnTensorPhysicalCoefficient_variable_analyticAt
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
