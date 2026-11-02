import krylov.Functions.RFCReferenceChange

/-!
Article: main_krylov, thm:Htransfer, true moving-reference midpoint geometry.
Use: replace the minimizer-Hessian CG reference by the actual first-secant
reference in all compatible tensor slices. Source: joint analyticity of
actual nonstagnating CG steps and their genuine finite displacement sums.
-/
namespace krylov.Functions
noncomputable section
open Set Metric Matrix Finset krylov.Methods krylov.Reference krylov.Stability krylov.Correction
open scoped InnerProductSpace BigOperators Matrix.Norms.L2Operator
variable {k : ℕ}

set_option maxHeartbeats 800000 in
/-- True CG steps change by a uniform first-order amount under simultaneous
perturbation of their actual positive base and initial gradient.
Article: main_krylov, thm:Htransfer, genuine reference replacement. -/
theorem compact_reference_step_changes
    (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (hb : base.PosDef)
    (K : Set (EuclideanSpace ℝ (Fin (k+1)))) (hK : IsCompact K)
    (hpre : ∀ g∈K, ∀ i≤k, CG.gradient (cgOperator base) g i≠0) :
    ∃ δ C : ℝ, 0<δ ∧ 0<C ∧ ∀ g∈K,
      ∀ Δ : Matrix (Fin (k+1)) (Fin (k+1)) ℝ,
      ∀ v : EuclideanSpace ℝ (Fin (k+1)), ‖(Δ,v)‖≤δ → ∀ i<k+1,
      ‖referenceStep (cgOperator (base+Δ)) (g+v) i-referenceStep (cgOperator base) g i‖≤C*‖(Δ,v)‖ := by
  let F := fun p : EuclideanSpace ℝ (Fin (k+1)) ×
      (Matrix (Fin (k+1)) (Fin (k+1)) ℝ × EuclideanSpace ℝ (Fin (k+1)))=>
    fun i : Fin (k+1)=>referenceStep (cgOperator (base+p.2.1)) (p.1+p.2.2) i.val
  have ha g (hg : g∈K) : AnalyticAt ℝ F (g,0) := by
    apply AnalyticAt.pi
    intro i
    have hbase : AnalyticAt ℝ (fun p : EuclideanSpace ℝ (Fin (k+1)) ×
        (Matrix (Fin (k+1)) (Fin (k+1)) ℝ × EuclideanSpace ℝ (Fin (k+1)))=>base+p.2.1) (g,0) :=
      analyticAt_const.add (analyticAt_fst.comp analyticAt_snd)
    have hQa := (matrixOperator_contDiffAt _ (g,0) hbase.contDiffAt).analyticAt
    have hga : AnalyticAt ℝ (fun p : EuclideanSpace ℝ (Fin (k+1)) ×
        (Matrix (Fin (k+1)) (Fin (k+1)) ℝ × EuclideanSpace ℝ (Fin (k+1)))=>p.1+p.2.2) (g,0) :=
      analyticAt_fst.add (analyticAt_snd.comp analyticAt_snd)
    exact referenceStep_analyticAt _ _ (g,0) hQa hga
      (by simpa only [Prod.fst_zero,add_zero] using! (cgOperator_positive base hb).1)
      (by simpa only [Prod.fst_zero,add_zero] using! (cgOperator_positive base hb).2)
      i.val (by simpa only [Prod.fst_zero,Prod.snd_zero,add_zero] using! (fun (j : ℕ) (hj : j ≤ i.val)=>hpre g hg j (by omega)))
  obtain ⟨δ,C,hδ,hC,hbound⟩ := compact_reference_full_first_order F K hK ha
  refine ⟨δ,C,hδ,hC,?_⟩
  intro g hg Δ v hΔ i hi
  have hin : ‖((0 : EuclideanSpace ℝ (Fin (k+1))),(Δ,v))‖=‖(Δ,v)‖ := by simp
  have hh := (norm_le_pi_norm (F (g,(Δ,v))-F (g,0)) (⟨i,hi⟩ : Fin (k+1))).trans
    (by simpa only [add_zero,hin] using hbound g hg 0 (Δ,v) (hin ▸ hΔ))
  simpa only [F,Pi.sub_apply,Prod.fst_zero,Prod.snd_zero,add_zero] using hh

/-- Genuine reference midpoint and correction-node perturbations inherit
the compact first-order bound of their true finite CG step sums.
Article: main_krylov, thm:Htransfer. -/
theorem compact_reference_midpoint_changes
    (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (hb : base.PosDef)
    (K : Set (EuclideanSpace ℝ (Fin (k+1)))) (hK : IsCompact K)
    (hpre : ∀ g∈K, ∀ i≤k, CG.gradient (cgOperator base) g i≠0) :
    ∃ δ C : ℝ, 0<δ ∧ 0<C ∧ ∀ g∈K,
      ∀ Δ : Matrix (Fin (k+1)) (Fin (k+1)) ℝ,
      ∀ v : EuclideanSpace ℝ (Fin (k+1)), ‖(Δ,v)‖≤δ →
      ∀ u : EuclideanSpace ℝ (Fin (k+1)), ∀ i<k+1,
      ‖fcOwnReferenceMidpoint (cgOperator (base+Δ)) (g+v) u i-
        fcOwnReferenceMidpoint (cgOperator base) g u i‖≤C*‖(Δ,v)‖ ∧
      ‖(u+CG.displacement (cgOperator (base+Δ)) (g+v) (i+1))-
        (u+CG.displacement (cgOperator base) g (i+1))‖≤C*‖(Δ,v)‖ := by
  obtain ⟨δ,C,hδ,hC,hsteps⟩ := compact_reference_step_changes base hb K hK hpre
  refine ⟨δ,((k:ℝ)+2)*C,hδ,by positivity,?_⟩
  intro g hg Δ v hΔ u i hi
  have hdisp j (hj : j≤k+1) :
      ‖CG.displacement (cgOperator (base+Δ)) (g+v) j-CG.displacement (cgOperator base) g j‖≤(j:ℝ)*C*‖(Δ,v)‖ := by
    change ‖(∑ l∈range j,referenceStep (cgOperator (base+Δ)) (g+v) l)-
      ∑ l∈range j,referenceStep (cgOperator base) g l‖≤_
    rw [←sum_sub_distrib]
    calc
      _ ≤ ∑ l∈range j,‖referenceStep (cgOperator (base+Δ)) (g+v) l-referenceStep (cgOperator base) g l‖ := norm_sum_le _ _
      _ ≤ ∑ _l∈range j,C*‖(Δ,v)‖ := sum_le_sum (fun l hl=>hsteps g hg Δ v hΔ l (by simp only [Finset.mem_range] at hl; omega))
      _ = _ := by simp; ring
  have hcount : (i:ℝ)+1≤(k:ℝ)+2 := by exact_mod_cast (show i+1≤k+2 by omega)
  have hn : 0≤C*‖(Δ,v)‖ := by positivity
  constructor
  · have he : fcOwnReferenceMidpoint (cgOperator (base+Δ)) (g+v) u i-
        fcOwnReferenceMidpoint (cgOperator base) g u i=
        (CG.displacement (cgOperator (base+Δ)) (g+v) i-CG.displacement (cgOperator base) g i)+
        (1/2:ℝ) • (referenceStep (cgOperator (base+Δ)) (g+v) i-referenceStep (cgOperator base) g i) := by
      unfold fcOwnReferenceMidpoint
      module
    rw [he]
    have hh := norm_add_le (CG.displacement (cgOperator (base+Δ)) (g+v) i-CG.displacement (cgOperator base) g i)
      ((1/2:ℝ) • (referenceStep (cgOperator (base+Δ)) (g+v) i-referenceStep (cgOperator base) g i))
    rw [norm_smul,Real.norm_of_nonneg (by norm_num : (0:ℝ)≤1/2)] at hh
    exact hh.trans (by nlinarith only [hdisp i (by omega),hsteps g hg Δ v hΔ i hi,mul_le_mul_of_nonneg_right hcount hn,hn])
  · rw [add_sub_add_left_eq_sub]
    have hh := hdisp (i+1) (by omega)
    push_cast at hh
    exact hh.trans (by nlinarith only [mul_le_mul_of_nonneg_right hcount hn])

end
end krylov.Functions
