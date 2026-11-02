import krylov.XR.ThresholdRigidity
import krylov.XR.RelativeCorrection

/-!
Article: main_krylov, thm:metric, the original physical metric selection.
Use: coincidence of the actual robust thresholds on every nonzero
residual, or on just a nonempty open set, is equivalent to a positive
scalar multiple of the observed model metric. Source: the proved moment
rigidity and genuine positive-root coordinate equivalence.
-/

/-!
Article: krylov, Theorem F.1 [thm:metric].

Threshold coincidence on all residuals or a nonempty open set is equivalent to proportional
metrics. The physical relative correction has the exact minimax value and complete
subcritical/critical/supercritical minimizer sets.
The formal coefficient vector is the actual window correction; the uncertainty interval is
exactly the relative-norm budget. The zero residual and empty dimension are included.
-/
namespace krylov.XR
noncomputable section
open Matrix krylov.Reference krylov.Secant krylov.Nonlinear
open scoped InnerProductSpace Matrix.Norms.L2Operator
variable {p : ℕ}

/-- Normalizing a true positive form by any positive physical metric
gives a true positive canonical model. Article: main_krylov, thm:metric. -/
theorem relativeOperator_posDef (Xi T : Matrix (Fin p) (Fin p) ℝ)
    (hXi : Xi.PosDef) (hT : T.PosDef) : (relativeOperator Xi T).PosDef := by
  have hu := (isUnit_iff_isUnit_det _).mpr (metricRoot_det_unit Xi hXi)
  have hi := Matrix.isUnit_nonsing_inv_iff.mpr hu
  have hh := hT.conjTranspose_mul_mul_same (Matrix.mulVec_injective_of_isUnit hi)
  simpa only [conjTranspose_eq_transpose_of_trivial,transpose_nonsing_inv,
    (metricRoot_isSymm Xi).eq,relativeOperator] using hh

/-- The canonical model is scalar precisely when the true physical
model is the same scalar times the chosen metric. Article: thm:metric. -/
theorem relativeOperator_scalar_iff (Xi T : Matrix (Fin p) (Fin p) ℝ)
    (hXi : Xi.PosDef) (c : ℝ) : relativeOperator Xi T=c • 1 ↔ T=c • Xi := by
  constructor
  · intro h
    have hh := congrArg (fun A=>metricRoot Xi*A*metricRoot Xi) h
    simpa only [relativeOperator_reconstruct Xi T hXi,Matrix.mul_smul,Matrix.smul_mul,
      Matrix.mul_one,metricRoot_square Xi hXi] using hh
  · intro h
    rw [h,relativeOperator_smul,relativeOperator_base Xi hXi]

/-- Both actual robust thresholds of a positive scalar model equal that
scalar on every nonzero residual. Article: main_krylov, thm:metric. -/
theorem scalar_model_thresholds (N : Matrix (Fin p) (Fin p) ℝ) (hN : N.PosDef)
    (c : ℝ) (hc : 0<c) (hscalar : N=c • 1)
    (r : EuclideanSpace ℝ (Fin p)) (hr : r≠0) :
    newtonThreshold N r=c ∧ zeroThreshold N r=c := by
  have ha (v : EuclideanSpace ℝ (Fin p)) : cgOperator N v=c • v := by
    simp only [hscalar,cgOperator,map_smul,map_one,_root_.smul_apply,one_apply_eq_self]
  have hi (v : EuclideanSpace ℝ (Fin p)) : cgOperator N⁻¹ v=c⁻¹ • v := by
    have hh := threshold_inverse_cancel N hN (c⁻¹ • v)
    rw [ha,smul_smul,mul_inv_cancel₀ hc.ne',one_smul] at hh
    exact hh
  have hn : 0<‖r‖ := norm_pos_iff.mpr hr
  constructor
  · unfold newtonThreshold
    simp only [hi,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hc)]
    field_simp
  · unfold zeroThreshold
    rw [ha,norm_smul,Real.norm_eq_abs,abs_of_pos hc]
    exact mul_div_cancel_right₀ c hn.ne'

/-- The physical metric rigidity theorem with the article's weakest
nonempty-open-set hypothesis. Article: main_krylov, thm:metric. -/
theorem metric_thresholds_open_iff (Xi T : Matrix (Fin p) (Fin p) ℝ)
    (hXi : Xi.PosDef) (hT : T.PosDef) :
    (∃ U : Set (EuclideanSpace ℝ (Fin p)),IsOpen U ∧ U.Nonempty ∧
      ∀ r∈U,r≠0 → newtonThreshold (relativeOperator Xi T) r=
        zeroThreshold (relativeOperator Xi T) r) ↔
    ∃ c : ℝ,0<c ∧ Xi=c⁻¹ • T := by
  have hN := relativeOperator_posDef Xi T hXi hT
  constructor
  · rintro ⟨U,hU,hne,heq⟩
    obtain ⟨c,hc,hs⟩ := thresholds_open_rigidity _ hN U hU hne heq
    have hp := (relativeOperator_scalar_iff Xi T hXi c).mp hs
    refine ⟨c,hc,?_⟩
    rw [hp,smul_smul,inv_mul_cancel₀ hc.ne',one_smul]
  · rintro ⟨c,hc,hphysical⟩
    have hp : T=c • Xi := by rw [hphysical,smul_smul,mul_inv_cancel₀ hc.ne',one_smul]
    have hs := (relativeOperator_scalar_iff Xi T hXi c).mpr hp
    refine ⟨Set.univ,isOpen_univ,Set.univ_nonempty,?_⟩
    intro r _ hr
    have hh := scalar_model_thresholds _ hN c hc hs r hr
    exact hh.1.trans hh.2.symm

/-- Coincidence for every actual nonzero residual selects exactly the
same physical model metric. Article: main_krylov, thm:metric. -/
theorem metric_thresholds_all_iff (Xi T : Matrix (Fin p) (Fin p) ℝ)
    (hXi : Xi.PosDef) (hT : T.PosDef) :
    (∀ r : EuclideanSpace ℝ (Fin p),r≠0 →
      newtonThreshold (relativeOperator Xi T) r=zeroThreshold (relativeOperator Xi T) r) ↔
    ∃ c : ℝ,0<c ∧ Xi=c⁻¹ • T := by
  constructor
  · intro hh
    apply (metric_thresholds_open_iff Xi T hXi hT).mp
    exact ⟨Set.univ,isOpen_univ,Set.univ_nonempty,fun r _ hr=>hh r hr⟩
  · rintro ⟨c,hc,hphysical⟩ r hr
    have hp : T=c • Xi := by rw [hphysical,smul_smul,mul_inv_cancel₀ hc.ne',one_smul]
    have hs := (relativeOperator_scalar_iff Xi T hXi c).mpr hp
    have hh := scalar_model_thresholds _ (relativeOperator_posDef Xi T hXi hT) c hc hs r hr
    exact hh.1.trans hh.2.symm

/-- On the selected physical metric, the original threshold value is
the scalar c stated in the article. Article: main_krylov, thm:metric. -/
theorem metric_threshold_common_value (Xi T : Matrix (Fin p) (Fin p) ℝ)
    (hXi : Xi.PosDef) (hT : T.PosDef) (c : ℝ) (hc : 0<c) (hphysical : Xi=c⁻¹ • T)
    (r : EuclideanSpace ℝ (Fin p)) (hr : r≠0) :
    newtonThreshold (relativeOperator Xi T) r=c ∧ zeroThreshold (relativeOperator Xi T) r=c := by
  have hp : T=c • Xi := by rw [hphysical,smul_smul,mul_inv_cancel₀ hc.ne',one_smul]
  exact scalar_model_thresholds _ (relativeOperator_posDef Xi T hXi hT) c hc
    ((relativeOperator_scalar_iff Xi T hXi c).mpr hp) r hr

end
end krylov.XR
