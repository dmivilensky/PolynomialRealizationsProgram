import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Tactic

/-!
Article: main_krylov, prop:deep, genuine source execution and singular-model certification.
Use: The exact original determinant/adjugate mechanism that forces unbounded residuals.
Source: original RFC array execution, earlier-package integer checker
soundness, standard real continuity and the intermediate value theorem.
-/

namespace krylov.Correction
noncomputable section
open Set
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A genuine continuous determinant with opposite endpoint signs and a uniformly nonzero adjugate numerator forces an unbounded actual quotient residual on nonsingular interior parameters.
Use: Turn the verified original source determinant and numerator bounds into the actual unbounded residual conclusion.
Article: main_krylov, prop:deep, actual checked source-family argument.
Proof: For every proposed residual bound, choose a sufficiently small positive determinant value. The standard intermediate value theorem attains it at a genuine interior parameter. The uniform numerator lower bound divided by this true positive value dominates the bounded incoming gradient by the reverse triangle inequality. -/
theorem unbounded_det_quotient (f : ℝ → ℝ) (v g : ℝ → E)
    {a b ε M : ℝ} (hab : a<b) (hf : ContinuousOn f (Icc a b))
    (hleft : 0<f a) (hright : f b<0) (hε : 0<ε) (hM : 0≤M)
    (hv : ∀ t∈Icc a b, ε≤‖v t‖) (hg : ∀ t∈Icc a b, ‖g t‖≤M) :
    ∀ R : ℝ, ∃ t∈Ioo a b, 0<f t ∧ R<‖g t-(f t)⁻¹ • v t‖ := by
  -- Attain a genuine small positive determinant value before applying the physical norm lower bound.
  intro R
  let q := |R|+M+1
  have hq : 0<q := by dsimp only [q]; positivity
  let δ := min (f a/2) (ε/(2*q))
  have hδ : 0<δ := lt_min (half_pos hleft) (div_pos hε (by positivity))
  have hδleft : δ<f a := (min_le_left _ _).trans_lt (half_lt_self hleft)
  have hδbound : 2*q*δ≤ε := by
    have hh := (le_div_iff₀ (by positivity : 0<2*q)).mp (min_le_right (f a/2) (ε/(2*q)))
    nlinarith
  obtain ⟨t,ht,hft⟩ := intermediate_value_Icc' hab.le hf ⟨by linarith,le_of_lt hδleft⟩
  have htleft : a<t := lt_of_le_of_ne ht.1 (by intro he; subst t; exact hδleft.ne hft.symm)
  have htright : t<b := lt_of_le_of_ne ht.2 (by intro he; subst t; linarith)
  have hnorm : ε/δ≤‖δ⁻¹ • v t‖ := by
    rw [norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hδ.le)]
    simpa only [div_eq_mul_inv,mul_comm] using mul_le_mul_of_nonneg_left (hv t ht) (inv_nonneg.mpr hδ.le)
  have hsize : 2*q≤ε/δ := (le_div_iff₀ hδ).mpr hδbound
  have htri := norm_sub_norm_le (δ⁻¹ • v t) (g t)
  rw [norm_sub_rev] at htri
  refine ⟨t,⟨htleft,htright⟩,by rw [hft]; exact hδ,?_⟩
  rw [hft]
  have hgb := hg t ht
  dsimp only [q] at hsize
  nlinarith [le_abs_self R]

end
end krylov.Correction
