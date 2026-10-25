import polyak.Numerics.Parametric.Invertible

/-!
Article: Appendix B, Neumann remainder for implicit-branch derivatives.
Use: the checked norm defect bounds the actual solution of the differentiated
source equations, including its deviation from the preconditioned approximation.
-/
noncomputable section
namespace polyak.Numerics.Parametric

theorem norm_solution_le {n : ℕ} (R D : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ))
    (q : ℝ) (hq : q<1) (hM : ‖ContinuousLinearMap.id ℝ _-R.comp D‖≤q)
    (v b : Fin n → ℝ) (hv : D v=b) : ‖v‖≤‖R b‖/(1-q) := by
  have hdecomp : v=R b+(ContinuousLinearMap.id ℝ (Fin n → ℝ)-R.comp D) v := by
    simp [hv]
  have hb : ‖v‖≤‖R b‖+q*‖v‖ := by
    calc
      ‖v‖=‖R b+(ContinuousLinearMap.id ℝ (Fin n → ℝ)-R.comp D) v‖ := congrArg norm hdecomp
      _≤‖R b‖+‖(ContinuousLinearMap.id ℝ (Fin n → ℝ)-R.comp D) v‖ := norm_add_le _ _
      _≤‖R b‖+q*‖v‖ := add_le_add le_rfl
        (((ContinuousLinearMap.id ℝ (Fin n → ℝ)-R.comp D).le_opNorm v).trans
          (mul_le_mul_of_nonneg_right hM (norm_nonneg v)))
  apply (le_div_iff₀ (by linarith : 0<1-q)).mpr
  nlinarith

theorem norm_solution_error_le {n : ℕ} (R D : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ))
    (q : ℝ) (hq0 : 0≤q) (hq : q<1)
    (hM : ‖ContinuousLinearMap.id ℝ _-R.comp D‖≤q)
    (v b : Fin n → ℝ) (hv : D v=b) : ‖v-R b‖≤q*‖R b‖/(1-q) := by
  have he : v-R b=(ContinuousLinearMap.id ℝ (Fin n → ℝ)-R.comp D) v := by simp [hv]
  rw [he]
  calc
    _≤‖ContinuousLinearMap.id ℝ (Fin n → ℝ)-R.comp D‖*‖v‖ :=
      (ContinuousLinearMap.id ℝ (Fin n → ℝ)-R.comp D).le_opNorm v
    _≤q*‖v‖ := mul_le_mul_of_nonneg_right hM (norm_nonneg v)
    _≤q*(‖R b‖/(1-q)) := mul_le_mul_of_nonneg_left (norm_solution_le R D q hq hM v b hv) hq0
    _=_ := by ring

end polyak.Numerics.Parametric
