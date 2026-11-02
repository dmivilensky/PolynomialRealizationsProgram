import krylov.Functions.PlanarCorrectionLocalization

/-!
Article: main_krylov, prop:Fcycle(iii), actual unrestricted-output correction remainder.
Use: prove the true cubic gradients differ from their genuine last-point
Hessian models by O(p⁴) at every common output with cubic-small gradients.
Source: exact polynomial Taylor identity and the derived global/local output
enclosures, without assuming that the method chooses a small correction.
-/
namespace krylov.Functions
noncomputable section
open Set Metric NormedSpace krylov.Tensor.BinaryCubic

/-- The actual affine Hessian's coordinate action, from the full cubic family.
Article: main_krylov, prop:Fcycle(iii). -/
def planarValueCoordinateHessianAction (p r : ℝ) (t : krylov.Tensor.BinaryCubic)
    (x v : ℝ × ℝ) : ℝ × ℝ :=
  ((t.t0*x.1+t.t1*x.2-t.t0*p/2)*v.1+(t.t1*x.1+t.t2*x.2-t.t1*p/2)*v.2,
    (t.t1*x.1+t.t2*x.2-t.t1*p/2)*v.1+(t.t2*x.1+t.t3*x.2-t.t2*p-t.t3*r*p/2)*v.2)

/-- The real terminal affine model of the actual objective gradient.
Article: main_krylov, thm:Fplanar and prop:Fcycle(iii). -/
def planarCubicTerminalModel (p r : ℝ) (t : krylov.Tensor.BinaryCubic) (v : ℝ × ℝ) : ℝ × ℝ :=
  planarCubicGradient p r t (p,r*p)+v+planarValueCoordinateHessianAction p r t (p,r*p) v

/-- The displayed coordinate Hessian action is read from the genuine actual
second differential. Article: main_krylov, prop:Fcycle(iii). -/
theorem planarValueCoordinateHessianAction_actual (p r : ℝ) (t : krylov.Tensor.BinaryCubic)
    (x v : ℝ × ℝ) : planarValueCoordinateHessianAction p r t x v=
    planarDifferentialCoordinates (planarValueHessian (ContinuousLinearMap.fst ℝ ℝ ℝ)
      (ContinuousLinearMap.snd ℝ ℝ ℝ) p r t x v) := by
  ext <;> simp [planarValueCoordinateHessianAction,planarDifferentialCoordinates,planarValueHessian,
    ContinuousLinearMap.smulRight_apply]

/-- The actual cubic objective has its exact last-point Taylor identity, whose
only nonlinear remainder is the genuine homogeneous quadratic gradient.
Article: main_krylov, prop:Fcycle(iii). -/
theorem planarCubicGradient_terminal_identity (p r : ℝ) (t : krylov.Tensor.BinaryCubic) (v : ℝ × ℝ) :
    planarCubicGradient p r t ((p,r*p)+v)-planarCubicTerminalModel p r t v=
      planarValueCoordinateDerivative 0 r t v := by
  ext <;> simp only [planarCubicGradient,planarCubicTerminalModel,planarValueCoordinateDerivative,
    planarValueCoordinateHessianAction,Prod.fst_add,Prod.snd_add,Prod.fst_sub,Prod.snd_sub] <;> ring

/-- The genuine homogeneous cubic-gradient remainder has a global quadratic
norm bound. Article: main_krylov, prop:Fcycle(iii).
Proof: bound the actual polynomial on the compact unit ball and use its
proved degree-two homogeneity in every direction, including zero. -/
theorem planarValueCoordinateDerivative_homogeneous_bound (r : ℝ) (t : krylov.Tensor.BinaryCubic) :
    ∃ B : ℝ, 0<B ∧ ∀ v : ℝ × ℝ, ‖planarValueCoordinateDerivative 0 r t v‖≤B*‖v‖^2 := by
  have hc : Continuous (planarValueCoordinateDerivative 0 r t) := by
    unfold planarValueCoordinateDerivative
    fun_prop
  obtain ⟨B,hB⟩ := (isCompact_closedBall (0 : ℝ × ℝ) 1).exists_bound_of_continuousOn hc.continuousOn
  refine ⟨|B|+1,by positivity,?_⟩
  intro v
  by_cases hv : v=0
  · subst v
    simp [planarValueCoordinateDerivative]
  have hb := hB (normalize v) (by simp only [mem_closedBall,dist_zero_right,norm_normalize hv,le_refl])
  have he : planarValueCoordinateDerivative 0 r t v=
      ‖v‖^2 • planarValueCoordinateDerivative 0 r t (normalize v) := by
    have hh := planarValueCoordinateDerivative_scale 0 r ‖v‖ t (normalize v)
    simpa only [mul_zero,norm_smul_normalize] using hh
  rw [he,norm_smul,Real.norm_of_nonneg (sq_nonneg _)]
  have hBB : B≤|B|+1 := (le_abs_self B).trans (by linarith)
  exact (mul_le_mul_of_nonneg_left (hb.trans hBB) (sq_nonneg _)).trans_eq (mul_comm _ _)

/-- Every actual unrestricted common cubic-small output has a uniform
fourth-order error in both genuine terminal affine gradient models.
Article: main_krylov, prop:Fcycle(iii).
The small correction is proved from the two true gradients; it is not an
assumption imposed on the output policy. -/
theorem planarCubic_common_output_affine_error (r : ℝ) (t u : krylov.Tensor.BinaryCubic)
    (hobs : observe r t=observe r u) (hd : u.t2-t.t2≠0) (hr : r≠0)
    (A : ℝ) (hA : 0≤A) :
    ∃ C : ℝ, 0<C ∧ ∀ p : ℝ, 0<p → p≤1 → ∀ z : ℝ × ℝ,
      ‖fderiv ℝ (planarCubicObjective p r t) z‖≤A*p^3 →
      ‖fderiv ℝ (planarCubicObjective p r u) z‖≤A*p^3 →
      ‖planarCubicGradient p r t z-planarCubicTerminalModel p r t (z-(p,r*p))‖≤C*p^4 ∧
      ‖planarCubicGradient p r u z-planarCubicTerminalModel p r u (z-(p,r*p))‖≤C*p^4 := by
  obtain ⟨M,hM,hloc⟩ := planarCubic_common_output_correction_localization r t u hobs hd hr A hA
  obtain ⟨Bt,hBt,htbound⟩ := planarValueCoordinateDerivative_homogeneous_bound r t
  obtain ⟨Bu,hBu,hubound⟩ := planarValueCoordinateDerivative_homogeneous_bound r u
  refine ⟨(Bt+Bu)*M^2+1,by positivity,?_⟩
  intro p hp hp₁ z ht hu
  have hs := hloc p hp hp₁ z ht hu
  have hsq : ‖z-(p,r*p)‖^2≤M^2*p^4 := by
    have hh := (sq_le_sq₀ (norm_nonneg _) (by positivity : 0≤M*p^2)).mpr hs
    exact hh.trans_eq (by ring)
  have hterm (w : krylov.Tensor.BinaryCubic) (B : ℝ) (hB : 0≤B)
      (hw : ∀ v : ℝ × ℝ, ‖planarValueCoordinateDerivative 0 r w v‖≤B*‖v‖^2) :
      ‖planarCubicGradient p r w z-planarCubicTerminalModel p r w (z-(p,r*p))‖≤B*M^2*p^4 := by
    have he := planarCubicGradient_terminal_identity p r w (z-(p,r*p))
    rw [add_sub_cancel] at he
    rw [he]
    exact (hw _).trans ((mul_le_mul_of_nonneg_left hsq hB).trans_eq (by ring))
  have hp₄ : 0≤p^4 := by positivity
  have hCt : Bt*M^2≤(Bt+Bu)*M^2+1 := by nlinarith only [mul_nonneg hBu.le (sq_nonneg M)]
  have hCu : Bu*M^2≤(Bt+Bu)*M^2+1 := by nlinarith only [mul_nonneg hBt.le (sq_nonneg M)]
  exact ⟨(hterm t Bt hBt.le htbound).trans (mul_le_mul_of_nonneg_right hCt hp₄),
    (hterm u Bu hBu.le hubound).trans (mul_le_mul_of_nonneg_right hCu hp₄)⟩
/-- Every actual unrestricted common cubic-small output has a uniform
fourth-order error in both genuine terminal affine gradient models.
Article: main_krylov, prop:Fcycle(iii).
The small correction is proved from the two true gradients; it is not an
assumption imposed on the output policy. -/
theorem planarCubic_common_output_coordinate_affine_error (r : ℝ) (t u : krylov.Tensor.BinaryCubic)
    (hobs : observe r t=observe r u) (hd : u.t2-t.t2≠0) (hr : r≠0)
    (A : ℝ) (hA : 0≤A) :
    ∃ C : ℝ, 0<C ∧ ∀ p : ℝ, 0<p → p≤1 → ∀ z : ℝ × ℝ,
      ‖planarCubicGradient p r t z‖≤A*p^3 →
      ‖planarCubicGradient p r u z‖≤A*p^3 →
      ‖planarCubicGradient p r t z-planarCubicTerminalModel p r t (z-(p,r*p))‖≤C*p^4 ∧
      ‖planarCubicGradient p r u z-planarCubicTerminalModel p r u (z-(p,r*p))‖≤C*p^4 := by
  obtain ⟨M,hM,hloc⟩ := planarCubic_common_output_coordinate_localization r t u hobs hd hr A hA
  obtain ⟨Bt,hBt,htbound⟩ := planarValueCoordinateDerivative_homogeneous_bound r t
  obtain ⟨Bu,hBu,hubound⟩ := planarValueCoordinateDerivative_homogeneous_bound r u
  refine ⟨(Bt+Bu)*M^2+1,by positivity,?_⟩
  intro p hp hp₁ z ht hu
  have hs := hloc p hp hp₁ z ht hu
  have hsq : ‖z-(p,r*p)‖^2≤M^2*p^4 := by
    have hh := (sq_le_sq₀ (norm_nonneg _) (by positivity : 0≤M*p^2)).mpr hs
    exact hh.trans_eq (by ring)
  have hterm (w : krylov.Tensor.BinaryCubic) (B : ℝ) (hB : 0≤B)
      (hw : ∀ v : ℝ × ℝ, ‖planarValueCoordinateDerivative 0 r w v‖≤B*‖v‖^2) :
      ‖planarCubicGradient p r w z-planarCubicTerminalModel p r w (z-(p,r*p))‖≤B*M^2*p^4 := by
    have he := planarCubicGradient_terminal_identity p r w (z-(p,r*p))
    rw [add_sub_cancel] at he
    rw [he]
    exact (hw _).trans ((mul_le_mul_of_nonneg_left hsq hB).trans_eq (by ring))
  have hp₄ : 0≤p^4 := by positivity
  have hCt : Bt*M^2≤(Bt+Bu)*M^2+1 := by nlinarith only [mul_nonneg hBu.le (sq_nonneg M)]
  have hCu : Bu*M^2≤(Bt+Bu)*M^2+1 := by nlinarith only [mul_nonneg hBt.le (sq_nonneg M)]
  exact ⟨(hterm t Bt hBt.le htbound).trans (mul_le_mul_of_nonneg_right hCt hp₄),
    (hterm u Bu hBu.le hubound).trans (mul_le_mul_of_nonneg_right hCu hp₄)⟩

end
end krylov.Functions
