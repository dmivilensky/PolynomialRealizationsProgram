import krylov.Functions.PlanarOutputLocalization

/-!
Article: main_krylov, prop:Fcycle(iii), true local correction enclosure.
Use: after the global unrestricted-output bound, prove that every common
cubic-small output is quadratically close to the last observed point for the
actual canonical scalar cubic functions. Source: exact polynomial scaling,
compactness, and the already proved true global data-fibre localization.
-/
namespace krylov.Functions
noncomputable section
open Set Metric krylov.Tensor.BinaryCubic

/-- The actual canonical reference quadratic ending at the last planar point.
Article: main_krylov, prop:Fcycle(iii). -/
def planarReferenceQuadratic (p r : ℝ) (z : ℝ × ℝ) : ℝ :=
  (z.1-p)^2/2+(z.2-r*p)^2/2

/-- The actual full cubic objective with its prescribed exact data fibre.
Article: main_krylov, prop:Fcycle(iii). -/
def planarCubicObjective (p r : ℝ) (t : krylov.Tensor.BinaryCubic) (z : ℝ × ℝ) : ℝ :=
  planarReferenceQuadratic p r z+planarValueFamily
    (ContinuousLinearMap.fst ℝ ℝ ℝ) (ContinuousLinearMap.snd ℝ ℝ ℝ) p r t z

/-- The actual full gradient coordinates of the canonical objective.
Article: main_krylov, prop:Fcycle(iii). -/
def planarCubicGradient (p r : ℝ) (t : krylov.Tensor.BinaryCubic) (z : ℝ × ℝ) : ℝ × ℝ :=
  z-(p,r*p)+planarValueCoordinateDerivative p r t z

/-- The genuine reference quadratic differential.
Article: main_krylov, prop:Fcycle(iii). -/
theorem planarReferenceQuadratic_hasFDerivAt (p r : ℝ) (z : ℝ × ℝ) :
    HasFDerivAt (planarReferenceQuadratic p r)
      ((z.1-p) • ContinuousLinearMap.fst ℝ ℝ ℝ+(z.2-r*p) • ContinuousLinearMap.snd ℝ ℝ ℝ) z := by
  have h₁ := (((ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt (x:=z)).sub_const p).pow 2
  have h₂ := (((ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt (x:=z)).sub_const (r*p)).pow 2
  have h := (h₁.const_mul (1/2:ℝ)).add (h₂.const_mul (1/2:ℝ))
  have hfun : (fun x : ℝ × ℝ=>(1/2:ℝ)*((ContinuousLinearMap.fst ℝ ℝ ℝ) x-p)^2+
      (1/2:ℝ)*((ContinuousLinearMap.snd ℝ ℝ ℝ) x-r*p)^2)=planarReferenceQuadratic p r := by
    ext x
    simp only [planarReferenceQuadratic,ContinuousLinearMap.coe_fst',ContinuousLinearMap.coe_snd']
    ring
  change HasFDerivAt (fun x : ℝ × ℝ=>(1/2:ℝ)*((ContinuousLinearMap.fst ℝ ℝ ℝ) x-p)^2+
    (1/2:ℝ)*((ContinuousLinearMap.snd ℝ ℝ ℝ) x-r*p)^2) _ z at h
  rw [hfun] at h
  apply h.congr_fderiv
  apply ContinuousLinearMap.ext
  intro v
  simp only [ContinuousLinearMap.coe_fst',ContinuousLinearMap.coe_snd',add_apply,smul_apply,
    smul_eq_mul,nsmul_eq_mul,Nat.reduceSub,pow_one]
  ring

/-- The displayed full gradient coordinates are extracted from the genuine
actual scalar objective derivative. Article: main_krylov, prop:Fcycle(iii). -/
theorem planarCubicGradient_actual (p r : ℝ) (t : krylov.Tensor.BinaryCubic) (z : ℝ × ℝ) :
    planarCubicGradient p r t z=planarDifferentialCoordinates (fderiv ℝ (planarCubicObjective p r t) z) := by
  have hd := ((planarReferenceQuadratic_hasFDerivAt p r z).add
    (planarValueFamily_hasFDerivAt (ContinuousLinearMap.fst ℝ ℝ ℝ) (ContinuousLinearMap.snd ℝ ℝ ℝ) p r t z)).fderiv
  change fderiv ℝ (planarCubicObjective p r t) z=_ at hd
  rw [hd,planarCubicGradient,planarValueCoordinateDerivative_actual]
  ext <;> simp [planarDifferentialCoordinates]

/-- Joint scale covariance of the genuine full cubic differential perturbation.
Article: main_krylov, prop:Fcycle(iii), actual shrinking polynomial family. -/
theorem planarValueCoordinateDerivative_scale (p r q : ℝ) (t : krylov.Tensor.BinaryCubic) (z : ℝ × ℝ) :
    planarValueCoordinateDerivative (q*p) r t (q • z)=q^2 • planarValueCoordinateDerivative p r t z := by
  ext <;> simp only [planarValueCoordinateDerivative,Prod.smul_fst,Prod.smul_snd,smul_eq_mul] <;> ring

/-- Every genuinely p-sized point has a uniform quadratic actual cubic-gradient
perturbation. Article: main_krylov, prop:Fcycle(iii).
The bound is derived from the true polynomial's compact unit-scale image. -/
theorem planarValueCoordinateDerivative_scaled_bound (r : ℝ) (t : krylov.Tensor.BinaryCubic)
    (M : ℝ) : ∃ B : ℝ, 0<B ∧ ∀ p : ℝ, 0<p → ∀ z : ℝ × ℝ, ‖z‖≤M*p →
      ‖planarValueCoordinateDerivative p r t z‖≤B*p^2 := by
  have hc : Continuous (planarValueCoordinateDerivative 1 r t) := by
    unfold planarValueCoordinateDerivative
    fun_prop
  obtain ⟨B,hB⟩ := (isCompact_closedBall (0 : ℝ × ℝ) M).exists_bound_of_continuousOn hc.continuousOn
  refine ⟨|B|+1,by positivity,?_⟩
  intro p hp z hz
  let v := p⁻¹ • z
  have hv : ‖v‖≤M := by
    rw [show v=p⁻¹ • z from rfl,norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hp.le)]
    exact (mul_le_mul_of_nonneg_left hz (inv_nonneg.mpr hp.le)).trans_eq (by field_simp)
  have hb := hB v (by simpa only [mem_closedBall,dist_zero_right] using hv)
  have he : planarValueCoordinateDerivative p r t z=p^2 • planarValueCoordinateDerivative 1 r t v := by
    have hh := planarValueCoordinateDerivative_scale 1 r p t v
    simpa only [mul_one,v,smul_smul,mul_inv_cancel₀ hp.ne',one_smul] using hh
  rw [he,norm_smul,Real.norm_of_nonneg (sq_nonneg p)]
  have hBB : B≤|B|+1 := (le_abs_self B).trans (by linarith)
  exact (mul_le_mul_of_nonneg_left (hb.trans hBB) (sq_nonneg p)).trans_eq (mul_comm _ _)

/-- The true post-search gradient is exactly the printed common observed
coefficient in the first planar direction. Article: main_krylov, thm:Fplanar. -/
theorem planarCubicGradient_last (p r : ℝ) (t : krylov.Tensor.BinaryCubic) :
    planarCubicGradient p r t (p,r*p)=(r*p^2/2*(t.t1+r*t.t2),0) := by
  ext <;> simp only [planarCubicGradient,planarValueCoordinateDerivative,Prod.fst_add,Prod.snd_add,
    Prod.fst_sub,Prod.snd_sub] <;> ring

/-- Any arbitrary common output with cubic-small actual differentials is
quadratically close to the real last observed point, with no prior output
neighborhood assumption. Article: main_krylov, prop:Fcycle(iii). -/
theorem planarCubic_common_output_correction_localization (r : ℝ) (t u : krylov.Tensor.BinaryCubic)
    (hobs : observe r t=observe r u) (hd : u.t2-t.t2≠0) (hr : r≠0)
    (A : ℝ) (hA : 0≤A) :
    ∃ C : ℝ, 0<C ∧ ∀ p : ℝ, 0<p → p≤1 → ∀ z : ℝ × ℝ,
      ‖fderiv ℝ (planarCubicObjective p r t) z‖≤A*p^3 →
      ‖fderiv ℝ (planarCubicObjective p r u) z‖≤A*p^3 → ‖z-(p,r*p)‖≤C*p^2 := by
  obtain ⟨M,hM,hglobal⟩ := planarValue_actual_common_output_localization r t u hobs hd hr A hA
  obtain ⟨B,hB,hperturb⟩ := planarValueCoordinateDerivative_scaled_bound r t M
  refine ⟨A+B,by positivity,?_⟩
  intro p hp hp₁ z ht hu
  have hz : ‖z‖≤M*p := hglobal p hp hp₁ (planarReferenceQuadratic p r) z
    (planarReferenceQuadratic_hasFDerivAt p r z).differentiableAt ht hu
  have hgrad : ‖planarCubicGradient p r t z‖≤A*p^3 := by
    rw [planarCubicGradient_actual]
    exact (planarDifferentialCoordinates_norm _).trans ht
  have he : z-(p,r*p)=planarCubicGradient p r t z-planarValueCoordinateDerivative p r t z := by
    rw [planarCubicGradient,add_sub_cancel_right]
  rw [he]
  apply (norm_sub_le _ _).trans
  have hb := hperturb p hp z hz
  have hpp := mul_le_mul_of_nonneg_left hp₁ (by positivity : 0≤A*p^2)
  nlinarith only [hgrad,hb,hpp]

/-- The same true correction enclosure in gradient coordinates, allowing
exact transport to the Euclidean Riesz-gradient norm.
Article: main_krylov, prop:Fcycle(iii). -/
theorem planarCubic_common_output_coordinate_localization (r : ℝ) (t u : krylov.Tensor.BinaryCubic)
    (hobs : observe r t=observe r u) (hd : u.t2-t.t2≠0) (hr : r≠0)
    (A : ℝ) (hA : 0≤A) :
    ∃ C : ℝ, 0<C ∧ ∀ p : ℝ, 0<p → p≤1 → ∀ z : ℝ × ℝ,
      ‖planarCubicGradient p r t z‖≤A*p^3 →
      ‖planarCubicGradient p r u z‖≤A*p^3 → ‖z-(p,r*p)‖≤C*p^2 := by
  obtain ⟨M,hM,hglobal⟩ := planarValue_common_output_localization r t u hobs hd hr A hA
  obtain ⟨B,hB,hperturb⟩ := planarValueCoordinateDerivative_scaled_bound r t M
  refine ⟨A+B,by positivity,?_⟩
  intro p hp hp₁ z ht hu
  have hz : ‖z‖≤M*p := hglobal p hp hp₁ (fun z=>z-(p,r*p)) z ht hu
  have he : z-(p,r*p)=planarCubicGradient p r t z-planarValueCoordinateDerivative p r t z := by
    rw [planarCubicGradient,add_sub_cancel_right]
  rw [he]
  apply (norm_sub_le _ _).trans
  have hb := hperturb p hp z hz
  have hpp := mul_le_mul_of_nonneg_left hp₁ (by positivity : 0≤A*p^2)
  nlinarith only [ht,hb,hpp]

end
end krylov.Functions
