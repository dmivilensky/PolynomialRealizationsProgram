import jacobi.Reference.SlopeAnalytic
import jacobi.Reference.SlopeBounds

/-!
Article: jacobi, Appendix C.2 (green part and regularized kernel series).
A fixed frequency Cauchy circle gives the genuine derivative of the
actual spatial slope. The original energy-frequency chain rule then
gives |partial_z partial_t f|=O(omega^(-gamma)) on every fixed
physical strip away from zero. This avoids assuming joint analyticity
or interchanging two derivatives before either has been constructed.
Use: waveSlope_frequency_deriv_bound treats the source slope exponent 1-gamma on its genuine frequency Cauchy circles for every alpha>-1.
-/
namespace jacobi.Reference
noncomputable section
open Real Set _root_.Complex
set_option backward.isDefEq.respectTransparency false

/-- Comparable positive bases give a uniform real-power comparison at every real exponent.
Use: waveSlope_frequency_deriv_bound treats the source slope exponent 1-gamma on its genuine frequency Cauchy circles for every alpha>-1.
Article: jacobi, Appendix C.2 (green part and regularized kernel series).
Proof: for nonnegative exponent use x<=2*r; for nonpositive exponent
use r/2<=x. The sum of the two positive scaling constants covers both cases. -/
theorem rpow_half_double_bound {r x : ℝ} (hr : 0<r) (hl : r/2≤x) (hu : x≤2*r) (p : ℝ) :
    x^p≤((2:ℝ)^p+(2:ℝ)^(-p))*r^p := by
  -- Splitting on the exponent is necessary because the original source range includes gamma on both sides of one.
  have hx : 0<x := (by positivity : 0<r/2).trans_le hl
  by_cases hp : 0≤p
  · have h := Real.rpow_le_rpow hx.le hu hp
    rw [Real.mul_rpow (by norm_num : (0:ℝ)≤2) hr.le] at h
    apply h.trans
    nlinarith [mul_nonneg (Real.rpow_nonneg (by norm_num : (0:ℝ)≤2) (-p)) (Real.rpow_nonneg hr.le p)]
  · have h := Real.rpow_le_rpow_of_nonpos (by positivity : 0<r/2) hl (le_of_not_ge hp)
    rw [Real.div_rpow hr.le (by norm_num : (0:ℝ)≤2),div_eq_mul_inv,
      ← Real.rpow_neg (by norm_num : (0:ℝ)≤2)] at h
    apply h.trans
    nlinarith [mul_nonneg (Real.rpow_nonneg (by norm_num : (0:ℝ)≤2) p) (Real.rpow_nonneg hr.le p)]

/-- A genuine unit frequency circle around a sufficiently large positive real source frequency stays comparable to that frequency and in the fixed imaginary strip.
Use: waveSlope_frequency_deriv_bound applies the actual source slope bound on the whole Cauchy circle.
Article: jacobi, Appendix C.2 (green part and regularized kernel series).
Proof: the direct and reverse triangle inequalities give the two norm
bounds. The imaginary part of the center is zero, so its true unit
distance bounds the entire imaginary part of each circle point. -/
theorem real_frequency_unit_disk {w : ℝ} (hw : 2≤w) {v : ℂ} (hv : ‖v-(w:ℂ)‖≤1) :
    w/2≤‖v‖ ∧ ‖v‖≤2*w ∧ |v.im|≤1 := by
  -- These are bounds for the actual complex frequency, without selecting a square root.
  have hp : 0<w := by linarith
  have hl := norm_sub_norm_le (w:ℂ) v
  rw [norm_sub_rev,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hp] at hl
  have hu := norm_add_le (v-(w:ℂ)) (w:ℂ)
  rw [sub_add_cancel,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hp] at hu
  have hi := (Complex.abs_im_le_norm (v-(w:ℂ))).trans hv
  simp only [Complex.sub_im,Complex.ofReal_im,sub_zero] at hi
  exact ⟨by linarith,by linarith,hi⟩

/-- The actual frequency derivative of the original spatial slope has its full high-frequency size uniformly away from zero.
Use: slope_energy_deriv_bound obtains the genuine mixed spectral-spatial estimate needed for differentiating the original F series.
Article: jacobi, Appendix C.2 (green part and regularized kernel series).
Source: Cauchy's derivative estimate, Complex.norm_cderiv_le.
Proof: every point of a unit frequency circle stays above the actual
slope threshold, has comparable frequency norm and imaginary part
at most one. The proved genuine spatial slope bound is uniform there;
the actual entire slope permits the community Cauchy estimate. -/
theorem waveSlope_frequency_deriv_bound {a : ℝ} (ha : -1<a) {d : ℝ} (hd : 0<d) :
    ∃ C : ℝ,0<C ∧ ∀ w:ℝ,2*max 1 (1/d)≤w →
      ∀ t∈Icc d (1/2),
        ‖deriv (fun v => waveSlope a v t) (w:ℂ)‖≤C*w^(1-gamma a) := by
  -- The Cauchy circle belongs to the true source frequency plane and its radius is exactly one.
  obtain ⟨B,hB,hbound⟩ := waveSlope_away_bound ha hd
  let P : ℝ := (2:ℝ)^(1-gamma a)+(2:ℝ)^(-(1-gamma a))
  have hP : 0<P := by dsimp [P]; positivity
  refine ⟨B*P*Real.exp 1,by positivity,fun w hw t ht => ?_⟩
  have hw2 : 2≤w := by linarith [le_max_left 1 (1/d)]
  have hwp : 0<w := by linarith
  have ht' : t∈Ioo (0:ℝ) 1 := ⟨hd.trans_le ht.1,by linarith [ht.2]⟩
  have hdif : DifferentiableOn ℂ (fun v => waveSlope a v t) univ :=
    fun v _ => (waveSlope_frequency_analytic ha ht' v).differentiableAt.differentiableWithinAt
  rw [← Complex.cderiv_eq_deriv isOpen_univ hdif (by norm_num : (0:ℝ)<1) (subset_univ _)]
  have hcircle (v : ℂ) (hv : v∈Metric.sphere (w:ℂ) 1) :
      ‖waveSlope a v t‖≤(B*P*Real.exp 1)*w^(1-gamma a) := by
    have hdist : ‖v-(w:ℂ)‖≤1 := by
      rw [← dist_eq_norm]
      exact (Metric.mem_sphere.mp hv).le
    obtain ⟨hl,hu,hi⟩ := real_frequency_unit_disk hw2 hdist
    have hscale : max 1 (1/d)≤‖v‖ := by linarith
    have hs := hbound v hscale t ht
    have hr := rpow_half_double_bound hwp hl hu (1-gamma a)
    have he : Real.exp (t*|v.im|)≤Real.exp 1 := by
      apply Real.exp_le_exp.mpr
      nlinarith [mul_le_mul_of_nonneg_left hi (hd.le.trans ht.1),ht.2]
    have hh := mul_le_mul hr he (Real.exp_pos _).le
      (mul_nonneg hP.le (Real.rpow_nonneg hwp.le _))
    apply hs.trans
    calc
      _ = B*(‖v‖^(1-gamma a)*Real.exp (t*|v.im|)) := by ring
      _ ≤ B*(P*w^(1-gamma a)*Real.exp 1) := mul_le_mul_of_nonneg_left hh hB.le
      _ = _ := by ring
  simpa only [div_one] using Complex.norm_cderiv_le (by norm_num : (0:ℝ)<1) hcircle

/-- The actual energy derivative of the original spatial slope has the sharp inverse-frequency bound throughout every fixed physical half strip.
Use: the real spectral mean value theorem bounds partial_t f(sigma_k)-partial_t f(tau_k), establishing the derivative summability needed for Appendix C.2 (c) and K regularity.
Article: jacobi, Appendix C.2 (green part and regularized kernel series).
Proof: the original frequency derivative is 2*omega times the actual
energy derivative of the same slope. Its genuine Cauchy bound divided
by the positive frequency has exactly the printed power omega^(-gamma). -/
theorem slope_energy_deriv_bound {a : ℝ} (ha : -1<a) {d : ℝ} (hd : 0<d) :
    ∃ C : ℝ,0<C ∧ ∀ w:ℝ,2*max 1 (1/d)≤w → ∀ t∈Icc d (1/2),
      ‖deriv (fun z => solutionSlope a z t)
        ((jacobi.Jacobi.endpointCorrection a:ℂ)+(w:ℂ)^2)‖≤C*w^(-gamma a) := by
  -- The division is performed only at genuine positive real source frequencies.
  obtain ⟨C,hC,hbound⟩ := waveSlope_frequency_deriv_bound ha hd
  refine ⟨C/2,by positivity,fun w hw t ht => ?_⟩
  have hw2 : 2≤w := by linarith [le_max_left 1 (1/d)]
  have hwp : 0<w := by linarith
  have ht' : t∈Ioo (0:ℝ) 1 := ⟨hd.trans_le ht.1,by linarith [ht.2]⟩
  have h := hbound w hw t ht
  rw [waveSlope_energy_derivative ha ht',norm_mul,norm_mul,
    Complex.norm_ofNat,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hwp] at h
  have hpow : w^(1-gamma a)=w^(-gamma a)*w := by
    rw [show 1-gamma a= -gamma a+1 by ring,Real.rpow_add hwp,Real.rpow_one]
  rw [hpow] at h
  nlinarith

end
end jacobi.Reference
