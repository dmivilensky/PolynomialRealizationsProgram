import jacobi.RootMass.Quadratures

/-!
Article: jacobi, Theorem D.8.
The literal nonsingular moment quadrature is strictly increasing from zero
to infinity. Its monotonicity uses the actual inverse and the certified Q
comparison; an explicit positive uniform lower bound for K proves its full
unbounded range. Every positive defining equation has an attained unique root.
Source: the exact rational certificate, Lebesgue strict comparison and intermediate values.
Use: the root in the final root-mass lower bound is unique for every positive spectral threshold.
-/
namespace jacobi.RootMass
noncomputable section
open MeasureTheory Real Set Filter
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- The genuine constraint quadrature is strictly increasing on its complete nonnegative parameter domain.
Use: the root in the final root-mass lower bound is unique for every positive spectral threshold.
Article: jacobi, Theorem D.8.
Proof: at each u in (0,1), the actual inverse state strictly increases in y.
The proved Q representation and certified strict Q comparison give strict
pointwise increase of the actual constraint integrand. Integrate over a set of positive measure. -/
theorem Ghat_strictMono {a : ℝ} (ha : -(17/5:ℝ)≤a) :
    StrictMonoOn (Ghat a (sharp_parameter ha)) (Ici (0:ℝ)) := by
  -- Endpoint changes do not affect strictness on the positive-measure open integration interval.
  intro x hx y hy hxy
  let hpa := sharp_parameter ha
  have hpoint (u : ℝ) (hu : u∈Ioo (0:ℝ) 1) :
      4*x^2*K a (node a hpa x u)<4*y^2*K a (node a hpa y u) := by
    have hr : 0<1-u^2 := by nlinarith [hu.1,hu.2,sq_nonneg (1-u)]
    have hn : node a hpa x u<node a hpa y u :=
      inverse_strictMono hpa (mul_nonneg hx hr.le) (mul_nonneg hy hr.le) (mul_lt_mul_of_pos_right hxy hr)
    have hQ := Q_strictMono ha (inverse_ge_one a hpa _) (inverse_ge_one a hpa _) hn
    rw [mul_assoc 4 (x^2),mul_assoc 4 (y^2),constraint_integrand_identity hpa hx hu,
      constraint_integrand_identity hpa hy hu]
    exact mul_lt_mul_of_pos_left (div_lt_div_of_pos_right hQ (sq_pos_of_pos hr)) (by norm_num)
  have hh := intervalIntegral.integral_lt_integral_of_ae_le_of_measure_setOfPred_lt_ne_zero
    (by norm_num : (0:ℝ)≤1) ((Ghat_integrable a hpa x).const_mul (4*x^2))
    ((Ghat_integrable a hpa y).const_mul (4*y^2))
  have hi : (∫ u in (0:ℝ)..1,4*x^2*K a (node a hpa x u))<
      ∫ u in (0:ℝ)..1,4*y^2*K a (node a hpa y u) := by
    apply hh
    · filter_upwards [ae_restrict_mem measurableSet_Ioc,
        ae_restrict_of_ae (show ∀ᵐ u : ℝ,u≠1 by simp [ae_iff])] with u hu hu1
      exact (hpoint u ⟨hu.1,lt_of_le_of_ne hu.2 hu1⟩).le
    · have hv : 0<(volume.restrict (Ioc (0:ℝ) 1)) (Ioo (0:ℝ) 1) := by
        rw [Measure.restrict_apply measurableSet_Ioo,inter_eq_self_of_subset_left Ioo_subset_Ioc_self]
        norm_num
      exact ne_of_gt (hv.trans_le (measure_mono (fun u hu => hpoint u hu)))
  simpa only [intervalIntegral.integral_const_mul,Ghat,hpa] using hi

/-- A genuine uniform positive lower bound for the nonsingular constraint weight on the whole unbounded profile domain.
Use: proves the full range of Ghat without a limiting or numerical assumption.
Article: jacobi, Theorem D.8.
Proof: on n>=1 and a>=-17/5, p(n)>=(3/5)*n² and
q(n)<=(4+abs(a))*n². Compare the positive rational functions and use n²>=1. -/
theorem K_lower {a n : ℝ} (ha : -(17/5:ℝ)≤a) (hn : 1≤n) :
    (27/(125*(4+|a|)):ℝ)≤K a n := by
  -- Explicit polynomial estimates replace a nonconstructive minimum on an unbounded interval.
  have hn0 : 0<n := zero_lt_one.trans_le hn
  have hC : 0<4+|a| := by positivity
  have hp := (p_bounds (sharp_parameter ha) hn).1.trans_le (p_bounds (sharp_parameter ha) hn).2.1
  have hq := q_pos (sharp_parameter ha) hn
  have hP : (3/5:ℝ)*n^2≤p a n := by
    have hh := mul_nonneg (show 0≤a+17/5 by linarith) hn0.le
    have hh' := mul_nonneg (sub_nonneg.mpr hn) (show 0≤(12/5:ℝ)*n-1 by linarith)
    unfold p
    nlinarith
  have hQ : q a n≤(4+|a|)*n^2 := by
    have hh := mul_le_mul_of_nonneg_right (le_abs_self a) hn0.le
    have hh' := mul_nonneg (abs_nonneg a) (show 0≤n^2-n by nlinarith)
    unfold q
    nlinarith
  have hnum : (27/125:ℝ)*n^6≤(p a n)^3 := by
    have hh := pow_le_pow_left₀ (by positivity : 0≤(3/5:ℝ)*n^2) hP 3
    convert hh using 1
    ring
  have hden : n^2*q a n≤(4+|a|)*n^4 := by
    nlinarith [mul_le_mul_of_nonneg_left hQ (sq_nonneg n)]
  have hl : ((27/125:ℝ)*n^6)/((4+|a|)*n^4)≤K a n :=
    (div_le_div_of_nonneg_right hnum (by positivity)).trans
      (div_le_div_of_nonneg_left (pow_pos hp 3).le (mul_pos (sq_pos_of_pos hn0) hq) hden)
  have he : ((27/125:ℝ)*n^6)/((4+|a|)*n^4)=(27/(125*(4+|a|)))*n^2 := by field_simp
  rw [he] at hl
  have hconst : 0≤(27/(125*(4+|a|)):ℝ) := by positivity
  exact (le_mul_of_one_le_right hconst (by nlinarith : 1≤n^2)).trans hl

/-- The actual constraint quadrature has an explicit quadratic lower bound.
Use: its range reaches every positive target T/b⁴.
Article: jacobi, Theorem D.8.
Proof: integrate the proved uniform positive K bound on the actual unit interval. -/
theorem Ghat_lower {a : ℝ} (ha : -(17/5:ℝ)≤a) (y : ℝ) :
    4*y^2*(27/(125*(4+|a|)))≤Ghat a (sharp_parameter ha) y := by
  have hh := intervalIntegral.integral_mono_on (by norm_num : (0:ℝ)≤1)
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (27/(125*(4+|a|)):ℝ)) volume 0 1)
    (Ghat_integrable a (sharp_parameter ha) y)
    (fun u _ => K_lower ha (inverse_ge_one a (sharp_parameter ha) _))
  norm_num only [intervalIntegral.integral_const,sub_zero,one_smul] at hh
  exact mul_le_mul_of_nonneg_left hh (by positivity)

/-- The literal defining constraint tends to infinity at its positive end.
Use: supplies actual global surjectivity and excludes missing large-threshold parameters.
Article: jacobi, Theorem D.8.
Proof: the explicit positive quadratic lower bound eventually exceeds every prescribed target. -/
theorem Ghat_atTop {a : ℝ} (ha : -(17/5:ℝ)≤a) : Tendsto (Ghat a (sharp_parameter ha)) atTop atTop := by
  -- The bound is uniform in the inverse-coordinate state.
  let C : ℝ := 27/(125*(4+|a|))
  have hC : 0<C := by dsimp only [C]; positivity
  apply tendsto_atTop.mpr
  intro R
  filter_upwards [eventually_ge_atTop (max (1:ℝ) (R/(4*C)))] with y hy
  have hy1 : 1≤y := (le_max_left _ _).trans hy
  have hRy : R≤4*C*y := by
    have hh : R/(4*C)≤y := (le_max_right _ _).trans hy
    nlinarith [(div_le_iff₀ (by positivity : 0<4*C)).mp hh]
  have hb := Ghat_lower ha y
  change 4*y^2*C≤_ at hb
  nlinarith [mul_nonneg (show 0≤4*C by positivity) (show 0≤y^2-y by nlinarith)]

/-- Every strictly positive target has one and only one actual positive root of the printed root-mass constraint.
Use: the final Lagrangian bound uses a genuinely existing unique parameter for all b>0 and edge spectra.
Article: jacobi, Theorem D.8.
Proof: continuity, the proved zero endpoint and the actual infinite upper
limit give a root by intermediate values. Its target is positive, so the
root is positive; strict monotonicity proves uniqueness. -/
theorem constraint_root {a T : ℝ} (ha : -(17/5:ℝ)≤a) (hT : 0<T) :
    ∃ y : ℝ,0<y ∧ Ghat a (sharp_parameter ha) y=T ∧
      ∀ z : ℝ,0<z → Ghat a (sharp_parameter ha) z=T → z=y := by
  -- The root is constructed from the genuine convergent integral, not supplied as a certificate.
  obtain ⟨y,hy,he⟩ := intermediate_value_Ici (Ghat_continuous a (sharp_parameter ha)).continuousOn
    (Ghat_atTop ha) (show T∈Ici (Ghat a (sharp_parameter ha) 0) by rw [Ghat_zero]; exact hT.le)
  have hyp : 0<y := lt_of_le_of_ne hy (by intro hh; rw [← hh,Ghat_zero] at he; exact hT.ne he)
  exact ⟨y,hyp,he,fun z hz hze => (Ghat_strictMono ha).injOn hz.le hyp.le (hze.trans he.symm)⟩

end
end jacobi.RootMass
