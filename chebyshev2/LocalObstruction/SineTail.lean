import chebyshev2.LocalObstruction.SineDecay
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
Article: chebyshev2, Theorem 6.1.
Equation (54): the weighted right tail of the actual sine density is o(n).
Use: `chebyshev2.LocalObstruction.weightedSineTail_original_formula` feeds
`chebyshev2.LocalObstruction.sineJost_scaled_left_tail_bound` (sine Jost scaled left tail
bound).
Proof chain: `chebyshev2.LocalObstruction.sine_green_scale_tail` — chebyshev2, Theorem 6.1; No
locally sharp C1 bound from finitely many spectral observations.
-/
namespace chebyshev2.LocalObstruction
noncomputable section
open Set Real MeasureTheory Filter Asymptotics chebyshev2.SineContinuum
open scoped Topology
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false

 /--
The stated quantitative bound `n y≤45*n x*exp (-2*(y-x))`.

Use: `chebyshev2.LocalObstruction.sine_weighted_density_bound` uses this bound to establish
the stated quantitative bound `exp (2*(y-x))*m y≤2025*n x^2*exp (-2*(y-x))`.

Article: chebyshev2, Theorem 6.1 via `chebyshev2.LocalObstruction.sine_green_scale_tail`.

Proof: Use the identities/estimates `chebyshev2.SineContinuum.n_theta_envelope` with the
arguments shown in the proof.
-/
theorem sine_right_decay {x y : ℝ} (hx : 1≤x) (hxy : x≤y) :
    n y≤45*n x*exp (-2*(y-x)) := by
  -- Use the identities/estimates `chebyshev2.SineContinuum.n_theta_envelope` with the
  -- arguments shown in the proof.
  have hx₀ : 0≤x := by linarith
  have hy₀ : 0≤y := hx₀.trans hxy
  have hlo := (n_theta_envelope x).1
  have hup := (n_theta_envelope y).2
  dsimp only [thetaRho] at hlo hup
  rw [abs_of_nonneg hx₀] at hlo
  rw [abs_of_nonneg hy₀] at hup
  rw [show -π*exp (2*x)/2= -(π*exp (2*x)/2) by ring] at hlo
  rw [show -π*exp (2*y)/2= -(π*exp (2*y)/2) by ring] at hup
  have hpx : 3≤exp (2*x) := by linarith [add_one_le_exp (2*x)]
  have hcoef : 4≤π*exp (2*x) := by nlinarith [pi_gt_three]
  have hfact : exp (2*y)=exp (2*x)*exp (2*(y-x)) := by
    rw [← exp_add]
    congr 1
    ring
  have hdiff : 2*exp (2*x)*(y-x)≤exp (2*y)-exp (2*x) := by
    have he := mul_le_mul_of_nonneg_left (add_one_le_exp (2*(y-x))) (exp_pos (2*x)).le
    rw [← hfact] at he
    nlinarith
  have hpow : 2*y-π*exp (2*y)/2≤2*x-π*exp (2*x)/2-2*(y-x) := by
    have he := mul_le_mul_of_nonneg_left hdiff pi_pos.le
    have hp := mul_le_mul_of_nonneg_right hcoef (sub_nonneg.mpr hxy)
    nlinarith
  have hlo' : 40*exp (2*x-π*exp (2*x)/2)≤45*n x := by
    rw [exp_sub,div_eq_mul_inv,← exp_neg]
    nlinarith [hlo]
  calc
    n y≤40*exp (2*y-π*exp (2*y)/2) := by
      rw [exp_sub,div_eq_mul_inv,← exp_neg]
      exact hup
    _ ≤ 40*exp (2*x-π*exp (2*x)/2-2*(y-x)) :=
      mul_le_mul_of_nonneg_left (exp_le_exp.mpr hpow) (by norm_num)
    _ = (40*exp (2*x-π*exp (2*x)/2))*exp (-2*(y-x)) := by
      rw [exp_sub,div_eq_mul_inv,← exp_neg]
      rw [show -(2*(y-x))= -2*(y-x) by ring,mul_assoc]
    _ ≤ 45*n x*exp (-2*(y-x)) :=
      mul_le_mul_of_nonneg_right hlo' (exp_pos _).le

 /--
The stated quantitative bound `exp (2*(y-x))*m y≤2025*n x^2*exp (-2*(y-x))`.

Use: `chebyshev2.LocalObstruction.weightedSineTail_bounds` uses this bound to establish
membership in the specified domain/enclosure: `weightedSineTail x ∈ Icc (0:ℝ) (2025/2*n x^2)`.

Article: chebyshev2, Theorem 6.1 via `chebyshev2.LocalObstruction.sine_green_scale_tail`.

Proof: Use the identities/estimates `chebyshev2.LocalObstruction.sine_right_decay`,
`chebyshev2.SineContinuum.n_positive` with the arguments shown in the proof.
-/
theorem sine_weighted_density_bound {x y : ℝ} (hx : 1≤x) (hxy : x≤y) :
    exp (2*(y-x))*m y≤2025*n x^2*exp (-2*(y-x)) := by
  -- Use the identities/estimates `chebyshev2.LocalObstruction.sine_right_decay`,
  -- `chebyshev2.SineContinuum.n_positive` with the arguments shown in the proof.
  have h := sine_right_decay hx hxy
  have hs := pow_le_pow_left₀ (n_positive y).le h 2
  apply (mul_le_mul_of_nonneg_left hs (exp_pos (2*(y-x))).le).trans_eq
  have he : exp (2*(y-x))*(exp (-2*(y-x)))^2=exp (-2*(y-x)) := by
    rw [pow_two,← mul_assoc,← exp_add]
    rw [show 2*(y-x)+(-2*(y-x))=0 by ring,exp_zero,one_mul]
  calc
    _ = (45*n x)^2*(exp (2*(y-x))*(exp (-2*(y-x)))^2) := by ring
    _ = _ := by rw [he]; ring

 /--
Defines `weightedSineTail` of type `ℝ` by `∫ y in Ioi x, exp (2*(y-x))*m y`.

Use: `chebyshev2.LocalObstruction.sineTailJ` uses this definition in the displayed
construction of `sineTailJ`. Its inputs and component formulas are fixed by that definition.

Article: chebyshev2, Theorem 6.1 via `chebyshev2.LocalObstruction.sine_green_scale_tail`.
-/
def weightedSineTail (x : ℝ) : ℝ := ∫ y in Ioi x, exp (2*(y-x))*m y

 /--
Integrability on the stated domain: `IntegrableOn (fun y => exp (-2*(y-x))) (Ioi x)`.

Use: `chebyshev2.LocalObstruction.weightedSineTail_bounds` uses this integrability result
to establish membership in the specified domain/enclosure: `weightedSineTail x ∈ Icc (0:ℝ)
(2025/2*n x^2)`.

Article: chebyshev2, Theorem 6.1 via `chebyshev2.LocalObstruction.sine_green_scale_tail`.

Proof: Prove equality of functions by evaluating both sides at an arbitrary argument.
-/
theorem sine_exponential_tail_integrable (x : ℝ) :
    IntegrableOn (fun y => exp (-2*(y-x))) (Ioi x) := by
  -- Prove equality of functions by evaluating both sides at an arbitrary argument.
  have he : (fun y => exp (-2*(y-x)))=fun y => exp (2*x)*exp (-2*y) := by
    funext y
    rw [← exp_add]
    congr 1
    ring
  rw [he]
  exact (integrableOn_exp_mul_Ioi (by norm_num : (-2:ℝ)<0) x).const_mul _

 /--
Exact identity `(∫ y in Ioi x, exp (-2*(y-x)))=1/2`.

Use: `chebyshev2.LocalObstruction.weightedSineTail_bounds` rewrites with this identity to
establish membership in the specified domain/enclosure: `weightedSineTail x ∈ Icc (0:ℝ)
(2025/2*n x^2)`.

Article: chebyshev2, Theorem 6.1 via `chebyshev2.LocalObstruction.sine_green_scale_tail`.

Proof: Prove equality of functions by evaluating both sides at an arbitrary argument.
-/
theorem sine_exponential_tail_integral (x : ℝ) :
    (∫ y in Ioi x, exp (-2*(y-x)))=1/2 := by
  -- Prove equality of functions by evaluating both sides at an arbitrary argument.
  have he : (fun y => exp (-2*(y-x)))=fun y => exp (2*x)*exp (-2*y) := by
    funext y
    rw [← exp_add]
    congr 1
    ring
  rw [he,integral_const_mul,integral_exp_mul_Ioi (by norm_num : (-2:ℝ)<0)]
  simp only [mul_neg,neg_div]
  rw [← mul_div_assoc,← exp_add]
  norm_num

 /--
Integrability on the stated domain: `IntegrableOn (fun y => exp (2*(y-x))*m y) (Ioi x)`.

Use: `chebyshev2.LocalObstruction.sineTailJ_bounds` uses this integrability result to
establish membership in the specified domain/enclosure: `sineTailJ x ∈ Icc (0:ℝ) (2025*n x^2)`.

Article: chebyshev2, Theorem 6.1 via `chebyshev2.LocalObstruction.sine_green_scale_tail`.

Proof: Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
at an arbitrary point in that intersection.
-/
theorem weightedSineTail_integrable {x : ℝ} (hx : 1≤x) :
    IntegrableOn (fun y => exp (2*(y-x))*m y) (Ioi x) := by
  apply ((sine_exponential_tail_integrable x).const_mul (2025*n x^2)).mono'
    (by exact (continuous_exp.comp (by fun_prop) |>.mul m_continuous).aestronglyMeasurable.restrict)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
  rw [Real.norm_of_nonneg (mul_nonneg (exp_pos _).le (m_positive y).le)]
  exact sine_weighted_density_bound hx hy.le

 /--
Membership in the specified domain/enclosure: `weightedSineTail x ∈ Icc (0:ℝ) (2025/2*n x^2)`.

Use: `chebyshev2.LocalObstruction.sineTailJ_bounds` uses this assertion to establish
membership in the specified domain/enclosure: `sineTailJ x ∈ Icc (0:ℝ) (2025*n x^2)`.

Article: chebyshev2, Theorem 6.1 via `chebyshev2.LocalObstruction.sine_green_scale_tail`.

Proof: Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
at an arbitrary point in that intersection.
-/
theorem weightedSineTail_bounds {x : ℝ} (hx : 1≤x) :
    weightedSineTail x ∈ Icc (0:ℝ) (2025/2*n x^2) := by
  -- Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
  -- at an arbitrary point in that intersection.
  refine ⟨integral_nonneg (fun y => mul_nonneg (exp_pos _).le (m_positive y).le),?_⟩
  have he := integral_mono_ae (weightedSineTail_integrable hx)
    ((sine_exponential_tail_integrable x).const_mul (2025*n x^2))
    (by filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
        exact sine_weighted_density_bound hx hy.le)
  rw [integral_const_mul,sine_exponential_tail_integral] at he
  convert! he using 1
  ring

 /--
The precise assertion is `weightedSineTail =o[atTop] n`.

Use: `chebyshev2.LocalObstruction.sine_convolution_tail` uses this identity to establish
the stated quantitative bound `(fun x => W₂ m x-sineTraceTailCoefficient*exp (-2*x)) =o[atTop]
n`.

Article: chebyshev2, Theorem 6.1 via
`chebyshev2.LocalObstruction.sine_ground_square_tail`.

Proof: Pass the established inequalities to the limit using the displayed filter convergence.
Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation at an
arbitrary point in that intersection.
-/
theorem weightedSineTail_littleO : weightedSineTail =o[atTop] n := by
  apply (isLittleO_iff_tendsto (fun x hx => ((n_positive x).ne' hx).elim)).mpr
  apply squeeze_zero' _ _ (by simpa only [mul_zero] using sine_amplitude_tendsto_zero.const_mul (2025/2:ℝ))
  · filter_upwards [eventually_ge_atTop (1:ℝ)] with x hx
    exact div_nonneg (weightedSineTail_bounds hx).1 (n_positive x).le
  · filter_upwards [eventually_ge_atTop (1:ℝ)] with x hx
    apply (div_le_iff₀ (n_positive x)).mpr
    nlinarith [(weightedSineTail_bounds hx).2]

 /--
Defines `sineTailJ` of type `ℝ` by `(∫ y in Ioi x, m y)+weightedSineTail x`.

Use: `chebyshev2.LocalObstruction.sineTailJ_bounds` uses this definition to establish
membership in the specified domain/enclosure: `sineTailJ x ∈ Icc (0:ℝ) (2025*n x^2)`.

Article: chebyshev2, Theorem 6.1 via `chebyshev2.LocalObstruction.sine_green_scale_tail`.
-/
def sineTailJ (x : ℝ) : ℝ := (∫ y in Ioi x, m y)+weightedSineTail x

 /--
Membership in the specified domain/enclosure: `sineTailJ x ∈ Icc (0:ℝ) (2025*n x^2)`.

Use: `chebyshev2.LocalObstruction.sineTailJ_littleO` uses this assertion to establish the
precise assertion is `sineTailJ =o[atTop] n`.

Article: chebyshev2, Theorem 6.1 via `chebyshev2.LocalObstruction.sine_green_scale_tail`.

Proof: Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
at an arbitrary point in that intersection.
-/
theorem sineTailJ_bounds {x : ℝ} (hx : 1≤x) :
    sineTailJ x ∈ Icc (0:ℝ) (2025*n x^2) := by
  -- Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
  -- at an arbitrary point in that intersection.
  have htail : (∫ y in Ioi x, m y)≤weightedSineTail x := by
    apply integral_mono_ae m_integrable.integrableOn (weightedSineTail_integrable hx)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    have he : 1≤exp (2*(y-x)) := one_le_exp (by have hxy : x<y := hy; linarith)
    exact le_mul_of_one_le_left (m_positive y).le he
  have hnonneg : 0≤(∫ y in Ioi x, m y) := integral_nonneg (fun y => (m_positive y).le)
  have hb := weightedSineTail_bounds hx
  exact ⟨add_nonneg hnonneg hb.1,by dsimp only [sineTailJ]; linarith [hb.2]⟩

 /--
The precise assertion is `sineTailJ =o[atTop] n`.

Use: `chebyshev2.LocalObstruction.sineJost_reflected_tail` uses this identity to establish
the stated quantitative bound `(fun x => jost s m (-x)-1) =o[atTop] n`.

Article: chebyshev2, Theorem 6.1 via `chebyshev2.LocalObstruction.sine_green_scale_tail`.

Proof: Pass the established inequalities to the limit using the displayed filter convergence.
Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation at an
arbitrary point in that intersection.
-/
theorem sineTailJ_littleO : sineTailJ =o[atTop] n := by
  apply (isLittleO_iff_tendsto (fun x hx => ((n_positive x).ne' hx).elim)).mpr
  apply squeeze_zero' _ _ (by simpa only [mul_zero] using sine_amplitude_tendsto_zero.const_mul (2025:ℝ))
  · filter_upwards [eventually_ge_atTop (1:ℝ)] with x hx
    exact div_nonneg (sineTailJ_bounds hx).1 (n_positive x).le
  · filter_upwards [eventually_ge_atTop (1:ℝ)] with x hx
    apply (div_le_iff₀ (n_positive x)).mpr
    nlinarith [(sineTailJ_bounds hx).2]

 /--
Exact identity `weightedSineTail x=exp (-2*x)*(∫ y in Ioi x, exp (2*y)*m y)`.

Use: `chebyshev2.LocalObstruction.sineTailJ_original_formula` rewrites with this identity
to establish the identity `sineTailJ x=(∫ y in Ioi x, m y)+exp (-2*x)*(∫ y in Ioi x, exp
(2*y)*m y)`.

Article: chebyshev2, Theorem 6.1 via `chebyshev2.LocalObstruction.sine_green_scale_tail`.

Proof: Prove equality of functions by evaluating both sides at an arbitrary argument.
-/
theorem weightedSineTail_original_formula (x : ℝ) :
    weightedSineTail x=exp (-2*x)*(∫ y in Ioi x, exp (2*y)*m y) := by
  -- Prove equality of functions by evaluating both sides at an arbitrary argument.
  rw [weightedSineTail,← integral_const_mul]
  congr 1
  funext y
  rw [← mul_assoc,← exp_add]
  congr 1
  congr 1
  ring

 /--
Exact identity `sineTailJ x=(∫ y in Ioi x, m y)+exp (-2*x)*(∫ y in Ioi x, exp (2*y)*m y)`.

Use: a standalone supporting identity for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: chebyshev2, Theorem 6.1.

Proof: Use the identities/estimates
`chebyshev2.LocalObstruction.weightedSineTail_original_formula` with the arguments shown in
the proof.
-/
theorem sineTailJ_original_formula (x : ℝ) :
    sineTailJ x=(∫ y in Ioi x, m y)+exp (-2*x)*(∫ y in Ioi x, exp (2*y)*m y) := by rw [sineTailJ,weightedSineTail_original_formula]

end
end chebyshev2.LocalObstruction
