import jacobi.Variational.Amplitude
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
Article: jacobi, Lemma D.3.
The 3/2 energy has its genuine derivative along every finite-energy density
direction. A common integrable majorant is proved from the two actual energy
integrands, so no smoothness, bounded support or positive lower bound on
the minimizing density is required.
Source: differentiation under the integral with an integrable derivative bound.
Use: identifies the objective gradient and bounds mixed square-root products.
-/
namespace jacobi.Variational
noncomputable section
open MeasureTheory Real Filter Set
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- The nonnegative 3/2 power is the density times its square root.
Use: identifies the objective gradient and bounds mixed square-root products.
Article: jacobi, Lemma D.3.
Proof: add the exponents one and one half, including at zero. -/
theorem rpow_three_halves {x : ℝ} (hx : 0≤x) : x^(3/2:ℝ)=x*sqrt x := by
  rw [show (3/2:ℝ)=1+1/2 by norm_num,Real.rpow_add_of_nonneg hx (by norm_num) (by norm_num),
    Real.rpow_one,← Real.sqrt_eq_rpow]

/-- Every actual nonzero density has strictly positive finite energy.
Use: excludes a zero spectral multiplier after the objective coefficient has been normalized.
Article: jacobi, Lemma D.3.
Proof: zero energy would make its nonnegative 3/2-power integrand vanish a.e.;
strict positivity of real powers then makes the density and its mass vanish. -/
theorem Density.energy_pos (m : Density) (hm : 0<m.mass) : 0<m.energy := by
  -- The implication is proved from the actual integrals, without a uniform lower density bound.
  apply lt_of_le_of_ne m.energy_nonneg
  intro hz
  have he := (integral_eq_zero_iff_of_nonneg (fun x => Real.rpow_nonneg (m.nonneg x) _)
    m.energy_integrable).mp hz.symm
  have ha : m.value=ᵐ[volume] 0 := by
    filter_upwards [he] with x hx
    by_contra h
    have hp : 0<m.value x := lt_of_le_of_ne (m.nonneg x) (Ne.symm h)
    exact (Real.rpow_pos_of_pos hp (3/2:ℝ)).ne' hx
  have hmass : m.mass=0 := by simpa only [Density.mass,Pi.zero_apply,integral_zero] using integral_congr_ae ha
  exact hm.ne' hmass

/-- Every mixed square-root density product is bounded by the two energy integrands.
Use: proves integrability of the objective's linear variation and its dominated derivative bound.
Article: jacobi, Lemma D.3.
Proof: if x<=y use sqrt(x)<=sqrt(y), and otherwise use y<=x. -/
theorem sqrt_product_energy_bound {x y : ℝ} (hx : 0≤x) (hy : 0≤y) :
    sqrt x*y≤x^(3/2:ℝ)+y^(3/2:ℝ) := by
  rw [rpow_three_halves hx,rpow_three_halves hy]
  rcases le_total x y with hxy | hyx
  · have h := mul_le_mul_of_nonneg_right (sqrt_le_sqrt hxy) hy
    nlinarith [mul_nonneg hx (sqrt_nonneg x)]
  · have h := mul_le_mul_of_nonneg_left hyx (sqrt_nonneg x)
    nlinarith [mul_nonneg hy (sqrt_nonneg y)]

/-- The actual objective gradient pairs integrably with every density difference.
Use: defines the finite objective coordinate of the multiplier separation cone.
Article: jacobi, Lemma D.3.
Proof: dominate its absolute value by two copies of the base energy integrand plus the competitor energy. -/
theorem energyVariation_integrable (m q : Density) :
    Integrable (fun x => sqrt (m.value x)*(q.value x-m.value x)) := by
  -- Two base-energy terms and one competitor-energy term dominate the absolute mixed variation.
  apply ((m.energy_integrable.const_mul 2).add q.energy_integrable).mono'
  · exact (m.measurable.sqrt.mul (q.measurable.sub m.measurable)).aestronglyMeasurable
  · exact Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (sqrt_nonneg _)]
      change sqrt (m.value x)*|q.value x-m.value x|≤2*m.value x^(3/2:ℝ)+q.value x^(3/2:ℝ)
      have hd : |q.value x-m.value x|≤q.value x+m.value x :=
        (abs_sub _ _).trans_eq (by rw [abs_of_nonneg (q.nonneg x),abs_of_nonneg (m.nonneg x)])
      have h := mul_le_mul_of_nonneg_left hd (sqrt_nonneg (m.value x))
      have he := sqrt_product_energy_bound (m.nonneg x) (q.nonneg x)
      rw [rpow_three_halves (m.nonneg x)] at *
      nlinarith

/-- A uniform integrable bound for every pointwise objective derivative near zero.
Use: licenses differentiation under the energy integral for arbitrary finite-energy competitors.
Article: jacobi, Lemma D.3.
Proof: abs(m+t*(q-m))<=2*(m+q) for abs(t)<=1; its square root is at most
2*(sqrt(m)+sqrt(q)). Each resulting mixed term is bounded by the two energy integrands. -/
theorem energyVariation_derivative_bound {a b t : ℝ} (ha : 0≤a) (hb : 0≤b) (ht : |t|≤1) :
    |(b-a)*(3/2:ℝ)*(a+t*(b-a))^(1/2:ℝ)|≤9*(a^(3/2:ℝ)+b^(3/2:ℝ)) := by
  -- A coarse homogeneous energy majorant suffices and remains integrable over the full line.
  have hd : |b-a|≤a+b := by simpa only [abs_of_nonneg ha,abs_of_nonneg hb,add_comm] using abs_sub b a
  have hv : |a+t*(b-a)|≤2*(a+b) := by
    have h := abs_add_le a (t*(b-a))
    rw [abs_of_nonneg ha,abs_mul] at h
    have hm := mul_le_mul_of_nonneg_right ht (abs_nonneg (b-a))
    nlinarith
  have hs : |(a+t*(b-a))^(1/2:ℝ)|≤2*(sqrt a+sqrt b) := by
    apply (abs_rpow_le_abs_rpow _ _).trans
    rw [← sqrt_eq_rpow]
    have hroot := Real.sq_sqrt (abs_nonneg (a+t*(b-a)))
    nlinarith [Real.sq_sqrt ha,Real.sq_sqrt hb,Real.sqrt_nonneg |a+t*(b-a)|,
      Real.sqrt_nonneg a,Real.sqrt_nonneg b,mul_nonneg (sqrt_nonneg a) (sqrt_nonneg b)]
  rw [abs_mul,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<3/2)]
  have hbound := mul_le_mul (mul_le_mul_of_nonneg_right hd (by norm_num : (0:ℝ)≤3/2)) hs
    (abs_nonneg _) (by positivity : 0≤(a+b)*(3/2:ℝ))
  have hmix1 := sqrt_product_energy_bound ha hb
  have hmix2 := sqrt_product_energy_bound hb ha
  rw [rpow_three_halves ha,rpow_three_halves hb] at *
  nlinarith

/-- The actual energy integral has the article's derivative along every finite-energy density direction.
Use: supplies the objective first variation in the full cone multiplier proof.
Article: jacobi, Lemma D.3.
Proof: differentiate the scalar 3/2 power at every point, including where
m=0. The proved homogeneous integrable bound allows the derivative to
pass through the Lebesgue integral and identifies its square-root formula. -/
theorem energy_hasDerivAt (m q : Density) :
    HasDerivAt (fun t : ℝ => ∫ x,(m.value x+t*(q.value x-m.value x))^(3/2:ℝ))
      ((3/2:ℝ)*(∫ x,sqrt (m.value x)*(q.value x-m.value x))) 0 := by
  -- The derivative bound works on a two-sided neighborhood, even though admissible density paths are one-sided.
  let F (t x : ℝ) := (m.value x+t*(q.value x-m.value x))^(3/2:ℝ)
  let D (t x : ℝ) := (q.value x-m.value x)*(3/2:ℝ)*(m.value x+t*(q.value x-m.value x))^(1/2:ℝ)
  let B (x : ℝ) := 9*(m.value x^(3/2:ℝ)+q.value x^(3/2:ℝ))
  have hFmeas : ∀ᶠ t : ℝ in 𝓝 0,AEStronglyMeasurable (F t) volume :=
    Eventually.of_forall fun t =>
      ((m.measurable.add (measurable_const.mul (q.measurable.sub m.measurable))).pow_const
        (3/2:ℝ)).aestronglyMeasurable
  have hFint : Integrable (F 0) := by simpa only [F,zero_mul,add_zero] using m.energy_integrable
  have hDmeas : AEStronglyMeasurable (D 0) volume := by
    simp only [D,zero_mul,add_zero]
    exact (((q.measurable.sub m.measurable).mul measurable_const).mul
      (m.measurable.pow_const (1/2:ℝ))).aestronglyMeasurable
  have hB : Integrable B := (m.energy_integrable.add q.energy_integrable).const_mul 9
  have hdiff : ∀ᵐ x : ℝ,∀ t∈Ioo (-1:ℝ) 1,HasDerivAt (fun t => F t x) (D t x) t :=
    Eventually.of_forall fun x t _ => by
      convert (((hasDerivAt_const t (m.value x)).add
        ((hasDerivAt_id t).mul_const (q.value x-m.value x))).rpow_const
          (Or.inr (by norm_num : (1:ℝ)≤3/2))) using 1 <;> norm_num [F,D]
  have hbound : ∀ᵐ x : ℝ,∀ t∈Ioo (-1:ℝ) 1,‖D t x‖≤B x :=
    Eventually.of_forall fun x t ht => by
      rw [Real.norm_eq_abs]
      exact energyVariation_derivative_bound (m.nonneg x) (q.nonneg x)
        (abs_le.mpr ⟨ht.1.le,ht.2.le⟩)
  have h := (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Ioo_mem_nhds (by norm_num : (-1:ℝ)<0) zero_lt_one)
    hFmeas hFint hDmeas hbound hB hdiff).2
  convert h using 1
  rw [← integral_const_mul]
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by
    dsimp only [D]
    rw [zero_mul,add_zero,← sqrt_eq_rpow]
    ring

end
end jacobi.Variational
